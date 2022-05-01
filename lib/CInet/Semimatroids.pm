# ABSTRACT: Check semimatroidality
package CInet::Semimatroids;

use Modern::Perl 2018;
use utf8::all;
use Export::Attrs;

use CInet::Base;
use CInet::Imset;
use CInet::Cube::Polyhedral;
use CInet::Bridge::SoPlex qw(soplex);

use List::Util qw(uniq);
use Array::Set qw(set_union set_intersect set_diff);
use Path::Tiny qw(path tempdir);
use IPC::Run3;

my $tempdir = tempdir;

sub h {
    my $cube = shift;
    my $h = [ map 0, $cube->vertices ];
    while (@_) {
        my $K = shift;
        my $v = shift // warn 'uneven number of arguments';
        $h->[ $cube->pack([ [], $K ])-1 ] = $v;
    }
    $h
}

use CInet::Hash::FaceKey;
tie my %LPS, 'CInet::Hash::FaceKey';
sub tight_polymatroids {
    # Cache the costly operation of writing the polymatroid $h component
    # of a linear constraint in the syntax of SoPlex.
    sub prepare_system {
        map {
            my ($h, $rel, $val) = @$_;
            my @c;
            for my $i (0 .. $h->$#*) {
                next if $h->[$i] == 0;
                my $a = abs($h->[$i]);
                push @c, ($h->[$i] < 0 ? '-' : '+'), $a, "x$i";
            }
            [ join(' ', @c), $rel, $val ]
        } @_
    }

    my $cube = shift;
    $LPS{[ $cube->set, [] ]} //= do {
        my $N = $cube->set;
        my @system;

        push @system, [ h($cube, [] => +1), '=', 0 ];

        for my $i (@$N) {
            my $K = set_diff($N, [$i]);
            push @system, [ h($cube, $N => +1, $K => -1), '=', 0 ];
        }

        for my $ijK ($cube->squares) {
            my ($i, $j, $K) = ($ijK->[0][0], $ijK->[0][1], $ijK->[1]);
            my $iK = set_union($K, [$i]);
            my $jK = set_union($K, [$j]);
            push @system, [ h($cube,
                    $iK => +1, $jK => +1,
                    set_intersect($iK, $jK) => -1,
                    set_union($iK, $jK) => -1,
                ), '>=', 0 ];
        }

        [ prepare_system @system ]
    }
}

# The relative interior of the face of the given CI structure.
sub face_for {
    my $G = shift;
    my @constr = map { [@$_] } @_; # deep copy
    my $cube = $G->cube;

    my $i = 1 + $cube->set->@*;
    for my $ijK ($cube->squares) {
        my $v = $G->cival($ijK);
        $constr[$i]->[1] = '=' if $v eq 0;
        $constr[$i]->[2] = '1' if $v eq 1;
        $i++;
    }

    @constr
}

sub modify_face {
    my ($cube, $ijK, $v, $system) = @_;
    my $i = $cube->set->@* + $cube->pack($ijK);
    $system->[$i]->[1] = '=' if $v eq 0;
    $system->[$i]->[2] = '1' if $v eq 1;
}

sub is_feasible {
    my $cube = shift;

    my $name = join '', map { sprintf "%x", rand 16 } 1..12;
    my $in  = $tempdir->child("$name.in");

    my $fh = $in->openw_utf8;
	say {$fh} "Maximize";
	say {$fh} " obj: 1";
    say {$fh} "Subject To";
    say {$fh} ' ' . join(' ', @$_) for @_;
    say {$fh} "End";
    close $fh;

    my $status;
    my $reader = sub {
        my $line = shift;
        $status = $line if $line =~ /^SoPlex status/;
    };
    run3 [soplex, '-f0', $in->realpath], \undef, $reader, \undef;
    die 'did not receive an answer from soplex' if not defined($status);

    $status !~ /infeasible/
}

sub is_semimatroid :Export(:DEFAULT) {
    my $A = shift;
    my $cube = $A->cube;
    my $H = tight_polymatroids($cube);
    is_feasible($cube => face_for($A, @$H))
}

sub semimatroid_completion :Export(:DEFAULT) {
    my $A = shift;
    my $cube = $A->cube;
    my $H = tight_polymatroids($cube);

    # Relax all non-containments to unspecified
    my $B = $A->clone;
    for my $ijK ($cube->squares) {
        $B->cival($ijK) = '*' unless $A->cival($ijK) eq 0;
    }
    # This defines the closed face of $A
    my @system = face_for($B, @$H);

    my $C = $A->clone;
    for my $ijK ($cube->squares) {
        next if $A->cival($ijK) eq 0;

        my @impl = @system; # deep copy
        modify_face($cube, $ijK, 1, \@impl);
        my $feas = is_feasible($cube => @impl);
        # Not feasible means $ijK is implied:
        $C->cival($ijK) = 0 if not $feas;
    }
    $C
}

":wq"
