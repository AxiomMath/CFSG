module

public import Certificates.Kernel.E27Lie.Co3Data
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.E27Lie.Defs
public import Certificates.Data.Kernel.Spor.Row

public section

namespace CertificateChecks.KernelE27Lie.Co3

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KS.Row CertificateChecks.KernelSpor

@[expose] noncomputable def mm (X Y : Nat) : Nat := pcomp (nat_lit 276) (nat_lit 9) (nat_lit 511) X Y

@[expose] noncomputable def ONE : Nat := pidn (nat_lit 276) (nat_lit 9)

@[expose] noncomputable def tb (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) TF o i

@[expose] noncomputable def key (i : Nat) : Nat := KF i

@[expose] noncomputable def gk (j : Nat) : Nat := KF (Nat.succ j)

@[expose] noncomputable def pp (i : Nat) : Nat := tb (nat_lit 0) i

@[expose] noncomputable def pj (i : Nat) : Nat := tb (nat_lit 69) i

@[expose] noncomputable def lt (j i : Nat) : Nat :=
  tb (Nat.add (nat_lit 138) (Nat.mul (nat_lit 69) j)) i

@[expose] noncomputable def sg (q : Nat) : Nat := tb (nat_lit 414) q

@[expose] noncomputable def W (a : Nat) : Nat := tb (nat_lit 483) a

@[expose] noncomputable def CI (a : Nat) : Nat := tb (nat_lit 552) a

@[expose] noncomputable def REP (c : Nat) : Nat := tb (nat_lit 621) c

@[expose] noncomputable def CB (c : Nat) : Nat := tb (nat_lit 625) c

@[expose] noncomputable def cw (c t : Nat) : Nat :=
  tb (nat_lit 629) (Nat.add (Nat.mul (nat_lit 81) c) t)

@[expose] noncomputable def wlen (j : Nat) : Nat := tb (nat_lit 900) j

@[expose] noncomputable def wl (j t : Nat) : Nat :=
  tb (Nat.add (nat_lit 901) (Nat.mul (nat_lit 7) j)) t

@[expose] noncomputable def letK (x : Nat) : Nat :=
  nIf(Nat.beq x (nat_lit 0), Co3C.S (nat_lit 0), Co3C.S (nat_lit 1))

@[expose] noncomputable def wordK (j k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE (fun t acc => mm acc (letK (wl j t))) k

@[expose] noncomputable def ch131000tree (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 2187) (fun i => bAnd(treeC mm key pp pj gk ONE (nat_lit 4) i,
    allN (nat_lit 4) fun j => leftC mm key lt gk (nat_lit 2187) j i)) q

@[expose] noncomputable def ch131000sort (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 2187) (sortC key sg (nat_lit 2187)) q

@[expose] noncomputable def ch131000kill (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 2187) (killC mm key W CI REP (nat_lit 2187) (nat_lit 107)) q

@[expose] noncomputable def ch131000rep (c : Nat) : Bool :=
  repC mm key REP CB cw ONE (nat_lit 2187) (nat_lit 81) c

@[expose] noncomputable def ch131000word (j : Nat) : Bool :=
  Nat.beq (wordK j (wlen j)) (gk j)

end CertificateChecks.KernelE27Lie.Co3

end
