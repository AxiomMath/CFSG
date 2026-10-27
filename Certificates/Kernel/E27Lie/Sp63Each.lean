module

public import Certificates.Kernel.E27Lie.Sp63Data
public import Certificates.Data.Kernel.E27Lie.Defs
public import Certificates.Data.Kernel.Spor.Row

public section

namespace CertificateChecks.KernelE27Lie.Sp63

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KS.Row

@[expose] noncomputable def L : Nat :=
  nat_lit 1671623677278685503141555994978895751093572942865858908798586945

@[expose] noncomputable def H : Nat :=
  nat_lit 53491957672917936100529791839324664034994334171707485081554782240

@[expose] noncomputable def CM : Nat :=
  nat_lit 96547219075955945024103736637267007212033175418715504703

@[expose] noncomputable def RM : Nat := nat_lit 68719476735

@[expose] noncomputable def ONE : Nat :=
  nat_lit 1645504557321580186574125978775002378553869913044102104863473665

@[expose] noncomputable def LV : Nat := nat_lit 1090785345

@[expose] noncomputable def HV : Nat := nat_lit 34905131040

@[expose] noncomputable def mm (X Y : Nat) : Nat :=
  mulR (nat_lit 3) (nat_lit 6) (nat_lit 36) (nat_lit 6) (nat_lit 3) L H CM RM X Y

@[expose] noncomputable def gk (j : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 0),
    nat_lit 1645504557321591878587224625998348008032531643308259352323817537,
    nIf(Nat.beq j (nat_lit 1),
      nat_lit 1696926574737867875391468765729919581834580408845432950569828353,
      nat_lit 1645504557321580186574125978775007449156270825961708091676295169))

@[expose] noncomputable def tb (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) TF o i

@[expose] noncomputable def key (i : Nat) : Nat :=
  rg (nat_lit 256)
    (nat_lit 115792089237316195423570985008687907853269984665640564039457584007913129639935)
    KF (nat_lit 0) i

@[expose] noncomputable def pp (i : Nat) : Nat := tb (nat_lit 0) i

@[expose] noncomputable def pj (i : Nat) : Nat := tb (nat_lit 616) i

@[expose] noncomputable def lt (j i : Nat) : Nat :=
  tb (Nat.add (nat_lit 1232) (Nat.mul (nat_lit 616) j)) i

@[expose] noncomputable def sg (q : Nat) : Nat := tb (nat_lit 3080) q

@[expose] noncomputable def W (a : Nat) : Nat := tb (nat_lit 3696) a

@[expose] noncomputable def CI (a : Nat) : Nat := tb (nat_lit 4312) a

@[expose] noncomputable def REP (c : Nat) : Nat := tb (nat_lit 4928) c

@[expose] noncomputable def CB (c : Nat) : Nat := tb (nat_lit 4934) c

@[expose] noncomputable def cw (c t : Nat) : Nat :=
  tb (nat_lit 4940) (Nat.add (Nat.mul (nat_lit 81) c) t)

@[expose] noncomputable def ch131008tree (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 19683) (fun i => bAnd(treeC mm key pp pj gk ONE (nat_lit 3) i,
    allN (nat_lit 3) fun j => leftC mm key lt gk (nat_lit 19683) j i)) q

@[expose] noncomputable def ch131008sort (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 19683) (sortC key sg (nat_lit 19683)) q

@[expose] noncomputable def ch131008kill (q : Nat) : Bool :=
  blkC (nat_lit 16) (nat_lit 19683) (killC mm key W CI REP (nat_lit 19683) (nat_lit 163)) q

@[expose] noncomputable def ch131008rep (c : Nat) : Bool :=
  repC mm key REP CB cw ONE (nat_lit 19683) (nat_lit 81) c

end CertificateChecks.KernelE27Lie.Sp63

end
