module

public import Certificates.Data.Kernel.Sp62Pk
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCodes
public import Mathlib

public section

namespace CFSG.KD.Sp62

@[expose] noncomputable def PW (A n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE (fun _ acc => MULF acc A) n

@[expose] noncomputable def VC (Z0 Z1 Z2 a b c : Nat) : Nat :=
  MULF (MULF (PW Z0 a) (PW Z1 b)) (PW Z2 c)

@[expose] noncomputable def J6 : Nat := 4328915976

@[expose] noncomputable def pairN (A B T : Nat) : Bool :=
  Nat.beq (MULF A B) ONE && Nat.beq (MULF B A) ONE && Nat.beq (MULF (MULF T J6) A) J6

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two in
@[expose] noncomputable def pairT (cc : List Nat × List Nat) : Bool :=
  canon6 cc.1 && canon6 cc.2 && canon6 (tr6 cc.1) && pairN (pk cc.1) (pk cc.2) (pk (tr6 cc.1))

end CFSG.KD.Sp62

end
