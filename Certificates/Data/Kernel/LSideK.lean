module

public import Certificates.Data.Kernel.Sp6A2K
public import Certificates.Data.Kernel.Sp62Twin
public import Certificates.Data.FF81Am6LSide

public section

namespace CFSG.KD.LSide

open CFSG.KD.Sp62 CFSG.KD.Sp6A2 CFSG.KC.Loop
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData

@[expose] noncomputable def sigK (Z0 S k : Nat) : Nat := MULF (MULF (PW Z0 k) S) (PW Z0 (3 - k))

@[expose] noncomputable def letL (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def allNL (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => Bool.rec (motive := fun _ => Bool) false acc (f i)) m

@[expose] noncomputable def admP (Z2 V VI S0 S1 S2 x : Nat) : Bool :=
  !(Nat.beq (MULF x x) ONE && Nat.beq (MULF x Z2) (MULF Z2 x) && Nat.beq (MULF x V) (MULF VI x)) ||
    Nat.beq x S0 || Nat.beq x S1 || Nat.beq x S2

@[expose] noncomputable def admK (R : Nat → Nat) (o n Z2 V VI S0 S1 S2 : Nat) : Bool :=
  letL Z2 fun Z2 => letL V fun V => letL VI fun VI => letL S0 fun S0 => letL S1 fun S1 =>
    letL S2 fun S2 => allNL n fun t => letL (recX R o t) fun x => admP Z2 V VI S0 S1 S2 x

@[expose] noncomputable def cnt3K (R : Nat → Nat) (o n A B C hi : Nat) : Nat :=
  sumBelow n hi fun t =>
    nIf(commF (recX R o t) A && commF (recX R o t) B && commF (recX R o t) C, 1, 0)

@[expose] noncomputable def frameK (p₁ p₂ p₃ : Fin 3) (a₁ a₂ a₃ : Nat) : Bool :=
  pairT (rhoC p₁ p₂ p₃ a₁ a₂ a₃, rhoIC p₁ p₂ p₃ a₁ a₂ a₃) &&
    Nat.beq (MULF (MULF (pk (rhoC p₁ p₂ p₃ a₁ a₂ a₃)) (PW (pk (zCode p₁)) a₁))
      (pk (rhoIC p₁ p₂ p₃ a₁ a₂ a₃))) (pk (zCode 2)) &&
    Nat.beq (MULF (MULF (pk (rhoC p₁ p₂ p₃ a₁ a₂ a₃)) (PW (pk (zCode p₂)) a₂))
      (pk (rhoIC p₁ p₂ p₃ a₁ a₂ a₃))) (pk (zCode 0)) &&
    Nat.beq (MULF (MULF (pk (rhoC p₁ p₂ p₃ a₁ a₂ a₃)) (PW (pk (zCode p₃)) a₃))
      (pk (rhoIC p₁ p₂ p₃ a₁ a₂ a₃))) (pk (zCode 1))

@[expose] noncomputable def frameCheckK : Bool :=
  (List.finRange 3).all fun p₁ => (List.finRange 3).all fun p₂ => (List.finRange 3).all fun p₃ =>
    [1, 2].all fun a₁ => [1, 2].all fun a₂ => [1, 2].all fun a₃ =>
      !(p₁ != p₂ && p₂ != p₃ && p₁ != p₃) || frameK p₁ p₂ p₃ a₁ a₂ a₃

end CFSG.KD.LSide
