module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin CFSG.Open
open scoped commutatorElement Pointwise

variable {Q : Type} [Group Q] [Finite Q]

theorem isEP_one_of_pSubgroup {T A P : Subgroup Q} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hT : IsSylowIn 2 T (⊤ : Subgroup Q)) (hAT : A ≤ T)
    (hA : CFSG.Open.IsElemAbelian 2 A)
    (hP : IsPGroup p P) (hPne : P ≠ ⊥)
    (hτP : CFSG.Quasithin.E1.tauOf (⊤ : Subgroup Q) T A ≤
      Subgroup.normalizer (P : Set Q))
    (hcomm : ⁅P, A⁆ = P)
    (hidx : (A ⊓ Subgroup.centralizer (P : Set Q)).relIndex A ≤ 2) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsEP 1 (⊤ : Subgroup Q) T A
      (P ⊔ CFSG.Quasithin.E1.tauOf (⊤ : Subgroup Q) T A) := by
  have h := CFSG.Quasithin.E1.isE_one_sup hp hp2 hT hAT hA hP hPne hτP hcomm
    (inf_le_left : A ⊓ Subgroup.centralizer (P : Set Q) ≤ A)
    (inf_le_right : A ⊓ Subgroup.centralizer (P : Set Q) ≤
      Subgroup.centralizer (P : Set Q)) hidx
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, Or.inl ⟨h.2.1, h.2.2⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

end
