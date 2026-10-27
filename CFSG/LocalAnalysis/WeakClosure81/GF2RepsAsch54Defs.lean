module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

@[expose] def Asch54Case (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L T : Subgroup Q), CFSG.Open.IsKGroup Q → L.Normal →
    IsSimpleGroup ↥L → (∃ a b : ↥L, a * b ≠ b * a) →
    Subgroup.centralizer (L : Set Q) = ⊥ → P ↥L → ¬ IsCalL0 ↥L →
    IsSylowIn 2 T ⊤ → ¬ HasUniqueMaxOver T →
    lGen IsCalL0 ⊤ T = ⊤ ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (perfectCore (⊤ : Subgroup Q)) ∧
        1 < CFSG.Open.pRank p (lGen IsCalL0 ⊤ T)

@[expose] def Asch54Chev2 : Prop := Asch54Case fun X _ => CFSG.Models.EvenLieType X

@[expose] def Asch54Alt : Prop :=
  Asch54Case fun X _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def Asch54Spor : Prop := Asch54Case fun X _ => CFSG.Models.SporadicRep X

@[expose] def Asch54ChevOdd : Prop := Asch54Case fun X _ => CFSG.Models.OddLieType X

end CFSG.LocalAnalysis.WeakClosure81

end
