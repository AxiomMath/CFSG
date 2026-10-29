module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExc
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSylowTorus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley

@[expose] def GGOrdPToralF4RestHard : Prop :=
  ∀ f : ℕ, 1 ≤ f →
    (∃ A : Subgroup (adjointGroup .F4 (GaloisField 2 f)), IsElemAbelian 3 A ∧
      3 ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (adjointGroup .F4 (GaloisField 2 f)) 3

section Reduction


theorem ggOrdPToralF4Rest_of_hard (h : GGOrdPToralF4RestHard) : GGOrdPToralF4Rest := by
  intro f p hf hp hp2 hsplit hA
  by_cases hp3 : p = 3
  · subst hp3
    exact h f hf hA
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    push Not at hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  haveI : Finite (adjointGroup .F4 (GaloisField 2 f)) := generated_group_finite .F4 _
  by_cases h1 : p ∣ 2 ^ f - 1
  · exact absurd ⟨hp5, h1⟩ hsplit
  by_cases h2 : p ∣ 2 ^ f + 1
  · have he : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) = 2 := by
      rw [hK]
      exact OrdPInnerExc.orderOf_natCast_eq_two_of_dvd_add_one hp hp2 h2
    exact OrdPInnerExc.ggOrdPToralMax_of_sylowTorus
      (OrdPInnerExc.sylowTorus_F4_two (GaloisField 2 f) hp (by omega) he)
  · obtain ⟨A, hAel, hAc⟩ := hA
    exact absurd hAc (not_le.2 (ggExcNonsplitRankInput_F4 (GaloisField 2 f) p hp hp2
      (by rw [hK]; exact h1) (by rw [hK]; exact h2) A hAel))

end Reduction

end CFSG.StandardType
