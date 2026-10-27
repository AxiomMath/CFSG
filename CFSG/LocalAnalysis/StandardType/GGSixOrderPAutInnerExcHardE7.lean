module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExc
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSylowTorus
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration

@[expose] def GGOrdPToralE7RestHard : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → p ≤ 7 → (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    (∃ A : Subgroup (adjointGroup .E7 (GaloisField 2 f)), IsElemAbelian p A ∧
      p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (adjointGroup .E7 (GaloisField 2 f)) p

section Reduction


theorem ggOrdPToralE7Rest_of_hard (h : GGOrdPToralE7RestHard) : GGOrdPToralE7Rest := by
  intro f p hf hp hp2 hsplit hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  haveI : Finite (adjointGroup .E7 (GaloisField 2 f)) := generated_group_finite .E7 _
  have hpq : ¬ p ∣ Nat.card (GaloisField 2 f) := by
    rw [hK]
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  by_cases h1 : p ∣ 2 ^ f - 1
  · by_cases hp11 : 11 ≤ p
    · exact absurd ⟨hp11, h1⟩ hsplit
    · exact h f p hf hp hp2 (OrdPInnerExc.prime_le_seven_of_lt_eleven hp (by omega)) (Or.inl h1) hA
  by_cases h2 : p ∣ 2 ^ f + 1
  · by_cases hp11 : 11 ≤ p
    · have he : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) = 2 := by
        rw [hK]
        exact OrdPInnerExc.orderOf_natCast_eq_two_of_dvd_add_one hp hp2 h2
      obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sylowTorus_E7 (GaloisField 2 f) hp (by omega) hpq
        (by rw [he]; decide) (Or.inl hp11)
      exact OrdPInnerExc.ggOrdPToralMax_of_sylowTorus hm
    · exact h f p hf hp hp2 (OrdPInnerExc.prime_le_seven_of_lt_eleven hp (by omega)) (Or.inr h2) hA
  · obtain ⟨A, hAel, hAc⟩ := hA
    exact absurd hAc (not_le.2 (ggExcNonsplitRankInput_E7 (GaloisField 2 f) p hp hp2
      (by rw [hK]; exact h1) (by rw [hK]; exact h2) A hAel))

end Reduction

end CFSG.StandardType
