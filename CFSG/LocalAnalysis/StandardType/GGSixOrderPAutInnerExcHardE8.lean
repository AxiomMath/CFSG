module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExc
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSylowTorus
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE8
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration

@[expose] def GGOrdPToralE8RestHard : Prop :=
  ∀ f p : ℕ, 1 ≤ f → p.Prime → p ≠ 2 → p ≤ 7 →
    (p = 5 ∨ p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    (∃ A : Subgroup (adjointGroup .E8 (GaloisField 2 f)), IsElemAbelian p A ∧
      p ^ 4 ≤ Nat.card A) →
      GGOrdPToralMax (adjointGroup .E8 (GaloisField 2 f)) p

section Reduction


theorem ggOrdPToralE8Rest_of_hard (h : GGOrdPToralE8RestHard) : GGOrdPToralE8Rest := by
  intro f p hf hp hp2 hsplit hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  haveI : Finite (adjointGroup .E8 (GaloisField 2 f)) := generated_group_finite .E8 _
  have hpq : ¬ p ∣ Nat.card (GaloisField 2 f) := by
    rw [hK]
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  by_cases hhard : p ≤ 7 ∧ (p = 5 ∨ p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1)
  · exact h f p hf hp hp2 hhard.1 hhard.2 hA
  have hp7 : 7 ≤ p := by
    by_contra hlt
    have h2' := hp.two_le
    have h6 : p ≤ 6 := by omega
    interval_cases p
    · exact hp2 rfl
    · refine hhard ⟨by norm_num, Or.inr ?_⟩
      have hx : ¬ 3 ∣ 2 ^ f := fun hd =>
        absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
          (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
      have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    · exact absurd hp (by norm_num)
    · exact hhard ⟨by norm_num, Or.inl rfl⟩
    · exact absurd hp (by norm_num)
  have hsmall : 11 ≤ p ∨ 3 ≤ orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) := by
    by_cases h11 : 11 ≤ p
    · exact Or.inl h11
    · have hp7' : p ≤ 7 := OrdPInnerExc.prime_le_seven_of_lt_eleven hp (by omega)
      refine Or.inr (PRankBounds.three_le_orderOf hp hpq Nat.card_pos ?_ ?_)
      · rw [hK]
        exact fun hd => hhard ⟨hp7', Or.inr (Or.inl hd)⟩
      · rw [hK]
        exact fun hd => hhard ⟨hp7', Or.inr (Or.inr hd)⟩
  by_cases hc : 3 ≤ degCount Tag.E8 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p))
  · obtain ⟨m, hm⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_sylowTorus_E8
      (GaloisField 2 f) hp hp7 hpq hc hsmall
    exact OrdPInnerExc.ggOrdPToralMax_of_sylowTorus hm
  · exfalso
    obtain ⟨A, hAel, hAc⟩ := hA
    have hp1 : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    have hp2' : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    by_cases h1c : degCount Tag.E8 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) ≤ 1
    · have hle := rankLE1_E8 (GaloisField 2 f) hp hpq h1c A hAel
      rw [pow_one] at hp1
      omega
    · have h2c : degCount Tag.E8 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) = 2 := by
        omega
      have hle :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_E8_of_degCount_eq_two
          (GaloisField 2 f) hp h2c A hAel
      omega

end Reduction

end CFSG.StandardType
