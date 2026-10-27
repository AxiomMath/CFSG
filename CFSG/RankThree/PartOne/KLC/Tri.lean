module

public import CFSG.RankThree.PartOne.KLC.TriTorus
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion
public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.RankThree.PartOne.S11d.LieCentralizerTags

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)


section Main


theorem lieGoodComponentFixT_trialityD4_of : LieGoodComponentFixT .trialityD4 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  obtain ⟨-, hCEM⟩ := lieModel_trialityD4_iff.mp hM
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hCEM.2
  have hK : Nat.card K = (2 ^ (p * f₀)) ^ 3 := hKcard
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv T e.toEquiv
  have hx' : orderOf (e x) = p := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hxp hx1
  have hy2' : (e y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hxy' : e x * e y = e y * e x := by rw [← map_mul, ← map_mul, hxy]
  have hpr' : CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = 1 := by
    rw [← pRank_congr_mulEquiv e hp.one_lt]
    exact hpr
  have hdvd : p ∣ Nat.card T := by
    have := orderOf_dvd_natCard x
    rwa [orderOf_eq_prime hxp hx1] at this
  have hq1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_two_pow
  obtain ⟨m, hm, hpm⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp (by omega)
    (by omega) hCEM).1 hdvd).2.2.2.2 rfl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  ·
    have h1 : p ∣ 2 ^ (p * f₀) - 1 := by
      refine Int.natCast_dvd_natCast.1 ?_
      rw [Nat.cast_sub hq1]
      simpa [exhaustionPhi] using hpm
    have := two_le_pRank_triality_phi1 (σ := σ.toRingHom)
      ⟨hp, hp5, hf, hK, hσ, h1⟩
    omega
  ·
    have := two_le_pRank_triality_phi2 (ℓ := 2) hf hK σ hσ hp (by omega)
      (by simpa [exhaustionPhi] using hpm)
    omega
  ·
    have := two_le_pRank_triality_phi36 (ℓ := 2) hf hK σ hσ (ε := 1) (Or.inl rfl) hp
      (by simpa [exhaustionPhi] using hpm)
    omega
  ·
    have := two_le_pRank_triality_phi36 (ℓ := 2) hf hK σ hσ (ε := -1) (Or.inr rfl) hp
      (by convert hpm using 1; simp [exhaustionPhi]; ring)
    omega
  ·
    obtain ⟨T₀, -, -, hcent⟩ := triality_cyclotomic_twelve_torus_and_prime_centralizers
      (ℓ := 2) (f := p * f₀) Nat.prime_two hf K hK σ hσ
    have hle : (2 ^ (p * f₀)) ^ 2 ≤ (2 ^ (p * f₀)) ^ 4 :=
      Nat.pow_le_pow_right (Nat.one_le_two_pow) (by norm_num)
    have h12 : p ∣ (2 ^ (p * f₀)) ^ 4 - (2 ^ (p * f₀)) ^ 2 + 1 := by
      refine Int.natCast_dvd_natCast.1 ?_
      push_cast [Nat.cast_sub hle]
      simpa [exhaustionPhi] using hpm
    obtain ⟨-, -, hx12⟩ := hcent p hp (by omega) h12
    obtain ⟨g, -, -, -, hodd⟩ := hx12 (e x) hx'
    have htc : e y ∈ Subgroup.centralizer ({e x} : Set (graphFixedRootGroup TwistTag.D4 K
        σ.toRingHom)) := Subgroup.mem_centralizer_singleton_iff.2 hxy'.symm
    have ht2' : orderOf (e y) = 2 := orderOf_eq_prime hy2' hy1'
    have h2 := Subgroup.orderOf_dvd_natCard _ htc
    rw [ht2'] at h2
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨j, hj⟩ := h2
    omega

end Main

theorem lieGoodComponentFixT_trialityD4 :
    LieGoodComponentFixT .trialityD4 := by
  exact lieGoodComponentFixT_trialityD4_of

end CFSG.RankThree.PartOne.KLC
