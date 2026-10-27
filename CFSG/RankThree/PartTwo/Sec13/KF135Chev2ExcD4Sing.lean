module

public import CFSG.LieType.Chevalley.GraphFixedData
import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCore
import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcG2Sing

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_singular_D4_threeSix {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1)
    {A : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ b ∈ A, b ≠ 1 ∧ ∃ w : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      w ≠ 1 ∧ w ^ 2 = 1 ∧ b * w = w * b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have hK3 : Nat.card K = 2 ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  set Ω := AlgebraicClosure K with hΩ
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  set Fr : Ω →+* Ω := iterateFrobenius Ω 2 f with hFrdef
  have hFr : ∀ c : Ω, Fr c = c ^ (2 ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have hq1 : (1 : ℤ) ≤ ((2 ^ f : ℕ) : ℤ) := by exact_mod_cast Nat.one_le_two_pow
  have hd0 : 0 ≤ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1 := by
    rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * (2 ^ f : ℕ) + 1 :=
    ⟨_, Int.toNat_of_nonneg hd0⟩
  have hpd' : p ∣ d := by
    rw [← hd] at hpd
    exact_mod_cast hpd
  obtain ⟨-, ⟨g, hgG, hFg⟩, -, hall⟩ :=
    triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ Ω Fr hFr hε hd
  obtain ⟨-, -, hp'⟩ := hall g hgG hFg
  obtain ⟨-, -, -, -, -, -, -, hsurv, -, hplanes⟩ := hp' p hp hp3 hpd'
  obtain ⟨c, hAc', ⟨M, hMA, hMc, hM⟩, -⟩ :=
    hplanes A ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).mpr hA) hAc
  obtain ⟨xs, hxsM, hxs1⟩ : ∃ xs ∈ M, xs ≠ 1 := by
    have hM1 : M ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hMc
      exact hp.one_lt.ne hMc
    obtain ⟨⟨x, hxM⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hM1
    exact ⟨x, hxM, fun h => hx1 (Subtype.ext h)⟩
  have hxT : (MulAut.conj c).toMonoidHom xs ∈ threeSixFixedTorsion K Ω σ Fr ε p g := by
    rw [← hAc']
    exact ⟨xs, hMA hxsM, rfl⟩
  obtain ⟨u, hu, hux⟩ := hxT
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu.1.1
  have hxa : threeSixEmb K Ω σ (c * xs * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ :=
    hux.symm
  have hne := hM xs hxsM a hxa
  have ha1 : rootDiagUnit TwistTag.D4.tag a ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hxa
    have h3 : c * xs * c⁻¹ = 1 := threeSixEmb_injective K Ω σ (hxa.trans (map_one _).symm)
    rw [conj_eq_one_iff] at h3
    exact hxs1 h3
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = p := orderOf_eq_prime hu.2 ha1
  obtain ⟨i, hi⟩ : ∃ i, survivingRoots a = trialitySigma i := by
    by_contra hnot
    push Not at hnot
    have hnoline : ∀ i, rootDiagUnit TwistTag.D4.tag a ∉ threeSixLine Ω Fr ε p i :=
      fun i hi => hnot i ((hsurv a hu ha1).1 i hi)
    exact hne.ne_empty ((hsurv a hu ha1).2 hnoline)
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4, (fun α => v • α) '' d4A2Sigma = survivingRoots a := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ :=
      CFSG.RankThree.Lattice.triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
    exact ⟨w, by rw [hi, d4A2Sigma_eq_trialityStdA2, ← hw]⟩
  obtain ⟨-, -, hR, -, -, -, -, -, -, -, z, -, X, hXR, -, hX2, -⟩ :=
    triality_three_six_singular_fixed_centralizers hℓ hf K hK σ hσ Ω Fr hFr hε hd g hgG hFg hp
      hp3 hpd' a hu.1 hord v hv (c * xs * c⁻¹) hxa
  set k := RingHom.eqLocusField Fr (RingHom.id Ω) with hk
  obtain ⟨y, hyX, hy⟩ := hX2 (transvSL k)
  have hyC : y ∈ Subgroup.centralizer {c * xs * c⁻¹} := by
    have h1 := hXR hyX
    rw [← hR] at h1
    exact Subgroup.commutator_le.mpr (fun y₁ hy₁ y₂ hy₂ =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy₁ hy₂)
        (Subgroup.inv_mem _ hy₁)) (Subgroup.inv_mem _ hy₂)) h1
  have hB2 : tsIota Ω (Matrix.SpecialLinearGroup.map k.subtype (transvSL k)) ^ 2 = 1 := by
    have h := map_pow ((subsystemGroup Tag.D4 Ω d4SuppA2).subtype.comp (d4A2Iota Ω))
      (Matrix.SpecialLinearGroup.map k.subtype (transvSL k)) 2
    rw [← map_pow (Matrix.SpecialLinearGroup.map k.subtype) (transvSL k) 2, transvSL_sq,
      map_one, map_one] at h
    exact h.symm
  have hy2 : y ^ 2 = 1 := by
    apply threeSixEmb_injective K Ω σ
    rw [map_pow, hy, map_one, conj_pow, hB2, mul_one, mul_inv_cancel]
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, map_one] at hy
    have h2 : tsIota Ω (Matrix.SpecialLinearGroup.map k.subtype (transvSL k)) = 1 := by
      have h3 := hy.symm
      rwa [conj_eq_one_iff] at h3
    have h4 : d4A2Iota Ω (Matrix.SpecialLinearGroup.map k.subtype (transvSL k)) = 1 :=
      Subtype.ext h2
    have h5 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) Ω =>
      (M : Matrix (Fin 3) (Fin 3) Ω) 0 1) (congrArg (d4A2Rep Ω) h4)
    simp only [d4A2Rep_d4A2Iota, map_one, coe_sl2BlockSL3] at h5
    change k.subtype 1 = (1 : Matrix (Fin 3) (Fin 3) Ω) 0 1 at h5
    rw [map_one, Matrix.one_apply_ne (by decide)] at h5
    exact one_ne_zero h5
  refine ⟨xs, hMA hxsM, hxs1, c⁻¹ * y * c, fun h1 => hy1 ?_, ?_, ?_⟩
  · calc y = c * (c⁻¹ * y * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · calc (c⁻¹ * y * c) ^ 2 = c⁻¹ * y ^ 2 * c := by rw [sq, sq]; group
      _ = 1 := by rw [hy2]; group
  · have h1 := Subgroup.mem_centralizer_singleton_iff.mp hyC
    calc xs * (c⁻¹ * y * c) = c⁻¹ * ((c * xs * c⁻¹) * y) * c := by group
      _ = c⁻¹ * (y * (c * xs * c⁻¹)) * c := by rw [h1]
      _ = c⁻¹ * y * c * xs := by group

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
