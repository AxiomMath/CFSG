module

public import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof2
public import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof4
public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE

public section

namespace CFSG.StandardType.E6IDB

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three

theorem six_dvd_of_three_dvd {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) (h3n : 3 ∣ n) : 6 ∣ n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · omega
  · exfalso
    have h4 : 3 ∣ 4 ^ k - 1 := by simpa using Nat.sub_one_dvd_pow_sub_one 4 k
    have e : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, pow_mul]
      ring
    have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rw [e] at h3
    generalize 4 ^ k = B at h1 h3 h4
    omega

section Cert

variable {K : Type} [Field K]

theorem exists_two_subgroup_of_commute_entrywise [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h6 : 6 ∣ n) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {X : Subgroup (MulAut (adjointGroup .E6 K))} (hX : IsElemAbelian 3 X)
    (hXI : X ≤ (hatAut .E6 K).range) (h5 : 3 ^ 5 ≤ Nat.card X)
    (hc : ∀ x ∈ X, x * entrywiseAdjointAut .E6 σ = entrywiseAdjointAut .E6 σ * x) :
    ∃ U : Subgroup (adjointGroup .E6 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ u ∈ U, entrywiseAdjointAut .E6 σ u ∈ U) ∧ ∀ x ∈ X, ∀ u ∈ U, x u ∈ U := by
  obtain ⟨m, rfl⟩ := h6
  have hk : Nat.card (fixSubfield σ) = 2 ^ (2 * m) := by
    rw [(CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two hn hK σ).2, hσ]
    congr 1
    omega
  have : Finite (fixSubfield σ) := Subtype.finite
  have : CharP (fixSubfield σ) 2 := charP_two_of_card hk
  have h3 : 3 ∣ Nat.card (fixSubfield σ) - 1 := by
    rw [hk]
    simpa using Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_right 2 m)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (6 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinj : Function.Injective ((hatAut .E6 K).comp (subfieldHat (τ := .E6) σ)) :=
    (hatAut_injective hK4).comp (subfieldHat_injective σ)
  have hmap : (X.comap ((hatAut .E6 K).comp (subfieldHat σ))).map
      ((hatAut .E6 K).comp (subfieldHat σ)) = X := by
    refine le_antisymm (Subgroup.map_comap_le _ _) fun x hx => ?_
    obtain ⟨w, rfl⟩ := hXI hx
    obtain ⟨w₀, rfl⟩ := exists_subfieldHat_eq_of_commute hK σ hk hK4 w (hc _ hx)
    exact ⟨w₀, hx, rfl⟩
  have hcard : Nat.card (X.comap ((hatAut .E6 K).comp (subfieldHat σ))) = Nat.card X := by
    have h := Subgroup.card_map_of_injective
      (K := X.comap ((hatAut .E6 K).comp (subfieldHat σ))) hinj
    rw [hmap] at h
    exact h.symm
  obtain ⟨U₀, hU₀, hU₀2, hU₀n⟩ := exists_normalized_two_of_le_hatGroup h3
    (isElemAbelian_comap hX hinj) (by rw [hcard]; exact h5)
  refine ⟨U₀.map (subfieldAdj σ), fun h => hU₀ ?_, hU₀2.map _, ?_, ?_⟩
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ (subfieldAdj_injective σ)] at h
  · rintro _ ⟨u, hu, rfl⟩
    rw [entrywiseAdjointAut_subfieldAdj]
    exact ⟨u, hu, rfl⟩
  · rintro x hx _ ⟨u, hu, rfl⟩
    rw [← hmap] at hx
    obtain ⟨w₀, hw₀, rfl⟩ := hx
    exact ⟨_, hU₀n w₀ hw₀ u hu, (hatAut_subfieldHat σ w₀ u).symm⟩

theorem ggInnerDiagBound_adjoint_E6 [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) (h3n : 3 ∣ n) :
    GGInnerDiagBound 3 5 (adjointGroup .E6 K) ((hatAut .E6 K).range : Set _) := by
  have : Finite (adjointGroup .E6 K) := generated_group_finite .E6 K
  have : ((hatAut .E6 K).range).Normal := normal_range_hatAut
  refine ggInnerDiagBound_of_conj_core (hatAut .E6 K).range
    {f | ∃ σ : K ≃+* K, orderOf σ = 3 ∧ entrywiseAdjointAut .E6 σ = f} (fun φ hφ hφ3 => ?_) ?_
  · obtain ⟨d, T, r, j, ψ, -, -, -, -, hTj, hr, hψ⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag .E6 (Or.inl rfl)
        hn K hK Nat.prime_three (by norm_num) φ hφ3 fun g a h => hφ (by
          rw [h]
          exact conj_mul_rootDiagAut_mem_range g a)
    refine ⟨_, ⟨T ^ j, hTj, rfl⟩, ψ, ?_⟩
    rw [← hr, ← conj_pow, hψ, ← entrywiseAdjointAut_pow]
  · rintro _ ⟨σ, hσ, rfl⟩ X hX hXJ h5 hXc
    exact exists_two_subgroup_of_commute_entrywise hn hK (six_dvd_of_three_dvd h3 h3n) hσ hX hXJ h5
      hXc

end Cert

end CFSG.StandardType.E6IDB

end
