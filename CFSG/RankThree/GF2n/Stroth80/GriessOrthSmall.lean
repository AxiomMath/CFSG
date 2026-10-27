module

public import CFSG.RankThree.GF2n.Stroth80.GriessLinear
public import CFSG.RankThree.PartOne.K159.Klein
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract
public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

section Equivs

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

@[expose] noncomputable def statedOmegaMulEquivDerived (hQ : ⇑Q = Q₀) :
    ↥(StatedOmega Q₀) ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans
    (MulEquiv.subgroupCongr (by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ]
      exact Subgroup.map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _))

end Equivs

section Commutator

variable {G : Type} [Group G]

@[expose] noncomputable def commutatorMulEquivDerived (H : Subgroup G) :
    ↥(commutator ↥H) ≃* ↥⁅H, H⁆ :=
  (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator H))

end Commutator

section Cover

variable {E X Y : Type} [Group E] [Group X] [Group Y]

theorem exists_surjective_of_mulEquiv (e : X ≃* Y) (π : E →* X) (hπ : Function.Surjective π) :
    ∃ π' : E →* Y, Function.Surjective π' ∧ π'.ker = π.ker :=
  ⟨(e : X →* Y).comp π, e.surjective.comp hπ, MonoidHom.ker_mulEquiv_comp π e⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem exists_hom_range_eq {H : Subgroup (GL ι K)} (π : E →* H) (hπ : Function.Surjective π) :
    ∃ π' : E →* GL ι K, π'.range = H ∧ π'.ker = π.ker :=
  ⟨H.subtype.comp π, by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hπ, Subgroup.map_top,
      Subgroup.range_subtype],
    MonoidHom.ker_comp_of_injective π H.subtype H.subtype_injective⟩

end Cover

section Isomorphisms

variable {K : Type} [Field K] [Finite K] {b c : K}

theorem exists_quadMinus_ne_zero_of_finrank {n : ℕ} (hn : 1 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) (hU : Module.finrank K U = n) :
    ∃ u ∈ U, CFSG.LieType.Universal.Spin.quadMinus n K b c u ≠ 0 := by
  by_contra h
  push Not at h
  refine CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hn hirr ⟨U, ?_, h⟩
  rw [hU, CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space hn]

variable [CharP K 2]

theorem nonempty_statedOmega_quadPlus_three_mulEquiv (hK : 4 ≤ Nat.card K) :
    Nonempty (↥(StatedOmega (StatedQuadPlus 3 K)) ≃* ↥(StatedSL 4 K)) := by
  obtain ⟨hnd, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := 3) le_rfl
  have hd : Module.finrank K (Fin 3 ⊕ Fin 3 → K) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨κ⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six
    (CFSG.LieType.Universal.Spin.quadPlus 3 K) hnd hd hT hK
  exact ⟨((statedOmegaMulEquivDerived (CFSG.LieType.Universal.Spin.coe_quadPlus 3 K)).trans
    (commutatorMulEquivDerived _).symm).trans κ⟩

theorem exists_statedOmega_quadMinus_two_mulEquiv (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Nat.card K ^ 2 ∧
      Nonempty (↥(StatedOmega (StatedQuadMinus 2 K b c)) ≃* ↥(StatedSL 2 F)) := by
  obtain ⟨F, _, _, D, _, _, -, -, hinj, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction
      (CFSG.LieType.Universal.Spin.quadMinus 2 K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)
      (CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_of_finrank (by norm_num) hirr U hU)
  exact ⟨F, inferInstance, D.finite_E, D.card_E,
    ⟨(((statedOmegaMulEquivDerived (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)).trans
      (MulEquiv.subgroupCongr hcomm)).trans (MonoidHom.ofInjective hinj).symm).trans
      (specialLinearGroupEquivStatedSL 2 F)⟩⟩

theorem exists_statedOmega_quadMinus_three_mulEquiv {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ f) ^ 2 ∧
      Nonempty (↥(StatedOmega (StatedQuadMinus 3 K b c)) ≃* ↥(StatedSU 4 (2 ^ f) F)) := by
  obtain ⟨F, _, _, D, _, _, -, -, hinj, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction
      (CFSG.LieType.Universal.Spin.quadMinus 3 K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr)
      (CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_of_finrank (by norm_num) hirr U hU)
  obtain ⟨f₁, h, hK₁, hbar⟩ := D.exists_unitaryFieldData
  obtain rfl : f₁ = f := Nat.pow_right_injective (le_refl 2) (hK₁.symm.trans hK)
  obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv h hbar
  exact ⟨F, inferInstance, h.finite, h.card_eq_sq,
    ⟨(((statedOmegaMulEquivDerived (CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c)).trans
      (MulEquiv.subgroupCongr hcomm)).trans (MonoidHom.ofInjective hinj).symm).trans θ⟩⟩

end Isomorphisms

section Orders

theorem genericOrders_psu (m f : ℕ) : genericOrders .PSU m 2 f = (Nat.gcd m (2 ^ f + 1), 1) := by
  simp [genericOrders]

theorem gcd_two_pow_two_pow_add_one {k f : ℕ} (hf : 1 ≤ f) :
    Nat.gcd (2 ^ k) (2 ^ f + 1) = 1 := by
  have h2 : ¬ 2 ∣ 2 ^ f + 1 := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)

theorem exceptionalOrders_psu_eq_one {m f : ℕ} (hf : 2 ≤ f) :
    exceptionalOrders .PSU m 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all <;> omega

end Orders

section Models

variable {K : Type} [Field K] [Finite K]

theorem lieModel_statedProj_su {n f : ℕ} (hn : 3 ≤ n) (hnf : (n, 2 ^ f) ≠ (3, 2)) (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Models.LieModel (StatedProj (StatedSU n (2 ^ f) K)) .PSU n 2 f := by
  have hadm : StatedLieAdmissible .PSU n 2 f := ⟨Nat.prime_two, hf, hn, hnf⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩⟩

end Models

section Families

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Group E] [Finite E]

theorem statedOmegaPlus_six_ker_eq_bot (hGA : GriessAllModelsStatement) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hE : Group.IsPerfect E) (π : E →* GL (Fin 3 ⊕ Fin 3) K)
    (hrange : π.range = StatedOmega (StatedQuadPlus 3 K)) (hker : π.ker ≤ Subgroup.center E) :
    π.ker = ⊥ := by
  obtain ⟨π₁, hπ₁, hk₁⟩ := exists_surjective_codRestrict π hrange
  obtain ⟨e⟩ := nonempty_statedOmega_quadPlus_three_mulEquiv (K := K) (hK ▸ two_pow_ge_four hf)
  obtain ⟨π₂, hπ₂, hk₂⟩ := exists_surjective_of_mulEquiv e π₁ hπ₁
  obtain ⟨π₃, hr₃, hk₃⟩ := exists_hom_range_eq π₂ hπ₂
  have h := statedSL_ker_card_dvd hGA (by norm_num) hf hK hE π₃ hr₃
    (by rw [hk₃, hk₂, hk₁]; exact hker)
  rw [exceptionalOrders_psl_eq_one hf (by omega) (by omega), hk₃, hk₂, hk₁] at h
  have h1 : Nat.card π.ker ∣ 1 * 1 := h
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

theorem statedOmegaMinus_four_ker_eq_bot (hGA : GriessAllModelsStatement) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hE : Group.IsPerfect E) (π : E →* GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
    (hrange : π.range = StatedOmega (StatedQuadMinus 2 K b c))
    (hker : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  obtain ⟨π₁, hπ₁, hk₁⟩ := exists_surjective_codRestrict π hrange
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_statedOmega_quadMinus_two_mulEquiv hirr
  obtain ⟨π₂, hπ₂, hk₂⟩ := exists_surjective_of_mulEquiv e π₁ hπ₁
  obtain ⟨π₃, hr₃, hk₃⟩ := exists_hom_range_eq π₂ hπ₂
  have hF' : Nat.card F = 2 ^ (2 * f) := by rw [hF, hK, ← pow_mul, mul_comm]
  have h := statedSL_ker_card_dvd hGA (m := 2) (f := 2 * f) le_rfl (by omega) hF' hE π₃ hr₃
    (by rw [hk₃, hk₂, hk₁]; exact hker)
  rw [exceptionalOrders_psl_eq_one (by omega) (by omega) (by omega), hk₃, hk₂, hk₁] at h
  have h1 : Nat.card π.ker ∣ 1 * 1 := h
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

theorem statedOmegaMinus_six_ker_eq_bot (hGA : GriessAllModelsStatement) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hE : Group.IsPerfect E) (π : E →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)
    (hrange : π.range = StatedOmega (StatedQuadMinus 3 K b c))
    (hker : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  obtain ⟨π₁, hπ₁, hk₁⟩ := exists_surjective_codRestrict π hrange
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_statedOmega_quadMinus_three_mulEquiv hK hirr
  obtain ⟨π₂, hπ₂, hk₂⟩ := exists_surjective_of_mulEquiv e π₁ hπ₁
  have hnf : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := fun h => by simp at h
  have h := card_ker_mul_card_dvd hGA
    (S := (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (2 ^ f) F))
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    (lieModel_statedProj_su (by norm_num) hnf (by omega) hF) hE π₂ hπ₂
    (by rw [hk₂, hk₁]; exact hker)
  have hgen : genericOrders .PSU 4 2 f = (1, 1) := by
    rw [genericOrders_psu]
    simpa using gcd_two_pow_two_pow_add_one (k := 2) (f := f) (by omega)
  rw [card_generic_prod_exceptional, hgen, exceptionalOrders_psu_eq_one hf, hk₂, hk₁] at h
  have h1 : Nat.card π.ker ∣ 1 * 1 * (1 * 1) := (Dvd.intro _ rfl).trans h
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

end Families

end CFSG.RankThree.GF2n.Stroth80
