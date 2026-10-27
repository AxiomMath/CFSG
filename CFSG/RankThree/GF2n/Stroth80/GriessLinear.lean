module

public import CFSG.RankThree.GF2n.Stroth80.GriessCover
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

section Basic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem exists_surjective_codRestrict {E : Type} [Group E] (π : E →* GL ι K)
    {H : Subgroup (GL ι K)} (h : π.range = H) :
    ∃ π₁ : E →* H, Function.Surjective π₁ ∧ π₁.ker = π.ker := by
  have hmem : ∀ e : E, π e ∈ H := fun e => h ▸ ⟨e, rfl⟩
  refine ⟨π.codRestrict H hmem, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨e, rfl⟩ := h ▸ hx
    exact ⟨e, rfl⟩
  · exact MonoidHom.ker_codRestrict π H hmem

end Basic

section Models

variable {K : Type} [Field K]

theorem two_pow_ge_four {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem card_statedScalars_subgroupOf_statedSL [Finite K] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card ((StatedScalars (Fin m) K).subgroupOf (StatedSL m K)) =
      Nat.gcd m (Nat.card K - 1) := by
  rw [← map_center_eq_statedScalars m K]
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K))
      (specialLinearGroupEquivStatedSL m K : Matrix.SpecialLinearGroup (Fin m) K →* StatedSL m K)
      (specialLinearGroupEquivStatedSL m K).injective).toEquiv]
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
    (⟨0, hm⟩ : Fin m)).toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd,
    Fintype.card_fin, Nat.gcd_comm]

theorem lieModel_statedProj_sl [Finite K] {m f : ℕ} (hm : 2 ≤ m) (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    Models.LieModel (StatedProj (StatedSL m K)) .PSL m 2 f := by
  have h4 := two_pow_ge_four hf
  have hadm : StatedLieAdmissible .PSL m 2 f :=
    ⟨Nat.prime_two, by omega, hm, fun h => by simp at h; omega, fun h => by simp at h; omega⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩⟩

theorem lieModel_statedProj_sp [Finite K] {m f : ℕ} (hm : 2 ≤ m) (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    Models.LieModel (StatedProj (StatedSp m K)) .PSp m 2 f := by
  have h4 := two_pow_ge_four hf
  have hadm : StatedLieAdmissible .PSp m 2 f :=
    ⟨Nat.prime_two, by omega, hm, fun h => by simp at h; omega⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩⟩

theorem lieModel_statedProj_omegaPlus [Finite K] {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    Models.LieModel (StatedProj (StatedOmega (StatedQuadPlus m K))) .POmegaPlus m 2 f := by
  have hadm : StatedLieAdmissible .POmegaPlus m 2 f := ⟨Nat.prime_two, hf, hm⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩⟩

theorem lieModel_statedProj_omegaMinus [Finite K] {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Models.LieModel (StatedProj (StatedOmega (StatedQuadMinus m K b c))) .POmegaMinus m 2 f := by
  have hadm : StatedLieAdmissible .POmegaMinus m 2 f := ⟨Nat.prime_two, hf, hm⟩
  exact ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr, ⟨MulEquiv.refl _⟩⟩⟩

end Models

section Orders

theorem genericOrders_psl (m f : ℕ) : genericOrders .PSL m 2 f = (Nat.gcd m (2 ^ f - 1), 1) := by
  simp [genericOrders]

theorem odd_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : ¬ 2 ∣ 2 ^ f - 1 := by
  have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h2 : 0 < 2 ^ f := by positivity
  omega

theorem genericOrders_psp_eq_one {m f : ℕ} (hf : 1 ≤ f) : genericOrders .PSp m 2 f = (1, 1) := by
  have h : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (odd_two_pow_sub_one hf)
  simp [genericOrders, h]

theorem exceptionalOrders_psp_eq_one {m f : ℕ} (hf : 2 ≤ f) :
    exceptionalOrders .PSp m 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all <;> omega

theorem genericOrders_omegaPlus_eq_one {m f : ℕ} (hf : 1 ≤ f) :
    genericOrders .POmegaPlus m 2 f = (1, 1) := by
  have h : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
  simp [genericOrders, h]

theorem exceptionalOrders_omegaPlus_eq_one {m f : ℕ} (hf : 2 ≤ f) :
    exceptionalOrders .POmegaPlus m 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all <;> omega

theorem genericOrders_omegaMinus_eq_one {m f : ℕ} (hm : 1 ≤ m) (hf : 1 ≤ f) :
    genericOrders .POmegaMinus m 2 f = (1, 1) := by
  have h2 : ¬ 2 ∣ (2 ^ f) ^ m + 1 := by
    have h1 : 2 ∣ (2 ^ f) ^ m := (dvd_pow_self 2 (by omega)).pow (by omega)
    omega
  have h : Nat.gcd 4 ((2 ^ f) ^ m + 1) = 1 := by
    have := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
    simpa using this
  simp [genericOrders, h]

theorem exceptionalOrders_omegaMinus_eq_one {m f : ℕ} :
    exceptionalOrders .POmegaMinus m 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem exceptionalOrders_psl_eq_one {m f : ℕ} (hf : 2 ≤ f) (h2 : ¬ (m = 2 ∧ f = 2))
    (h3 : ¬ (m = 3 ∧ f = 2)) : exceptionalOrders .PSL m 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all <;> omega

end Orders

section Families

variable {K : Type} [Field K] [Finite K] {E : Type} [Group E] [Finite E]

theorem statedSL_ker_card_dvd (hGA : GriessAllModelsStatement) {m f : ℕ} (hm : 2 ≤ m)
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (hE : Group.IsPerfect E) (π : E →* GL (Fin m) K)
    (hrange : π.range = StatedSL m K) (hker : π.ker ≤ Subgroup.center E) :
    Nat.card π.ker ∣ (exceptionalOrders .PSL m 2 f).1 * (exceptionalOrders .PSL m 2 f).2 := by
  obtain ⟨π₁, hπ₁, hk₁⟩ := exists_surjective_codRestrict π hrange
  have h := card_ker_mul_card_dvd hGA
    (S := (StatedScalars (Fin m) K).subgroupOf (StatedSL m K))
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    (lieModel_statedProj_sl hm hf hK) hE π₁ hπ₁ (hk₁ ▸ hker)
  rw [card_generic_prod_exceptional, genericOrders_psl,
    card_statedScalars_subgroupOf_statedSL (by omega), hk₁, hK] at h
  have hg : 0 < Nat.gcd m (2 ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  rw [mul_one, mul_comm (Nat.card π.ker)] at h
  exact Nat.dvd_of_mul_dvd_mul_left hg h

theorem statedSp_ker_eq_bot (hGA : GriessAllModelsStatement) {m f : ℕ} (hm : 2 ≤ m)
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (hE : Group.IsPerfect E)
    (π : E →* GL (Fin m ⊕ Fin m) K) (hrange : π.range = StatedSp m K)
    (hker : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  obtain ⟨π₁, hπ₁, hk₁⟩ := exists_surjective_codRestrict π hrange
  have h := card_ker_mul_card_dvd hGA
    (S := (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (StatedSp m K))
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    (lieModel_statedProj_sp hm hf hK) hE π₁ hπ₁ (hk₁ ▸ hker)
  rw [card_generic_prod_exceptional, genericOrders_psp_eq_one (by omega),
    exceptionalOrders_psp_eq_one hf, hk₁] at h
  have h1 : Nat.card π.ker ∣ 1 * 1 * (1 * 1) := (Dvd.intro _ rfl).trans h
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

theorem statedOmegaPlus_ker_eq_bot (hGA : GriessAllModelsStatement) {m f : ℕ} (hm : 4 ≤ m)
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (hE : Group.IsPerfect E)
    (π : E →* GL (Fin m ⊕ Fin m) K) (hrange : π.range = StatedOmega (StatedQuadPlus m K))
    (hker : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  obtain ⟨π₁, hπ₁, hk₁⟩ := exists_surjective_codRestrict π hrange
  have h := card_ker_mul_card_dvd hGA
    (S := (StatedScalars (Fin m ⊕ Fin m) K).subgroupOf (StatedOmega (StatedQuadPlus m K)))
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    (lieModel_statedProj_omegaPlus hm (by omega) hK) hE π₁ hπ₁ (hk₁ ▸ hker)
  rw [card_generic_prod_exceptional, genericOrders_omegaPlus_eq_one (by omega),
    exceptionalOrders_omegaPlus_eq_one hf, hk₁] at h
  have h1 : Nat.card π.ker ∣ 1 * 1 * (1 * 1) := (Dvd.intro _ rfl).trans h
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

theorem statedOmegaMinus_ker_eq_bot (hGA : GriessAllModelsStatement) {m f : ℕ} (hm : 4 ≤ m)
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hE : Group.IsPerfect E) (π : E →* GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
    (hrange : π.range = StatedOmega (StatedQuadMinus m K b c))
    (hker : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  obtain ⟨π₁, hπ₁, hk₁⟩ := exists_surjective_codRestrict π hrange
  have h := card_ker_mul_card_dvd hGA
    (S := (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus m K b c)))
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    (lieModel_statedProj_omegaMinus hm hf hK hirr) hE π₁ hπ₁ (hk₁ ▸ hker)
  rw [card_generic_prod_exceptional, genericOrders_omegaMinus_eq_one (by omega) hf,
    exceptionalOrders_omegaMinus_eq_one, hk₁] at h
  have h1 : Nat.card π.ker ∣ 1 * 1 * (1 * 1) := (Dvd.intro _ rfl).trans h
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

end Families

end CFSG.RankThree.GF2n.Stroth80
