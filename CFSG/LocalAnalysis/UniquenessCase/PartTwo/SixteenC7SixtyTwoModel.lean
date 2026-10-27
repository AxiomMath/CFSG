module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13

open scoped Matrix

section Model

@[expose] noncomputable def s16c7_z0 : WMod :=
  Multiplicative.ofAdd (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ZMod 2))

@[expose] noncomputable def s16c7_S : Subgroup (MulAut WMod) := (U3.prod U3).map rho

@[expose] noncomputable def s16c7_K : Subgroup (MulAut WMod) := (C3.prod C3).map rho

theorem s16c7_z0_ne_one : s16c7_z0 ≠ 1 := by
  intro h
  have h1 : (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2))
      = 0 := congrArg Multiplicative.toAdd h
  have h2 := congrFun (congrFun h1 0) 0
  exact absurd h2 (by decide)

theorem s16c7_z0_sq : s16c7_z0 ^ 2 = 1 := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  change (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2)) +
    Matrix.single 0 0 1 = 0
  decide

theorem s16c7_S_le_img : s16c7_S ≤ img := Subgroup.map_le_range _ _

theorem s16c7_K_le_img : s16c7_K ≤ img := Subgroup.map_le_range _ _

theorem s16c7_card_S : Nat.card s16c7_S = 64 := by
  have h : Nat.card s16c7_S = Nat.card U3 * Nat.card U3 := by
    rw [s16c7_S, Subgroup.card_map_of_injective rho_injective, card_prod_subgroup]
  rw [h, card_U3]

theorem s16c7_isSylow_S : CFSG.ABGLocalTools.IsSylowOf 2 s16c7_S img := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut WMod) := MulEquiv.finite_left
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨s16c7_S_le_img,
    IsPGroup.of_card (n := 6) (by rw [s16c7_card_S]; norm_num), ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := s16c7_S) (K := img)
  rw [inf_eq_left.mpr s16c7_S_le_img, s16c7_card_S, card_img] at h1
  have h3 : s16c7_S.relIndex img = 441 := by omega
  rw [h3]
  decide

theorem s16c7_card_K : Nat.card s16c7_K = 9 := by
  have h : Nat.card s16c7_K = Nat.card C3 * Nat.card C3 := by
    rw [s16c7_K, Subgroup.card_map_of_injective rho_injective, card_prod_subgroup]
  rw [h, card_C3]

private theorem fixS_aux : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2),
    ((!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X = X ∧
    (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X = X ∧
    (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X = X ∧
    X * (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X ∧
    X * (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X ∧
    X * (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X) →
    X = 0 ∨ X = Matrix.single 0 0 1 := by decide +kernel

private theorem fixK_aux : ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2),
    (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X = X →
    X * (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X →
    X = 0 ∨ X = Matrix.single 0 0 1 := by decide +kernel

private theorem mem_U3_of_mat (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hM : M.det ≠ 0)
    (h : M *ᵥ e0 = e0 ∧ e2 ᵥ* M = e2) : slOfMat M hM ∈ U3 := by
  refine ⟨?_, ?_⟩
  · change mat (slOfMat M hM) *ᵥ e0 = e0
    rw [mat_slOfMat]
    exact h.1
  · change e2 ᵥ* mat (slOfMat M hM) = e2
    rw [mat_slOfMat]
    exact h.2

private theorem toAdd_fix_left {v : WMod} {A : Subgroup ↥SL32} {B : Subgroup ↥SL32}
    (hv : v ∈ fixV ((A.prod B).map rho)) {a : ↥SL32} (ha : a ∈ A) :
    mat a * Multiplicative.toAdd v = Multiplicative.toAdd v := by
  have h : mat a * Multiplicative.toAdd v * (mat (1 : ↥SL32))ᵀ = Multiplicative.toAdd v :=
    congrArg Multiplicative.toAdd (mem_fixV.1 hv (rho (a, 1)) ⟨(a, 1), ⟨ha, B.one_mem⟩, rfl⟩)
  simpa [mat_one] using h

private theorem toAdd_fix_right {v : WMod} {A : Subgroup ↥SL32} {B : Subgroup ↥SL32}
    (hv : v ∈ fixV ((A.prod B).map rho)) {b : ↥SL32} (hb : b ∈ B) :
    Multiplicative.toAdd v * (mat b)ᵀ = Multiplicative.toAdd v := by
  have h : mat (1 : ↥SL32) * Multiplicative.toAdd v * (mat b)ᵀ = Multiplicative.toAdd v :=
    congrArg Multiplicative.toAdd (mem_fixV.1 hv (rho (1, b)) ⟨(1, b), ⟨A.one_mem, hb⟩, rfl⟩)
  simpa [mat_one] using h

private theorem fixV_le_of_eq {v : WMod} (h : Multiplicative.toAdd v = 0 ∨
    Multiplicative.toAdd v = Matrix.single 0 0 1) : v ∈ Subgroup.zpowers s16c7_z0 := by
  rcases h with h | h
  · rw [show v = 1 from Multiplicative.toAdd.injective h]
    exact Subgroup.one_mem _
  · rw [show v = s16c7_z0 from Multiplicative.toAdd.injective h]
    exact Subgroup.mem_zpowers _

theorem s16c7_fixV_S : fixV s16c7_S = Subgroup.zpowers s16c7_z0 := by
  apply le_antisymm
  · intro v hv
    have hS : v ∈ fixV ((U3.prod U3).map rho) := hv
    have h12 : slOfMat (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (by decide) ∈ U3 := mem_U3_of_mat _ _ (by decide)
    have h13 : slOfMat (!![1, 0, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (by decide) ∈ U3 := mem_U3_of_mat _ _ (by decide)
    have h23 : slOfMat (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2))
        (by decide) ∈ U3 := mem_U3_of_mat _ _ (by decide)
    exact fixV_le_of_eq (fixS_aux _ ⟨toAdd_fix_left hS h12, toAdd_fix_left hS h13,
      toAdd_fix_left hS h23, toAdd_fix_right hS h12, toAdd_fix_right hS h13,
      toAdd_fix_right hS h23⟩)
  · have hz : s16c7_z0 ∈ fixV s16c7_S := by
      refine mem_fixV.2 ?_
      rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact rho_fix_E00 (U3_le_P1 ha) (U3_le_P1 hb)
    exact Subgroup.zpowers_le.2 hz

theorem s16c7_fixV_K : fixV s16c7_K = Subgroup.zpowers s16c7_z0 := by
  apply le_antisymm
  · intro v hv
    have hK : v ∈ fixV ((C3.prod C3).map rho) := hv
    exact fixV_le_of_eq (fixK_aux _ (toAdd_fix_left hK (Subgroup.mem_zpowers c3))
      (toAdd_fix_right hK (Subgroup.mem_zpowers c3)))
  · have hz : s16c7_z0 ∈ fixV s16c7_K := by
      refine mem_fixV.2 ?_
      rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact rho_fix_E00 (C3_le_P1 ha) (C3_le_P1 hb)
    exact Subgroup.zpowers_le.2 hz

theorem s16c7_P1_mul {a : ↥SL32} (ha : a ∈ P1) : ∃ c ∈ C3, ∃ u ∈ U3, c * u = a := by
  have hcop : Nat.Coprime (Nat.card C3) (Nat.card U3) := by
    rw [card_C3, card_U3]
    decide
  have hinf : C3 ⊓ U3 = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hle : C3 ⊔ U3 ≤ P1 := sup_le C3_le_P1 U3_le_P1
  have h3 : 3 ∣ Nat.card ↥(C3 ⊔ U3) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : C3 ≤ C3 ⊔ U3)
    rwa [card_C3] at this
  have h8 : 8 ∣ Nat.card ↥(C3 ⊔ U3) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : U3 ≤ C3 ⊔ U3)
    rwa [card_U3] at this
  have h24 : 24 ∣ Nat.card ↥(C3 ⊔ U3) := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 8) h3 h8
    simpa using this
  have hle' : Nat.card ↥(C3 ⊔ U3) ≤ 24 := by
    have := Subgroup.card_le_of_le hle
    rwa [card_P1] at this
  have heq : Nat.card ↥(C3 ⊔ U3) = 24 := by
    have := Nat.le_of_dvd Nat.card_pos h24
    omega
  have hP1 : C3 ⊔ U3 = P1 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_P1, heq])
  have hc : Nat.card ↥(C3 ⊔ U3) ≤ Nat.card C3 * Nat.card U3 := by
    rw [heq, card_C3, card_U3]
  have hmul := coe_mul_eq_sup_of_card hinf hc
  have h2 : a ∈ ((C3 ⊔ U3 : Subgroup ↥SL32) : Set ↥SL32) := by rw [hP1]; exact ha
  rw [← hmul] at h2
  obtain ⟨c, hc', u, hu, rfl⟩ := h2
  exact ⟨c, hc', u, hu, rfl⟩

theorem s16c7_stab {h : MulAut WMod} (hh : h ∈ img) (hz : h s16c7_z0 = s16c7_z0) :
    ∃ x ∈ s16c7_K, ∃ t ∈ s16c7_S, h = x * t := by
  obtain ⟨⟨a, b⟩, rfl⟩ := hh
  obtain ⟨ha, hb⟩ := mem_P1_of_rho_E00 hz
  obtain ⟨c₁, hc₁, u₁, hu₁, rfl⟩ := s16c7_P1_mul ha
  obtain ⟨c₂, hc₂, u₂, hu₂, rfl⟩ := s16c7_P1_mul hb
  refine ⟨rho (c₁, c₂), ⟨(c₁, c₂), ⟨hc₁, hc₂⟩, rfl⟩, rho (u₁, u₂),
    ⟨(u₁, u₂), ⟨hu₁, hu₂⟩, rfl⟩, ?_⟩
  rw [← map_mul]
  rfl

theorem s16c7_toAdd_rho_z0 (a b : ↥SL32) :
    Multiplicative.toAdd (rho (a, b) s16c7_z0) =
      Matrix.vecMulVec (fun i => mat a i 0) (fun j => mat b j 0) := by
  change mat a * Matrix.single 0 0 1 * (mat b)ᵀ = _
  ext i j
  rw [mul_E00_mul_transpose]
  rfl

theorem s16c7_col_ne_zero (a : ↥SL32) : (fun i => mat a i 0) ≠ 0 := by
  intro h
  have h1 : mat a *ᵥ e0 = 0 := by
    ext i
    simpa [Matrix.mulVec_single] using congrFun h i
  have h2 : e0 = 0 := by
    calc e0 = (mat a⁻¹ * mat a) *ᵥ e0 := by rw [mat_inv_mul, Matrix.one_mulVec]
      _ = mat a⁻¹ *ᵥ (mat a *ᵥ e0) := by rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [h1, Matrix.mulVec_zero]
  have h3 := congrFun h2 0
  simp [e0] at h3

theorem s16c7_tau_z0 : tau s16c7_z0 = s16c7_z0 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau]
  change (Matrix.single 0 0 1 : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = _
  rw [Matrix.transpose_single]
  rfl

theorem s16c7_ncard_orbit :
    Set.ncard {w : WMod | ∃ n ∈ L3Wr.norm, n s16c7_z0 = w} ≤ 49 := by
  classical
  let f : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) → WMod :=
    fun p => Multiplicative.ofAdd (Matrix.vecMulVec p.1 p.2)
  let F : Finset ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :=
    (Finset.univ.erase 0) ×ˢ (Finset.univ.erase 0)
  have hF : F.card = 49 := by
    simp only [F, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    decide
  have hrho : ∀ a b : ↥SL32, rho (a, b) s16c7_z0 ∈ F.image f := by
    intro a b
    rw [Finset.mem_image]
    refine ⟨(fun i => mat a i 0, fun j => mat b j 0), ?_, ?_⟩
    · simp only [F, Finset.mem_product, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨s16c7_col_ne_zero a, s16c7_col_ne_zero b⟩
    · apply Multiplicative.toAdd.injective
      exact (s16c7_toAdd_rho_z0 a b).symm
  have hsub : {w : WMod | ∃ n ∈ L3Wr.norm, n s16c7_z0 = w} ⊆
      ((F.image f : Finset WMod) : Set WMod) := by
    rintro _ ⟨n, hn, rfl⟩
    obtain ⟨⟨a, b⟩, rfl | rfl⟩ := mem_norm_iff.1 hn
    · exact hrho a b
    · change rho (a, b) (tau s16c7_z0) ∈ F.image f
      rw [s16c7_tau_z0]
      exact hrho a b
  calc Set.ncard {w : WMod | ∃ n ∈ L3Wr.norm, n s16c7_z0 = w}
      ≤ Set.ncard ((F.image f : Finset WMod) : Set WMod) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (F.image f).card := Set.ncard_coe_finset _
    _ ≤ F.card := Finset.card_image_le
    _ = 49 := hF

end Model

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
