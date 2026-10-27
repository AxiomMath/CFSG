module

public import CFSG.Walter.ReeOrder.Ward.LTable

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

namespace WardL

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (W : WardL L q e)

include W in
theorem int_facts : 7 ≤ (q : ℤ) ∧ (e = 1 ∨ e = -1) := ⟨by exact_mod_cast W.q_ge, W.e_eq⟩

theorem int_div_two_inj {a b : ℤ} (h : (a : ℂ) / 2 = (b : ℂ) / 2) : a = b := by
  have h2 : (a : ℂ) = b := by linear_combination 2 * h
  exact_mod_cast h2

theorem deg2' : W.θ2 1 = (((q : ℤ) + e : ℤ) : ℂ) / 2 := by rw [W.deg2]; push_cast; ring
theorem deg3' : W.θ3 1 = (((q : ℤ) + e : ℤ) : ℂ) / 2 := by rw [W.deg3]; push_cast; ring
theorem deg4' : W.θ4 1 = (((2 * q : ℤ)) : ℂ) / 2 := by rw [W.deg4]; push_cast; ring
theorem degR' {θ : L → ℂ} (hθ : θ ∈ W.RFam) : θ 1 = (((2 * q - 2 * e : ℤ)) : ℂ) / 2 := by
  rw [W.degR θ hθ]; push_cast; ring
theorem degS' {θ : L → ℂ} (hθ : θ ∈ W.SFam) : θ 1 = (((2 * q + 2 * e : ℤ)) : ℂ) / 2 := by
  rw [W.degS θ hθ]; push_cast; ring
omit [Fintype L] in
theorem deg1' : (1 : L → ℂ) 1 = (((2 : ℤ)) : ℂ) / 2 := by simp

omit [Fintype L] in
theorem ne_of_deg_int {θ θ' : L → ℂ} {a b : ℤ} (hθ : θ 1 = (a : ℂ) / 2)
    (hθ' : θ' 1 = (b : ℂ) / 2) (hab : a ≠ b) : θ ≠ θ' := by
  intro h
  apply hab
  apply int_div_two_inj
  rw [← hθ, ← hθ', h]

theorem one_ne_θ2 : (1 : L → ℂ) ≠ W.θ2 :=
  ne_of_deg_int (deg1' (L := L)) W.deg2' (by obtain ⟨h1, h2⟩ := W.int_facts; omega)
theorem one_ne_θ3 : (1 : L → ℂ) ≠ W.θ3 :=
  ne_of_deg_int (deg1' (L := L)) W.deg3' (by obtain ⟨h1, h2⟩ := W.int_facts; omega)
theorem one_ne_θ4 : (1 : L → ℂ) ≠ W.θ4 :=
  ne_of_deg_int (deg1' (L := L)) W.deg4' (by obtain ⟨h1, h2⟩ := W.int_facts; omega)
theorem θ2_ne_θ4 : W.θ2 ≠ W.θ4 :=
  ne_of_deg_int W.deg2' W.deg4' (by obtain ⟨h1, h2⟩ := W.int_facts; omega)
theorem θ3_ne_θ4 : W.θ3 ≠ W.θ4 :=
  ne_of_deg_int W.deg3' W.deg4' (by obtain ⟨h1, h2⟩ := W.int_facts; omega)
theorem one_not_R : (1 : L → ℂ) ∉ W.RFam := fun h =>
  ne_of_deg_int (deg1' (L := L)) (W.degR' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl
theorem θ2_not_R : W.θ2 ∉ W.RFam := fun h =>
  ne_of_deg_int W.deg2' (W.degR' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl
theorem θ3_not_R : W.θ3 ∉ W.RFam := fun h =>
  ne_of_deg_int W.deg3' (W.degR' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl
theorem θ4_not_R : W.θ4 ∉ W.RFam := fun h =>
  ne_of_deg_int W.deg4' (W.degR' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl
theorem one_not_S : (1 : L → ℂ) ∉ W.SFam := fun h =>
  ne_of_deg_int (deg1' (L := L)) (W.degS' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl
theorem θ2_not_S : W.θ2 ∉ W.SFam := fun h =>
  ne_of_deg_int W.deg2' (W.degS' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl
theorem θ3_not_S : W.θ3 ∉ W.SFam := fun h =>
  ne_of_deg_int W.deg3' (W.degS' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl
theorem θ4_not_S : W.θ4 ∉ W.SFam := fun h =>
  ne_of_deg_int W.deg4' (W.degS' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl
theorem R_not_S {θ : L → ℂ} (hθ : θ ∈ W.RFam) : θ ∉ W.SFam := fun h =>
  ne_of_deg_int (W.degR' hθ) (W.degS' h) (by obtain ⟨h1, h2⟩ := W.int_facts; omega) rfl

theorem S_not_R {θ : L → ℂ} (hθ : θ ∈ W.SFam) : θ ∉ W.RFam := fun h => W.R_not_S h hθ

theorem irr_finset : (irreducibles_finite L).toFinset =
    insert 1 (insert W.θ2 (insert W.θ3 (insert W.θ4 (W.RFam ∪ W.SFam)))) := by
  ext θ
  rw [Set.Finite.mem_toFinset, W.mem_irr_iff]
  simp only [Finset.mem_insert, Finset.mem_union]

theorem sum_irr {M : Type*} [AddCommMonoid M] (f : (L → ℂ) → M) :
    ∑ θ ∈ (irreducibles_finite L).toFinset, f θ =
      f 1 + f W.θ2 + f W.θ3 + f W.θ4 + ∑ θ ∈ W.RFam, f θ + ∑ θ ∈ W.SFam, f θ := by
  rw [W.irr_finset]
  have hRS : Disjoint W.RFam W.SFam := Finset.disjoint_left.mpr fun θ hR hS => W.R_not_S hR hS
  rw [Finset.sum_insert (by simp [W.one_ne_θ2, W.one_ne_θ3, W.one_ne_θ4, W.one_not_R,
      W.one_not_S]),
    Finset.sum_insert (by simp [W.θ2_ne_θ3, W.θ2_ne_θ4, W.θ2_not_R, W.θ2_not_S]),
    Finset.sum_insert (by simp [W.θ3_ne_θ4, W.θ3_not_R, W.θ3_not_S]),
    Finset.sum_insert (by simp [W.θ4_not_R, W.θ4_not_S]), Finset.sum_union hRS]
  abel

theorem conj_eq {f : L → ℂ} (hf : f ∈ BlocksIrr L) (g y : L) : f (g⁻¹ * y * g) = f y := by
  have h := blocksVChar_isClassFunction (AddSubgroup.subset_closure hf) y g⁻¹
  rwa [inv_inv] at h

@[expose] noncomputable def Φ1 : L → ℂ := 1 - (e : ℂ) • W.θ4
@[expose] noncomputable def Φ2 : L → ℂ := (-(e : ℂ)) • (W.θ2 + W.θ4)
@[expose] noncomputable def Φ3 : L → ℂ := (-(e : ℂ)) • (W.θ3 + W.θ4)
@[expose] noncomputable def ΦS (θ : L → ℂ) : L → ℂ := θ + W.sbar θ

theorem Φ1_conj (g y : L) : W.Φ1 (g⁻¹ * y * g) = W.Φ1 y := by
  simp only [Φ1, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, conj_eq W.θ4_mem]
theorem Φ2_conj (g y : L) : W.Φ2 (g⁻¹ * y * g) = W.Φ2 y := by
  simp only [Φ2, Pi.smul_apply, Pi.add_apply, conj_eq W.θ2_mem, conj_eq W.θ4_mem]
theorem Φ3_conj (g y : L) : W.Φ3 (g⁻¹ * y * g) = W.Φ3 y := by
  simp only [Φ3, Pi.smul_apply, Pi.add_apply, conj_eq W.θ3_mem, conj_eq W.θ4_mem]

theorem J'_mul_one : W.J' = W.J' * ((1 : W.So) : L) := by simp

theorem θ4_even {y : L} (hy : Even (orderOf y)) : W.θ4 y = e := by
  obtain ⟨g, ρ, hρ, h⟩ := W.even_conj y hy
  rw [← conj_eq W.θ4_mem g y, h, (W.val_J'So ρ hρ).2.2.1]

theorem θ2_even {y : L} (hy : Even (orderOf y)) : W.θ2 y = -e := by
  obtain ⟨g, ρ, hρ, h⟩ := W.even_conj y hy
  rw [← conj_eq W.θ2_mem g y, h, (W.val_J'So ρ hρ).1]

theorem θ3_even {y : L} (hy : Even (orderOf y)) : W.θ3 y = -e := by
  obtain ⟨g, ρ, hρ, h⟩ := W.even_conj y hy
  rw [← conj_eq W.θ3_mem g y, h, (W.val_J'So ρ hρ).2.1]

theorem R_even {θ : L → ℂ} (hθ : θ ∈ W.RFam) {y : L} (hy : Even (orderOf y)) : θ y = 0 := by
  obtain ⟨g, ρ, hρ, h⟩ := W.even_conj y hy
  rw [← conj_eq (W.R_mem hθ) g y, h, (W.val_J'So ρ hρ).2.2.2 θ hθ]

theorem Φ1_even {y : L} (hy : Even (orderOf y)) : W.Φ1 y = 0 := by
  simp only [Φ1, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, W.θ4_even hy]
  linear_combination -W.e_sq_complex

theorem Φ2_even {y : L} (hy : Even (orderOf y)) : W.Φ2 y = 0 := by
  simp only [Φ2, Pi.smul_apply, Pi.add_apply, smul_eq_mul, W.θ2_even hy, W.θ4_even hy]
  ring

theorem Φ3_even {y : L} (hy : Even (orderOf y)) : W.Φ3 y = 0 := by
  simp only [Φ3, Pi.smul_apply, Pi.add_apply, smul_eq_mul, W.θ3_even hy, W.θ4_even hy]
  ring

theorem ΦS_even {θ : L → ℂ} (hθ : θ ∈ W.SFam) {y : L} (hy : Even (orderOf y)) :
    W.ΦS θ y = 0 := by
  obtain ⟨g, ρ, hρ, h⟩ := W.even_conj y hy
  have hθc := conj_eq (W.S_mem hθ) g y
  have hθ'c := conj_eq (W.S_mem (W.sbar_mem θ hθ)) g y
  simp only [ΦS, Pi.add_apply]
  rw [← hθc, ← hθ'c, h, W.valS_J'So θ hθ ⟨ρ, hρ⟩,
    W.valS_J'So (W.sbar θ) (W.sbar_mem θ hθ) ⟨ρ, hρ⟩, W.lam_sbar θ hθ, W.eps_sbar θ hθ]
  push_cast
  ring

theorem odd_values {y : L} (hy : Odd (orderOf y)) :
    W.θ4 y = W.θ2 y + W.θ3 y - e ∧ ∀ θ ∈ W.SFam, W.sbar θ y = θ y := by
  rcases W.odd_classes y hy with rfl | ⟨g, hg, hg1⟩ | ⟨g, hg, hg1⟩ | ⟨h23, h4, -, hS⟩
  · refine ⟨?_, fun θ hθ => ?_⟩
    · rw [W.deg2, W.deg3, W.deg4]
      ring
    · rw [W.degS θ hθ, W.degS _ (W.sbar_mem θ hθ)]
  · obtain ⟨h2, h3, h4, hS⟩ := W.val_Ro _ hg hg1
    refine ⟨?_, fun θ hθ => ?_⟩
    · rw [← conj_eq W.θ4_mem g y, ← conj_eq W.θ2_mem g y, ← conj_eq W.θ3_mem g y, h2, h3, h4]
      ring
    · rw [← conj_eq (W.S_mem hθ) g y, ← conj_eq (W.S_mem (W.sbar_mem θ hθ)) g y,
        hS θ hθ, hS _ (W.sbar_mem θ hθ)]
  · obtain ⟨h2, h3, h4, -⟩ := W.val_So _ hg hg1
    refine ⟨?_, fun θ hθ => ?_⟩
    · rw [← conj_eq W.θ4_mem g y, ← conj_eq W.θ2_mem g y, ← conj_eq W.θ3_mem g y, h2, h3, h4]
      ring
    · have hne : (⟨_, hg⟩ : W.So) ≠ 1 := fun h => hg1 (congrArg Subtype.val h)
      rw [← conj_eq (W.S_mem hθ) g y, ← conj_eq (W.S_mem (W.sbar_mem θ hθ)) g y,
        W.valS_So θ hθ ⟨_, hg⟩ hne, W.valS_So _ (W.sbar_mem θ hθ) ⟨_, hg⟩ hne, W.lam_sbar θ hθ]
  · refine ⟨by rw [h4, h23]; ring, fun θ hθ => ?_⟩
    rw [hS θ hθ, hS _ (W.sbar_mem θ hθ)]

omit [Fintype L] in
theorem conj_e : starRingEnd ℂ (e : ℂ) = e := map_intCast _ e

theorem inner_mem {θ θ' : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hθ' : θ' ∈ BlocksIrr L) :
    BlocksInnerProduct θ θ' = if θ = θ' then 1 else 0 := blocksInnerProduct_irr hθ hθ'

theorem inner_self {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) : BlocksInnerProduct θ θ = 1 := by
  rw [inner_mem hθ hθ]
  simp

theorem inner_ne {θ θ' : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hθ' : θ' ∈ BlocksIrr L) (h : θ ≠ θ') :
    BlocksInnerProduct θ θ' = 0 := by
  rw [inner_mem hθ hθ']
  simp [h]

theorem principal_ne : (1 : L → ℂ) ≠ W.θ2 ∧ (1 : L → ℂ) ≠ W.θ3 ∧ (1 : L → ℂ) ≠ W.θ4 ∧
    W.θ2 ≠ W.θ3 ∧ W.θ2 ≠ W.θ4 ∧ W.θ3 ≠ W.θ4 :=
  ⟨W.one_ne_θ2, W.one_ne_θ3, W.one_ne_θ4, W.θ2_ne_θ3, W.θ2_ne_θ4, W.θ3_ne_θ4⟩

theorem inner_principal :
    BlocksInnerProduct (1 : L → ℂ) 1 = 1 ∧ BlocksInnerProduct (1 : L → ℂ) W.θ2 = 0 ∧
    BlocksInnerProduct (1 : L → ℂ) W.θ3 = 0 ∧ BlocksInnerProduct (1 : L → ℂ) W.θ4 = 0 ∧
    BlocksInnerProduct W.θ2 1 = 0 ∧ BlocksInnerProduct W.θ2 W.θ2 = 1 ∧
    BlocksInnerProduct W.θ2 W.θ3 = 0 ∧ BlocksInnerProduct W.θ2 W.θ4 = 0 ∧
    BlocksInnerProduct W.θ3 1 = 0 ∧ BlocksInnerProduct W.θ3 W.θ2 = 0 ∧
    BlocksInnerProduct W.θ3 W.θ3 = 1 ∧ BlocksInnerProduct W.θ3 W.θ4 = 0 ∧
    BlocksInnerProduct W.θ4 1 = 0 ∧ BlocksInnerProduct W.θ4 W.θ2 = 0 ∧
    BlocksInnerProduct W.θ4 W.θ3 = 0 ∧ BlocksInnerProduct W.θ4 W.θ4 = 1 := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := W.principal_ne
  exact ⟨inner_self W.one_mem, inner_ne W.one_mem W.θ2_mem h12, inner_ne W.one_mem W.θ3_mem h13,
    inner_ne W.one_mem W.θ4_mem h14, inner_ne W.θ2_mem W.one_mem (Ne.symm h12),
    inner_self W.θ2_mem, inner_ne W.θ2_mem W.θ3_mem h23, inner_ne W.θ2_mem W.θ4_mem h24,
    inner_ne W.θ3_mem W.one_mem (Ne.symm h13), inner_ne W.θ3_mem W.θ2_mem (Ne.symm h23),
    inner_self W.θ3_mem, inner_ne W.θ3_mem W.θ4_mem h34,
    inner_ne W.θ4_mem W.one_mem (Ne.symm h14), inner_ne W.θ4_mem W.θ2_mem (Ne.symm h24),
    inner_ne W.θ4_mem W.θ3_mem (Ne.symm h34), inner_self W.θ4_mem⟩

theorem inner_principal_other {θ : L → ℂ} (hθ : θ ∈ W.RFam ∨ θ ∈ W.SFam) :
    BlocksInnerProduct (1 : L → ℂ) θ = 0 ∧ BlocksInnerProduct W.θ2 θ = 0 ∧
    BlocksInnerProduct W.θ3 θ = 0 ∧ BlocksInnerProduct W.θ4 θ = 0 ∧
    BlocksInnerProduct θ 1 = 0 ∧ BlocksInnerProduct θ W.θ2 = 0 ∧
    BlocksInnerProduct θ W.θ3 = 0 ∧ BlocksInnerProduct θ W.θ4 = 0 := by
  have hmem : θ ∈ BlocksIrr L := by rcases hθ with h | h; exacts [W.R_mem h, W.S_mem h]
  have h1 : (1 : L → ℂ) ≠ θ := by
    rintro rfl; rcases hθ with h | h; exacts [W.one_not_R h, W.one_not_S h]
  have h2 : W.θ2 ≠ θ := by
    rintro rfl; rcases hθ with h | h; exacts [W.θ2_not_R h, W.θ2_not_S h]
  have h3 : W.θ3 ≠ θ := by
    rintro rfl; rcases hθ with h | h; exacts [W.θ3_not_R h, W.θ3_not_S h]
  have h4 : W.θ4 ≠ θ := by
    rintro rfl; rcases hθ with h | h; exacts [W.θ4_not_R h, W.θ4_not_S h]
  exact ⟨inner_ne W.one_mem hmem h1, inner_ne W.θ2_mem hmem h2, inner_ne W.θ3_mem hmem h3,
    inner_ne W.θ4_mem hmem h4, inner_ne hmem W.one_mem (Ne.symm h1),
    inner_ne hmem W.θ2_mem (Ne.symm h2), inner_ne hmem W.θ3_mem (Ne.symm h3),
    inner_ne hmem W.θ4_mem (Ne.symm h4)⟩

theorem gram_principal :
    BlocksInnerProduct W.Φ1 W.Φ1 = 2 ∧ BlocksInnerProduct W.Φ1 W.Φ2 = 1 ∧
    BlocksInnerProduct W.Φ1 W.Φ3 = 1 ∧ BlocksInnerProduct W.Φ2 W.Φ1 = 1 ∧
    BlocksInnerProduct W.Φ2 W.Φ2 = 2 ∧ BlocksInnerProduct W.Φ2 W.Φ3 = 1 ∧
    BlocksInnerProduct W.Φ3 W.Φ1 = 1 ∧ BlocksInnerProduct W.Φ3 W.Φ2 = 1 ∧
    BlocksInnerProduct W.Φ3 W.Φ3 = 2 := by
  obtain ⟨i11, i12, i13, i14, i21, i22, i23, i24, i31, i32, i33, i34, i41, i42, i43, i44⟩ :=
    W.inner_principal
  have he := W.e_sq_complex
  simp only [Φ1, Φ2, Φ3, blocksInnerProduct_sub_left, blocksInnerProduct_sub_right,
    blocksInnerProduct_add_left, blocksInnerProduct_add_right, blocksInnerProduct_smul_left,
    blocksInnerProduct_smul_right, map_neg, conj_e, i11, i12, i13, i14, i21, i22, i23, i24,
    i31, i32, i33, i34, i41, i42, i43, i44]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | linear_combination he | linear_combination 2 * he

theorem gram_principal_other {θ : L → ℂ} (hθ : θ ∈ W.RFam ∨ θ ∈ W.SFam) :
    BlocksInnerProduct W.Φ1 θ = 0 ∧ BlocksInnerProduct W.Φ2 θ = 0 ∧
    BlocksInnerProduct W.Φ3 θ = 0 ∧ BlocksInnerProduct θ W.Φ1 = 0 ∧
    BlocksInnerProduct θ W.Φ2 = 0 ∧ BlocksInnerProduct θ W.Φ3 = 0 := by
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩ := W.inner_principal_other hθ
  simp only [Φ1, Φ2, Φ3, blocksInnerProduct_sub_left, blocksInnerProduct_sub_right,
    blocksInnerProduct_add_left, blocksInnerProduct_add_right, blocksInnerProduct_smul_left,
    blocksInnerProduct_smul_right, map_neg, conj_e, a1, a2, a3, a4, b1, b2, b3, b4]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem inner_RS {θ θ' : L → ℂ} (hθ : θ ∈ W.RFam ∨ θ ∈ W.SFam)
    (hθ' : θ' ∈ W.RFam ∨ θ' ∈ W.SFam) :
    BlocksInnerProduct θ θ' = if θ = θ' then 1 else 0 := by
  have hmem : ∀ {φ : L → ℂ}, (φ ∈ W.RFam ∨ φ ∈ W.SFam) → φ ∈ BlocksIrr L := by
    intro φ h; rcases h with h | h; exacts [W.R_mem h, W.S_mem h]
  exact inner_mem (hmem hθ) (hmem hθ')

theorem gram_principal_S {θ : L → ℂ} (hθ : θ ∈ W.SFam) :
    BlocksInnerProduct W.Φ1 (W.ΦS θ) = 0 ∧ BlocksInnerProduct W.Φ2 (W.ΦS θ) = 0 ∧
    BlocksInnerProduct W.Φ3 (W.ΦS θ) = 0 ∧ BlocksInnerProduct (W.ΦS θ) W.Φ1 = 0 ∧
    BlocksInnerProduct (W.ΦS θ) W.Φ2 = 0 ∧ BlocksInnerProduct (W.ΦS θ) W.Φ3 = 0 := by
  obtain ⟨a1, a2, a3, b1, b2, b3⟩ := W.gram_principal_other (Or.inr hθ)
  obtain ⟨c1, c2, c3, d1, d2, d3⟩ := W.gram_principal_other (Or.inr (W.sbar_mem θ hθ))
  simp only [ΦS, blocksInnerProduct_add_left, blocksInnerProduct_add_right, a1, a2, a3, b1, b2,
    b3, c1, c2, c3, d1, d2, d3, add_zero, and_self]

theorem gram_R_S {θ θ' : L → ℂ} (hθ : θ ∈ W.RFam) (hθ' : θ' ∈ W.SFam) :
    BlocksInnerProduct θ (W.ΦS θ') = 0 ∧ BlocksInnerProduct (W.ΦS θ') θ = 0 := by
  have hne : ∀ φ ∈ W.SFam, θ ≠ φ := fun φ hφ h => W.R_not_S hθ (h ▸ hφ)
  simp only [ΦS, blocksInnerProduct_add_left, blocksInnerProduct_add_right,
    W.inner_RS (Or.inl hθ) (Or.inr hθ'), W.inner_RS (Or.inl hθ) (Or.inr (W.sbar_mem θ' hθ')),
    W.inner_RS (Or.inr hθ') (Or.inl hθ), W.inner_RS (Or.inr (W.sbar_mem θ' hθ')) (Or.inl hθ),
    hne θ' hθ', hne _ (W.sbar_mem θ' hθ'), (hne θ' hθ').symm, (hne _ (W.sbar_mem θ' hθ')).symm,
    ↓reduceIte, add_zero, and_self]

theorem gram_S {θ θ' : L → ℂ} (hθ : θ ∈ W.SFam) (hθ' : θ' ∈ W.SFam) :
    BlocksInnerProduct (W.ΦS θ) (W.ΦS θ') =
      if θ' = θ ∨ θ' = W.sbar θ then 2 else 0 := by
  have hθb := W.sbar_mem θ hθ
  have hθb' := W.sbar_mem θ' hθ'
  simp only [ΦS, blocksInnerProduct_add_left, blocksInnerProduct_add_right,
    W.inner_RS (Or.inr hθ) (Or.inr hθ'), W.inner_RS (Or.inr hθ) (Or.inr hθb'),
    W.inner_RS (Or.inr hθb) (Or.inr hθ'), W.inner_RS (Or.inr hθb) (Or.inr hθb')]
  by_cases h1 : θ' = θ
  · subst h1
    have hne := W.sbar_ne θ' hθ'
    simp [hne, Ne.symm hne]
    norm_num
  · by_cases h2 : θ' = W.sbar θ
    · subst h2
      have hne := W.sbar_ne θ hθ
      simp [W.sbar_sbar θ hθ, hne, Ne.symm hne]
      norm_num
    · have h3 : θ ≠ W.sbar θ' := by
        intro h
        apply h2
        rw [h, W.sbar_sbar θ' hθ']
      have h4 : W.sbar θ ≠ W.sbar θ' := by
        intro h
        apply h1
        rw [← W.sbar_sbar θ hθ, h, W.sbar_sbar θ' hθ']
      simp [Ne.symm h1, h3, Ne.symm h2, h4, h1, h2]

end WardL

end CFSG.Walter.Ward
