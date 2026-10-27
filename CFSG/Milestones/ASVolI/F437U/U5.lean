module

public import CFSG.Milestones.ASVolI.F437U.U4
public import CFSG.Milestones.ASVolI.F431.BF436U5B
public import CFSG.Milestones.ASVolI.F429.bC2cU5Sp
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F429.aC7Gen

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.U5
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit

section U5Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem burnsideF437U_sum5 {M : Type*} [AddCommMonoid M] (g : HypIndex 2 1 → M) :
    ∑ a, g a = g ιe₁ + g ιe₂ + g ιz + g ιf₁ + g ιf₂ := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one]
  abel

theorem burnsideF437U_U5_hC :
    (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) + ((!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).map
      h.bar)ᵀ = -vecMulVec ![(0 : K), 0] fun j => h.bar (![(0 : K), 0] j) := by
  have := h.charP
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vecMulVec, CharTwo.add_self_eq_zero]

@[expose] noncomputable def burnsideF437U_U5_u : hypSU h 2 1 :=
  Classical.choose (exists_U_of_coord h 1 ![0, 0] !![0, 0; 0, 1] (burnsideF437U_U5_hC h))

theorem burnsideF437U_U5_u_U : burnsideF437U_U5_u h ∈ hypUnitriangular h 2 1 :=
  (Classical.choose_spec
    (exists_U_of_coord h 1 ![0, 0] !![0, 0; 0, 1] (burnsideF437U_U5_hC h))).1

theorem burnsideF437U_U5_mat_u (a b : HypIndex 2 1) :
    mat (burnsideF437U_U5_u h) a b =
      if a = b ∨ (a = ιe₁ ∧ b = ιe₂) ∨ (a = ιe₂ ∧ b = ιf₂) ∨ (a = ιe₁ ∧ b = ιf₂) ∨
        (a = ιf₂ ∧ b = ιf₁) then 1 else 0 := by
  have := h.charP
  obtain ⟨hU, c1, c2, c3, c4, c5, c6, c7⟩ := Classical.choose_spec
    (exists_U_of_coord h 1 ![0, 0] !![0, 0; 0, 1] (burnsideF437U_U5_hC h))
  change mat (burnsideF437U_U5_u h) _ _ = _ at c1 c2 c3 c4 c5 c6 c7
  have hU' : burnsideF437U_U5_u h ∈ hypUnitriangular h 2 1 := hU
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hU'
  obtain ⟨r1, r2, r3, r4, -, -⟩ := U_rel hU'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, add_zero, mul_zero, zero_add,
    mul_one] at c1 c2 c3 c4 c5 c6 c7
  simp only [c1, c2, c3, c5, c7, map_one, map_zero, mul_zero, zero_mul, one_mul, mul_one,
    add_zero, zero_add, CharTwo.add_self_eq_zero] at r1 r2 r3 r4
  rcases hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases hypIndex_cases b with rfl | rfl | rfl | rfl | rfl <;>
    simp_all

theorem burnsideF437U_U5_frob_u :
    (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom (burnsideF437U_U5_u h) =
      burnsideF437U_U5_u h := by
  apply mat_injective
  show (((fieldHom h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) (burnsideF437U_U5_u h) :
    hypSU h 2 1) : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
  rw [mat_fieldHom]
  ext a b
  rw [map_apply]
  change CFSG.Quasithin.H13.F431.Un.OL5.bar5 h (mat (burnsideF437U_U5_u h) a b) =
    mat (burnsideF437U_U5_u h) a b
  rw [burnsideF437U_U5_mat_u]
  split_ifs <;> simp

theorem burnsideF437U_U5_iso (y : hypSU h 2 1) (b : HypIndex 2 1) (hb : hypPartner b ≠ b) :
    ∑ a, h.bar (mat y (hypPartner a) b) * mat y a b = 0 := by
  have e := congrFun (congrFun (congrArg mat (inv_mul_cancel y)) (hypPartner b)) b
  rw [mat_mul, mul_apply, mat_one, one_apply_ne hb] at e
  simpa only [mat_inv_apply, hypPartner_hypPartner] using e

theorem burnsideF437U_bar_mul_self_eq_zero {c : K} (hc : h.bar c * c = 0) : c = 0 := by
  rcases mul_eq_zero.mp hc with h0 | h0
  · have := congrArg h.bar h0
    rwa [h.bar_bar, map_zero] at this
  · exact h0

theorem burnsideF437U_U5_borel : u5PtStab h ⊓ u5LnStab h = hypBorel h 2 1 := by
  ext g
  rw [Subgroup.mem_inf, mem_hypBorel]
  constructor
  · rintro ⟨g1, g2⟩ i hi1 hi2
    interval_cases i
    · exact UnitaryHigher.mem_isoStabilizer.mp g1
    · exact UnitaryHigher.mem_isoStabilizer.mp g2
  · intro hg
    exact ⟨UnitaryHigher.mem_isoStabilizer.mpr (hg 1 le_rfl (by norm_num)),
      UnitaryHigher.mem_isoStabilizer.mpr (hg 2 (by norm_num) le_rfl)⟩

theorem burnsideF437U_U5_U_sylow [Finite K] :
    IsSylowOf 2 (hypUnitriangular h 2 1) (⊤ : Subgroup (hypSU h 2 1)) := by
  obtain ⟨P, hP⟩ := (unitary_order_and_Sylow (r := 2) (ε := 1) h (by norm_num) (by norm_num)).2.1
  have := CFSG.Quasithin.H13.U4Par.isSylowTwoOf_top_of_sylow P
  rw [hP] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

theorem burnsideF437U_U5_pCore [Finite K] :
    pCoreOf 2 (u5PtStab h ⊓ u5LnStab h) = hypUnitriangular h 2 1 := by
  rw [burnsideF437U_U5_borel]
  have hN := UnitaryHigher.normalizer_hypUnitriangular h (r := 2) (ε := 1) (by norm_num)
    (by norm_num)
  refine burnsideF429a_pCoreOf_eq_of_sylow (burnsideF429_isSylowOf_of_le
    (burnsideF437U_U5_U_sylow h) (hypUnitriangular_le_hypBorel h) le_top) ?_
  intro b hb u hu
  rw [← hN] at hb
  exact (Subgroup.mem_normalizer_iff.mp hb u).mp hu

theorem burnsideF437U_U5_reg (g : hypSU h 2 1)
    (hg : g * burnsideF437U_U5_u h * g⁻¹ ∈ hypUnitriangular h 2 1) :
    g ∈ u5PtStab h ⊓ u5LnStab h := by
  have := h.charP
  obtain ⟨⟨x11, x22, -, -, -⟩, ⟨x21, x31, x51, x41, x32, x52, x42, -, -, -⟩⟩ := U_entries hg
  have hux : burnsideF437U_U5_u h * g⁻¹ = g⁻¹ * (g * burnsideF437U_U5_u h * g⁻¹) := by group
  have hM : mat (burnsideF437U_U5_u h) * mat g⁻¹ =
      mat g⁻¹ * mat (g * burnsideF437U_U5_u h * g⁻¹) := by
    rw [← mat_mul, ← mat_mul, hux]
  have e := fun a b => congrFun (congrFun hM a) b
  have c11 := e ιe₁ ιe₁
  have c21 := e ιe₂ ιe₁
  have c51 := e ιf₂ ιe₁
  have c22 := e ιe₂ ιe₂
  have c52 := e ιf₂ ιe₂
  simp only [mul_apply, burnsideF437U_sum5, burnsideF437U_U5_mat_u] at c11 c21 c51 c22 c52
  simp only [x21, x31, x51, x41, x32, x52, x42, x11, x22] at c11 c21 c51 c22 c52
  simp at c11 c21 c51 c22 c52
  set Y := mat g⁻¹ with hY
  have y51 : Y ιf₂ ιe₁ = 0 := by linear_combination c21
  have y41 : Y ιf₁ ιe₁ = 0 := by linear_combination c51
  have y21 : Y ιe₂ ιe₁ = 0 := by linear_combination c11 - c21
  have y52 : Y ιf₂ ιe₂ = 0 := by
    linear_combination c22 + mat (g * burnsideF437U_U5_u h * g⁻¹) ιe₁ ιe₂ * y21
  have y42 : Y ιf₁ ιe₂ = 0 := by
    linear_combination c52 + mat (g * burnsideF437U_U5_u h * g⁻¹) ιe₁ ιe₂ * y51
  have i1 := burnsideF437U_U5_iso h g⁻¹ ιe₁ (by decide)
  have i2 := burnsideF437U_U5_iso h g⁻¹ ιe₂ (by decide)
  simp only [burnsideF437U_sum5, hypPartner_inl, hypPartner_inr_inl, hypPartner_inr_inr] at i1 i2
  rw [← hY, y51, y41, y21] at i1
  rw [← hY, y52, y42] at i2
  simp only [map_zero, zero_mul, mul_zero, zero_add, add_zero] at i1 i2
  have y31 : Y ιz ιe₁ = 0 := burnsideF437U_bar_mul_self_eq_zero h i1
  have y32 : Y ιz ιe₂ = 0 := burnsideF437U_bar_mul_self_eq_zero h i2
  have hyP : g⁻¹ ∈ u5PtStab h := by
    rw [mem_u5PtStab_iff]
    intro a ha
    rcases hypIndex_cases a with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl ha
    · exact y21
    · exact y31
    · exact y51
    · exact y41
  have hyL : g⁻¹ ∈ u5LnStab h := by
    rw [mem_u5LnStab_iff]
    rintro a b (rfl | rfl) (rfl | rfl | rfl)
    · exact y31
    · exact y51
    · exact y41
    · exact y32
    · exact y52
    · exact y42
  have := (u5PtStab h ⊓ u5LnStab h).inv_mem (Subgroup.mem_inf.mpr ⟨hyP, hyL⟩)
  rwa [inv_inv] at this

theorem burnsideF437U_U5_reg₁ (g : hypSU h 2 1)
    (hg : g * burnsideF437U_U5_u h * g⁻¹ ∈ u5PtStab h) : g ∈ u5PtStab h := by
  have := h.charP
  rw [mem_u5PtStab_iff] at hg
  have x21 := hg ιe₂ (by decide)
  have x31 := hg ιz (by decide)
  have x51 := hg ιf₂ (by decide)
  have x41 := hg ιf₁ (by decide)
  set l := mat (g * burnsideF437U_U5_u h * g⁻¹) ιe₁ ιe₁ with hl
  have hux : burnsideF437U_U5_u h * g⁻¹ = g⁻¹ * (g * burnsideF437U_U5_u h * g⁻¹) := by group
  have hM : mat (burnsideF437U_U5_u h) * mat g⁻¹ =
      mat g⁻¹ * mat (g * burnsideF437U_U5_u h * g⁻¹) := by
    rw [← mat_mul, ← mat_mul, hux]
  have e := fun a b => congrFun (congrFun hM a) b
  have c11 := e ιe₁ ιe₁
  have c21 := e ιe₂ ιe₁
  have c31 := e ιz ιe₁
  have c41 := e ιf₁ ιe₁
  have c51 := e ιf₂ ιe₁
  simp only [mul_apply, burnsideF437U_sum5, burnsideF437U_U5_mat_u] at c11 c21 c31 c41 c51
  simp only [x21, x31, x51, x41, ← hl] at c11 c21 c31 c41 c51
  simp at c11 c21 c31 c41 c51
  set Y := mat g⁻¹ with hY
  have hcol : Y ιf₁ ιe₁ = 0 ∧ Y ιf₂ ιe₁ = 0 ∧ Y ιe₂ ιe₁ = 0 := by
    by_cases hl1 : l = 1
    · rw [hl1] at c11 c21 c51
      refine ⟨by linear_combination c51, by linear_combination c21, ?_⟩
      linear_combination c11 - c21
    · exfalso
      have hl1' : (1 : K) - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
      have y4 : Y ιf₁ ιe₁ = 0 := by
        have : Y ιf₁ ιe₁ * (1 - l) = 0 := by linear_combination c41
        exact (mul_eq_zero.mp this).resolve_right hl1'
      have y5 : Y ιf₂ ιe₁ = 0 := by
        have : Y ιf₂ ιe₁ * (1 - l) = 0 := by linear_combination c51 - y4
        exact (mul_eq_zero.mp this).resolve_right hl1'
      have y3 : Y ιz ιe₁ = 0 := by
        have : Y ιz ιe₁ * (1 - l) = 0 := by linear_combination c31
        exact (mul_eq_zero.mp this).resolve_right hl1'
      have y2 : Y ιe₂ ιe₁ = 0 := by
        have : Y ιe₂ ιe₁ * (1 - l) = 0 := by linear_combination c21 - y5
        exact (mul_eq_zero.mp this).resolve_right hl1'
      have y1 : Y ιe₁ ιe₁ = 0 := by
        have : Y ιe₁ ιe₁ * (1 - l) = 0 := by linear_combination c11 - y2 - y5
        exact (mul_eq_zero.mp this).resolve_right hl1'
      have hone := congrFun (congrFun (congrArg mat (inv_mul_cancel g⁻¹)) ιe₁) ιe₁
      rw [mat_mul, mul_apply, burnsideF437U_sum5, mat_one, one_apply_eq] at hone
      rw [← hY, y1, y2, y3, y4, y5] at hone
      simp at hone
  obtain ⟨y41, y51, y21⟩ := hcol
  have i1 := burnsideF437U_U5_iso h g⁻¹ ιe₁ (by decide)
  simp only [burnsideF437U_sum5, hypPartner_inl, hypPartner_inr_inl, hypPartner_inr_inr] at i1
  rw [← hY, y51, y41, y21] at i1
  simp only [map_zero, zero_mul, mul_zero, zero_add, add_zero] at i1
  have y31 : Y ιz ιe₁ = 0 := burnsideF437U_bar_mul_self_eq_zero h i1
  have hyP : g⁻¹ ∈ u5PtStab h := by
    rw [mem_u5PtStab_iff]
    intro a ha
    rcases hypIndex_cases a with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl ha
    · exact y21
    · exact y31
    · exact y51
    · exact y41
  have := (u5PtStab h).inv_mem hyP
  rwa [inv_inv] at this

theorem burnsideF437U_U5_mem_fix (g : hypSU h 2 1) :
    g ∈ burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom ↔
      ∀ a b, h.bar (mat g a b) = mat g a b := by
  rw [burnsideF437U_mem_fix]
  have hm : mat ((fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom g) =
      (mat g).map h.bar := by
    show (((fieldHom h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) g : hypSU h 2 1) :
      GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
    rw [mat_fieldHom]
    rfl
  constructor
  · intro hg a b
    have := congrFun (congrFun (congrArg mat hg) a) b
    rw [hm, Matrix.map_apply] at this
    exact this
  · intro hg
    apply mat_injective
    rw [hm]
    ext a b
    exact hg a b

theorem burnsideF437U_U5_range_spEmb :
    (burnsideF429b_U5_spEmb h).range =
      burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom := by
  ext g
  rw [burnsideF437U_U5_mem_fix]
  constructor
  · rintro ⟨A, rfl⟩ a b
    have := congrFun (congrFun (burnsideF429b_U5_incl_bar h
      ((A : GL (Fin 2 ⊕ Fin 2) h.fixedField) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField))
      a) b
    rw [Matrix.map_apply] at this
    rw [burnsideF429b_U5_mat_spEmb]
    exact this
  · intro hg
    exact burnsideF429b_U5_exists_spEmb h g hg

theorem burnsideF437U_U5_idx_vals :
    burnsideF429b_U5_idx.symm (.inl (.inl 0)) = ιe₁ ∧
      burnsideF429b_U5_idx.symm (.inl (.inl 1)) = ιe₂ ∧
      burnsideF429b_U5_idx.symm (.inl (.inr 0)) = ιf₁ ∧
      burnsideF429b_U5_idx.symm (.inl (.inr 1)) = ιf₂ := ⟨rfl, rfl, rfl, rfl⟩

theorem burnsideF437U_U5_spEmb_mem_pt (A : StatedSp 2 h.fixedField) :
    burnsideF429b_U5_spEmb h A ∈ u5PtStab h ↔ ∀ b, b ≠ Sum.inl 0 →
      ((A : GL (Fin 2 ⊕ Fin 2) h.fixedField) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField)
        b (Sum.inl 0) = 0 := by
  rw [mem_u5PtStab_iff, burnsideF429b_U5_mat_spEmb]
  constructor
  · intro hA b hb
    have := hA (burnsideF429b_U5_idx.symm (.inl b)) (fun e => hb (Sum.inl_injective
      (burnsideF429b_U5_idx.symm.injective (e.trans burnsideF437U_U5_idx_vals.1.symm))))
    rw [← burnsideF437U_U5_idx_vals.1, burnsideF429b_U5_incl_apply] at this
    exact Subtype.ext this
  · intro hA a ha
    rcases burnsideF429b_U5_idx_cases a with rfl | ⟨a', rfl⟩
    · rw [burnsideF429b_U5_incl_z_left]
      simp
    · rw [← burnsideF437U_U5_idx_vals.1, burnsideF429b_U5_incl_apply,
        hA a' (fun e => ha (by rw [e]; rfl))]
      rfl

theorem burnsideF437U_U5_spEmb_mem_ln (A : StatedSp 2 h.fixedField) :
    burnsideF429b_U5_spEmb h A ∈ u5LnStab h ↔
      ∀ i j, burnsideF4m_spM A (Sum.inr i) (Sum.inl j) = 0 := by
  rw [mem_u5LnStab_iff, burnsideF429b_U5_mat_spEmb]
  obtain ⟨v1, v2, v3, v4⟩ := burnsideF437U_U5_idx_vals
  constructor
  · intro hA i j
    have := hA (burnsideF429b_U5_idx.symm (.inl (.inr i)))
      (burnsideF429b_U5_idx.symm (.inl (.inl j)))
      (by fin_cases j <;> simp [v1, v2]) (by fin_cases i <;> simp [v3, v4])
    rw [burnsideF429b_U5_incl_apply] at this
    exact Subtype.ext this
  · rintro hA a b hb ha
    have hb' : b = burnsideF429b_U5_idx.symm (.inl (.inl 0)) ∨
        b = burnsideF429b_U5_idx.symm (.inl (.inl 1)) := by rw [v1, v2]; exact hb
    rcases ha with rfl | rfl | rfl
    · rw [burnsideF429b_U5_incl_z_left]
      rcases hb with rfl | rfl <;> simp
    · rcases hb' with rfl | rfl
      · rw [← v4, burnsideF429b_U5_incl_apply]
        exact congrArg Subtype.val (hA 1 0)
      · rw [← v4, burnsideF429b_U5_incl_apply]
        exact congrArg Subtype.val (hA 1 1)
    · rcases hb' with rfl | rfl
      · rw [← v3, burnsideF429b_U5_incl_apply]
        exact congrArg Subtype.val (hA 0 0)
      · rw [← v3, burnsideF429b_U5_incl_apply]
        exact congrArg Subtype.val (hA 0 1)

theorem burnsideF437U_U5_map_Q0 :
    (CFSG.QuasithinUnique.Setup.X7a.Q2 h.fixedField 0).map (burnsideF429b_U5_spEmb h) =
      u5PtStab h ⊓
        burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    exact ⟨(burnsideF437U_U5_spEmb_mem_pt h A).mpr (CFSG.Quasithin.H13.U4Par.col_of_mem_Q2_zero hA),
      burnsideF437U_U5_range_spEmb h ▸ ⟨A, rfl⟩⟩
  · rintro g ⟨hgP, hgF⟩
    rw [← burnsideF437U_U5_range_spEmb h] at hgF
    obtain ⟨A, rfl⟩ := hgF
    refine ⟨A, CFSG.Quasithin.H13.U4Par.mem_Q2_zero_of_col
      ((burnsideF437U_U5_spEmb_mem_pt h A).mp hgP) ?_, rfl⟩
    have hinv : burnsideF429b_U5_spEmb h A⁻¹ ∈ u5PtStab h := by
      rw [map_inv]
      exact (u5PtStab h).inv_mem hgP
    exact (burnsideF437U_U5_spEmb_mem_pt h A⁻¹).mp hinv

theorem burnsideF437U_U5_map_Q1 :
    (CFSG.QuasithinUnique.Setup.X7a.Q2 h.fixedField 1).map (burnsideF429b_U5_spEmb h) =
      u5LnStab h ⊓
        burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨A, hA, rfl⟩
    exact ⟨(burnsideF437U_U5_spEmb_mem_ln h A).mpr (burnsideF4m_spQ1_bl hA),
      burnsideF437U_U5_range_spEmb h ▸ ⟨A, rfl⟩⟩
  · rintro g ⟨hgP, hgF⟩
    rw [← burnsideF437U_U5_range_spEmb h] at hgF
    obtain ⟨A, rfl⟩ := hgF
    refine ⟨A, burnsideF4m_spQ1_of_bl ((burnsideF437U_U5_spEmb_mem_ln h A).mp hgP) ?_, rfl⟩
    have hinv : burnsideF429b_U5_spEmb h A⁻¹ ∈ u5LnStab h := by
      rw [map_inv]
      exact (u5LnStab h).inv_mem hgP
    exact (burnsideF437U_U5_spEmb_mem_ln h A⁻¹).mp hinv

theorem burnsideF437U_U5_par [Finite K] :
    IsLieParabolics 2
      (burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom)
      (burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom ⊓
        (u5PtStab h ⊓ u5LnStab h))
      (burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom ⊓
        u5PtStab h)
      (burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom ⊓
        u5LnStab h) := by
  haveI := CFSG.Quasithin.H13.U4Par.charP_fixedField h
  haveI : Finite h.fixedField := Subtype.finite
  have hmap := burnsideF48_isLieParabolics_map (burnsideF429b_U5_spEmb h)
    (burnsideF429b_U5_spEmb_injective h) (burnsideF437U_sp_isLieParabolics h.fixedField)
  rw [Subgroup.map_inf_eq _ _ _ (burnsideF429b_U5_spEmb_injective h), burnsideF437U_U5_map_Q0,
    burnsideF437U_U5_map_Q1, ← MonoidHom.range_eq_map, burnsideF437U_U5_range_spEmb] at hmap
  set F := burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom
  have e1 : F ⊓ (u5PtStab h ⊓ u5LnStab h) = u5PtStab h ⊓ F ⊓ (u5LnStab h ⊓ F) := by
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [e1, inf_comm F (u5PtStab h), inf_comm F (u5LnStab h)]
  exact hmap

theorem burnsideF437U_U5_ctr [Finite K] (z : hypSU h 2 1)
    (hz : z ∈ burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom)
    (hc : ∀ y ∈ burnsideF437U_fix (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom,
      z * y = y * z) : z = 1 := by
  haveI := CFSG.Quasithin.H13.U4Par.charP_fixedField h
  haveI : Finite h.fixedField := Subtype.finite
  rw [← burnsideF437U_U5_range_spEmb] at hz
  obtain ⟨A, rfl⟩ := hz
  have hA : A ∈ Subgroup.center (StatedSp 2 h.fixedField) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have := hc (burnsideF429b_U5_spEmb h B) (by rw [← burnsideF437U_U5_range_spEmb]; exact ⟨B, rfl⟩)
    rw [← map_mul, ← map_mul] at this
    exact (burnsideF429b_U5_spEmb_injective h this).symm
  rw [CFSG.HardMathSupport.Dickson.Bal207.center_statedSp_eq_bot_of_charP_two,
    Subgroup.mem_bot] at hA
  rw [hA, map_one]

end U5Model

section U5Main

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF437U_U5_model (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂) {fb : E}
    (hgr : hyp.toHypF_4_4g.chart.IsGraphInv fb) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 1 K) (φ : hypSU h 2 1 →* E),
      Function.Injective φ ∧ φ.range = Gp ∧ Gp ⊓ M₁ = (u5PtStab h).map φ ∧
      Gp ⊓ M₂ = (u5LnStab h).map φ ∧ ∃ a : hypSU h 2 1, ∀ x, fb * φ x * fb⁻¹ =
        φ (a * (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom (a⁻¹ * x * a) *
          a⁻¹) := by
  obtain ⟨K, fK, h, Ψ, a, h1, h2, hs⟩ := burnsideF4m_u5_exists_frob_conj hyp.toHypF_4_4g hgr
  have hπ : Function.Bijective (hypProj h 2 1) :=
    ⟨burnsideF4m_u5_proj_injective h, hypProj_surjective h 2 1⟩
  set π' : hypSU h 2 1 ≃* hypPSU h 2 1 := MulEquiv.ofBijective (hypProj h 2 1) hπ with hπ'
  set φ : hypSU h 2 1 →* E := Gp.subtype.comp (Ψ.toMonoidHom.comp (hypProj h 2 1)) with hφdef
  have hφ : Function.Injective φ :=
    Gp.subtype_injective.comp (Ψ.injective.comp (burnsideF4m_u5_proj_injective h))
  have hrange : φ.range = Gp := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      (hypProj_surjective h 2 1), ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr
      Ψ.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap : ∀ Q : Subgroup (hypSU h 2 1),
      (Q.map (hypProj h 2 1)).map (Gp.subtype.comp Ψ.toMonoidHom) = Q.map φ := by
    intro Q
    rw [Subgroup.map_map]
    rfl
  refine ⟨K, fK, h, φ, hφ, hrange, ?_, ?_, π'.symm (Ψ.symm a), fun x => ?_⟩
  · rw [h1, ← hmap]
    rfl
  · rw [h2, ← hmap]
    rfl
  · set a' := π'.symm (Ψ.symm a) with ha'
    have hφa : φ a' = (a : E) := by
      show ((Ψ (hypProj h 2 1 (π'.symm (Ψ.symm a))) : ↥Gp) : E) = (a : E)
      have : hypProj h 2 1 (π'.symm (Ψ.symm a)) = Ψ.symm a := π'.apply_symm_apply (Ψ.symm a)
      rw [this, MulEquiv.apply_symm_apply]
    have e2 : ((Ψ (hypProj h 2 1 (a'⁻¹ * x * a')) : ↥Gp) : E) = (a : E)⁻¹ * φ x * a := by
      rw [← hφa]
      simp [hφdef, map_mul, map_inv]
    have hγ : hypProj h 2 1 ((fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom
        (a'⁻¹ * x * a')) = fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)
          (hypProj h 2 1 (a'⁻¹ * x * a')) := (fieldP_apply h _ _).symm
    rw [map_mul, map_mul, map_inv, hφa]
    show fb * φ x * fb⁻¹ = (a : E) * ((Ψ (hypProj h 2 1
      ((fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom (a'⁻¹ * x * a'))) :
        ↥Gp) : E) * (a : E)⁻¹
    rw [hγ, ← hs, e2]
    group

theorem burnsideF437U_fixedInputDeg_U5 : burnsideF437_FixedInputDeg .U5 1 := by
  intro E _ Gp M₁ M₂ hyp fb hinv hFG
  haveI := hyp.finite
  haveI := hyp.normal
  have hfield : ¬ hyp.toHypF_4_4g.chart.IsFieldInv fb := by
    rintro ⟨-, -, sd, hsd, hdeg, -⟩
    omega
  have hgr : hyp.toHypF_4_4g.chart.IsGraphInv fb := hFG.resolve_left hfield
  have hidx : Gp.index = 2 := by
    rcases burnsideF429_F429_one_Un_two (Or.inr rfl) hyp with h | h
    · exact absurd (h ▸ Subgroup.mem_top fb) hinv.not_mem
    · exact h.1
  obtain ⟨K, fK, h, φ, hφ, hrange, h1, h2, a, hact⟩ := burnsideF437U_U5_model hyp hgr
  haveI : Finite K := h.finite
  have hpc := burnsideF437U_U5_pCore h
  obtain ⟨hpar, huniq, hrig⟩ := burnsideF437U_fixedFacts_of_model φ hφ hrange
    (fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)).toMonoidHom h1 h2
    (burnsideF437U_U5_frob_u h) (by rw [hpc]; exact burnsideF437U_U5_u_U h)
    (fun g hg => burnsideF437U_U5_reg h g (by rwa [hpc] at hg))
    (by rw [hpc]; exact burnsideF437U_U5_U_sylow h) (burnsideF437U_U5_par h)
    (burnsideF437U_U5_ctr h) hidx hinv a hact
  exact ⟨fun hf => absurd hf hfield, hpar, huniq, hrig⟩

end U5Main

end CFSG.ASVolI
