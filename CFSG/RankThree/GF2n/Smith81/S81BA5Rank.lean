module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Geom
public import CFSG.RankThree.GF2n.Smith81.S81BA5Form
public import CFSG.RankThree.GF2n.Smith81.S81BRank

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

theorem finrank_S0 : Module.finrank K (S0 K) = 3 := by
  let L : (Fin 3 → K) →ₗ[K] (Fin 6 → K) :=
    { toFun := fun x => ![x 0, 0, x 1, 0, x 2, 0]
      map_add' := by
        intro x y
        funext j
        fin_cases j <;> simp
      map_smul' := by
        intro c x
        funext j
        fin_cases j <;> simp }
  have hinj : Function.Injective L := by
    intro x y hxy
    have h0 := congrFun hxy 0
    have h1 := congrFun hxy 2
    have h2 := congrFun hxy 4
    funext j
    fin_cases j <;> simp_all [L]
  have hrange : LinearMap.range L = S0 K := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      show ∀ j : Fin 6, j.val % 2 = 1 → L x j = 0
      intro j hj
      fin_cases j <;> simp_all [L]
    · intro hv
      have hv' : ∀ j : Fin 6, j.val % 2 = 1 → v j = 0 := hv
      have h1 : v 1 = 0 := hv' 1 (by decide)
      have h3 : v 3 = 0 := hv' 3 (by decide)
      have h5 : v 5 = 0 := hv' 5 (by decide)
      refine ⟨![v 0, v 2, v 4], ?_⟩
      funext j
      fin_cases j <;> simp [L, h1, h3, h5]
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

theorem finrank_imgS0 (G : GL (Fin 6) K) : Module.finrank K (imgS0 G) = 3 := by
  have hinj : Function.Injective (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)) := by
    rw [Matrix.coe_mulVecLin]
    exact Matrix.mulVec_injective_iff_isUnit.2 G.isUnit
  rw [imgS0, ← (Submodule.equivMapOfInjective _ hinj (S0 K)).finrank_eq]
  exact finrank_S0

private theorem a8_imgS0_mul (H G : GL (Fin 6) K) :
    imgS0 (H * G) = (imgS0 G).map (Matrix.mulVecLin (H : Matrix (Fin 6) (Fin 6) K)) := by
  unfold imgS0
  rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

private theorem a8_span_smul_image {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*}
    (s : Set ι) (f : ι → V) (d : ι → K) (hd : ∀ i, d i ≠ 0) :
    Submodule.span K ((fun i => d i • f i) '' s) = Submodule.span K (f '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have h1 : d i • f i ∈ Submodule.span K ((fun i => d i • f i) '' s) :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have h2 := Submodule.smul_mem (Submodule.span K ((fun i => d i • f i) '' s)) (d i)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ (hd i), one_smul] at h2

private theorem a8_le_span_of_basis {ι : Type*} [Fintype ι] (Z : Submodule K (Fin 6 → K))
    (b : Module.Basis ι K Z) (col : Fin 6 → (Fin 6 → K)) (S : Set (Fin 6)) (f : ι → Fin 6)
    (hf : ∀ j, f j ∈ S) (hcol : ∀ j, col (f j) = (b j : Fin 6 → K)) :
    Z ≤ Submodule.span K (col '' S) := by
  intro x hx
  have hx' : x = ∑ j, b.repr ⟨x, hx⟩ j • (b j : Fin 6 → K) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  rw [hx']
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨f j, hf j, hcol j⟩)

private theorem a8_col_mul_diag (M' : Matrix (Fin 6) (Fin 6) K) (d : Fin 6 → K) (i : Fin 6) :
    (M' * Matrix.diagonal d).col i = d i • M'.col i := by
  funext r
  show (M' * Matrix.diagonal d) r i = d i • M' r i
  rw [Matrix.mul_diagonal, smul_eq_mul, mul_comm]

private theorem a8_frame (X Y A P T R : Submodule K (Fin 6 → K)) (a p t r : ℕ)
    (hAX : A ≤ X) (hAY : A ≤ Y)
    (hXP : A ⊔ P = X) (hYT : A ⊔ T = Y) (hXYR : X ⊔ Y ⊔ R = ⊤)
    (bA : Module.Basis (Fin a) K A) (bP : Module.Basis (Fin p) K P) (bT : Module.Basis (Fin t) K T)
    (bR : Module.Basis (Fin r) K R)
    (hp : a + p = 3) (ht : a + t = 3) (hr : r = a) :
    ∃ M : Matrix (Fin 6) (Fin 6) K, IsUnit M.det ∧
      X = Submodule.span K ((fun i : Fin 6 => M.col i) '' {i : Fin 6 | i.val < 3}) ∧
      Y = Submodule.span K ((fun i : Fin 6 => M.col i) ''
        {i : Fin 6 | i.val < a ∨ (3 ≤ i.val ∧ i.val < 6 - a)}) := by
  classical
  have hPX : P ≤ X := le_sup_right.trans hXP.le
  have hTY : T ≤ Y := le_sup_right.trans hYT.le
  let col : Fin 6 → (Fin 6 → K) := fun i =>
    if h1 : i.val < a then (bA ⟨i.val, h1⟩ : Fin 6 → K)
    else if h2 : i.val < 3 then (bP ⟨i.val - a, by omega⟩ : Fin 6 → K)
    else if h3 : i.val < 6 - a then (bT ⟨i.val - 3, by omega⟩ : Fin 6 → K)
    else (bR ⟨i.val - (6 - a), by have := i.isLt; omega⟩ : Fin 6 → K)
  have hmemA : ∀ i : Fin 6, i.val < a → col i ∈ A := by
    intro i hi
    have hc : col i = (bA ⟨i.val, hi⟩ : Fin 6 → K) := by
      simp only [col, dif_pos hi]
    rw [hc]
    exact (bA _).2
  have hmemP : ∀ i : Fin 6, ¬ i.val < a → i.val < 3 → col i ∈ P := by
    intro i h1 h2
    have hc : col i = (bP ⟨i.val - a, by omega⟩ : Fin 6 → K) := by
      simp only [col, dif_neg h1, dif_pos h2]
    rw [hc]
    exact (bP _).2
  have hmemT : ∀ i : Fin 6, ¬ i.val < a → ¬ i.val < 3 → i.val < 6 - a → col i ∈ T := by
    intro i h1 h2 h3
    have hc : col i = (bT ⟨i.val - 3, by omega⟩ : Fin 6 → K) := by
      simp only [col, dif_neg h1, dif_neg h2, dif_pos h3]
    rw [hc]
    exact (bT _).2
  have hcolA : ∀ (i : Fin 6) (j : Fin a), i.val = j.val → col i = (bA j : Fin 6 → K) := by
    intro i j hi
    have h1 : i.val < a := by have := j.isLt; omega
    have hij : (⟨i.val, h1⟩ : Fin a) = j := Fin.ext hi
    simp only [col, dif_pos h1, hij]
  have hcolP : ∀ (i : Fin 6) (j : Fin p), i.val = a + j.val → col i = (bP j : Fin 6 → K) := by
    intro i j hi
    have hj := j.isLt
    have h1 : ¬ i.val < a := by omega
    have h2 : i.val < 3 := by omega
    have hij : (⟨i.val - a, by omega⟩ : Fin p) = j := Fin.ext (by show i.val - a = j.val; omega)
    simp only [col, dif_neg h1, dif_pos h2, hij]
  have hcolT : ∀ (i : Fin 6) (j : Fin t), i.val = 3 + j.val → col i = (bT j : Fin 6 → K) := by
    intro i j hi
    have hj := j.isLt
    have h1 : ¬ i.val < a := by omega
    have h2 : ¬ i.val < 3 := by omega
    have h3 : i.val < 6 - a := by omega
    have hij : (⟨i.val - 3, by omega⟩ : Fin t) = j := Fin.ext (by show i.val - 3 = j.val; omega)
    simp only [col, dif_neg h1, dif_neg h2, dif_pos h3, hij]
  have hcolR : ∀ (i : Fin 6) (j : Fin r), i.val = 6 - a + j.val → col i = (bR j : Fin 6 → K) := by
    intro i j hi
    have hj := j.isLt
    have hi6 := i.isLt
    have h1 : ¬ i.val < a := by omega
    have h2 : ¬ i.val < 3 := by omega
    have h3 : ¬ i.val < 6 - a := by omega
    have hij : (⟨i.val - (6 - a), by omega⟩ : Fin r) = j :=
      Fin.ext (by show i.val - (6 - a) = j.val; omega)
    simp only [col, dif_neg h1, dif_neg h2, dif_neg h3, hij]
  have hX_sub : X ≤ Submodule.span K (col '' {i : Fin 6 | i.val < 3}) := by
    rw [← hXP]
    apply sup_le
    · exact a8_le_span_of_basis A bA col _ (fun j => ⟨j.val, by have := j.isLt; omega⟩)
        (fun j => by show j.val < 3; have := j.isLt; omega)
        (fun j => hcolA _ j rfl)
    · exact a8_le_span_of_basis P bP col _ (fun j => ⟨a + j.val, by have := j.isLt; omega⟩)
        (fun j => by show a + j.val < 3; have := j.isLt; omega)
        (fun j => hcolP _ j rfl)
  have hY_sub : Y ≤ Submodule.span K
      (col '' {i : Fin 6 | i.val < a ∨ (3 ≤ i.val ∧ i.val < 6 - a)}) := by
    rw [← hYT]
    apply sup_le
    · exact a8_le_span_of_basis A bA col _ (fun j => ⟨j.val, by have := j.isLt; omega⟩)
        (fun j => by show j.val < a ∨ _; left; exact j.isLt)
        (fun j => hcolA _ j rfl)
    · exact a8_le_span_of_basis T bT col _ (fun j => ⟨3 + j.val, by have := j.isLt; omega⟩)
        (fun j => by
          show _ ∨ (3 ≤ 3 + j.val ∧ 3 + j.val < 6 - a)
          right
          have := j.isLt
          omega)
        (fun j => hcolT _ j rfl)
  have hXeq : X = Submodule.span K (col '' {i : Fin 6 | i.val < 3}) := by
    apply le_antisymm hX_sub
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    by_cases h1 : i.val < a
    · exact hAX (hmemA i h1)
    · exact hPX (hmemP i h1 hi)
  have hYeq : Y = Submodule.span K
      (col '' {i : Fin 6 | i.val < a ∨ (3 ≤ i.val ∧ i.val < 6 - a)}) := by
    apply le_antisymm hY_sub
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rcases hi with hi | ⟨hi1, hi2⟩
    · exact hAY (hmemA i hi)
    · exact hTY (hmemT i (by omega) (by omega) hi2)
  have hspan : (⊤ : Submodule K (Fin 6 → K)) ≤ Submodule.span K (Set.range col) := by
    have hR_sub : R ≤ Submodule.span K (col '' Set.univ) :=
      a8_le_span_of_basis R bR col _ (fun j => ⟨6 - a + j.val, by have := j.isLt; omega⟩)
        (fun j => Set.mem_univ _) (fun j => hcolR _ j rfl)
    rw [Set.image_univ] at hR_sub
    have hX' := hX_sub.trans (Submodule.span_mono (Set.image_subset_range col _))
    have hY' := hY_sub.trans (Submodule.span_mono (Set.image_subset_range col _))
    rw [← hXYR]
    exact sup_le (sup_le hX' hY') hR_sub
  have hLI : LinearIndependent K col :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  set M : Matrix (Fin 6) (Fin 6) K := Matrix.of fun r c => col c r with hM_def
  have hMcol : M.col = col := by
    funext j
    funext r
    rfl
  have hMunit : IsUnit M := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hMcol]
    exact hLI
  refine ⟨M, (Matrix.isUnit_iff_isUnit_det M).1 hMunit, ?_, ?_⟩
  · rw [hMcol]
    exact hXeq
  · rw [hMcol]
    exact hYeq

private theorem a8_adapt (X Y : Submodule K (Fin 6 → K)) (k : ℕ)
    (hX : Module.finrank K X = 3) (hY : Module.finrank K Y = 3)
    (hk : Module.finrank K ↥(X ⊓ Y) = k) :
    ∃ M : Matrix (Fin 6) (Fin 6) K, IsUnit M.det ∧
      X = Submodule.span K ((fun i : Fin 6 => M.col i) '' {i : Fin 6 | i.val < 3}) ∧
      Y = Submodule.span K ((fun i : Fin 6 => M.col i) ''
        {i : Fin 6 | i.val < k ∨ (3 ≤ i.val ∧ i.val < 6 - k)}) := by
  classical
  obtain ⟨C, hAC⟩ := Submodule.exists_isCompl (X ⊓ Y)
  obtain ⟨R, hRC⟩ := Submodule.exists_isCompl (X ⊔ Y)
  have hAX : X ⊓ Y ≤ X := inf_le_left
  have hAY : X ⊓ Y ≤ Y := inf_le_right
  have hXP : (X ⊓ Y) ⊔ (X ⊓ C) = X := by
    apply le_antisymm (sup_le hAX inf_le_left)
    intro x hx
    have hx' : x ∈ (X ⊓ Y) ⊔ C := by
      rw [hAC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    have hzX : z ∈ X := by
      have := Submodule.sub_mem X hx (hAX hy)
      simpa using this
    exact Submodule.add_mem_sup hy ⟨hzX, hz⟩
  have hYT : (X ⊓ Y) ⊔ (Y ⊓ C) = Y := by
    apply le_antisymm (sup_le hAY inf_le_left)
    intro x hx
    have hx' : x ∈ (X ⊓ Y) ⊔ C := by
      rw [hAC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    have hzY : z ∈ Y := by
      have := Submodule.sub_mem Y hx (hAY hy)
      simpa using this
    exact Submodule.add_mem_sup hy ⟨hzY, hz⟩
  have hXYR : X ⊔ Y ⊔ R = ⊤ := hRC.sup_eq_top
  have hAP : (X ⊓ Y) ⊓ (X ⊓ C) = ⊥ := by
    apply eq_bot_iff.2
    calc (X ⊓ Y) ⊓ (X ⊓ C) ≤ (X ⊓ Y) ⊓ C := inf_le_inf_left _ inf_le_right
      _ = ⊥ := hAC.inf_eq_bot
  have hAT : (X ⊓ Y) ⊓ (Y ⊓ C) = ⊥ := by
    apply eq_bot_iff.2
    calc (X ⊓ Y) ⊓ (Y ⊓ C) ≤ (X ⊓ Y) ⊓ C := inf_le_inf_left _ inf_le_right
      _ = ⊥ := hAC.inf_eq_bot
  have hfinP := Submodule.finrank_sup_add_finrank_inf_eq (X ⊓ Y) (X ⊓ C)
  rw [hXP, hAP, finrank_bot, hX] at hfinP
  have hfinT := Submodule.finrank_sup_add_finrank_inf_eq (X ⊓ Y) (Y ⊓ C)
  rw [hYT, hAT, finrank_bot, hY] at hfinT
  have hfin2 := Submodule.finrank_sup_add_finrank_inf_eq X Y
  have hfin3 := Submodule.finrank_add_eq_of_isCompl hRC
  rw [Module.finrank_fin_fun] at hfin3
  rw [hX, hY] at hfin2
  have hp : Module.finrank K ↥(X ⊓ Y) + Module.finrank K ↥(X ⊓ C) = 3 := by omega
  have ht : Module.finrank K ↥(X ⊓ Y) + Module.finrank K ↥(Y ⊓ C) = 3 := by omega
  have hr : Module.finrank K ↥R = Module.finrank K ↥(X ⊓ Y) := by omega
  subst hk
  exact a8_frame X Y (X ⊓ Y) (X ⊓ C) (Y ⊓ C) R _ _ _ _ hAX hAY hXP hYT hXYR
    (Module.finBasis K _) (Module.finBasis K _) (Module.finBasis K _) (Module.finBasis K _)
    hp ht hr

theorem exists_pair_equiv {G G' : GL (Fin 6) K}
    (h : Module.finrank K ↥(imgS0 G ⊓ S0 K) = Module.finrank K ↥(imgS0 G' ⊓ S0 K)) :
    ∃ H : GL (Fin 6) K, (H : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ imgS0 H = S0 K ∧
      imgS0 (H * G) = imgS0 G' := by
  classical
  have hS0 : Module.finrank K (S0 K) = 3 := finrank_S0
  have hS : Module.finrank K (imgS0 G) = 3 := finrank_imgS0 G
  have hS' : Module.finrank K (imgS0 G') = 3 := finrank_imgS0 G'
  have hk : Module.finrank K ↥(S0 K ⊓ imgS0 G') = Module.finrank K ↥(S0 K ⊓ imgS0 G) := by
    rw [inf_comm (S0 K) (imgS0 G), inf_comm (S0 K) (imgS0 G')]
    exact h.symm
  obtain ⟨M, hM, hX, hY⟩ :=
    a8_adapt (S0 K) (imgS0 G) (Module.finrank K ↥(S0 K ⊓ imgS0 G)) hS0 hS rfl
  obtain ⟨M', hM', hX', hY'⟩ :=
    a8_adapt (S0 K) (imgS0 G') (Module.finrank K ↥(S0 K ⊓ imgS0 G)) hS0 hS' hk
  have hMd : M.det ≠ 0 := isUnit_iff_ne_zero.1 hM
  have hM'd : M'.det ≠ 0 := isUnit_iff_ne_zero.1 hM'
  set c : K := M.det * M'.det⁻¹ with hc_def
  have hc : c ≠ 0 := mul_ne_zero hMd (inv_ne_zero hM'd)
  set d : Fin 6 → K := fun j => if j = 0 then c else 1 with hd_def
  have hd : ∀ j, d j ≠ 0 := by
    intro j
    by_cases hj : j = 0
    · simp only [hd_def, hj, if_true]
      exact hc
    · simp only [hd_def, hj, if_false]
      exact one_ne_zero
  set N : Matrix (Fin 6) (Fin 6) K := M' * Matrix.diagonal d with hN_def
  have hNdet : N.det = M.det := by
    have hprod : ∏ j, d j = c := by
      simp [hd_def]
    rw [hN_def, Matrix.det_mul, Matrix.det_diagonal, hprod, hc_def]
    field_simp
  set Hm : Matrix (Fin 6) (Fin 6) K := N * M⁻¹ with hHm_def
  have hdet1 : Hm.det = 1 := by
    rw [hHm_def, Matrix.det_mul, hNdet, Matrix.det_nonsing_inv]
    simp [hMd]
  have hHunit : IsUnit Hm := (Matrix.isUnit_iff_isUnit_det Hm).2 (by rw [hdet1]; exact isUnit_one)
  obtain ⟨H, hHval⟩ : ∃ H : GL (Fin 6) K, (H : Matrix (Fin 6) (Fin 6) K) = Hm :=
    ⟨hHunit.unit, hHunit.unit_spec⟩
  have hHM : Hm * M = N := by
    rw [hHm_def, Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.mul_one]
  have hcol : ∀ i : Fin 6, Hm *ᵥ M.col i = d i • M'.col i := by
    intro i
    rw [← Matrix.mulVec_single_one M i, Matrix.mulVec_mulVec, hHM, Matrix.mulVec_single_one,
      hN_def, a8_col_mul_diag]
  have hdetH : (H : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    rw [hHval]
    exact hdet1
  have hfun : (fun x : Fin 6 => Matrix.mulVecLin Hm (M.col x)) = fun i => d i • M'.col i := by
    funext i
    exact hcol i
  refine ⟨H, hdetH, ?_, ?_⟩
  · unfold imgS0
    rw [hHval]
    conv_lhs => rw [hX]
    conv_rhs => rw [hX']
    rw [Submodule.map_span, Set.image_image, hfun]
    exact a8_span_smul_image _ _ _ hd
  · rw [a8_imgS0_mul, hHval]
    conv_lhs => rw [hY]
    conv_rhs => rw [hY']
    rw [Submodule.map_span, Set.image_image, hfun]
    exact a8_span_smul_image _ _ _ hd

theorem rho_p0_eq_smul_of_imgS0_eq {G G' : GL (Fin 6) K} (h : imgS0 G = imgS0 G') :
    ∃ c : K, c ≠ 0 ∧ rho K G (p0 K) = c • rho K G' (p0 K) := by
  have hstab : imgS0 (G'⁻¹ * G) = S0 K := by
    have h1 : imgS0 (G'⁻¹ * G) =
        (imgS0 G).map (Matrix.mulVecLin ((G'⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
      unfold imgS0
      rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]
    rw [h1, h]
    exact s81A12_hId G' (S0 K)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (rho_p0_mem_span_of_imgS0 hstab)
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    refine p0_ne_zero ((rhoEquiv K (G'⁻¹ * G)).injective ?_)
    rw [map_zero, rhoEquiv_apply, ← hc, zero_smul]
  · have key : rho K G = rho K G' * rho K (G'⁻¹ * G) := by
      rw [← rho_mul, mul_inv_cancel_left]
    rw [key, Module.End.mul_apply, ← hc, map_smul]

theorem U0_norm : ∀ h ∈ Gam K, (∃ c : K, c ≠ 0 ∧ h (p0 K) = c • p0 K) →
    conjSub h (U0 K) = U0 K := by
  rintro h hh ⟨c, hc, hpc⟩
  obtain ⟨G, -, rfl⟩ := Subgroup.mem_map.1 hh
  have hG : imgS0 G = S0 K :=
    imgS0_eq_of_rho_p0 hc ((rhoEquiv_apply G (p0 K)).symm.trans hpc)
  rw [U0_eq_Urad, conjSub_Urad]
  exact congrArg (Urad K) hG

theorem class_invariant {G G' : GL (Fin 6) K} (hG : (G : Matrix (Fin 6) (Fin 6) K).det = 1)
    (hG' : (G' : Matrix (Fin 6) (Fin 6) K).det = 1)
    (hk : Module.finrank K ↥(imgS0 G ⊓ S0 K) = Module.finrank K ↥(imgS0 G' ⊓ S0 K)) :
    (rho K G (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔
      rho K G' (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K)) ∧
    (beta K (p0 K) (rho K G (p0 K)) = 0 ↔ beta K (p0 K) (rho K G' (p0 K)) = 0) := by
  obtain ⟨H, hdetH, hHS, hHG⟩ := exists_pair_equiv hk
  have hHmem : H ∈ StatedSL 6 K := CFSG.Open.StatedAPI.mem_statedSL_of_det hdetH
  have hΓ : rhoEquiv K H ∈ Gam K := Subgroup.mem_map_of_mem (rhoEquiv K) hHmem
  have hrho1 : rho K (1 : GL (Fin 6) K) = 1 := map_one (TauCeti.extPowerRep K 6 3)
  have himg1 : imgS0 (1 : GL (Fin 6) K) = S0 K := by simp [imgS0]
  obtain ⟨c₁, hc₁, hH1⟩ := rho_p0_eq_smul_of_imgS0_eq (G := H) (G' := 1) (hHS.trans himg1.symm)
  have hHp : rhoEquiv K H (p0 K) = c₁ • p0 K := by
    rw [rhoEquiv_apply, hH1, hrho1]
    simp
  obtain ⟨c₂, hc₂, hHG'⟩ := rho_p0_eq_smul_of_imgS0_eq hHG
  have hHGp : rhoEquiv K H (rho K G (p0 K)) = c₂ • rho K G' (p0 K) := by
    rw [← hHG', rhoEquiv_apply, rho_mul, Module.End.mul_apply]
  have hU : conjSub (rhoEquiv K H) (U0 K) = U0 K := U0_norm (rhoEquiv K H) hΓ ⟨c₁, hc₁, hHp⟩
  have hline : (Submodule.span K {p0 K}).map (rhoEquiv K H : Cube K →ₗ[K] Cube K) =
      Submodule.span K {p0 K} := by
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hHp,
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc₁)]
  have hW : (Wsp (Submodule.span K {p0 K}) (U0 K)).map (rhoEquiv K H : Cube K →ₗ[K] Cube K) =
      Wsp (Submodule.span K {p0 K}) (U0 K) := by
    rw [← Wsp_map, hU, hline]
  have hstab : ∀ v : Cube K, rhoEquiv K H v ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔
      v ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
    intro v
    have h2 : rhoEquiv K H v ∈ (Wsp (Submodule.span K {p0 K}) (U0 K)).map
        (rhoEquiv K H : Cube K →ₗ[K] Cube K) ↔ v ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    rwa [hW] at h2
  have hβ : beta K (p0 K) (rho K G (p0 K)) = c₁ * c₂ * beta K (p0 K) (rho K G' (p0 K)) := by
    have h1 := Gam_beta_inv hΓ (p0 K) (rho K G (p0 K))
    rw [hHp, hHGp] at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    ring
  refine ⟨?_, ?_⟩
  · rw [← hstab (rho K G (p0 K)), hHGp, Submodule.smul_mem_iff _ hc₂]
  · rw [hβ]
    simp [hc₁, hc₂]

private def nfCsub (K : Type) [Field K] (I : Finset (Fin 6)) : Submodule K (Fin 6 → K) :=
  Submodule.span K (Set.range fun j : I => e K (j : Fin 6))

private theorem nfEqSum {I : Finset (Fin 6)} {v : Fin 6 → K} (hv : ∀ j, j ∉ I → v j = 0) :
    v = ∑ j ∈ I, v j • e K j := by
  funext k
  by_cases hk : k ∈ I
  · simp [Finset.sum_apply, e, Pi.single_apply, mul_ite, hk]
  · simp [Finset.sum_apply, e, Pi.single_apply, mul_ite, hk, hv k hk]

private theorem nfMemCsub {I : Finset (Fin 6)} {v : Fin 6 → K} :
    v ∈ nfCsub K I ↔ ∀ j, j ∉ I → v j = 0 := by
  constructor
  · intro hv
    rw [nfCsub] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨j, hj⟩, rfl⟩ := hx
      intro i hi
      have hij : i ≠ j := by
        rintro rfl
        exact hi hj
      simp [e, Pi.single_apply, hij]
    | zero => intro j _; rfl
    | add x y _ _ hx hy => intro j hj; simp [hx j hj, hy j hj]
    | smul a x _ hx => intro j hj; simp [hx j hj]
  · intro hv
    rw [nfCsub, nfEqSum hv]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Set.mem_range_self (⟨j, hj⟩ : I)

private theorem nfCsubInf (I J : Finset (Fin 6)) :
    nfCsub K I ⊓ nfCsub K J = nfCsub K (I ∩ J) := by
  ext v
  simp only [Submodule.mem_inf, nfMemCsub, Finset.mem_inter]
  constructor
  · rintro ⟨h1, h2⟩ j hj
    by_cases hI : j ∈ I
    · exact h2 j fun hJ => hj ⟨hI, hJ⟩
    · exact h1 j hI
  · intro h
    exact ⟨fun j hj => h j fun hIJ => hj hIJ.1, fun j hj => h j fun hIJ => hj hIJ.2⟩

private theorem nfFinrankCsub (I : Finset (Fin 6)) : Module.finrank K (nfCsub K I) = I.card := by
  have hli : LinearIndependent K (fun j : I => e K (j : Fin 6)) :=
    (Pi.linearIndependent_single_one (Fin 6) K).comp (fun j : I => (j : Fin 6))
      Subtype.val_injective
  rw [nfCsub, finrank_span_eq_card hli, Fintype.card_coe]

private theorem nfS0 : S0 K = nfCsub K {0, 2, 4} := by
  have key : ∀ j : Fin 6, j ∉ ({0, 2, 4} : Finset (Fin 6)) ↔ j.val % 2 = 1 := by decide
  ext v
  rw [nfMemCsub, s81A12_mem_S0]
  constructor
  · intro hv j hj
    exact hv j ((key j).mp hj)
  · intro hv j hj
    exact hv j ((key j).mpr hj)

private theorem nfSpanRangeComp (g : Fin 3 → Fin 6) :
    Submodule.span K (Set.range fun i => e K (g i)) =
      nfCsub K ((Finset.univ : Finset (Fin 3)).image g) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, nfCsub]
    exact Submodule.subset_span (Set.mem_range_self
      (⟨g i, Finset.mem_image_of_mem g (Finset.mem_univ i)⟩ :
        ((Finset.univ : Finset (Fin 3)).image g)))
  · rw [nfCsub, Submodule.span_le]
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    rw [SetLike.mem_coe]
    exact Submodule.subset_span (Set.mem_range_self i)

private theorem nfImgS0 (G : GL (Fin 6) K) {g : Fin 3 → Fin 6}
    (hG : ∀ i, (G : Matrix (Fin 6) (Fin 6) K).mulVec (e K (![(0 : Fin 6), 2, 4] i)) = e K (g i)) :
    imgS0 G = nfCsub K ((Finset.univ : Finset (Fin 3)).image g) := by
  have hset : (Finset.univ : Finset (Fin 3)).image (![(0 : Fin 6), 2, 4]) = {0, 2, 4} := by
    decide
  have hS0 : S0 K = Submodule.span K (Set.range fun i => e K (![(0 : Fin 6), 2, 4] i)) := by
    rw [nfSpanRangeComp (K := K) ![(0 : Fin 6), 2, 4], hset, nfS0]
  have hfun : (Matrix.mulVecLin (G : Matrix (Fin 6) (Fin 6) K)) ∘
      (fun i => e K (![(0 : Fin 6), 2, 4] i)) = fun i => e K (g i) := by
    funext i
    rw [Function.comp_apply, Matrix.mulVecLin_apply]
    exact hG i
  rw [imgS0, hS0, Submodule.map_span, ← nfSpanRangeComp (K := K) g, ← Set.range_comp, hfun]

private theorem nfFinrankInf (G : GL (Fin 6) K) {g : Fin 3 → Fin 6}
    (hG : ∀ i, (G : Matrix (Fin 6) (Fin 6) K).mulVec (e K (![(0 : Fin 6), 2, 4] i)) = e K (g i)) :
    Module.finrank K ↥(imgS0 G ⊓ S0 K) =
      ((Finset.univ : Finset (Fin 3)).image g ∩ ({0, 2, 4} : Finset (Fin 6))).card := by
  rw [nfImgS0 G hG, nfS0, nfCsubInf, nfFinrankCsub]

private theorem nfLinIndep {g : Fin 3 → Fin 6} (hg : Function.Injective g) :
    LinearIndependent K (fun i => e K (g i)) :=
  (Pi.linearIndependent_single_one (Fin 6) K).comp g hg

private theorem nfExistsG {g : Fin 3 → Fin 6} (hg : Function.Injective g) :
    ∃ G : GL (Fin 6) K, (G : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      ∀ i, (G : Matrix (Fin 6) (Fin 6) K).mulVec (e K (![(0 : Fin 6), 2, 4] i)) = e K (g i) := by
  have hf : Function.Injective (![(0 : Fin 6), 2, 4]) := by decide
  obtain ⟨m, hdet, hm⟩ := exists_sl_of_linearIndependent (by norm_num : 3 < 6)
    (nfLinIndep (K := K) hf) (nfLinIndep (K := K) hg)
  have hm0 : m.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero m hm0, hdet, fun i => hm i⟩

private theorem nfP0Fam : ιMulti K 3 (fun i => e K (![(0 : Fin 6), 2, 4] i)) = p0 K := by
  rw [p0_eq]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem nfRhoP0 (G : GL (Fin 6) K) {g : Fin 3 → Fin 6}
    (hG : ∀ i, (G : Matrix (Fin 6) (Fin 6) K).mulVec (e K (![(0 : Fin 6), 2, 4] i)) = e K (g i)) :
    rho K G (p0 K) = ιMulti K 3 (fun i => e K (g i)) := by
  rw [← nfP0Fam, rho_ιMulti]
  congr 1
  funext i
  exact hG i

private theorem nfExistsGProps {g : Fin 3 → Fin 6} (hg : Function.Injective g) :
    ∃ G : GL (Fin 6) K, (G : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      Module.finrank K ↥(imgS0 G ⊓ S0 K) =
        ((Finset.univ : Finset (Fin 3)).image g ∩ ({0, 2, 4} : Finset (Fin 6))).card ∧
      rho K G (p0 K) = ιMulti K 3 (fun i => e K (g i)) := by
  obtain ⟨G, hdet, hG⟩ := nfExistsG (K := K) hg
  exact ⟨G, hdet, nfFinrankInf G hG, nfRhoP0 G hG⟩

private theorem nfFam013 :
    ιMulti K 3 (fun i => e K (![(0 : Fin 6), 1, 3] i)) = cubeBasis K S013 := by
  rw [cubeBasis_S013]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem nfFam135 :
    ιMulti K 3 (fun i => e K (![(1 : Fin 6), 3, 5] i)) = cubeBasis K S135 := by
  rw [cubeBasis_S135]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem nfFam034 : ιMulti K 3 (fun i => e K (![(0 : Fin 6), 3, 4] i)) = r0 K := by
  rw [r0_eq]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem nfP0MemW0 : p0 K ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  rw [mem_Wsp]
  intro u hu
  rw [U0_fix u hu, sub_self]
  exact Submodule.zero_mem _

private theorem nfCube013NotMem : cubeBasis K S013 ∉ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  intro hmem
  have hodd : 2 ≤ (S013.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by
    show 2 ≤ (({0, 1, 3} : Finset (Fin 6)).filter (fun i : Fin 6 => i.val % 2 = 1)).card
    decide
  have h1 := coord_eq_zero_of_mem_W0 hmem S013 hodd
  rw [coord_cubeBasis, if_pos rfl] at h1
  exact one_ne_zero h1

private theorem nfCube135NotMem : cubeBasis K S135 ∉ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  intro hmem
  have hodd : 2 ≤ (S135.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by
    show 2 ≤ (({1, 3, 5} : Finset (Fin 6)).filter (fun i : Fin 6 => i.val % 2 = 1)).card
    decide
  have h1 := coord_eq_zero_of_mem_W0 hmem S135 hodd
  rw [coord_cubeBasis, if_pos rfl] at h1
  exact one_ne_zero h1

private theorem nfBeta013 : beta K (p0 K) (cubeBasis K S013) = 0 := by
  have hnd : ¬ Disjoint S024.val S013.val := by
    show ¬ Disjoint ({0, 2, 4} : Finset (Fin 6)) ({0, 1, 3} : Finset (Fin 6))
    decide
  exact beta_cubeBasis_of_not_disjoint hnd

private theorem nfBeta135 : beta K (p0 K) (cubeBasis K S135) ≠ 0 := by
  have hd : Disjoint S024.val S135.val := by
    show Disjoint ({0, 2, 4} : Finset (Fin 6)) ({1, 3, 5} : Finset (Fin 6))
    decide
  exact beta_cubeBasis_ne_zero_of_disjoint hd

private theorem nfZero : ∃ Gk : GL (Fin 6) K, (Gk : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      Module.finrank K ↥(imgS0 Gk ⊓ S0 K) = 0 ∧
      (rho K Gk (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔ 2 ≤ 0) ∧
      (beta K (p0 K) (rho K Gk (p0 K)) = 0 ↔ 1 ≤ 0) := by
  have hinj : Function.Injective (![(1 : Fin 6), 3, 5]) := by decide
  obtain ⟨G, hdet, hfr, hρ⟩ := nfExistsGProps (K := K) hinj
  refine ⟨G, hdet, ?_, ?_, ?_⟩
  · rw [hfr]
    decide
  · rw [hρ, nfFam135]
    exact iff_of_false nfCube135NotMem (by norm_num)
  · rw [hρ, nfFam135]
    exact iff_of_false nfBeta135 (by norm_num)

private theorem nfOne : ∃ Gk : GL (Fin 6) K, (Gk : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      Module.finrank K ↥(imgS0 Gk ⊓ S0 K) = 1 ∧
      (rho K Gk (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔ 2 ≤ 1) ∧
      (beta K (p0 K) (rho K Gk (p0 K)) = 0 ↔ 1 ≤ 1) := by
  have hinj : Function.Injective (![(0 : Fin 6), 1, 3]) := by decide
  obtain ⟨G, hdet, hfr, hρ⟩ := nfExistsGProps (K := K) hinj
  refine ⟨G, hdet, ?_, ?_, ?_⟩
  · rw [hfr]
    decide
  · rw [hρ, nfFam013]
    exact iff_of_false nfCube013NotMem (by norm_num)
  · rw [hρ, nfFam013]
    exact iff_of_true nfBeta013 (by norm_num)

private theorem nfTwo : ∃ Gk : GL (Fin 6) K, (Gk : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      Module.finrank K ↥(imgS0 Gk ⊓ S0 K) = 2 ∧
      (rho K Gk (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔ 2 ≤ 2) ∧
      (beta K (p0 K) (rho K Gk (p0 K)) = 0 ↔ 1 ≤ 2) := by
  have hinj : Function.Injective (![(0 : Fin 6), 3, 4]) := by decide
  obtain ⟨G, hdet, hfr, hρ⟩ := nfExistsGProps (K := K) hinj
  refine ⟨G, hdet, ?_, ?_, ?_⟩
  · rw [hfr]
    decide
  · rw [hρ, nfFam034]
    exact iff_of_true r0_mem_W0 (by norm_num)
  · rw [hρ, nfFam034]
    exact iff_of_true (beta_p0_of_mem_W0 r0_mem_W0) (by norm_num)

private theorem nfThree : ∃ Gk : GL (Fin 6) K, (Gk : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      Module.finrank K ↥(imgS0 Gk ⊓ S0 K) = 3 ∧
      (rho K Gk (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔ 2 ≤ 3) ∧
      (beta K (p0 K) (rho K Gk (p0 K)) = 0 ↔ 1 ≤ 3) := by
  have hinj : Function.Injective (![(0 : Fin 6), 2, 4]) := by decide
  obtain ⟨G, hdet, hfr, hρ⟩ := nfExistsGProps (K := K) hinj
  refine ⟨G, hdet, ?_, ?_, ?_⟩
  · rw [hfr]
    decide
  · rw [hρ, nfP0Fam]
    exact iff_of_true nfP0MemW0 (by norm_num)
  · rw [hρ, nfP0Fam]
    exact iff_of_true (beta_p0_of_mem_W0 nfP0MemW0) (by norm_num)

theorem exists_normal_form (k : ℕ) (hk : k ≤ 3) :
    ∃ Gk : GL (Fin 6) K, (Gk : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      Module.finrank K ↥(imgS0 Gk ⊓ S0 K) = k ∧
      (rho K Gk (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔ 2 ≤ k) ∧
      (beta K (p0 K) (rho K Gk (p0 K)) = 0 ↔ 1 ≤ k) := by
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · exact nfZero
  · exact nfOne
  · exact nfTwo
  · exact nfThree

private theorem s81b2e_rho_one : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem s81b2e_rho_p0_ne_zero (G : GL (Fin 6) K) : rho K G (p0 K) ≠ 0 := by
  intro h0
  have h1 : rho K G⁻¹ (rho K G (p0 K)) = p0 K := by
    rw [← Module.End.mul_apply, ← rho_mul, inv_mul_cancel, s81b2e_rho_one, Module.End.one_apply]
  rw [h0, map_zero] at h1
  exact p0_ne_zero (K := K) h1.symm

theorem rho_p0_mem_span_iff {G : GL (Fin 6) K} :
    rho K G (p0 K) ∈ Submodule.span K {p0 K} ↔ Module.finrank K ↥(imgS0 G ⊓ S0 K) = 3 := by
  constructor
  · intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact s81b2e_rho_p0_ne_zero G hc.symm
    rw [imgS0_eq_of_rho_p0 hc0 hc.symm, inf_idem]
    exact finrank_S0 (K := K)
  · intro hfin
    have hinf : imgS0 G ⊓ S0 K = S0 K :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (hfin.trans (finrank_S0 (K := K)).symm)
    have hle : S0 K ≤ imgS0 G := (le_of_eq hinf.symm).trans inf_le_left
    have himg : imgS0 G = S0 K :=
      (Submodule.eq_of_le_of_finrank_eq hle
        ((finrank_S0 (K := K)).trans (finrank_imgS0 G).symm)).symm
    exact rho_p0_mem_span_of_imgS0 himg

theorem rho_p0_mem_W0_iff {G : GL (Fin 6) K} (hG : (G : Matrix (Fin 6) (Fin 6) K).det = 1) :
    rho K G (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔
      2 ≤ Module.finrank K ↥(imgS0 G ⊓ S0 K) := by
  have hk3 : Module.finrank K ↥(imgS0 G ⊓ S0 K) ≤ 3 :=
    (Submodule.finrank_mono (inf_le_right : imgS0 G ⊓ S0 K ≤ S0 K)).trans
      (finrank_S0 (K := K)).le
  obtain ⟨Gk, hdet, hkk, hW, -⟩ :=
    exists_normal_form (K := K) (Module.finrank K ↥(imgS0 G ⊓ S0 K)) hk3
  exact (class_invariant hG hdet hkk.symm).1.trans hW

theorem beta_rho_p0_eq_zero_iff {G : GL (Fin 6) K} (hG : (G : Matrix (Fin 6) (Fin 6) K).det = 1) :
    beta K (p0 K) (rho K G (p0 K)) = 0 ↔ 1 ≤ Module.finrank K ↥(imgS0 G ⊓ S0 K) := by
  have hk3 : Module.finrank K ↥(imgS0 G ⊓ S0 K) ≤ 3 :=
    (Submodule.finrank_mono (inf_le_right : imgS0 G ⊓ S0 K ≤ S0 K)).trans
      (finrank_S0 (K := K)).le
  obtain ⟨Gk, hdet, hkk, -, hbeta⟩ :=
    exists_normal_form (K := K) (Module.finrank K ↥(imgS0 G ⊓ S0 K)) hk3
  exact (class_invariant hG hdet hkk.symm).2.trans hbeta

private theorem a5_rho_one : rho K (1 : GL (Fin 6) K) = 1 := map_one (TauCeti.extPowerRep K 6 3)

private theorem a5_imgS0_one : imgS0 (1 : GL (Fin 6) K) = S0 K := by
  unfold imgS0
  simp only [Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]

private theorem a5_gam_rep {g : Cube K ≃ₗ[K] Cube K} (hg : g ∈ Gam K) :
    ∃ G : GL (Fin 6) K, (G : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ rhoEquiv K G = g := by
  obtain ⟨G, hG, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨G, CFSG.Open.StatedAPI.mem_statedSL_iff.mp hG, rfl⟩

private theorem a5_finrank_le (G : GL (Fin 6) K) :
    Module.finrank K ↥(imgS0 G ⊓ S0 K) ≤ 3 := by
  have h := Submodule.finrank_mono (inf_le_right : imgS0 G ⊓ S0 K ≤ S0 K)
  rwa [finrank_S0] at h

private theorem a5_card_inter [Finite K] (G : GL (Fin 6) K) :
    Nat.card ↥(U0 K ⊓ conjSub (rhoEquiv K G) (U0 K)) =
      Nat.card K ^ (Module.finrank K ↥(imgS0 G ⊓ S0 K) * Module.finrank K ↥(imgS0 G ⊓ S0 K)) := by
  have hconj : conjSub (rhoEquiv K G) (U0 K) = Urad K (imgS0 G) := by
    rw [U0_eq_Urad]
    exact conjSub_Urad G (S0 K)
  have h := card_Urad_inf (S0 K) (imgS0 G) finrank_S0 (finrank_imgS0 G)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (S0 K) (imgS0 G)
  rw [finrank_S0, finrank_imgS0] at hsum
  have hb : Module.finrank K ↥(S0 K ⊓ imgS0 G) = Module.finrank K ↥(imgS0 G ⊓ S0 K) := by
    rw [inf_comm (S0 K) (imgS0 G)]
  have ha : 6 - Module.finrank K ↥(S0 K ⊔ imgS0 G) = Module.finrank K ↥(imgS0 G ⊓ S0 K) := by
    omega
  rw [hconj, U0_eq_Urad, h, hb, ha]

theorem a5_rank4 : ∀ g₁ ∈ Gam K, ∀ g₂ ∈ Gam K,
    (g₁ (p0 K) ∈ Submodule.span K {p0 K} ↔ g₂ (p0 K) ∈ Submodule.span K {p0 K}) →
    (g₁ (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔
      g₂ (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K)) →
    (beta K (p0 K) (g₁ (p0 K)) = 0 ↔ beta K (p0 K) (g₂ (p0 K)) = 0) →
      ∃ h ∈ Gam K, (∃ c : K, c ≠ 0 ∧ h (p0 K) = c • p0 K) ∧
        ∃ c : K, c ≠ 0 ∧ h (g₁ (p0 K)) = c • g₂ (p0 K) := by
  intro g₁ hg₁ g₂ hg₂ hsp hW hb
  obtain ⟨G₁, hd₁, rfl⟩ := a5_gam_rep hg₁
  obtain ⟨G₂, hd₂, rfl⟩ := a5_gam_rep hg₂
  simp only [rhoEquiv_apply] at hsp hW hb
  rw [rho_p0_mem_span_iff, rho_p0_mem_span_iff] at hsp
  rw [rho_p0_mem_W0_iff hd₁, rho_p0_mem_W0_iff hd₂] at hW
  rw [beta_rho_p0_eq_zero_iff hd₁, beta_rho_p0_eq_zero_iff hd₂] at hb
  have hk : Module.finrank K ↥(imgS0 G₁ ⊓ S0 K) = Module.finrank K ↥(imgS0 G₂ ⊓ S0 K) := by
    have h₁ := a5_finrank_le G₁
    have h₂ := a5_finrank_le G₂
    omega
  obtain ⟨H, hdH, hH1, hH2⟩ := exists_pair_equiv hk
  have hHmem : rhoEquiv K H ∈ Gam K :=
    Subgroup.mem_map.mpr ⟨H, CFSG.Open.StatedAPI.mem_statedSL_of_det hdH, rfl⟩
  obtain ⟨c, hc, hcH⟩ :=
    rho_p0_eq_smul_of_imgS0_eq (G := H) (G' := 1) (hH1.trans a5_imgS0_one.symm)
  obtain ⟨c', hc', hcG⟩ := rho_p0_eq_smul_of_imgS0_eq hH2
  have e3 : rhoEquiv K H (rhoEquiv K G₁ (p0 K)) = rho K (H * G₁) (p0 K) := by
    simp only [rhoEquiv_apply, rho_mul, Module.End.mul_apply]
  refine ⟨rhoEquiv K H, hHmem, ⟨c, hc, ?_⟩, ⟨c', hc', ?_⟩⟩
  · rw [rhoEquiv_apply, hcH, a5_rho_one, Module.End.one_apply]
  · rw [e3, hcG, rhoEquiv_apply]

theorem U0_card [Finite K] : Nat.card (U0 K) = Nat.card K ^ 9 := by
  have h := card_Urad_inf (S0 K) (S0 K) finrank_S0 finrank_S0
  rw [inf_idem (Urad K (S0 K)), inf_idem (S0 K), sup_idem (S0 K), finrank_S0] at h
  rw [U0_eq_Urad, h] <;> norm_num

theorem a5_U_inter_Q [Finite K] : ∀ g ∈ Gam K,
    g (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) → g (p0 K) ∉ Submodule.span K {p0 K} →
      Nat.card ↥(U0 K ⊓ conjSub g (U0 K)) = Nat.card K ^ (6 - 2) := by
  intro g hg hW hsp
  obtain ⟨G, hd, rfl⟩ := a5_gam_rep hg
  rw [rhoEquiv_apply] at hW hsp
  rw [a5_card_inter G]
  have h2 := (rho_p0_mem_W0_iff hd).mp hW
  have h3 : Module.finrank K ↥(imgS0 G ⊓ S0 K) ≠ 3 :=
    fun h => hsp (rho_p0_mem_span_iff.mpr h)
  have hle := a5_finrank_le G
  have hk : Module.finrank K ↥(imgS0 G ⊓ S0 K) = 2 := by omega
  simp only [hk]

theorem a5_U_inter_M [Finite K] : ∀ g ∈ Gam K,
    beta K (p0 K) (g (p0 K)) = 0 → g (p0 K) ∉ Wsp (Submodule.span K {p0 K}) (U0 K) →
      Nat.card ↥(U0 K ⊓ conjSub g (U0 K)) = Nat.card K := by
  intro g hg hb hW
  obtain ⟨G, hd, rfl⟩ := a5_gam_rep hg
  rw [rhoEquiv_apply] at hb hW
  rw [a5_card_inter G]
  have h1 := (beta_rho_p0_eq_zero_iff hd).mp hb
  have h2 : ¬ 2 ≤ Module.finrank K ↥(imgS0 G ⊓ S0 K) :=
    fun h => hW ((rho_p0_mem_W0_iff hd).mpr h)
  have hle := a5_finrank_le G
  have hk : Module.finrank K ↥(imgS0 G ⊓ S0 K) = 1 := by omega
  simp only [hk, mul_one, pow_one]

theorem a5_U_inter_O [Finite K] : ∀ g ∈ Gam K,
    beta K (p0 K) (g (p0 K)) ≠ 0 → Nat.card ↥(U0 K ⊓ conjSub g (U0 K)) = 1 := by
  intro g hg hb
  obtain ⟨G, hd, rfl⟩ := a5_gam_rep hg
  rw [rhoEquiv_apply] at hb
  rw [a5_card_inter G]
  have h1 : ¬ 1 ≤ Module.finrank K ↥(imgS0 G ⊓ S0 K) :=
    fun h => hb ((beta_rho_p0_eq_zero_iff hd).mpr h)
  have hle := a5_finrank_le G
  have hk : Module.finrank K ↥(imgS0 G ⊓ S0 K) = 0 := by omega
  simp only [hk, mul_zero, pow_zero]

theorem a5MinuscRank [Finite K] : MinuscRank (Gam K) (p0 K) (U0 K) (beta K) 10 6 :=
  ⟨fun _ hg v w => Gam_beta_inv hg v w, beta_skew, fun _ hr => beta_p0_of_mem_W0 hr,
    special_exists, opposite_exists, U0_card, U0_norm, a5_rank4, a5_U_inter_Q, a5_U_inter_M,
    a5_U_inter_O⟩

end CFSG.RankThree.GF2n.Smith81.A5Cube
