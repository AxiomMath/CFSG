module

public import CFSG.Quasithin.Background.JonesParshallSL3

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix Matrix.SpecialLinearGroup
open scoped commutatorElement

variable {F : Type} [Field F]

theorem diag_mul_one_add_single_mul {d e : Fin 3 → F} (hde : ∀ k, d k * e k = 1) {i j : Fin 3}
    (b : F) : diagonal d * (1 + single i j b) * diagonal e = 1 + single i j (d i * b * e j) := by
  ext k l
  simp only [mul_diagonal, diagonal_mul, Matrix.add_apply, one_apply, single_apply]
  split_ifs with h1 h2 h2
  · obtain ⟨rfl, rfl⟩ := h2
    subst h1
    rw [mul_add, add_mul, mul_one, hde]
  · subst h1
    rw [add_zero, mul_one, hde]
  · obtain ⟨rfl, rfl⟩ := h2
    ring
  · ring

@[expose] def sl3Diag (d : Fin 3 → F) (h : d 0 * d 1 * d 2 = 1) : SL3 F :=
  ⟨diagonal d, by rw [det_diagonal, Fin.prod_univ_three, h]⟩

theorem sl3Diag_coe (d : Fin 3 → F) (h : d 0 * d 1 * d 2 = 1) :
    ((sl3Diag d h : SL3 F) : Matrix (Fin 3) (Fin 3) F) = diagonal d := rfl

theorem sl3Diag_ne_zero {d : Fin 3 → F} (h : d 0 * d 1 * d 2 = 1) (k : Fin 3) : d k ≠ 0 := by
  intro hk
  fin_cases k <;> simp_all

theorem sl3Diag_inv_prod {d : Fin 3 → F} (h : d 0 * d 1 * d 2 = 1) :
    (d 0)⁻¹ * (d 1)⁻¹ * (d 2)⁻¹ = 1 := by
  rw [← mul_inv, ← mul_inv, h, inv_one]

theorem sl3Diag_mul (d e : Fin 3 → F) (h : d 0 * d 1 * d 2 = 1) (h' : e 0 * e 1 * e 2 = 1)
    (h'' : (d 0 * e 0) * (d 1 * e 1) * (d 2 * e 2) = 1) :
    sl3Diag d h * sl3Diag e h' = sl3Diag (fun k => d k * e k) h'' := by
  apply Subtype.ext
  change diagonal d * diagonal e = diagonal (fun k => d k * e k)
  rw [diagonal_mul_diagonal]

theorem sl3Diag_inv {d : Fin 3 → F} (h : d 0 * d 1 * d 2 = 1) :
    (sl3Diag d h)⁻¹ = sl3Diag (fun k => (d k)⁻¹) (sl3Diag_inv_prod h) := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  change diagonal d * diagonal (fun k => (d k)⁻¹) = 1
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  exact mul_inv_cancel₀ (sl3Diag_ne_zero h k)

theorem sl3Diag_conj_transvection {d : Fin 3 → F} (h : d 0 * d 1 * d 2 = 1) {i j : Fin 3}
    (hij : i ≠ j) (b : F) :
    sl3Diag d h * transvection hij b * (sl3Diag d h)⁻¹ = transvection hij (d i * b * (d j)⁻¹) := by
  rw [sl3Diag_inv]
  apply Subtype.ext
  change diagonal d * (1 + single i j b) * diagonal (fun k => (d k)⁻¹) =
    1 + single i j (d i * b * (d j)⁻¹)
  exact diag_mul_one_add_single_mul (fun k => mul_inv_cancel₀ (sl3Diag_ne_zero h k)) b

theorem transvection_mem_commutator3 {c : F} (hc : c ≠ 0) (hc2 : c ^ 2 ≠ 1) {i j : Fin 3}
    (hij : i ≠ j) (b : F) : transvection hij b ∈ commutator (SL3 F) := by
  set d : Fin 3 → F := fun k => if k = i then c else if k = j then c⁻¹ else 1 with hd
  have hdi : d i = c := by simp [hd]
  have hdj : d j = c⁻¹ := by simp [hd, hij.symm]
  have hprod : d 0 * d 1 * d 2 = 1 := by
    fin_cases i <;> fin_cases j <;> simp at hij <;> simp [hd, hc]
  have hc2' : c ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hc2
  obtain ⟨b', hb'⟩ : ∃ b' : F, b' * (c ^ 2 - 1) = b := ⟨b / (c ^ 2 - 1), div_mul_cancel₀ _ hc2'⟩
  have e : ⁅sl3Diag d hprod, transvection hij b'⁆ = transvection hij b := by
    rw [commutatorElement_def, sl3Diag_conj_transvection, transvection_inv, hdi, hdj,
      ← transvection_add, inv_inv]
    congr 1
    linear_combination hb'
  rw [← e]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

@[expose] def sl3W01 : SL3 F := ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def sl3W12 : SL3 F := ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], by simp [det_fin_three]⟩

@[expose] def diag3 (a b c : F) (h : a * b * c = 1) : SL3 F :=
  ⟨diagonal ![a, b, c], by rw [det_diagonal, Fin.prod_univ_three]; simpa using h⟩

theorem diag3_congr {a b c a' b' c' : F} {h : a * b * c = 1} {h' : a' * b' * c' = 1}
    (ha : a = a') (hb : b = b') (hc : c = c') : diag3 a b c h = diag3 a' b' c' h' := by
  subst ha hb hc
  rfl

theorem diag3_mul {a b c a' b' c' : F} (h : a * b * c = 1) (h' : a' * b' * c' = 1)
    (h'' : (a * a') * (b * b') * (c * c') = 1) :
    diag3 a b c h * diag3 a' b' c' h' = diag3 (a * a') (b * b') (c * c') h'' := by
  apply Subtype.ext
  change diagonal ![a, b, c] * diagonal ![a', b', c'] = diagonal ![a * a', b * b', c * c']
  rw [diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem diag3_inv {a b c : F} (h : a * b * c = 1) :
    (diag3 a b c h)⁻¹ = diag3 a⁻¹ b⁻¹ c⁻¹ (by rw [← mul_inv, ← mul_inv, h, inv_one]) := by
  have ha : a ≠ 0 := fun h0 => by simp [h0] at h
  have hb : b ≠ 0 := fun h0 => by simp [h0] at h
  have hc : c ≠ 0 := fun h0 => by simp [h0] at h
  refine inv_eq_of_mul_eq_one_right ?_
  rw [diag3_mul _ _ (by field_simp)]
  apply Subtype.ext
  change diagonal ![a * a⁻¹, b * b⁻¹, c * c⁻¹] = 1
  rw [mul_inv_cancel₀ ha, mul_inv_cancel₀ hb, mul_inv_cancel₀ hc, ← diagonal_one]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem sl3W01_mul {a b c : F} (h : a * b * c = 1) (h' : b * a * c = 1) :
    sl3W01 * diag3 a b c h = diag3 b a c h' * sl3W01 := by
  apply Subtype.ext
  change !![(0 : F), -1, 0; 1, 0, 0; 0, 0, 1] * diagonal ![a, b, c] =
    diagonal ![b, a, c] * !![(0 : F), -1, 0; 1, 0, 0; 0, 0, 1]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [mul_apply, Fin.sum_univ_three]

theorem sl3W12_mul {a b c : F} (h : a * b * c = 1) (h' : a * c * b = 1) :
    sl3W12 * diag3 a b c h = diag3 a c b h' * sl3W12 := by
  apply Subtype.ext
  change !![(1 : F), 0, 0; 0, 0, -1; 0, 1, 0] * diagonal ![a, b, c] =
    diagonal ![a, c, b] * !![(1 : F), 0, 0; 0, 0, -1; 0, 1, 0]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [mul_apply, Fin.sum_univ_three]

theorem comm_w01_diag3 {x : F} (hx : x ≠ 0) :
    ⁅(sl3W01 : SL3 F), diag3 1 x x⁻¹ (by field_simp)⁆ = diag3 x x⁻¹ 1 (by field_simp) := by
  rw [commutatorElement_def, sl3W01_mul _ (by field_simp), mul_inv_cancel_right, diag3_inv,
    diag3_mul _ _ (by field_simp)]
  exact diag3_congr (by simp) (by simp) (by field_simp)

theorem comm_w12_diag3 {y : F} (hy : y ≠ 0) :
    ⁅(sl3W12 : SL3 F), diag3 y⁻¹ 1 y (by field_simp)⁆ = diag3 1 y y⁻¹ (by field_simp) := by
  rw [commutatorElement_def, sl3W12_mul _ (by field_simp), mul_inv_cancel_right, diag3_inv,
    diag3_mul _ _ (by field_simp)]
  exact diag3_congr (by field_simp) (by simp) (by simp)

theorem sl3Diag_mem_commutator (d : Fin 3 → F) (h : d 0 * d 1 * d 2 = 1) :
    sl3Diag d h ∈ commutator (SL3 F) := by
  have h0 := sl3Diag_ne_zero h 0
  have h1 := sl3Diag_ne_zero h 1
  have he : d 0 * d 1 ≠ 0 := mul_ne_zero h0 h1
  have hd2 : d 2 = (d 0 * d 1)⁻¹ := by
    rw [eq_comm, inv_eq_iff_eq_inv, eq_comm]
    exact (eq_inv_of_mul_eq_one_left h).symm
  have hd : sl3Diag d h = diag3 (d 0) (d 0)⁻¹ 1 (by field_simp) *
      diag3 1 (d 0 * d 1) (d 0 * d 1)⁻¹ (by field_simp) := by
    rw [diag3_mul _ _ (by field_simp)]
    apply Subtype.ext
    change diagonal d = diagonal ![d 0 * 1, (d 0)⁻¹ * (d 0 * d 1), 1 * (d 0 * d 1)⁻¹]
    congr 1
    funext k
    fin_cases k
    · simp
    · simp
      field_simp
    · simp [hd2]
  rw [hd, ← comm_w01_diag3 h0, ← comm_w12_diag3 he]
  exact Subgroup.mul_mem _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem sl3_commutator_eq_top {c : F} (hc : c ≠ 0) (hc2 : c ^ 2 ≠ 1) :
    commutator (SL3 F) = ⊤ := by
  refine eq_top_iff.mpr fun M _ => ?_
  refine diagonal_transvection_induction' (fun M => M ∈ commutator (SL3 F)) M
    (fun i j hij a ha => ?_) (fun i j hij a => transvection_mem_commutator3 hc hc2 hij a)
    (fun A B hA hB => Subgroup.mul_mem _ hA hB)
  have hp : (fun k => if k = i then a else if k = j then a⁻¹ else 1 : Fin 3 → F) 0 *
      (fun k => if k = i then a else if k = j then a⁻¹ else 1 : Fin 3 → F) 1 *
      (fun k => if k = i then a else if k = j then a⁻¹ else 1 : Fin 3 → F) 2 = 1 := by
    fin_cases i <;> fin_cases j <;> simp at hij <;> simp [ha]
  exact sl3Diag_mem_commutator _ hp

end CFSG.Quasithin.JonesParshall
