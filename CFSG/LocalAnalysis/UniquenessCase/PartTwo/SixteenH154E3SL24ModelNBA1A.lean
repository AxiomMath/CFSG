module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNA
public import CFSG.Quasithin.Vol2.Ch6Semilinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

@[expose] def s16h_qp (v : Orth3) : Fin 2 → GF4 :=
  fun i => if i = 0 then (Multiplicative.toAdd v).1 else (Multiplicative.toAdd v).2.1

@[expose] def s16h_lift (w : Fin 2 → GF4) : Orth3 :=
  Multiplicative.ofAdd (w 0, w 1, 0)

theorem s16h_qp_add (v w : Orth3) : s16h_qp (v * w) = s16h_qp v + s16h_qp w := by
  funext i
  fin_cases i <;> simp [s16h_qp, toAdd_mul]

theorem s16h_qp_inv (v : Orth3) : s16h_qp v⁻¹ = -s16h_qp v := by
  funext i
  fin_cases i <;> simp [s16h_qp, toAdd_inv]

theorem s16h_qp_lift (w : Fin 2 → GF4) : s16h_qp (s16h_lift w) = w := by
  funext i
  fin_cases i <;> simp [s16h_qp, s16h_lift]

theorem s16h_qp_eq_zero_iff (v : Orth3) : s16h_qp v = 0 ↔ v ∈ orth3Z := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [s16h_qp, h0, h1]

theorem s16h_qp_eq_of_mul_inv_mem {a b : Orth3} (h : a * b⁻¹ ∈ orth3Z) :
    s16h_qp a = s16h_qp b := by
  have h0 : s16h_qp (a * b⁻¹) = 0 := (s16h_qp_eq_zero_iff _).mpr h
  rw [s16h_qp_add, s16h_qp_inv] at h0
  funext i
  have hi := congrFun h0 i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hi
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hi)

theorem s16h_mem_Z_of_qp_eq {a b : Orth3} (h : s16h_qp a = s16h_qp b) : a * b⁻¹ ∈ orth3Z := by
  rw [← s16h_qp_eq_zero_iff, s16h_qp_add, s16h_qp_inv, h]
  simp

theorem s16h_lift_qp_mul_inv_mem (v : Orth3) : s16h_lift (s16h_qp v) * v⁻¹ ∈ orth3Z := by
  rw [← s16h_qp_eq_zero_iff, s16h_qp_add, s16h_qp_lift, s16h_qp_inv]
  simp

theorem s16h_qp_orth3Aut (γ : ↥(StatedSL 2 GF4)) (v : Orth3) :
    s16h_qp (s16h_orth3Aut γ v) =
      (((γ : Matrix.GeneralLinearGroup (Fin 2) GF4) : Matrix (Fin 2) (Fin 2) GF4)).mulVec
        (s16h_qp v) := by
  funext i
  fin_cases i <;>
    simp [s16h_qp, s16h_orth3Aut, s16h_orth3ActM, Matrix.mulVec, Fin.sum_univ_two]

theorem s16h_qp_orth3Scal (μ : GF4) (hμ : μ ≠ 0) (v : Orth3) :
    s16h_qp (orth3Scal μ hμ v) = μ • s16h_qp v := by
  funext i
  fin_cases i <;> simp [s16h_qp, orth3Scal, Pi.smul_apply]

theorem s16h_qp_orth3Phi (v : Orth3) :
    s16h_qp (orth3Phi v) = fun i => (s16h_qp v i) ^ 2 := by
  funext i
  fin_cases i <;> simp [s16h_qp, orth3Phi]

@[expose] def s16h_sl2X_stated : ↥(StatedSL 2 GF4) :=
  ⟨Matrix.SpecialLinearGroup.toGL (CFSG.Quasithin.H13.sl2X (1 : GF4)), by
    rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
    exact ⟨CFSG.Quasithin.H13.sl2X (1 : GF4), rfl⟩⟩

@[expose] def s16h_sl2Y_stated : ↥(StatedSL 2 GF4) :=
  ⟨Matrix.SpecialLinearGroup.toGL (CFSG.Quasithin.H13.sl2Y (1 : GF4)), by
    rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
    exact ⟨CFSG.Quasithin.H13.sl2Y (1 : GF4), rfl⟩⟩

theorem s16h_orth3Z_of_fix_gens : ∀ v : Orth3,
    s16h_orth3Aut s16h_sl2X_stated v = v →
    s16h_orth3Aut s16h_sl2Y_stated v = v →
    (Multiplicative.toAdd v).1 = 0 ∧ (Multiplicative.toAdd v).2.1 = 0 := by
  decide +kernel

theorem s16h_orth3Z_fixed (v : Orth3) :
    v ∈ orth3Z ↔ ∀ σ ∈ orth3L, σ v = v := by
  constructor
  · intro hv σ hσ
    rw [s16h_orth3L_eq_range] at hσ
    obtain ⟨γ, rfl⟩ := hσ
    exact s16h_orth3Aut_fix_Z γ hv
  · intro hv
    show (Multiplicative.toAdd v).1 = 0 ∧ (Multiplicative.toAdd v).2.1 = 0
    exact s16h_orth3Z_of_fix_gens v
      (hv _ (by rw [s16h_orth3L_eq_range]; exact ⟨s16h_sl2X_stated, rfl⟩))
      (hv _ (by rw [s16h_orth3L_eq_range]; exact ⟨s16h_sl2Y_stated, rfl⟩))

theorem s16h_orth3_normalizer_preserves_Z {n : MulAut Orth3}
    (hn : n ∈ Subgroup.normalizer (orth3L : Set (MulAut Orth3))) :
    ∀ v : Orth3, v ∈ orth3Z → n v ∈ orth3Z := by
  intro v hv
  rw [s16h_orth3Z_fixed] at hv ⊢
  intro σ hσ
  have hconj : n⁻¹ * σ * n ∈ orth3L :=
    (Subgroup.mem_normalizer_iff.mp (inv_mem hn) σ).mp hσ
  have hfix : (n⁻¹ * σ * n) v = v := hv _ hconj
  show σ (n v) = n v
  have hcomp : σ * n = n * (n⁻¹ * σ * n) := by group
  calc σ (n v) = (σ * n) v := rfl
    _ = (n * (n⁻¹ * σ * n)) v := by rw [hcomp]
    _ = n ((n⁻¹ * σ * n) v) := rfl
    _ = n v := by rw [hfix]

theorem s16h_gf4_ringAut_eq (σ : GF4 ≃+* GF4) :
    (∀ x : GF4, σ x = x) ∨ (∀ x : GF4, σ x = x ^ 2) := by
  have hroots : ∀ y : GF4, y ^ 2 + y + 1 = 0 →
      y = GF4.ofNat' 2 ∨ y = GF4.ofNat' 3 := by
    decide +kernel
  have hroot : σ (GF4.ofNat' 2) ^ 2 + σ (GF4.ofNat' 2) + 1 = 0 := by
    have h : (GF4.ofNat' 2 : GF4) ^ 2 + GF4.ofNat' 2 + 1 = 0 := by decide +kernel
    calc σ (GF4.ofNat' 2) ^ 2 + σ (GF4.ofNat' 2) + 1
        = σ ((GF4.ofNat' 2) ^ 2) + σ (GF4.ofNat' 2) + σ 1 := by simp
      _ = σ ((GF4.ofNat' 2) ^ 2 + GF4.ofNat' 2 + 1) := by rw [map_add, map_add]
      _ = σ 0 := by rw [h]
      _ = 0 := map_zero σ
  have hval := hroots _ hroot
  have h3 : (GF4.ofNat' 3 : GF4) = GF4.ofNat' 2 + 1 := by decide +kernel
  have hall : ∀ x : GF4, x = 0 ∨ x = 1 ∨ x = GF4.ofNat' 2 ∨ x = GF4.ofNat' 3 := by
    decide +kernel
  rcases hval with h | h
  · left
    intro x
    rcases hall x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact h
    · rw [h3, map_add, map_one, h]
  · right
    intro x
    rcases hall x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · rw [h]
      decide +kernel
    · rw [h3, map_add, map_one, h]
      decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
