module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Base
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {E : Type} [Field E] [Finite E] [CharP E 2]

open scoped Classical in
@[expose] noncomputable def colSL (v : Fin 2 → E) (hv : v ≠ 0) : SL(2, E) :=
  if h : v 0 = 0 then ⟨!![0, -(v 1)⁻¹; v 1, 0], by
    have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h, h1])
    simp [Matrix.det_fin_two, h1]⟩
  else ⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [Matrix.det_fin_two, h]⟩

omit [Finite E] [CharP E 2] in
theorem colSL_mulVec_e1 (v : Fin 2 → E) (hv : v ≠ 0) :
    (colSL v hv : Matrix (Fin 2) (Fin 2) E) *ᵥ ![1, 0] = v := by
  by_cases h : v 0 = 0
  · ext i; fin_cases i <;> simp [colSL, h, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext i; fin_cases i <;> simp [colSL, h, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [Finite E] [CharP E 2] in
theorem smul_e1 (y : SL(2, E)) :
    y • (![1, 0] : Fin 2 → E) =
      ![(y : Matrix (Fin 2) (Fin 2) E) 0 0, (y : Matrix (Fin 2) (Fin 2) E) 1 0] := by
  ext i; fin_cases i <;> simp [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [CharP E 2] in
omit [Finite E] in
theorem eq_uSL_of_smul_e1 (y : SL(2, E)) (h : y • (![1, 0] : Fin 2 → E) = ![1, 0]) :
    ∃ d, y = uSL d := by
  rw [smul_e1] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  have hdet := y.2
  rw [Matrix.det_fin_two, h0, h1] at hdet
  refine ⟨(y : Matrix (Fin 2) (Fin 2) E) 0 1, Subtype.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp [coe_uSL, h0]
  · simp [coe_uSL]
  · simp [coe_uSL, h1]
  · simpa [coe_uSL, h0, h1] using hdet

theorem exists_conj_unitriangular (P : Subgroup SL(2, E)) (hP : IsPGroup 2 P) :
    ∃ g : SL(2, E), ∀ x ∈ P, ∃ d, g⁻¹ * x * g = uSL d := by
  have hcard := hP.card_modEq_card_fixedPoints (Fin 2 → E)
  have hE : 2 ∣ Nat.card E := by
    have := Fintype.ofFinite E
    obtain ⟨n, hn, hq⟩ := FiniteField.card E 2
    rw [Nat.card_eq_fintype_card, hq]
    exact dvd_pow_self 2 n.ne_zero
  have heven : 2 ∣ Nat.card (Fin 2 → E) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2)]
    simpa [Fintype.card_fin, sq] using Dvd.dvd.mul_right hE _
  have hfix : ∃ v : Fin 2 → E, v ≠ 0 ∧ ∀ x : P, x • v = v := by
    by_contra hcon
    push Not at hcon
    have hsub : MulAction.fixedPoints P (Fin 2 → E) ⊆ {0} := by
      intro v hv
      by_contra hv0
      obtain ⟨x, hx⟩ := hcon v hv0
      exact hx (hv x)
    have h1 : Nat.card (MulAction.fixedPoints P (Fin 2 → E)) ≤ 1 := by
      calc Nat.card (MulAction.fixedPoints P (Fin 2 → E))
          ≤ Nat.card ({0} : Set (Fin 2 → E)) := Nat.card_mono (Set.finite_singleton _) hsub
        _ = 1 := Nat.card_unique
    have h0 : 0 < Nat.card (MulAction.fixedPoints P (Fin 2 → E)) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, fun x => smul_zero x⟩⟩, inferInstance⟩
    have h2 : Nat.card (MulAction.fixedPoints P (Fin 2 → E)) = 1 := by omega
    rw [h2] at hcard
    have h3 := Nat.mod_eq_zero_of_dvd heven
    unfold Nat.ModEq at hcard
    omega
  obtain ⟨v, hv0, hv⟩ := hfix
  refine ⟨colSL v hv0, fun x hx => eq_uSL_of_smul_e1 _ ?_⟩
  have e1 := colSL_mulVec_e1 v hv0
  have h1 : (colSL v hv0) • (![1, 0] : Fin 2 → E) = v := by
    simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using e1
  rw [mul_smul, mul_smul, h1, show x • v = v from hv ⟨x, hx⟩, inv_smul_eq_iff, h1]

end CFSG.Quasithin.H11
