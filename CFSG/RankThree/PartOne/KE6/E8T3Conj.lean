module

public import CFSG.RankThree.PartOne.KE.E8A2Sigma
public import CFSG.RankThree.PartOne.KE6.E8T3Data
public import CFSG.RankThree.PartOne.KE6.E8T3Tables

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
open scoped Matrix

theorem smul_neg_E8 (T : WeylGroup Tag.E8) (x : V8) : T • (-x) = -(T • x) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_neg]

theorem e8T3W_rel (x : V8) : e8T3W • e8T3W • x + e8T3W • x + x = 0 := by
  have h := congrArg (fun M => M *ᵥ x) e8T3_sq
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec] at h
  rw [← weylMatrix_e8T3W, weylMatrix_mulVec, weylMatrix_mulVec] at h
  exact h

theorem rel_conj {T : WeylGroup Tag.E8} (hrel : ∀ x : V8, T • T • x + T • x + x = 0)
    (g : WeylGroup Tag.E8) (x : V8) :
    (g * T * g⁻¹) • (g * T * g⁻¹) • x + (g * T * g⁻¹) • x + x = 0 := by
  have h := hrel (g⁻¹ • x)
  have h2 := congrArg (fun y => g • y) h
  simp only [smul_add_E8, smul_zero_E8, smul_inv_smul] at h2
  simpa [mul_smul] using h2

theorem e8T3W_smul_eq {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : V8) :
    e8T3W • x = ε • (e8T3We ε • x) := by
  rw [e8T3We_smul hε, smul_smul]
  have : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [this, one_smul]

theorem conj_smul_eq {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {w : WeylGroup Tag.E8}
    (hw : ∀ x : V8, w • x = e8T3We ε • x) (g : WeylGroup Tag.E8) (x : V8) :
    (g⁻¹ * w * g) • x = ε • ((g⁻¹ * e8T3W * g) • x) := by
  rw [mul_smul, mul_smul, hw, e8T3We_smul hε, smul_zsmul_E8, mul_smul, mul_smul]

theorem stab_of_We {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {S : Set V8}
    (hneg : ∀ α ∈ S, -α ∈ S) (hS : ∀ α ∈ S, e8T3We ε • α ∈ S) (α : V8) (hα : α ∈ S) :
    e8T3W • α ∈ S := by
  rw [e8T3W_smul_eq hε]
  rcases hε with rfl | rfl
  · rw [one_smul]; exact hS α hα
  · rw [neg_one_smul]; exact hneg _ (hS α hα)

theorem sigmaRootE8_one_values :
    sigmaRootE8 1 0 1 = (Pi.single 0 1 : V8) ∧ sigmaRootE8 1 1 2 = (Pi.single 2 1 : V8) ∧
      sigmaRootE8 1 0 2 = (Pi.single 0 1 : V8) + (Pi.single 2 1 : V8) := by
  simp only [sigmaRootE8, wbE8, one_smul]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem e8T3_shape_aux {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {T W : WeylGroup Tag.E8}
    (hW : ∀ x : V8, W • x = ε • (T • x)) (π : Equiv.Perm (Fin 3))
    (h01 : T • (Pi.single 0 1 : V8) = sigmaRootE8 1 (π 0) (π 1))
    (h12 : T • (Pi.single 2 1 : V8) = sigmaRootE8 1 (π 1) (π 2))
    (h02 : T • ((Pi.single 0 1 : V8) + (Pi.single 2 1 : V8)) = sigmaRootE8 1 (π 0) (π 2)) :
    ∀ i j : Fin 3, i ≠ j → W • sigmaRootE8 1 i j =
      if ε = 1 then sigmaRootE8 1 (π i) (π j) else sigmaRootE8 1 (π j) (π i) := by
  obtain ⟨v01, v12, v02⟩ := sigmaRootE8_one_values
  have hneg : ∀ i j : Fin 3, W • sigmaRootE8 1 j i = -(W • sigmaRootE8 1 i j) := fun i j => by
    rw [← sigmaRootE8_neg, smul_neg_E8]
  have key : ∀ i j : Fin 3, (i, j) = (0, 1) ∨ (i, j) = (1, 2) ∨ (i, j) = (0, 2) →
      W • sigmaRootE8 1 i j =
        if ε = 1 then sigmaRootE8 1 (π i) (π j) else sigmaRootE8 1 (π j) (π i) := by
    intro i j hij
    have hε' : ε = 1 ∨ ε = -1 := hε
    rcases hij with h | h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [v01, hW, h01]
      rcases hε' with rfl | rfl
      · simp
      · simp [← sigmaRootE8_neg 1 (π 0) (π 1)]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [v12, hW, h12]
      rcases hε' with rfl | rfl
      · simp
      · simp [← sigmaRootE8_neg 1 (π 1) (π 2)]
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [v02, hW, h02]
      rcases hε' with rfl | rfl
      · simp
      · simp [← sigmaRootE8_neg 1 (π 0) (π 2)]
  have hcases : ∀ i j : Fin 3, i ≠ j → ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 2) ∨
      (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 0)) := by decide
  intro i j hij
  rcases hcases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact key _ _ (Or.inl rfl)
  · exact key _ _ (Or.inr (Or.inl rfl))
  · exact key _ _ (Or.inr (Or.inr rfl))
  · have := key 0 1 (Or.inl rfl)
    rw [hneg 0 1, this]
    rcases hε with rfl | rfl <;> simp [sigmaRootE8_neg]
  · have := key 1 2 (Or.inr (Or.inl rfl))
    rw [hneg 1 2, this]
    rcases hε with rfl | rfl <;> simp [sigmaRootE8_neg]
  · have := key 0 2 (Or.inr (Or.inr rfl))
    rw [hneg 0 2, this]
    rcases hε with rfl | rfl <;> simp [sigmaRootE8_neg]

theorem e8T3_shape_std {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {T W : WeylGroup Tag.E8}
    (hW : ∀ x : V8, W • x = ε • (T • x)) (hcols : [colT T 0, colT T 2] ∈ rotCols 0 2) :
    ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j → W • sigmaRootE8 1 i j =
      if ε = 1 then sigmaRootE8 1 (π i) (π j) else sigmaRootE8 1 (π j) (π i) := by
  obtain ⟨v01, v12, v02⟩ := sigmaRootE8_one_values
  simp only [rotCols, List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
    and_true] at hcols
  have e20 : sigmaRootE8 1 2 0 = -((Pi.single 0 1 : V8) + (Pi.single 2 1 : V8)) := by
    rw [← v02, sigmaRootE8_neg]
  have e10 : sigmaRootE8 1 1 0 = -(Pi.single 0 1 : V8) := by
    rw [← v01, sigmaRootE8_neg]
  have e21 : sigmaRootE8 1 2 1 = -(Pi.single 2 1 : V8) := by
    rw [← v12, sigmaRootE8_neg]
  rcases hcols with ⟨hc0, hc2⟩ | ⟨hc0, hc2⟩
  ·
    have e1 : T • (Pi.single 0 1 : V8) = Pi.single 2 1 := hc0
    have e2 : T • (Pi.single 2 1 : V8) = -((Pi.single 0 1 : V8) + (Pi.single 2 1 : V8)) := hc2
    refine ⟨finRotate 3, e8T3_shape_aux hε hW (finRotate 3) ?_ ?_ ?_⟩
    · have h1 : (finRotate 3 0 : Fin 3) = 1 := by decide
      have h2 : (finRotate 3 1 : Fin 3) = 2 := by decide
      rw [h1, h2, v12]
      exact e1
    · have h1 : (finRotate 3 1 : Fin 3) = 2 := by decide
      have h2 : (finRotate 3 2 : Fin 3) = 0 := by decide
      rw [h1, h2, e20]
      exact e2
    · have h1 : (finRotate 3 0 : Fin 3) = 1 := by decide
      have h2 : (finRotate 3 2 : Fin 3) = 0 := by decide
      rw [h1, h2, e10, smul_add_E8, e1, e2]
      abel
  ·
    have e1 : T • (Pi.single 0 1 : V8) = -((Pi.single 0 1 : V8) + (Pi.single 2 1 : V8)) := hc0
    have e2 : T • (Pi.single 2 1 : V8) = Pi.single 0 1 := hc2
    refine ⟨(finRotate 3).symm, e8T3_shape_aux hε hW (finRotate 3).symm ?_ ?_ ?_⟩
    · have h1 : ((finRotate 3).symm 0 : Fin 3) = 2 := by decide
      have h2 : ((finRotate 3).symm 1 : Fin 3) = 0 := by decide
      rw [h1, h2, e20]
      exact e1
    · have h1 : ((finRotate 3).symm 1 : Fin 3) = 0 := by decide
      have h2 : ((finRotate 3).symm 2 : Fin 3) = 1 := by decide
      rw [h1, h2, v01]
      exact e2
    · have h1 : ((finRotate 3).symm 0 : Fin 3) = 2 := by decide
      have h2 : ((finRotate 3).symm 2 : Fin 3) = 1 := by decide
      rw [h1, h2, e21, smul_add_E8, e1, e2]
      abel

end CFSG.RankThree.PartOne.KE6
