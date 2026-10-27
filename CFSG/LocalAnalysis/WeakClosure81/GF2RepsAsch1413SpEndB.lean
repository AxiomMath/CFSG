module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup
open scoped Matrix

private lemma a1413SpEndB_trace_eq_zero {K : Type} [Field K]
    {X : Matrix (Fin 2) (Fin 2) K} (hX : X * X = -1) (hdet : X.det = 1) : X.trace = 0 := by
  have h1 : X * X.adjugate = 1 := by
    rw [Matrix.mul_adjugate, hdet, one_smul]
  have h2 : X.adjugate = X.trace • (1 : Matrix (Fin 2) (Fin 2) K) - X := by
    rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h2] at h1
  have h3 : X.trace • X = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hX, sub_neg_eq_add] at h1
    have h1' : X.trace • X + 1 = 0 + 1 := by rw [h1, zero_add]
    exact add_right_cancel h1'
  have hX0 : X ≠ 0 := by
    intro h
    have h' : X * X = 0 := by rw [h, Matrix.mul_zero]
    rw [hX] at h'
    exact (neg_ne_zero.mpr one_ne_zero) h'
  exact (smul_eq_zero.mp h3).resolve_right hX0

private lemma a1413SpEndB_smul_eq_of_ne_zero {K : Type} [Field K] {v : Fin 2 → K}
    (hv : v ≠ 0) {a b : K} (h : a • v = b • v) : a = b := by
  have h' : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  have h2 : ∀ i, (a - b) * v i = 0 := by
    intro i
    have := congrFun h' i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hv (funext hc)
  exact sub_eq_zero.mp ((mul_eq_zero.mp (h2 i)).resolve_right hi)

private lemma a1413SpEndB_eq_zero_of_mulVec_eq_zero {K : Type} [Field K]
    {P : Matrix (Fin 2) (Fin 2) K} {v w : Fin 2 → K}
    (hvw : LinearIndependent K ![v, w]) (hv : P *ᵥ v = 0) (hw : P *ᵥ w = 0) : P = 0 := by
  set C : Matrix (Fin 2) (Fin 2) K := Matrix.of (fun i j => ![v, w] j i) with hC
  have hCcol : C.col = ![v, w] := by
    funext j
    rfl
  have hunit : IsUnit C := Matrix.linearIndependent_cols_iff_isUnit.mp (hCcol ▸ hvw)
  obtain ⟨u, hu⟩ := hunit
  have hPC : P * C = 0 := by
    ext i j
    fin_cases j
    · show ((P * C).col 0) i = 0
      rw [Matrix.col_mul_eq_mulVec_col, hCcol]
      simp [hv]
    · show ((P * C).col 1) i = 0
      rw [Matrix.col_mul_eq_mulVec_col, hCcol]
      simp [hw]
  calc P = P * 1 := (Matrix.mul_one P).symm
    _ = P * (C * ↑u⁻¹) := by rw [← hu, Units.mul_inv]
    _ = (P * C) * ↑u⁻¹ := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hPC, Matrix.zero_mul]

private lemma a1413SpEndB_det_ne_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {P G H G' H' : Matrix (Fin 2) (Fin 2) K} (hG : G * G = -1) (hH : H * H = -1)
    (hGH : G * H = -(H * G)) (hP : P ≠ 0) (hPG : P * G = G' * P)
    (hPH : P * H = H' * P) : P.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set w := G *ᵥ v with hwdef
  have hw0 : P *ᵥ w = 0 := by
    rw [hwdef, Matrix.mulVec_mulVec, hPG, ← Matrix.mulVec_mulVec, hv0, Matrix.mulVec_zero]
  set u := H *ᵥ v with hudef
  have hu0 : P *ᵥ u = 0 := by
    rw [hudef, Matrix.mulVec_mulVec, hPH, ← Matrix.mulVec_mulVec, hv0, Matrix.mulVec_zero]
  have hwmem : w ∈ Submodule.span K {v} := by
    by_contra hwmem
    have hvw : LinearIndependent K ![v, w] := by
      rw [LinearIndependent.pair_iff' hv]
      intro a ha
      exact hwmem (by rw [← ha]; exact Submodule.mem_span_singleton.mpr ⟨a, rfl⟩)
    exact hP (a1413SpEndB_eq_zero_of_mulVec_eq_zero hvw hv0 hw0)
  have humem : u ∈ Submodule.span K {v} := by
    by_contra humem
    have huv : LinearIndependent K ![v, u] := by
      rw [LinearIndependent.pair_iff' hv]
      intro a ha
      exact humem (by rw [← ha]; exact Submodule.mem_span_singleton.mpr ⟨a, rfl⟩)
    exact hP (a1413SpEndB_eq_zero_of_mulVec_eq_zero huv hv0 hu0)
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hwmem
  obtain ⟨mu, hmu⟩ := Submodule.mem_span_singleton.mp humem
  have hGv : G *ᵥ v = lam • v := by rw [← hwdef, hlam]
  have hHv : H *ᵥ v = mu • v := by rw [← hudef, hmu]
  have hlam2 : lam * lam = -1 := by
    have h1 : (lam * lam) • v = (-1 : K) • v := by
      calc (lam * lam) • v = lam • (lam • v) := by rw [smul_smul]
        _ = lam • (G *ᵥ v) := by rw [hGv]
        _ = G *ᵥ (lam • v) := by rw [Matrix.mulVec_smul]
        _ = G *ᵥ (G *ᵥ v) := by rw [hGv]
        _ = (G * G) *ᵥ v := by rw [Matrix.mulVec_mulVec]
        _ = (-1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by rw [hG]
        _ = -v := by rw [Matrix.neg_mulVec, Matrix.one_mulVec]
        _ = (-1 : K) • v := by rw [neg_smul, one_smul]
    exact a1413SpEndB_smul_eq_of_ne_zero hv h1
  have hmu2 : mu * mu = -1 := by
    have h1 : (mu * mu) • v = (-1 : K) • v := by
      calc (mu * mu) • v = mu • (mu • v) := by rw [smul_smul]
        _ = mu • (H *ᵥ v) := by rw [hHv]
        _ = H *ᵥ (mu • v) := by rw [Matrix.mulVec_smul]
        _ = H *ᵥ (H *ᵥ v) := by rw [hHv]
        _ = (H * H) *ᵥ v := by rw [Matrix.mulVec_mulVec]
        _ = (-1 : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by rw [hH]
        _ = -v := by rw [Matrix.neg_mulVec, Matrix.one_mulVec]
        _ = (-1 : K) • v := by rw [neg_smul, one_smul]
    exact a1413SpEndB_smul_eq_of_ne_zero hv h1
  have hcross : mu * lam = -(lam * mu) := by
    have h1 : (mu * lam) • v = (-(lam * mu)) • v := by
      calc (mu * lam) • v = mu • (lam • v) := by rw [smul_smul]
        _ = mu • (G *ᵥ v) := by rw [hGv]
        _ = G *ᵥ (mu • v) := by rw [Matrix.mulVec_smul]
        _ = G *ᵥ (H *ᵥ v) := by rw [hHv]
        _ = (G * H) *ᵥ v := by rw [Matrix.mulVec_mulVec]
        _ = (-(H * G)) *ᵥ v := by rw [hGH]
        _ = -(H *ᵥ (G *ᵥ v)) := by rw [Matrix.neg_mulVec, Matrix.mulVec_mulVec]
        _ = -(H *ᵥ (lam • v)) := by rw [hGv]
        _ = -(lam • (H *ᵥ v)) := by rw [Matrix.mulVec_smul]
        _ = -(lam • (mu • v)) := by rw [hHv]
        _ = (-(lam * mu)) • v := by rw [smul_smul, neg_smul]
    exact a1413SpEndB_smul_eq_of_ne_zero hv h1
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, mul_zero] at hlam2
    exact (neg_ne_zero.mpr one_ne_zero) hlam2.symm
  have hmu0 : mu ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmu2
    exact (neg_ne_zero.mpr one_ne_zero) hmu2.symm
  have h2mul : (2 : K) * (lam * mu) = 0 := by
    have h := hcross
    rw [mul_comm mu lam] at h
    linear_combination h
  rcases mul_eq_zero.mp h2mul with h | h
  · exact h2 h
  · exact (mul_ne_zero hlam0 hmu0) h

private lemma a1413SpEndB_mul_single_apply {K : Type} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (A * Matrix.single i j (1 : K) * B) i j = A i i * B j j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne, Matrix.mul_apply]

private lemma a1413SpEndB_sum_single_mul {K : Type} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) :
    ∑ i : Fin 2, ∑ j : Fin 2, (A * Matrix.single i j (1 : K) * B) i j =
      A.trace * B.trace := by
  simp only [a1413SpEndB_mul_single_apply, Matrix.trace_fin_two, Fin.sum_univ_two]
  ring

open Matrix

variable {K : Type} [Field K]

private noncomputable def a1413SpEndB_Bmat (a c : K) (P : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks !![a, c * P.adjugate 0 0; c * P 0 0, -a] !![0, c * P.adjugate 0 1; c * P 0 1, 0]
    !![0, c * P.adjugate 1 0; c * P 1 0, 0] !![a, c * P.adjugate 1 1; c * P 1 1, -a]

private lemma a1413SpEndB_Bmat_sq (a c : K) (P : Matrix (Fin 2) (Fin 2) K) :
    a1413SpEndB_Bmat a c P * a1413SpEndB_Bmat a c P = (a ^ 2 + P.det * c ^ 2) • 1 := by
  have h1 : ((a ^ 2 + P.det * c ^ 2) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) =
      fromBlocks ((a ^ 2 + P.det * c ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0
        ((a ^ 2 + P.det * c ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K)) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp
  rw [h1, a1413SpEndB_Bmat, fromBlocks_multiply]
  congr 1 <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.adjugate_fin_two] <;>
    ring)

private lemma a1413SpEndB_Bmat_sim (a c : K) (P : Matrix (Fin 2) (Fin 2) K) :
    (a1413SpEndB_Bmat a c P)ᵀ * formJ 2 K * a1413SpEndB_Bmat a c P =
      (a ^ 2 + P.det * c ^ 2) • formJ 2 K := by
  rw [formJ_eq_blk, a1413SpEndB_Bmat, blk, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_smul]
  congr 1 <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.adjugate_fin_two,
      J₁, diag2] <;> ring)

private lemma a1413SpEndB_Bmat_comm (a c : K) (P g₁ g₂ : Matrix (Fin 2) (Fin 2) K)
    (hg : P * g₁ = g₂ * P) (hg' : P.adjugate * g₂ = g₁ * P.adjugate) :
    a1413SpEndB_Bmat a c P * blk g₁ g₂ = blk g₁ g₂ * a1413SpEndB_Bmat a c P := by
  rw [Matrix.adjugate_fin_two] at hg'
  have e1 := congrFun (congrFun hg 0) 0
  have e2 := congrFun (congrFun hg 0) 1
  have e3 := congrFun (congrFun hg 1) 0
  have e4 := congrFun (congrFun hg 1) 1
  have e5 := congrFun (congrFun hg' 0) 0
  have e6 := congrFun (congrFun hg' 0) 1
  have e7 := congrFun (congrFun hg' 1) 0
  have e8 := congrFun (congrFun hg' 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one] at e1 e2 e3 e4 e5 e6 e7 e8
  rw [a1413SpEndB_Bmat, blk, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, diag2] <;>
    first
    | ring1
    | linear_combination c * e1 | linear_combination (-c) * e1
    | linear_combination c * e2 | linear_combination (-c) * e2
    | linear_combination c * e3 | linear_combination (-c) * e3
    | linear_combination c * e4 | linear_combination (-c) * e4
    | linear_combination c * e5 | linear_combination (-c) * e5
    | linear_combination c * e6 | linear_combination (-c) * e6
    | linear_combination c * e7 | linear_combination (-c) * e7
    | linear_combination c * e8 | linear_combination (-c) * e8)

private lemma a1413SpEndB_adj_intertwine (P g₁ g₂ : Matrix (Fin 2) (Fin 2) K)
    (hP : P.det ≠ 0) (hg : P * g₁ = g₂ * P) : P.adjugate * g₂ = g₁ * P.adjugate := by
  have e1 : P.adjugate * (P * g₁) * P.adjugate = P.adjugate * (g₂ * P) * P.adjugate := by
    rw [hg]
  have L : P.adjugate * (P * g₁) * P.adjugate = P.det • (g₁ * P.adjugate) := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul]
  have R : P.adjugate * (g₂ * P) * P.adjugate = P.det • (P.adjugate * g₂) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
      Matrix.mul_one, Matrix.mul_smul]
  exact (smul_right_injective _ hP (L.symm.trans (e1.trans R))).symm

theorem sp4_commutant_B {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    {g₁ g₂ h₁ h₂ : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg₁ : g₁ * g₁ = negOneSL) (hg₂ : g₂ * g₂ = negOneSL) (hh₁ : h₁ * h₁ = negOneSL)
    (hh₂ : h₂ * h₂ = negOneSL) (hgh₁ : g₁ * h₁ = negOneSL * (h₁ * g₁))
    (hgh₂ : g₂ * h₂ = negOneSL * (h₂ * g₂)) :
    ∃ (B : gsp 2 K) (d : K), d ≠ 0 ∧ (∀ l : K, l ^ 2 ≠ d) ∧
      ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1 ∧
      ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
        ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K ∧
      conjSp 2 K B (blkSL K (g₁, g₂)) = blkSL K (g₁, g₂) ∧
      conjSp 2 K B (blkSL K (h₁, h₂)) = blkSL K (h₁, h₂) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  haveI : Fintype K := Fintype.ofFinite K
  set G1 : Matrix (Fin 2) (Fin 2) K := (g₁ : Matrix (Fin 2) (Fin 2) K) with hG1def
  set G2 : Matrix (Fin 2) (Fin 2) K := (g₂ : Matrix (Fin 2) (Fin 2) K) with hG2def
  set H1 : Matrix (Fin 2) (Fin 2) K := (h₁ : Matrix (Fin 2) (Fin 2) K) with hH1def
  set H2 : Matrix (Fin 2) (Fin 2) K := (h₂ : Matrix (Fin 2) (Fin 2) K) with hH2def
  have hG1 : G1 * G1 = -1 := by
    rw [hG1def]
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL] using congrArg Subtype.val hg₁
  have hG2 : G2 * G2 = -1 := by
    rw [hG2def]
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL] using congrArg Subtype.val hg₂
  have hH1 : H1 * H1 = -1 := by
    rw [hH1def]
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL] using congrArg Subtype.val hh₁
  have hH2 : H2 * H2 = -1 := by
    rw [hH2def]
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL] using congrArg Subtype.val hh₂
  have hGH1 : G1 * H1 = -(H1 * G1) := by
    rw [hG1def, hH1def]
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL, neg_one_mul] using
      congrArg Subtype.val hgh₁
  have hGH2 : G2 * H2 = -(H2 * G2) := by
    rw [hG2def, hH2def]
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL, neg_one_mul] using
      congrArg Subtype.val hgh₂
  have htrG1 : G1.trace = 0 := by
    refine a1413SpEndB_trace_eq_zero hG1 ?_
    simpa [hG1def] using g₁.2
  have htrG2 : G2.trace = 0 := by
    refine a1413SpEndB_trace_eq_zero hG2 ?_
    simpa [hG2def] using g₂.2
  have htrH1 : H1.trace = 0 := by
    refine a1413SpEndB_trace_eq_zero hH1 ?_
    simpa [hH1def] using h₁.2
  have htrH2 : H2.trace = 0 := by
    refine a1413SpEndB_trace_eq_zero hH2 ?_
    simpa [hH2def] using h₂.2
  have htrGH2 : (G2 * H2).trace = 0 := by
    have hsq : (G2 * H2) * (G2 * H2) = -1 := by
      have e : ∀ X : Matrix (Fin 2) (Fin 2) K, G2 * (H2 * X) = -(H2 * (G2 * X)) := fun X => by
        rw [← Matrix.mul_assoc, hGH2, neg_mul, Matrix.mul_assoc]
      rw [Matrix.mul_assoc, e]
      rw [show G2 * (G2 * H2) = -H2 by rw [← Matrix.mul_assoc, hG2, neg_one_mul]]
      rw [mul_neg, hH2, neg_neg]
    refine a1413SpEndB_trace_eq_zero hsq ?_
    rw [Matrix.det_mul]
    simpa [hG2def, hH2def] using mul_eq_one.mpr ⟨g₂.2, h₂.2⟩
  let Φ : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K := fun M =>
    M - G2 * M * G1 - H2 * M * H1 - (G2 * H2) * M * (G1 * H1)
  have hΦG : ∀ M, G2 * Φ M = Φ M * G1 := by
    intro M
    dsimp only [Φ]
    have fG1 : ∀ X : Matrix (Fin 2) (Fin 2) K, G1 * (G1 * X) = -X := fun X => by
      rw [← Matrix.mul_assoc, hG1, neg_one_mul]
    have fG2 : ∀ X : Matrix (Fin 2) (Fin 2) K, G2 * (G2 * X) = -X := fun X => by
      rw [← Matrix.mul_assoc, hG2, neg_one_mul]
    have fH1 : ∀ X : Matrix (Fin 2) (Fin 2) K, H1 * (H1 * X) = -X := fun X => by
      rw [← Matrix.mul_assoc, hH1, neg_one_mul]
    have fH2 : ∀ X : Matrix (Fin 2) (Fin 2) K, H2 * (H2 * X) = -X := fun X => by
      rw [← Matrix.mul_assoc, hH2, neg_one_mul]
    have fGH2 : ∀ X : Matrix (Fin 2) (Fin 2) K, G2 * (H2 * X) = -(H2 * (G2 * X)) := fun X => by
      rw [← Matrix.mul_assoc, hGH2, neg_mul, Matrix.mul_assoc]
    noncomm_ring [hG1, hG2, hH1, hH2, hGH1, hGH2, fG1, fG2, fH1, fH2, fGH2]
  have hΦH : ∀ M, H2 * Φ M = Φ M * H1 := by
    intro M
    dsimp only [Φ]
    have fG1 : ∀ X : Matrix (Fin 2) (Fin 2) K, G1 * (G1 * X) = -X := fun X => by
      rw [← Matrix.mul_assoc, hG1, neg_one_mul]
    have fG2 : ∀ X : Matrix (Fin 2) (Fin 2) K, G2 * (G2 * X) = -X := fun X => by
      rw [← Matrix.mul_assoc, hG2, neg_one_mul]
    have fH1 : ∀ X : Matrix (Fin 2) (Fin 2) K, H1 * (H1 * X) = -X := fun X => by
      rw [← Matrix.mul_assoc, hH1, neg_one_mul]
    have fH2 : ∀ X : Matrix (Fin 2) (Fin 2) K, H2 * (H2 * X) = -X := fun X => by
      rw [← Matrix.mul_assoc, hH2, neg_one_mul]
    have fGH1 : ∀ X : Matrix (Fin 2) (Fin 2) K, G1 * (H1 * X) = -(H1 * (G1 * X)) := fun X => by
      rw [← Matrix.mul_assoc, hGH1, neg_mul, Matrix.mul_assoc]
    noncomm_ring [hG1, hG2, hH1, hH2, hGH1, hGH2, fG1, fG2, fH1, fH2, fGH1]
  have hsum : ∑ i : Fin 2, ∑ j : Fin 2, (Φ (Matrix.single i j (1 : K))) i j = 4 := by
    have h1 : ∀ i j : Fin 2, (Φ (Matrix.single i j (1 : K))) i j =
        (Matrix.single i j (1 : K)) i j -
          ((G2 * Matrix.single i j (1 : K) * G1) : Matrix (Fin 2) (Fin 2) K) i j -
          ((H2 * Matrix.single i j (1 : K) * H1) : Matrix (Fin 2) (Fin 2) K) i j -
          (((G2 * H2) * Matrix.single i j (1 : K) * (G1 * H1)) :
            Matrix (Fin 2) (Fin 2) K) i j := by
      intro i j
      dsimp only [Φ]
      simp only [Matrix.sub_apply]
    have hsingle : ∑ i : Fin 2, ∑ j : Fin 2, (Matrix.single i j (1 : K)) i j = 4 := by
      simp only [Fin.sum_univ_two, Matrix.single]
      norm_num
    have hcongr : (∑ i : Fin 2, ∑ j : Fin 2, (Φ (Matrix.single i j (1 : K))) i j) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          ((Matrix.single i j (1 : K)) i j -
            (G2 * Matrix.single i j (1 : K) * G1) i j -
            (H2 * Matrix.single i j (1 : K) * H1) i j -
            ((G2 * H2) * Matrix.single i j (1 : K) * (G1 * H1)) i j) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
    rw [hcongr]
    simp only [Finset.sum_sub_distrib]
    rw [hsingle, a1413SpEndB_sum_single_mul G2 G1, a1413SpEndB_sum_single_mul H2 H1,
      a1413SpEndB_sum_single_mul (G2 * H2) (G1 * H1)]
    rw [htrG2, htrG1, htrH2, htrH1, htrGH2]
    ring
  have hex : ∃ M : Matrix (Fin 2) (Fin 2) K, Φ M ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    have hzero : (∑ i : Fin 2, ∑ j : Fin 2, (Φ (Matrix.single i j (1 : K))) i j) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [not_not.mp (h (Matrix.single i j (1 : K)))]
      rfl
    rw [hsum] at hzero
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    exact h4 hzero
  obtain ⟨M0, hM0⟩ := hex
  set P : Matrix (Fin 2) (Fin 2) K := Φ M0 with hPdef
  have hP : P ≠ 0 := by simpa [hPdef] using hM0
  have hPG : P * G1 = G2 * P := by
    have := hΦG M0
    rw [hPdef]
    exact this.symm
  have hPH : P * H1 = H2 * P := by
    have := hΦH M0
    rw [hPdef]
    exact this.symm
  have hdet : P.det ≠ 0 :=
    a1413SpEndB_det_ne_zero h2 hG1 hH1 hGH1 hP hPG hPH
  set P' : GL (Fin 2) K := Matrix.nonsingInvUnit P (isUnit_iff_ne_zero.mpr hdet) with hP'def
  have hP'coe : ((P' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = P := rfl
  have hP'G : (P' : Matrix (Fin 2) (Fin 2) K) * G1 = G2 * (P' : Matrix (Fin 2) (Fin 2) K) := by
    rw [hP'coe]; exact hPG
  have hP'H : (P' : Matrix (Fin 2) (Fin 2) K) * H1 = H2 * (P' : Matrix (Fin 2) (Fin 2) K) := by
    rw [hP'coe]; exact hPH
  set δ : K := P.det with hδdef
  have hδ0 : δ ≠ 0 := by simpa [hδdef] using hdet
  have hP'trans : (P' : Matrix (Fin 2) (Fin 2) K)ᵀ * J₁ * (P' : Matrix (Fin 2) (Fin 2) K) =
      δ • J₁ := by
    rw [hP'coe, hδdef]
    exact transpose_mul_J₁_mul P
  have hchar : ringChar K ≠ 2 := by
    intro hc
    have hcard : Fintype.card K % 2 = 0 := FiniteField.even_card_iff_char_two.mp hc
    rw [Nat.card_eq_fintype_card] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr hcard)
  obtain ⟨d, hdnsq⟩ := FiniteField.exists_nonsquare (F := K) hchar
  have hd0 : d ≠ 0 := by
    intro h0
    exact hdnsq ⟨0, by rw [h0]; ring⟩
  have hdsq : ∀ l : K, l ^ 2 ≠ d := fun l hl => hdnsq ⟨l, by simpa [sq] using hl.symm⟩
  have hcardodd : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  have hdeg2 : (Polynomial.C δ * Polynomial.X ^ 2 -
      Polynomial.C d : Polynomial K).degree = 2 := by
    have hlt : (Polynomial.C d : Polynomial K).degree <
        (Polynomial.C δ * Polynomial.X ^ 2 : Polynomial K).degree := by
      rw [Polynomial.degree_C_mul_X_pow 2 hδ0]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_C_mul_X_pow 2 hδ0]
    norm_num
  obtain ⟨a, c, hac⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X : Polynomial K) ^ 2)
    (g := Polynomial.C δ * Polynomial.X ^ 2 - Polynomial.C d)
    (Polynomial.degree_X_pow 2) hdeg2 hcardodd
  have hac' : a ^ 2 + δ * c ^ 2 = d := by
    have h := hac
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C] at h
    linear_combination h
  set Bm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := a1413SpEndB_Bmat a c P with hBm
  have hdet' : a ^ 2 + P.det * c ^ 2 = d := by rw [← hδdef]; exact hac'
  have hBB : Bm * Bm = d • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [hBm, a1413SpEndB_Bmat_sq, hdet']
  have hsim : Bmᵀ * formJ 2 K * Bm = d • formJ 2 K := by
    rw [hBm, a1413SpEndB_Bmat_sim, hdet']
  have hcg : Bm * blk G1 G2 = blk G1 G2 * Bm := by
    rw [hBm]
    exact a1413SpEndB_Bmat_comm a c P G1 G2 hPG (a1413SpEndB_adj_intertwine P G1 G2 hdet hPG)
  have hch : Bm * blk H1 H2 = blk H1 H2 * Bm := by
    rw [hBm]
    exact a1413SpEndB_Bmat_comm a c P H1 H2 hPH (a1413SpEndB_adj_intertwine P H1 H2 hdet hPH)
  have hBinv1 : Bm * (d⁻¹ • Bm) = 1 := by
    rw [Matrix.mul_smul, hBB, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have hBinv2 : (d⁻¹ • Bm) * Bm = 1 := by
    rw [Matrix.smul_mul, hBB, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  let B₀ : GL (Fin 2 ⊕ Fin 2) K := ⟨Bm, d⁻¹ • Bm, hBinv1, hBinv2⟩
  have hB₀coe : (B₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Bm := rfl
  let B : gsp 2 K :=
    ⟨B₀, mem_gsp.mpr ⟨Units.mk0 d hd0, by rw [hB₀coe, Units.val_mk0]; exact hsim⟩⟩
  refine ⟨B, d, hd0, hdsq, ?_, ?_, ?_, ?_⟩
  · change (B₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (B₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1
    rw [hB₀coe]
    exact hBB
  · change (B₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      (B₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K
    rw [hB₀coe]
    exact hsim
  · apply Subtype.ext
    rw [coe_conjSp, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    change Bm * blk G1 G2 = blk G1 G2 * Bm
    exact hcg
  · apply Subtype.ext
    rw [coe_conjSp, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    change Bm * blk H1 H2 = blk H1 H2 * Bm
    exact hch

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
