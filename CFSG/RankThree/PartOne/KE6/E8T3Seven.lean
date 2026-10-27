module

public import CFSG.RankThree.PartOne.KE6.E8T3Data
public import CFSG.RankThree.PartOne.KE6.E8T3Arith
public import Certificates.Certificate14972
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice RootSpace
open CFSG.RankThree.E6 (charVal charVal_single charVal_dualMatrix dualMatrix weylMatrix
  eq_of_charVal_single weylMatrix_injective weylMatrix_pow weylMatrix_one)
open CFSG.RankThree.PartOne.KE (rootKernel dualWeylStabilizer mem_dualWeylStabilizer
  charVal_smul_eq_sum)
open scoped Matrix

theorem e8Seven_count : E8SevenCount :=
  Certificates.certificate14972

theorem e8_image_rootKernel {K : Type*} [CommRing K] {z z' : Fin Tag.E8.rank → K}
    {a : WeylGroup Tag.E8} (h : ∀ x, charVal z' (a • x) = charVal z x) :
    (a • ·) '' rootKernel z = rootKernel z' := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul hα.1 a, by rw [h]; exact hα.2⟩
  · intro hβ
    refine ⟨a⁻¹ • β, ⟨IsRoot.smul hβ.1 a⁻¹, ?_⟩, smul_inv_smul a β⟩
    rw [← h, smul_inv_smul]
    exact hβ.2

theorem e8_mem_dualStab_conj {K : Type*} [CommRing K] {z z' : Fin Tag.E8.rank → K}
    {a : WeylGroup Tag.E8} (h : ∀ x, charVal z' (a • x) = charVal z x) (g : WeylGroup Tag.E8) :
    g ∈ dualWeylStabilizer z ↔ a * g * a⁻¹ ∈ dualWeylStabilizer z' := by
  simp only [mem_dualWeylStabilizer]
  constructor
  · intro hg x
    rw [mul_smul, mul_smul, h, hg, ← h, smul_inv_smul]
  · intro hg x
    have := hg (a • x)
    rw [mul_smul, mul_smul, inv_smul_smul, h, h] at this
    exact this

theorem e8Count7_eq_ncard (z : Fin Tag.E8.rank → ZMod 7) :
    e8Count7 z = (rootKernel z).ncard :=
  (ncard_isRoot_and (τ := Tag.E8) (fun v => charVal z v = 0)).symm

theorem e8Count7_transport {z z' : Fin Tag.E8.rank → ZMod 7} {a : WeylGroup Tag.E8}
    (h : ∀ x, charVal z' (a • x) = charVal z x) : e8Count7 z' = e8Count7 z := by
  rw [e8Count7_eq_ncard, e8Count7_eq_ncard, ← e8_image_rootKernel h]
  exact Set.ncard_image_of_injective _ (MulAction.injective a)

@[expose] def e8Vt7 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7) :=
  ((toMat Tag.E8.rank e8T3MList).map (Int.cast : ℤ → ZMod 7))ᵀ

@[expose] def e8T2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7) :=
  !![5, 0, 2, 3, 0, 0, 0, 0; 5, 5, 6, 4, 0, 0, 0, 0; 1, 6, 6, 5, 0, 0, 0, 0; 6, 5, 3, 2, 0, 0, 0, 0;
    5, 1, 6, 6, 1, 0, 0, 0; 2, 0, 6, 2, 0, 1, 0, 0; 0, 4, 2, 0, 0, 0, 1, 0; 3, 2, 3, 0, 0, 0, 0, 1]

@[expose] def e8R2f : Matrix (Fin 8) (Fin 8) (ZMod 7) :=
  !![1, 0, 0, 0, 2, 5, 2, 2; 0, 1, 0, 0, 5, 2, 3, 1; 0, 0, 1, 0, 1, 6, 4, 3; 0, 0, 0, 1, 0, 2, 6, 4;
    0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def e8R2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7) := e8R2f

@[expose] def e8T4 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7) :=
  !![2, 0, 4, 5, 0, 0, 0, 0; 3, 2, 4, 2, 0, 0, 0, 0; 1, 6, 3, 3, 0, 0, 0, 0; 6, 3, 1, 4, 0, 0, 0, 0;
    3, 1, 4, 4, 1, 0, 0, 0; 4, 0, 6, 4, 0, 1, 0, 0; 0, 2, 4, 0, 0, 0, 1, 0; 5, 4, 5, 0, 0, 0, 0, 1]

@[expose] def e8R4f : Matrix (Fin 8) (Fin 8) (ZMod 7) :=
  !![1, 0, 0, 0, 4, 2, 4, 4; 0, 1, 0, 0, 3, 5, 6, 1; 0, 0, 1, 0, 1, 4, 6, 5; 0, 0, 0, 1, 0, 4, 6, 2;
    0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def e8R4 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7) := e8R4f

theorem e8T2_mul : e8T2 * (e8Vt7 - (2 : ZMod 7) • 1) = e8R2 := by decide +kernel

theorem e8T4_mul : e8T4 * (e8Vt7 - (4 : ZMod 7) • 1) = e8R4 := by decide +kernel

theorem echelon_aux {M T R : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7)} {r : ZMod 7}
    (hTR : T * (M - r • 1) = R) {z : Fin Tag.E8.rank → ZMod 7} (h : M *ᵥ z = r • z) :
    R *ᵥ z = 0 := by
  have h0 : (M - r • 1) *ᵥ z = 0 := by
    rw [Matrix.sub_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  rw [← hTR, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem read_eig2 {z : Fin 8 → ZMod 7} (h0 : e8R2f *ᵥ z = 0) :
    z = e8Eig2 (z 4) (z 5) (z 6) (z 7) := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  simp [e8R2f, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3
  funext j
  fin_cases j
  · simp [e8Eig2]; linear_combination e0
  · simp [e8Eig2]; linear_combination e1
  · simp [e8Eig2]; linear_combination e2
  · simp [e8Eig2]; linear_combination e3
  all_goals simp [e8Eig2]

theorem read_eig4 {z : Fin 8 → ZMod 7} (h0 : e8R4f *ᵥ z = 0) :
    z = e8Eig4 (z 4) (z 5) (z 6) (z 7) := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  simp [e8R4f, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3
  funext j
  fin_cases j
  · simp [e8Eig4]; linear_combination e0
  · simp [e8Eig4]; linear_combination e1
  · simp [e8Eig4]; linear_combination e2
  · simp [e8Eig4]; linear_combination e3
  all_goals simp [e8Eig4]

theorem e8_eig2_param {z : Fin Tag.E8.rank → ZMod 7} (h : e8Vt7 *ᵥ z = (2 : ZMod 7) • z) :
    z = e8Eig2 (z 4) (z 5) (z 6) (z 7) :=
  read_eig2 (echelon_aux e8T2_mul h)

theorem e8_eig4_param {z : Fin Tag.E8.rank → ZMod 7} (h : e8Vt7 *ᵥ z = (4 : ZMod 7) • z) :
    z = e8Eig4 (z 4) (z 5) (z 6) (z 7) :=
  read_eig4 (echelon_aux e8T4_mul h)

theorem e8Eig2_zero : e8Eig2 0 0 0 0 = 0 := by decide

theorem e8Eig4_zero : e8Eig4 0 0 0 0 = 0 := by decide

theorem e8_eigen_count {z : Fin Tag.E8.rank → ZMod 7} (hz : z ≠ 0)
    {r : ZMod 7} (hr : r = 2 ∨ r = 4) (h : e8Vt7 *ᵥ z = r • z) :
    e8Count7 z = 30 ∨ e8Count7 z = 72 := by
  rcases hr with rfl | rfl
  · have hp := e8_eig2_param h
    have hnz : z 4 ≠ 0 ∨ z 5 ≠ 0 ∨ z 6 ≠ 0 ∨ z 7 ≠ 0 := by
      by_contra hcon
      simp only [not_or, ne_eq, not_not] at hcon
      apply hz
      rw [hp, hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2]
      exact e8Eig2_zero
    have := (e8Seven_count (z 4) (z 5) (z 6) (z 7) hnz).1
    rwa [← hp] at this
  · have hp := e8_eig4_param h
    have hnz : z 4 ≠ 0 ∨ z 5 ≠ 0 ∨ z 6 ≠ 0 ∨ z 7 ≠ 0 := by
      by_contra hcon
      simp only [not_or, ne_eq, not_not] at hcon
      apply hz
      rw [hp, hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2]
      exact e8Eig4_zero
    have := (e8Seven_count (z 4) (z 5) (z 6) (z 7) hnz).2
    rwa [← hp] at this

@[expose] def e8G0 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd [0, 2, 3, 4, 5, 6]

@[expose] def e8G0List : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, -1, 1], [0, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, -1, 1],
   [0, 1, 1, 0, 0, 0, -1, 1], [0, 0, 0, 1, 0, 0, -1, 1], [0, 0, 0, 0, 1, 0, -1, 1],
   [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 0, 1]]

theorem weylMatrix_e8G0 : weylMatrix e8G0 = toMat Tag.E8.rank e8G0List :=
  weylMatrix_wordProd_of (by decide +kernel)

theorem e8G0_pow : e8G0 ^ 7 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e8G0, weylMatrix_one, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8G0_ne_one : e8G0 ≠ 1 := by
  intro h
  have h1 := congrArg weylMatrix h
  rw [weylMatrix_e8G0, weylMatrix_one] at h1
  exact (by decide +kernel : toMat Tag.E8.rank e8G0List ≠ 1) h1

theorem orderOf_e8G0 : orderOf e8G0 = 7 :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_eq_prime e8G0_pow e8G0_ne_one

@[expose] def e8Gt7 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7) :=
  ((toMat Tag.E8.rank e8G0List).map (Int.cast : ℤ → ZMod 7))ᵀ

@[expose] def e8T0 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7) :=
  !![4, 5, 2, 0, 0, 0, 0, 0; 5, 5, 2, 0, 0, 0, 0, 0; 5, 5, 3, 0, 0, 0, 0, 0; 5, 5, 3, 1, 0, 0, 0, 0;
    5, 5, 3, 1, 1, 0, 0, 0; 5, 5, 3, 1, 1, 1, 0, 0; 6, 0, 5, 4, 3, 2, 1, 0; 6, 5, 5, 4, 5, 6, 0, 1]

@[expose] def e8R0f : Matrix (Fin 8) (Fin 8) (ZMod 7) :=
  !![1, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def e8R0 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 7) := e8R0f

theorem e8T0_mul : e8T0 * (e8Gt7 - (1 : ZMod 7) • 1) = e8R0 := by decide +kernel

theorem read_fix {y : Fin 8 → ZMod 7} (h0 : e8R0f *ᵥ y = 0) :
    y = ![0, y 1, 0, 0, 0, 0, 0, y 7] := by
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e3 := congrFun h0 3
  have e4 := congrFun h0 4
  have e5 := congrFun h0 5
  simp [e8R0f, Matrix.mulVec, dotProduct, Fin.sum_univ_eight] at e0 e1 e2 e3 e4 e5
  funext j
  fin_cases j
  · simpa using e0
  · simp
  · simpa using e1
  · simpa using e2
  · simpa using e3
  · simpa using e4
  · simpa using e5
  · simp

theorem dualMatrix_e8G0 : dualMatrix (ZMod 7) e8G0 = e8Gt7 := by
  unfold dualMatrix e8Gt7
  rw [weylMatrix_e8G0]

theorem e8G0_dualMatrix_fix {y : Fin Tag.E8.rank → ZMod 7}
    (h : e8G0 ∈ dualWeylStabilizer y) : e8Gt7 *ᵥ y = (1 : ZMod 7) • y := by
  have h1 : (dualMatrix (ZMod 7) e8G0).mulVec y = y := by
    refine eq_of_charVal_single fun j => ?_
    rw [charVal_dualMatrix, mem_dualWeylStabilizer.1 h, charVal_single]
  rw [dualMatrix_e8G0] at h1
  rw [one_smul]
  exact h1

theorem e8G0_fix {y : Fin Tag.E8.rank → ZMod 7} (h : e8G0 ∈ dualWeylStabilizer y) :
    y = ![0, y 1, 0, 0, 0, 0, 0, y 7] :=
  read_fix (echelon_aux e8T0_mul (e8G0_dualMatrix_fix h))

theorem e8_fix_count : ∀ a b : ZMod 7, (a ≠ 0 ∨ b ≠ 0) →
    e8Count7 ![0, a, 0, 0, 0, 0, 0, b] ≠ 30 ∧ e8Count7 ![0, a, 0, 0, 0, 0, 0, b] ≠ 72 := by
  decide +kernel

theorem factorization_seven : (696729600 : ℕ).factorization 7 = 1 := by
  have h : (696729600 : ℕ) = 7 * 99532800 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_fix {z : Fin Tag.E8.rank → ZMod 7}
    (h7 : 7 ∣ Nat.card (dualWeylStabilizer z)) :
    ∃ (a : WeylGroup Tag.E8) (z' : Fin Tag.E8.rank → ZMod 7),
      (∀ x, charVal z' (a • x) = charVal z x) ∧ e8G0 ∈ dualWeylStabilizer z' := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype (WeylGroup Tag.E8) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hW : Nat.card (WeylGroup Tag.E8) = 696729600 :=
    (CFSG.RankThree.Chevalley.E8_weyl_length_polynomial).2
  have hfac : (Nat.card (WeylGroup Tag.E8)).factorization 7 = 1 := by
    rw [hW]
    exact factorization_seven
  let P : Sylow 7 (WeylGroup Tag.E8) := Sylow.ofCard (Subgroup.zpowers (g : WeylGroup Tag.E8))
    (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg, hfac, pow_one])
  let P₀ : Sylow 7 (WeylGroup Tag.E8) := Sylow.ofCard (Subgroup.zpowers e8G0)
    (by rw [Nat.card_zpowers, orderOf_e8G0, hfac, pow_one])
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E8) P₀ P
  have hmem : x * e8G0 * x⁻¹ ∈ dualWeylStabilizer z := by
    have h1 : e8G0 ∈ (P₀ : Subgroup (WeylGroup Tag.E8)) := Subgroup.mem_zpowers e8G0
    have h2 : (MulAut.conj x) e8G0 ∈ ((x • P₀ : Sylow 7 (WeylGroup Tag.E8)) :
        Subgroup (WeylGroup Tag.E8)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [hx] at h2
    have h3 : (MulAut.conj x) e8G0 ∈ Subgroup.zpowers (g : WeylGroup Tag.E8) := h2
    rw [MulAut.conj_apply] at h3
    exact (Subgroup.zpowers_le.2 g.2) h3
  set z' : Fin Tag.E8.rank → ZMod 7 := fun i =>
    charVal z (x • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) with hz'
  have hz'x : ∀ y, charVal z' y = charVal z (x • y) := fun y => by
    rw [charVal_smul_eq_sum]
    rfl
  have hconj : ∀ y, charVal z' (x⁻¹ • y) = charVal z y := fun y => by
    rw [hz'x, smul_inv_smul]
  refine ⟨x⁻¹, z', hconj, ?_⟩
  have := (e8_mem_dualStab_conj hconj (x * e8G0 * x⁻¹)).1 hmem
  simpa [mul_assoc] using this

theorem charVal_zero_col (x : Fin Tag.E8.rank → ℤ) :
    charVal (0 : Fin Tag.E8.rank → ZMod 7) x = 0 := by
  simp [charVal]

theorem e8Fix_zero : (![0, 0, 0, 0, 0, 0, 0, 0] : Fin Tag.E8.rank → ZMod 7) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem e8T3_seven_stab
    {z : Fin Tag.E8.rank → ZMod 7} (hz : z ≠ 0) {r : ZMod 7} (hr : r = 2 ∨ r = 4)
    (h : e8Vt7 *ᵥ z = r • z) : ¬ 7 ∣ Nat.card (dualWeylStabilizer z) := by
  intro h7
  obtain ⟨a, z', hz', hfix⟩ := exists_conj_fix h7
  have hcount : e8Count7 z' = e8Count7 z := e8Count7_transport hz'
  have hz'0 : z' ≠ 0 := by
    intro h0
    apply hz
    funext i
    rw [← charVal_single z i, ← hz', h0]
    exact charVal_zero_col _
  have hform := e8G0_fix hfix
  have hne : z' 1 ≠ 0 ∨ z' 7 ≠ 0 := by
    by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    apply hz'0
    rw [hform, hcon.1, hcon.2]
    exact e8Fix_zero
  have h1 := e8_fix_count (z' 1) (z' 7) hne
  rw [← hform] at h1
  have h2 := e8_eigen_count hz hr h
  rw [← hcount] at h2
  rcases h2 with h2 | h2
  · exact h1.1 h2
  · exact h1.2 h2

theorem e8Vt7_of_eigencolumn {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    {z : Fin Tag.E8.rank → ZMod 7}
    (h : ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod 7))ᵀ *ᵥ z = (q : ZMod 7) • z) :
    e8Vt7 *ᵥ z = ((ε : ZMod 7) * (q : ZMod 7)) • z := by
  rcases hε with rfl | rfl
  · have hM : ((weylMatrix (e8T3We 1)).map (Int.cast : ℤ → ZMod 7))ᵀ = e8Vt7 := by
      rw [weylMatrix_e8T3We (Or.inl rfl), one_smul]
      rfl
    rw [hM] at h
    rw [Int.cast_one, one_mul]
    exact h
  · have hM : ((weylMatrix (e8T3We (-1))).map (Int.cast : ℤ → ZMod 7))ᵀ = -e8Vt7 := by
      rw [weylMatrix_e8T3We (Or.inr rfl), neg_one_smul]
      ext i j
      simp [e8Vt7]
    rw [hM, Matrix.neg_mulVec] at h
    have h' : e8Vt7 *ᵥ z = -((q : ZMod 7) • z) := by
      rw [← h, neg_neg]
    rw [h', Int.cast_neg, Int.cast_one, neg_one_mul, neg_smul]

theorem e8T3_dualStab_prime {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 + ε * q + 1) {z : Fin Tag.E8.rank → ZMod p} (hz : z ≠ 0)
    (hzM : ((weylMatrix (e8T3We ε)).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = (q : ZMod p) • z) :
    ¬ p ∣ Nat.card (dualWeylStabilizer z) := by
  obtain ⟨-, hx, -, hp7, -⟩ := e8T3_data hε hp hp3 hpq
  rcases hp7.lt_or_eq with h7 | h7
  · intro hdvd
    have : Fintype (WeylGroup Tag.E8) := Fintype.ofFinite _
    exact CFSG.RankThree.PartOne.KE.not_dvd_card_weylGroup_E hp h7 (Or.inr (Or.inr rfl))
      (hdvd.trans (Subgroup.card_subgroup_dvd_card _))
  · subst h7
    have hr : ∀ r : ZMod 7, r ^ 2 + r + 1 = 0 → r = 2 ∨ r = 4 := by decide
    have hx' : ((ε : ZMod 7) * (q : ZMod 7)) ^ 2 + (ε : ZMod 7) * (q : ZMod 7) + 1 = 0 := hx
    exact e8T3_seven_stab hz (hr _ hx') (e8Vt7_of_eigencolumn hε hzM)

end CFSG.RankThree.PartOne.KE6
