module

public import Certificates.Certificate14976

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

section Pairing

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
@[expose] def e7T3A (z : Fin Tag.E7.rank → ZMod p) : ZMod p × ZMod p × ZMod p :=
  (pair (toVec Tag.E7.rank e7T3B1List) z, pair (toVec Tag.E7.rank e7T3B2List) z,
    pair (toVec Tag.E7.rank e7T3B3List) z)

omit [Fact p.Prime] in
theorem pair_mulVec_eq {n : ℕ} {K : Type*} [CommRing K] (M : Matrix (Fin n) (Fin n) ℤ)
    (c : Fin n → ℤ) (z : Fin n → K) :
    pair (M *ᵥ c) z = ∑ k, (c k : K) * pair (fun i => M i k) z := by
  simp only [pair, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem e7T3_pair_cols {ρ : ZMod p} {z : Fin Tag.E7.rank → ZMod p} (hρ1 : IsUnit (1 - ρ))
    (hz : ((toMat Tag.E7.rank e7T3WList).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ρ • z)
    (hfix : lmulVec Tag.E7.rank e7T3WList e7T3FList = e7T3FList) (k : Fin Tag.E7.rank) :
    pair (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) i k) z =
      ![0, (e7T3A z).1, ρ * (e7T3A z).1, (e7T3A z).2.1, ρ * (e7T3A z).2.1, (e7T3A z).2.2,
        ρ * (e7T3A z).2.2] k := by
  have hWf : (toMat Tag.E7.rank e7T3WList) *ᵥ toVec Tag.E7.rank e7T3FList =
      toVec Tag.E7.rank e7T3FList := by
    rw [← toVec_lmulVec, hfix]
  have hk : (fun i => toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) i k) =
      toVec Tag.E7.rank (e7T3ColsList.getD k []) := by
    funext i
    rw [toMat_lcols]
    rfl
  rw [hk]
  have hW : ∀ b : List ℤ, pair (toVec Tag.E7.rank (lmulVec Tag.E7.rank e7T3WList b)) z =
      ρ * pair (toVec Tag.E7.rank b) z := fun b => by
    rw [toVec_lmulVec, pair_mulVec hz]
  have hF : pair (toVec Tag.E7.rank e7T3FList) z = 0 := by
    have h := pair_mulVec hz (toVec Tag.E7.rank e7T3FList)
    rw [hWf] at h
    have h2 : (1 - ρ) * pair (toVec Tag.E7.rank e7T3FList) z = 0 := by
      rw [sub_mul, one_mul, ← h, sub_self]
    exact (hρ1.mul_right_eq_zero).1 h2
  fin_cases k
  · exact hF
  · rfl
  · exact hW e7T3B1List
  · rfl
  · exact hW e7T3B2List
  · rfl
  · exact hW e7T3B3List

theorem e7T3_pair_row {ρ : ZMod p} (hρ1 : IsUnit (1 - ρ))
    {z : Fin Tag.E7.rank → ZMod p}
    (hz : ((toMat Tag.E7.rank e7T3WList).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ρ • z)
    (l : List ℤ) :
    pair (toVec Tag.E7.rank l) z = rowDot ρ (e7T3Row l) (e7T3A z) := by
  have hinv : lmul Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) e7T3BinvList = lid Tag.E7.rank :=
    (Certificates.certificate14976).2.1
  have hfix : lmulVec Tag.E7.rank e7T3WList e7T3FList = e7T3FList :=
    (Certificates.certificate14976).2.2.1
  set co := lmulVec Tag.E7.rank e7T3BinvList l with hco
  have h1 : toVec Tag.E7.rank l =
      toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList) *ᵥ toVec Tag.E7.rank co := by
    rw [hco, toVec_lmulVec, Matrix.mulVec_mulVec, ← toMat_lmul, hinv, toMat_lid,
      Matrix.one_mulVec]
  rw [h1, pair_mulVec_eq, Finset.sum_congr rfl fun k _ =>
    congrArg (HMul.hMul _) (e7T3_pair_cols hρ1 hz hfix k)]
  erw [Fin.sum_univ_seven]
  simp only [e7T3Row, rowDot, ev, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, vget, toVec]
  rw [← hco]
  simp
  ring

theorem e7T3_a_ne_zero {ρ : ZMod p} (hρ1 : IsUnit (1 - ρ))
    {z : Fin Tag.E7.rank → ZMod p}
    (hz : ((toMat Tag.E7.rank e7T3WList).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ρ • z)
    (hz0 : z ≠ 0) : e7T3A z ≠ (0, 0, 0) := by
  intro h
  have hfix : lmulVec Tag.E7.rank e7T3WList e7T3FList = e7T3FList :=
    (Certificates.certificate14976).2.2.1
  have hdet : (toMat Tag.E7.rank (lcols Tag.E7.rank e7T3ColsList)).det = 1 := by
    rw [det_toMat_eq]
    exact (Certificates.certificate14976).1
  have h1 : (e7T3A z).1 = 0 := congrArg Prod.fst h
  have h2 : (e7T3A z).2.1 = 0 := congrArg (fun t => t.2.1) h
  have h3 : (e7T3A z).2.2 = 0 := congrArg (fun t => t.2.2) h
  refine hz0 (eq_zero_of_pair_cols_eq_zero (hdet ▸ isUnit_one) fun j => ?_)
  rw [e7T3_pair_cols hρ1 hz hfix j]
  fin_cases j <;> simp [h1, h2, h3] <;> rfl

theorem e7T3_pair_zero_iff (hp3 : 3 < p) {ρ : ZMod p}
    (hρ : ρ ^ 2 + ρ + 1 = 0) (hρ1 : IsUnit (1 - ρ)) {z : Fin Tag.E7.rank → ZMod p}
    (hz : ((toMat Tag.E7.rank e7T3WList).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ρ • z)
    {l : List ℤ} (hl : l ∈ Tag.E7.artifactRoots) :
    pair (toVec Tag.E7.rank l) z = 0 ↔
      ∃ i : Fin 21, RowIs l i ∧ rowDot ρ (e7T3G i) (e7T3A z) = 0 := by
  rw [e7T3_pair_row hρ1 hz l]
  constructor
  · intro h
    obtain ⟨i, u, hu, hrow⟩ := (Certificates.certificate14976).2.2.2.2.1 l hl
    refine ⟨i, ⟨u, hu, hrow⟩, ?_⟩
    rw [hrow, rowDot_escale hρ] at h
    exact (mul_eq_zero.1 h).resolve_left (ev_ne_zero_of_mem_eUnits hp3 hρ hu)
  · rintro ⟨i, ⟨u, hu, hrow⟩, h⟩
    rw [hrow, rowDot_escale hρ, h, mul_zero]

theorem e7T3_kernel_of_cls
    (hp3 : 3 < p) {ρ : ZMod p} (hρ : ρ ^ 2 + ρ + 1 = 0) (hρ1 : IsUnit (1 - ρ))
    {z : Fin Tag.E7.rank → ZMod p}
    (hz : ((toMat Tag.E7.rank e7T3WList).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ρ • z)
    {c : E7T3Cert} (hc : c ∈ e7T3Certs)
    (hmem : ∀ l : Fin 21, rowDot ρ (e7T3G l) (e7T3A z) = 0 ↔ l.val ∈ c.cls) :
    {r | IsRoot Tag.E7 r ∧ pair r z = 0} =
      {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} := by
  obtain ⟨-, hcls, hsub, hiff⟩ := (Certificates.certificate14976).2.2.2.2.2.1 c hc
  ext α
  constructor
  · rintro ⟨hα, hp⟩
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
    obtain ⟨i, hrow, hi0⟩ := (e7T3_pair_zero_iff hp3 hρ hρ1 hz hl).1 hp
    exact ⟨l, (hiff l hl).1 ⟨i.val, (hmem i).1 hi0, hrow⟩, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    have hlr : l ∈ Tag.E7.artifactRoots := hsub l hl
    refine ⟨isRoot_toVec hlr, ?_⟩
    obtain ⟨i, hi, hrow⟩ := (hiff l hlr).2 hl
    refine (e7T3_pair_zero_iff hp3 hρ hρ1 hz hlr).2 ⟨⟨i, hcls i hi⟩, hrow, ?_⟩
    exact (hmem ⟨i, hcls i hi⟩).2 hi

theorem e7T3_root_kernel
    (hp3 : 3 < p) {ρ : ZMod p} (hρ : ρ ^ 2 + ρ + 1 = 0) {z : Fin Tag.E7.rank → ZMod p}
    (hz0 : z ≠ 0)
    (hz : ((toMat Tag.E7.rank e7T3WList).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ρ • z) :
    {r | IsRoot Tag.E7 r ∧ pair r z = 0} = ∅ ∨ ∃ c ∈ e7T3Certs,
      {r | IsRoot Tag.E7 r ∧ pair r z = 0} =
        {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} := by
  obtain ⟨-, -, -, hrows, -, -, hsingles, hflats, -, -, -, -⟩ := Certificates.certificate14976
  have hρ1 : IsUnit (1 - ρ) := by
    rw [isUnit_iff_ne_zero]
    intro h
    have hρ' : ρ = 1 := by linear_combination -h
    rw [hρ'] at hρ
    have h3 : ((3 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination hρ
    exact intCast_zmod_ne_zero (by norm_num) (by omega) h3
  have ha := e7T3_a_ne_zero hρ1 hz hz0
  rcases rank3_kernel hp3 hρ hrows (e7T3A z) ha with h | ⟨k, hk⟩ | ⟨i, j, hij, hij'⟩
  · left
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hα hp
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
    obtain ⟨i, -, hi⟩ := (e7T3_pair_zero_iff hp3 hρ hρ1 hz hl).1 hp
    exact h i hi
  · right
    obtain ⟨c, hc, hcls⟩ := hsingles k
    refine ⟨c, hc, e7T3_kernel_of_cls hp3 hρ hρ1 hz hc fun l => ?_⟩
    rw [hk l, hcls]
    simp [Fin.ext_iff]
  · right
    obtain ⟨c, hc, hcl⟩ := hflats i j hij
    refine ⟨c, hc, e7T3_kernel_of_cls hp3 hρ hρ1 hz hc fun l => ?_⟩
    rw [hij' l, hcl l]


end Pairing

section Structure

theorem neg_one_smul_map_transpose_mulVec {n : ℕ} {K : Type*} [CommRing K]
    (M : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → K) :
    (((-1 : ℤ) • M).map (Int.cast : ℤ → K))ᵀ *ᵥ z = -((M.map (Int.cast : ℤ → K))ᵀ *ᵥ z) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]

theorem e7T3_kernel_structure
    {L : Type} [Field L] (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hΦ : (q : ZMod p) ^ 2 + (ε : ZMod p) * q + 1 = 0)
    {a : Fin Tag.E7.rank → Lˣ} (ha : a ∈ fixedCharTuples (ε • e7T3W) Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ c ∈ e7T3Certs,
      rootCharKernel a = {α | ∃ l ∈ c.rootList, α = toVec Tag.E7.rank l} ∧ c.Good := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz0, hzM, hzk⟩ := exists_eigencolumn_of_mem_fixedCharTuples (ε • e7T3W) Fr hFr hp ha
    hap ha1
  have hz' : ((toMat Tag.E7.rank e7T3WList).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z =
      ((ε : ZMod p) * q) • z := by
    rw [← e7T3W_eq]
    rcases hε with rfl | rfl
    · simpa using hzM
    · have h1 := neg_one_smul_map_transpose_mulVec e7T3W z
      rw [h1] at hzM
      have h2 : (e7T3W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = -((q : ZMod p) • z) :=
        neg_eq_iff_eq_neg.1 hzM
      rw [h2, Int.cast_neg, Int.cast_one, neg_one_mul]
      funext j
      simp
      rfl
  have hρ : ((ε : ZMod p) * q) ^ 2 + (ε : ZMod p) * q + 1 = 0 := by
    rcases hε with rfl | rfl <;> simp at hΦ ⊢ <;> linear_combination hΦ
  rw [hzk]
  rcases e7T3_root_kernel hp3 hρ hz0 hz' with h | ⟨c, hc, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hc, h, (Certificates.certificate14976).2.2.2.2.2.1 c hc⟩


section Extract

theorem e7T3_cert_kinds {c : E7T3Cert} (hc : c ∈ e7T3Certs) :
    c.comps.map E7T3Comp.kind ∈ ([[0], [1], [2], [3], [0, 1]] : List (List ℕ)) :=
  (Certificates.certificate14976).2.2.2.2.2.2.2.2.2.1 c hc

theorem e7T3_cert_e0 {c : E7T3Cert} (hc : c ∈ e7T3Certs)
    (hk : c.comps.map E7T3Comp.kind = [1]) : [1, 0, 0, 0, 0, 0, 0] ∉ c.rootList :=
  (Certificates.certificate14976).2.2.2.2.2.2.2.2.2.2.1 c hc hk

theorem e7T3_cert_size {c : E7T3Cert} (hc : c ∈ e7T3Certs) :
    c.rootList.length ≤ 30 :=
  (Certificates.certificate14976).2.2.2.2.2.2.2.2.2.2.2 c hc

theorem e7T3_cert_negD4 {c : E7T3Cert} (hc : c ∈ e7T3Certs)
    {cm : E7T3Comp} (hcm : cm ∈ c.comps) (hk : cm.kind = 2) :
    ∀ l ∈ e7StdRoots (e7T3Nodes 2),
      lmulVec 7 (e7wl (e7T3NegD4 ++ cm.u)) (e7T3Perm 2 cm.rot l) =
        vneg 7 (lmulVec 7 (e7wl cm.u) (e7T3Perm 2 cm.rot l)) :=
  (Certificates.certificate14976).2.2.2.2.2.2.2.2.1 c hc cm hcm hk

end Extract

end Structure

end CFSG.RankThree.PartOne.KE
