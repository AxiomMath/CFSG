module

public import CFSG.RankThree.PartOne.KE8F.E8Gauss
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem zpow_finsetSum' {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι) (f : ι → ℤ) (a : G) :
    a ^ (∑ k ∈ s, f k) = ∏ k ∈ s, a ^ f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, _root_.zpow_add, ih]

section Basis

variable {L : Type} [Field L]

@[expose] def e8P4col (k : Fin Tag.E8.rank) : Fin Tag.E8.rank → ℤ := fun i => e8P4B i k

@[expose] def bs (b : Fin Tag.E8.rank → Lˣ) (k : Fin Tag.E8.rank) : Lˣ := rootChar b (e8P4col k)

theorem rootChar_eq_prod_col (b : Fin Tag.E8.rank → Lˣ) (x : Fin Tag.E8.rank → ℤ) :
    rootChar b x = ∏ k, (bs b k) ^ ((e8P4Binv *ᵥ x) k) := by
  have hx : ∀ i, x i = ∑ k, e8P4B i k * (e8P4Binv *ᵥ x) k := by
    intro i
    have h := congrFun (congrArg (fun M => M *ᵥ x) e8P4B_mul_Binv) i
    simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h
    rw [← h]
    simp [Matrix.mulVec, dotProduct]
  have h2 : ∀ i, b i ^ x i = ∏ k, (b i ^ e8P4B i k) ^ ((e8P4Binv *ᵥ x) k) := by
    intro i
    conv_lhs => rw [hx i]
    rw [zpow_finsetSum']
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [_root_.zpow_mul]
  simp only [rootChar, h2, bs, e8P4col]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_zpow]

@[expose] def ofBasis (β : Fin Tag.E8.rank → Lˣ) : Fin Tag.E8.rank → Lˣ :=
  fun i => ∏ k, β k ^ e8P4Binv k i

theorem bs_ofBasis (β : Fin Tag.E8.rank → Lˣ) (k : Fin Tag.E8.rank) : bs (ofBasis β) k = β k := by
  have h1 : ∀ m, (∏ i, (β m ^ e8P4Binv m i) ^ e8P4B i k) = β m ^ (if m = k then (1 : ℤ) else 0) := by
    intro m
    have h : ∑ i, e8P4Binv m i * e8P4B i k = if m = k then 1 else 0 := by
      have := congrFun (congrFun e8P4Binv_mul_B m) k
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    rw [← h, zpow_finsetSum']
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [_root_.zpow_mul]
  have h2 : bs (ofBasis β) k = ∏ i, ∏ m, (β m ^ e8P4Binv m i) ^ e8P4B i k := by
    simp only [bs, rootChar, ofBasis, e8P4col]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_zpow]
  rw [h2, Finset.prod_comm]
  rw [Finset.prod_congr rfl fun m _ => h1 m]
  rw [Finset.prod_eq_single k]
  · simp
  · intro m _ hm
    simp [hm]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem ofBasis_bs (b : Fin Tag.E8.rank → Lˣ) : ofBasis (bs b) = b := by
  funext i
  have h := rootChar_eq_prod_col b (Pi.single i 1)
  rw [CTTorus.rootChar_single] at h
  rw [h]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp


end Basis

section Fixed

variable {L : Type} [Field L]

@[expose] def ev (j : Fin 4) : Fin Tag.E8.rank :=
  ⟨2 * j.val, by have : Tag.E8.rank = 8 := rfl; omega⟩

@[expose] def od (j : Fin 4) : Fin Tag.E8.rank :=
  ⟨2 * j.val + 1, by have : Tag.E8.rank = 8 := rfl; omega⟩

theorem e8P4J_ev_col (j : Fin 4) (m : Fin Tag.E8.rank) :
    e8P4J m (ev j) = if m = od j then 1 else 0 := by
  fin_cases j <;> fin_cases m <;> decide

theorem e8P4J_od_col (j : Fin 4) (m : Fin Tag.E8.rank) :
    e8P4J m (od j) = if m = ev j then -1 else 0 := by
  fin_cases j <;> fin_cases m <;> decide

theorem V_col_ev (j : Fin 4) : e8P4V *ᵥ e8P4col (ev j) = e8P4col (od j) := by
  funext i
  have h := congrFun (congrFun e8P4V_mul_B i) (ev j)
  simp only [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct, e8P4col]
  rw [h]
  simp [e8P4J_ev_col]

theorem V_col_od (j : Fin 4) : e8P4V *ᵥ e8P4col (od j) = - e8P4col (ev j) := by
  funext i
  have h := congrFun (congrFun e8P4V_mul_B i) (od j)
  simp only [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct, e8P4col, Pi.neg_apply]
  rw [h]
  simp [e8P4J_od_col]


theorem rootChar_neg' (b : Fin Tag.E8.rank → Lˣ) (u : Fin Tag.E8.rank → ℤ) :
    rootChar b (-u) = (rootChar b u)⁻¹ := by
  have h := rootChar_add b u (-u)
  rw [add_neg_cancel, rootChar_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem zpow_pow_comm' (x : Lˣ) (c : ℤ) (q : ℕ) : (x ^ c) ^ q = (x ^ q) ^ c := by
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]

theorem pair_aux {x y : Lˣ} {q : ℕ} (h1 : y = x ^ q) (h2 : x ^ (q * q + 1) = 1) (c d : ℤ) :
    x ^ (-d) * y ^ c = (x ^ c) ^ q * (y ^ d) ^ q := by
  have hx : x ^ (q * q) = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h2)
  have hy : y ^ q = x⁻¹ := by rw [h1, ← pow_mul, hx]
  rw [zpow_pow_comm', zpow_pow_comm', hy, ← h1, _root_.inv_zpow']
  exact mul_comm _ _

theorem mem_fixedCharTuples_e8P4_iff {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (b : Fin Tag.E8.rank → Lˣ) :
    b ∈ fixedCharTuples e8P4V Fr ↔
      ∀ j : Fin 4, bs b (od j) = bs b (ev j) ^ q ∧ bs b (ev j) ^ (q * q + 1) = 1 := by
  rw [mem_fixedCharTuples_iff]
  constructor
  · intro h j
    have h1 := h (e8P4col (ev j))
    rw [V_col_ev, CTTorus.map_units_eq_pow hFr] at h1
    have h2 := h (e8P4col (od j))
    rw [V_col_od, CTTorus.map_units_eq_pow hFr, rootChar_neg'] at h2
    refine ⟨h1, ?_⟩
    have h3 : (bs b (ev j))⁻¹ = (bs b (ev j)) ^ (q * q) := by
      have : (bs b (od j)) ^ q = (bs b (ev j)) ^ (q * q) := by
        have h1' : bs b (od j) = bs b (ev j) ^ q := h1
        rw [h1', ← pow_mul]
      rw [← this]
      exact h2
    exact (by rw [pow_succ, ← h3]; exact inv_mul_cancel _)
  · intro hj u
    have hc : e8P4Binv *ᵥ (e8P4V *ᵥ u) = e8P4J *ᵥ (e8P4Binv *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, e8P4Binv_mul_V, ← Matrix.mulVec_mulVec]
    rw [rootChar_eq_prod_col b (e8P4V *ᵥ u), hc, rootChar_eq_prod_col b u, map_prod]
    set c := e8P4Binv *ᵥ u with hcdef
    simp only [CTTorus.map_units_eq_pow hFr]
    have hprod : ∀ f : Fin Tag.E8.rank → Lˣ,
        ∏ k, f k = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := fun f => Fin.prod_univ_eight f
    rw [hprod, hprod]
    have e0 : (e8P4J *ᵥ c) 0 = -c 1 := e8P4J_even' c 0
    have e1 : (e8P4J *ᵥ c) 1 = c 0 := e8P4J_odd' c 0
    have e2 : (e8P4J *ᵥ c) 2 = -c 3 := e8P4J_even' c 1
    have e3 : (e8P4J *ᵥ c) 3 = c 2 := e8P4J_odd' c 1
    have e4 : (e8P4J *ᵥ c) 4 = -c 5 := e8P4J_even' c 2
    have e5 : (e8P4J *ᵥ c) 5 = c 4 := e8P4J_odd' c 2
    have e6 : (e8P4J *ᵥ c) 6 = -c 7 := e8P4J_even' c 3
    have e7 : (e8P4J *ᵥ c) 7 = c 6 := e8P4J_odd' c 3
    rw [e0, e1, e2, e3, e4, e5, e6, e7]
    have p0 : bs b 0 ^ (-c 1) * bs b 1 ^ c 0 = (bs b 0 ^ c 0) ^ q * (bs b 1 ^ c 1) ^ q :=
      pair_aux (hj 0).1 (hj 0).2 (c 0) (c 1)
    have p1 : bs b 2 ^ (-c 3) * bs b 3 ^ c 2 = (bs b 2 ^ c 2) ^ q * (bs b 3 ^ c 3) ^ q :=
      pair_aux (hj 1).1 (hj 1).2 (c 2) (c 3)
    have p2 : bs b 4 ^ (-c 5) * bs b 5 ^ c 4 = (bs b 4 ^ c 4) ^ q * (bs b 5 ^ c 5) ^ q :=
      pair_aux (hj 2).1 (hj 2).2 (c 4) (c 5)
    have p3 : bs b 6 ^ (-c 7) * bs b 7 ^ c 6 = (bs b 6 ^ c 6) ^ q * (bs b 7 ^ c 7) ^ q :=
      pair_aux (hj 3).1 (hj 3).2 (c 6) (c 7)
    calc _ = (bs b 0 ^ (-c 1) * bs b 1 ^ c 0) * (bs b 2 ^ (-c 3) * bs b 3 ^ c 2) *
          (bs b 4 ^ (-c 5) * bs b 5 ^ c 4) * (bs b 6 ^ (-c 7) * bs b 7 ^ c 6) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [p0, p1, p2, p3]
          simp only [mul_assoc]


@[expose] def cg (b : Fin Tag.E8.rank → Lˣ) (j : Fin 4) : Lˣ := bs b (ev j)

theorem gA_eq (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : gA x j = (e8P4Binv *ᵥ x) (ev j) := rfl

theorem gB_eq (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : gB x j = (e8P4Binv *ᵥ x) (od j) := rfl

theorem rootChar_T0 {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {b : Fin Tag.E8.rank → Lˣ}
    (hb : b ∈ fixedCharTuples e8P4V Fr) (α : Fin Tag.E8.rank → ℤ) :
    rootChar b α = ∏ j : Fin 4, (cg b j) ^ (gA α j + (q : ℤ) * gB α j) := by
  have hj := (mem_fixedCharTuples_e8P4_iff hFr b).1 hb
  have hprod : ∀ f : Fin Tag.E8.rank → Lˣ,
      ∏ k, f k = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := fun f => Fin.prod_univ_eight f
  rw [rootChar_eq_prod_col b α, hprod, Fin.prod_univ_four]
  have key : ∀ j : Fin 4, (cg b j) ^ (gA α j + (q : ℤ) * gB α j) =
      bs b (ev j) ^ (e8P4Binv *ᵥ α) (ev j) * bs b (od j) ^ (e8P4Binv *ᵥ α) (od j) := by
    intro j
    have h1 : bs b (od j) = bs b (ev j) ^ q := (hj j).1
    rw [h1, ← zpow_natCast (bs b (ev j)) q, ← _root_.zpow_mul, ← _root_.zpow_add]
    rfl
  rw [key, key, key, key]
  have ev0 : ev 0 = 0 := rfl
  have ev1 : ev 1 = 2 := rfl
  have ev2 : ev 2 = 4 := rfl
  have ev3 : ev 3 = 6 := rfl
  have od0 : od 0 = 1 := rfl
  have od1 : od 1 = 3 := rfl
  have od2 : od 2 = 5 := rfl
  have od3 : od 3 = 7 := rfl
  rw [ev0, ev1, ev2, ev3, od0, od1, od2, od3]
  simp only [mul_assoc]

end Fixed

end CFSG.RankThree.PartOne.KE8F
