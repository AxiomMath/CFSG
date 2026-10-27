module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagCut
public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {n : ℕ} {d : List ℕ}

private theorem q2cFPo_getD_le (hd : IsCut n d) {i j : ℕ} (hij : i ≤ j) (hj : j < d.length) :
    d.getD i 0 ≤ d.getD j 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  clear hij
  induction k with
  | zero => simp
  | succ k ih =>
    exact le_trans (ih (by omega)) (le_of_lt (hd.strict (i + k) (by omega)))

theorem q2cFPo_le_last (hd : IsCut n d) {b : ℕ} (hb : b < d.length) : d.getD b 0 ≤ n := by
  have h := q2cFPo_getD_le hd (i := b) (j := d.length - 1) (by omega) (by omega)
  rwa [hd.last] at h

theorem q2cFPo_blockSize_le (hd : IsCut n d) {b : ℕ} (hb : b + 1 < d.length) :
    blockSize d b ≤ n := by
  have h := q2cFPo_le_last hd hb
  unfold blockSize
  omega

@[expose] def q2cFPo_Wb {n : ℕ} (d : List ℕ) (b : ℕ) : Submodule K (Fin n → K) where
  carrier := {v | ∀ j : Fin n, ¬ (d.getD b 0 ≤ j.val ∧ j.val < d.getD (b + 1) 0) → v j = 0}
  add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun a _ hv j hj => by simp [hv j hj]

theorem q2cFPo_Wb_inf_Vsub {b : ℕ} :
    q2cFPo_Wb (K := K) (n := n) d b ⊓ Vsub n (d.getD b 0) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro v ⟨hvW, hvV⟩
  funext j
  by_cases hj : d.getD b 0 ≤ j.val
  · exact hvV j hj
  · exact hvW j (fun h => hj h.1)

theorem q2cFPo_Wb_le_Vsub {b : ℕ} :
    q2cFPo_Wb (K := K) (n := n) d b ≤ Vsub n (d.getD (b + 1) 0) := by
  intro v hv j hj
  exact hv j (fun h => absurd h.2 (not_lt.mpr hj))

private lemma q2cFPo_exists_avoid (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (T : Finset K) (hT : T.card ≤ 3) : ∃ c : K, c ∉ T := by
  classical
  haveI := Fintype.ofFinite K
  have h16 : 16 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK, pow_two]
    exact Nat.mul_le_mul hq hq
  have hcard : T.card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨c, hc⟩

private lemma q2cFPo_exists_avoid3 (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (a b c : K) : ∃ x : K, x ≠ a ∧ x ≠ b ∧ x ≠ c := by
  classical
  let T : Finset K := {a, b, c}
  have hT : T.card ≤ 3 := Finset.card_le_three
  obtain ⟨x, hx⟩ := q2cFPo_exists_avoid (K := K) (f := f) hK hq T hT
  refine ⟨x, ?_, ?_, ?_⟩ <;> intro h <;> exact hx (by simp [T, h])

private lemma q2cFPo_sg_eq_iff (hK : Nat.card K = (2 ^ f) ^ 2) (x y : K) :
    sg K f x = y ↔ x = sg K f y := by
  constructor
  · intro h
    rw [← sg_sg hK x, h]
  · intro h
    rw [h, sg_sg hK y]

private lemma q2cFPo_sg_ne_iff (hK : Nat.card K = (2 ^ f) ^ 2) (x y : K) :
    sg K f x ≠ y ↔ x ≠ sg K f y :=
  not_congr (q2cFPo_sg_eq_iff hK x y)

theorem q2cFPo_exists_nodes (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ∃ ω : Fin 4 → K, Function.Injective ω ∧
      ∀ i j : Fin 4, i.val + j.val ≤ 2 → sg K f (ω i) ≠ ω j := by
  classical
  obtain ⟨c0, hc0m, -, -⟩ := exists_sg_moved_avoid (K := K) (f := f) hK hq 0 0
  obtain ⟨c1, hc1m, hc10, hc1s0⟩ :=
    exists_sg_moved_avoid (K := K) (f := f) hK hq c0 (sg K f c0)
  obtain ⟨c2, hc2a, hc2b, hc2c⟩ :=
    q2cFPo_exists_avoid3 (K := K) (f := f) hK hq c0 c1 (sg K f c0)
  obtain ⟨c3, hc3a, hc3b, hc3c⟩ :=
    q2cFPo_exists_avoid3 (K := K) (f := f) hK hq c0 c1 c2
  let ω : Fin 4 → K := ![c0, c1, c2, c3]
  have hω0 : ω 0 = c0 := rfl
  have hω1 : ω 1 = c1 := rfl
  have hω2 : ω 2 = c2 := rfl
  have hω3 : ω 3 = c3 := rfl
  have h01 : sg K f c0 ≠ c1 := hc1s0.symm
  have h02 : sg K f c0 ≠ c2 := hc2c.symm
  have h10 : sg K f c1 ≠ c0 := (q2cFPo_sg_ne_iff hK c1 c0).mpr hc1s0
  have h20 : sg K f c2 ≠ c0 := (q2cFPo_sg_ne_iff hK c2 c0).mpr hc2c
  refine ⟨ω, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hω0, hω1, hω2, hω3]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [hω0, hω1, hω2, hω3, hc0m, hc1m, h01, h02, h10, h20]

@[expose] noncomputable def q2cFPo_bvec {n : ℕ} (d : List ℕ) (pol : List Bool) (ω : Fin 4 → K)
    (b : ℕ) (t : Fin 4) : Fin n → K :=
  fun k =>
    if d.getD b 0 ≤ k.val ∧ k.val < d.getD (b + 1) 0 then
      if pol.getD b false then (if k.val - d.getD b 0 = t.val then 1 else 0)
      else ω t ^ (k.val - d.getD b 0)
    else 0

theorem q2cFPo_bvec_mem_Wb (pol : List Bool) (ω : Fin 4 → K) (b : ℕ) (t : Fin 4) :
    q2cFPo_bvec (K := K) (n := n) d pol ω b t ∈ q2cFPo_Wb (K := K) (n := n) d b := by
  intro j hj
  simp only [q2cFPo_bvec]
  rw [if_neg hj]

@[expose] noncomputable def q2cFPo_A {n : ℕ} (d : List ℕ) (pol : List Bool) (ω : Fin 4 → K)
    (b r : ℕ) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range fun t : {t : Fin 4 // t.val < r} =>
    q2cFPo_bvec (K := K) (n := n) d pol ω b t.1)

theorem q2cFPo_A_mono (pol : List Bool) (ω : Fin 4 → K) (b : ℕ) {r r' : ℕ} (h : r ≤ r') :
    q2cFPo_A (K := K) (n := n) d pol ω b r ≤ q2cFPo_A (K := K) (n := n) d pol ω b r' := by
  apply Submodule.span_mono
  rintro v ⟨t, rfl⟩
  exact ⟨⟨t.1, lt_of_lt_of_le t.2 h⟩, rfl⟩

theorem q2cFPo_A_le_Wb (pol : List Bool) (ω : Fin 4 → K) (b r : ℕ) :
    q2cFPo_A (K := K) (n := n) d pol ω b r ≤ q2cFPo_Wb (K := K) (n := n) d b := by
  apply Submodule.span_le.mpr
  rintro v ⟨t, rfl⟩
  exact q2cFPo_bvec_mem_Wb pol ω b t.1

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
