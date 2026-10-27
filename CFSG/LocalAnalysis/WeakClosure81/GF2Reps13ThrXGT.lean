module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private lemma w16t_adj_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} [Fact p.Prime]
    {G : SimpleGraph ι} {v : ι → ι → ι → ZMod p}
    (hv : ∀ i j, G.Adj i j → ∀ k, v i j k ≠ 0 ↔ (k = i ∨ k = j))
    {y : ι → ZMod p} (hy : ∀ i j (h : G.Adj i j), ∑ k, v i j k * y k = 0)
    {i j : ι} (h : G.Adj i j) : y i = 0 ↔ y j = 0 := by
  have hne : i ≠ j := G.ne_of_adj h
  have hpair : Finset.sum ({i, j} : Finset ι) (fun k => v i j k * y k)
      = Finset.sum (Finset.univ : Finset ι) (fun k => v i j k * y k) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    have hx' : x ≠ i ∧ x ≠ j := by
      have hx'' := hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx''
      exact not_or.mp hx''
    have hx0 : v i j x = 0 := by
      by_contra hne'
      rcases (hv i j h x).1 hne' with hxi | hxj
      · exact hx'.1 hxi
      · exact hx'.2 hxj
    simp [hx0]
  have hsum : (∑ k, v i j k * y k) = v i j i * y i + v i j j * y j := by
    rw [← hpair, Finset.sum_pair (f := fun k => v i j k * y k) hne]
  have heq : v i j i * y i + v i j j * y j = 0 := by
    rw [← hsum]
    exact hy i j h
  have hi : v i j i ≠ 0 := (hv i j h i).2 (Or.inl rfl)
  have hj : v i j j ≠ 0 := (hv i j h j).2 (Or.inr rfl)
  constructor
  · intro hyi
    have hzero : v i j j * y j = 0 := by simpa [hyi] using heq
    exact (mul_eq_zero.mp hzero).resolve_left hj
  · intro hyj
    have hzero : v i j i * y i = 0 := by simpa [hyj] using heq
    exact (mul_eq_zero.mp hzero).resolve_left hi

private lemma w16t_walk_zero {ι : Type*} {p : ℕ} {G : SimpleGraph ι} {y : ι → ZMod p}
    (hzw : ∀ i j, G.Adj i j → (y i = 0 ↔ y j = 0)) :
    ∀ {a b : ι}, G.Walk a b → y a = 0 → y b = 0 := by
  intro a b w
  induction w with
  | nil => exact id
  | cons h w ih => exact fun ha => ih ((hzw _ _ h).1 ha)

private lemma w16t_eq_zero_of_sum_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}
    [Fact p.Prime] {G : SimpleGraph ι} (hG : G.Connected) {v : ι → ι → ι → ZMod p}
    (hv : ∀ i j, G.Adj i j → ∀ k, v i j k ≠ 0 ↔ (k = i ∨ k = j))
    {i₀ : ι} {y : ι → ZMod p}
    (hy : ∀ i j (h : G.Adj i j), ∑ k, v i j k * y k = 0) (hi₀ : y i₀ = 0) : y = 0 := by
  funext k
  obtain ⟨w⟩ := hG i₀ k
  exact w16t_walk_zero (fun i j h => w16t_adj_zero_iff hv hy h) w hi₀

theorem w16t_card_span_edges {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℕ} [Fact p.Prime]
    (G : SimpleGraph ι) (hG : G.Connected) (v : ι → ι → ι → ZMod p)
    (hv : ∀ i j, G.Adj i j → ∀ k, v i j k ≠ 0 ↔ (k = i ∨ k = j)) :
    p ^ (Fintype.card ι - 1) ≤
      Nat.card ↥(Submodule.span (ZMod p) {w : ι → ZMod p | ∃ i j, G.Adj i j ∧ w = v i j}) := by
  classical
  let S : Submodule (ZMod p) (ι → ZMod p) :=
    Submodule.span (ZMod p) {w : ι → ZMod p | ∃ i j, G.Adj i j ∧ w = v i j}
  change p ^ (Fintype.card ι - 1) ≤ Nat.card ↥S
  obtain ⟨i₀⟩ := hG.nonempty
  let E := {e : ι × ι // G.Adj e.1 e.2}
  let M : Matrix E ι (ZMod p) := fun e => v e.1.1 e.1.2
  have hrow : Set.range M.row = {w : ι → ZMod p | ∃ i j, G.Adj i j ∧ w = v i j} := by
    ext w
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨e.1.1, e.1.2, e.2, rfl⟩
    · rintro ⟨i, j, h, rfl⟩
      exact ⟨⟨(i, j), h⟩, rfl⟩
  have hfin : Module.finrank (ZMod p) S = M.rank := by
    have hS : S = Submodule.span (ZMod p) (Set.range M.row) :=
      (congrArg (Submodule.span (ZMod p)) hrow).symm
    rw [hS, ← Matrix.rank_eq_finrank_span_row M]
  have hker : Module.finrank (ZMod p) (LinearMap.ker M.mulVecLin) ≤ 1 := by
    let ψ : (LinearMap.ker M.mulVecLin) →ₗ[ZMod p] ZMod p :=
      (LinearMap.proj i₀).comp (Submodule.subtype (LinearMap.ker M.mulVecLin))
    have hψ : Function.Injective ψ := by
      intro y z hyz
      have hyz' : (y : ι → ZMod p) i₀ = (z : ι → ZMod p) i₀ := by
        simpa [ψ, LinearMap.proj_apply] using hyz
      apply Subtype.ext
      funext k
      have hw0 : (fun k => (y : ι → ZMod p) k - (z : ι → ZMod p) k) i₀ = 0 := by
        simpa only [sub_eq_zero] using hyz'
      have h1 : M.mulVecLin ((y : LinearMap.ker M.mulVecLin) : ι → ZMod p) = 0 :=
        LinearMap.mem_ker.mp y.2
      have h2 : M.mulVecLin ((z : LinearMap.ker M.mulVecLin) : ι → ZMod p) = 0 :=
        LinearMap.mem_ker.mp z.2
      have hwsum : ∀ i j (h : G.Adj i j),
          ∑ k, v i j k * ((y : ι → ZMod p) k - (z : ι → ZMod p) k) = 0 := by
        intro i j hij
        have hw : M.mulVecLin ((y : ι → ZMod p) - (z : ι → ZMod p)) = 0 := by
          rw [map_sub, h1, h2]
          simp
        have he := congrFun hw ⟨(i, j), hij⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum] at he
        simpa [M] using he
      have hzero := w16t_eq_zero_of_sum_zero hG hv hwsum hw0
      exact sub_eq_zero.mp (congrFun hzero k)
    have hle := LinearMap.finrank_le_finrank_of_injective hψ
    rwa [Module.finrank_self] at hle
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hfun : Module.finrank (ZMod p) (ι → ZMod p) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card (ZMod p)
  have hrank : M.rank + Module.finrank (ZMod p) (LinearMap.ker M.mulVecLin)
      = Fintype.card ι := by
    have h := hrn
    rw [hfun] at h
    exact h
  have hrank_ge : Fintype.card ι - 1 ≤ M.rank := by
    have hcard_le : Fintype.card ι ≤ M.rank + 1 := by
      calc Fintype.card ι
          = M.rank + Module.finrank (ZMod p) (LinearMap.ker M.mulVecLin) := hrank.symm
        _ ≤ M.rank + 1 := Nat.add_le_add_left hker M.rank
    exact Nat.sub_le_iff_le_add.2 hcard_le
  have hcardS : Nat.card ↥S = p ^ M.rank := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact congrArg (fun n => p ^ n) hfin
  calc p ^ (Fintype.card ι - 1) ≤ p ^ M.rank :=
        Nat.pow_le_pow_right (Fact.out : p.Prime).pos hrank_ge
    _ = Nat.card ↥S := hcardS.symm

end CFSG.LocalAnalysis.WeakClosure81
