module

public import CFSG.Certificates.SchreierChainOrderStabilizers
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFJTri
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Certificates CFSG.Monster.B.Co2

theorem eq_one_of_fix_base {n : ℕ} (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup)
    (hfix : ∀ b ∈ Q.base.toList, g b = b) : g = 1 := by
  have h := Q.levelSubgroup_eq_pointwise_stabilizer hQ Q.baseCount le_rfl
  have hmem : g ∈ Q.levelSubgroup Q.baseCount := by
    rw [h, Subgroup.mem_inf]
    refine ⟨hg, ?_⟩
    rw [mem_fixingSubgroup_iff]
    intro b hb
    rw [Equiv.Perm.smul_def]
    refine hfix b ?_
    exact List.mem_of_mem_take hb
  rw [Q.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact Subgroup.mem_bot.mp hmem

@[expose] def imgWord (S : Array (Array ℕ)) (w : List ℕ) (i : ℕ) : ℕ :=
  w.foldr (fun l j => (S[l]!)[j]!) i

variable {n : ℕ}

theorem apply_wordProd {S : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin n)}
    (hrep : ∀ l, l < S.size → Rep n S[l]! (g l)) :
    ∀ (w : List ℕ), (∀ l ∈ w, l < S.size) → ∀ i : Fin n,
      (((w.map g).prod i : Fin n) : ℕ) = imgWord S w i
  | [], _, i => rfl
  | l :: w, hw, i => by
    have hl : l < S.size := hw l (List.mem_cons_self ..)
    have ih := apply_wordProd hrep w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) i
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ← hrep l hl, ih]
    rfl

theorem not_isSolvable_of_chain_triangle (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (S : Array (Array ℕ)) (g : ℕ → Equiv.Perm (Fin n)) (hrep : ∀ l, l < S.size → Rep n S[l]! (g l))
    {wx wy : List ℕ} (hwx : ∀ l ∈ wx, l < S.size ∧ g l ∈ Q.originalSubgroup)
    (hwy : ∀ l ∈ wy, l < S.size ∧ g l ∈ Q.originalSubgroup) {N : ℕ} (hN : N.Coprime 6)
    (hx2 : ∀ b ∈ Q.base.toList, imgWord S wx (imgWord S wx b) = b)
    (hy3 : ∀ b ∈ Q.base.toList, imgWord S wy (imgWord S wy (imgWord S wy b)) = b)
    (hxy : ∀ b ∈ Q.base.toList,
      (fun j => imgWord S wx (imgWord S wy j))^[N] b = b)
    (p : Fin n) (hp : imgWord S wx p ≠ p) : ¬ Group.IsSolvable ↥Q.originalSubgroup := by
  set x : Equiv.Perm (Fin n) := (wx.map g).prod with hxdef
  set y : Equiv.Perm (Fin n) := (wy.map g).prod with hydef
  have hxQ : x ∈ Q.originalSubgroup :=
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hz
      exact (hwx l hl).2
  have hyQ : y ∈ Q.originalSubgroup :=
    Subgroup.list_prod_mem _ fun z hz => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hz
      exact (hwy l hl).2
  have hxv : ∀ i : Fin n, ((x i : Fin n) : ℕ) = imgWord S wx i :=
    apply_wordProd hrep wx (fun l hl => (hwx l hl).1)
  have hyv : ∀ i : Fin n, ((y i : Fin n) : ℕ) = imgWord S wy i :=
    apply_wordProd hrep wy (fun l hl => (hwy l hl).1)
  have hx2' : x ^ 2 = 1 := by
    refine eq_one_of_fix_base Q hQ (Subgroup.pow_mem _ hxQ 2) fun b hb => ?_
    apply Fin.ext
    rw [pow_two, Equiv.Perm.mul_apply, hxv, hxv]
    exact hx2 b hb
  have hy3' : y ^ 3 = 1 := by
    refine eq_one_of_fix_base Q hQ (Subgroup.pow_mem _ hyQ 3) fun b hb => ?_
    apply Fin.ext
    rw [pow_succ, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hyv, hyv, hyv]
    exact hy3 b hb
  have hiter : ∀ (m : ℕ) (b : Fin n), (((x * y) ^ m) b : ℕ) =
      (fun j => imgWord S wx (imgWord S wy j))^[m] b := by
    intro m
    induction m with
    | zero => intro b; rfl
    | succ m ih =>
      intro b
      rw [pow_succ, Equiv.Perm.mul_apply, ih, Function.iterate_succ_apply, Equiv.Perm.mul_apply,
        hxv, hyv]
  have hxy' : (x * y) ^ N = 1 := by
    refine eq_one_of_fix_base Q hQ (Subgroup.pow_mem _ (Subgroup.mul_mem _ hxQ hyQ) N)
      fun b hb => ?_
    apply Fin.ext
    rw [hiter]
    exact hxy b hb
  refine not_isSolvable_of_triangle _ hxQ hyQ hx2' hy3' hN hxy' fun h1 => hp ?_
  have := hxv p
  rw [h1, Equiv.Perm.one_apply] at this
  exact this.symm

end CFSG.Quasithin.SBd19F
