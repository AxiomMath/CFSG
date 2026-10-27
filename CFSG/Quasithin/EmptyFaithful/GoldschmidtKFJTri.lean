module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.SBd19F

open Subgroup
open scoped commutatorElement

theorem eq_one_of_commute_triangle {M : Type*} [Group M] {a b : M} (hab : Commute a b)
    (ha : a ^ 2 = 1) (hb : b ^ 3 = 1) {n : ℕ} (hn : n.Coprime 6) (h : (a * b) ^ n = 1) :
    a = 1 ∧ b = 1 := by
  have ha6 : a ^ 6 = 1 := by
    have := pow_mul a 2 3
    rw [ha, one_pow] at this
    exact this
  have hb6 : b ^ 6 = 1 := by
    have := pow_mul b 3 2
    rw [hb, one_pow] at this
    exact this
  have h6 : (a * b) ^ 6 = 1 := by rw [hab.mul_pow, ha6, hb6, one_mul]
  have hg : (a * b) ^ Nat.gcd 6 n = 1 := pow_gcd_eq_one.mpr ⟨h6, h⟩
  rw [Nat.gcd_comm, hn] at hg
  have hab1 : a * b = 1 := by simpa using hg
  have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab1
  have hb2 : b ^ 2 = 1 := by
    rw [hb', inv_pow, ha, inv_one]
  have hb1 : b = 1 := by
    calc b = b ^ 3 * (b ^ 2)⁻¹ := by group
      _ = 1 := by rw [hb, hb2]; group
  refine ⟨?_, hb1⟩
  rw [hb1, mul_one] at hab1
  exact hab1

variable {G : Type*} [Group G]

theorem mem_derivedSeries_succ_of_triangle {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 3 = 1) {n : ℕ}
    (hn : n.Coprime 6) (hxy : (x * y) ^ n = 1) (k : ℕ) (hxk : x ∈ derivedSeries G k)
    (hyk : y ∈ derivedSeries G k) :
    x ∈ derivedSeries G (k + 1) ∧ y ∈ derivedSeries G (k + 1) := by
  have : (derivedSeries G (k + 1)).Normal := derivedSeries_normal G (k + 1)
  let π : G →* G ⧸ derivedSeries G (k + 1) := QuotientGroup.mk' _
  have hmem : ⁅x, y⁆ ∈ derivedSeries G (k + 1) := by
    rw [derivedSeries_succ]
    exact commutator_mem_commutator hxk hyk
  have hcomm : Commute (π x) (π y) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  obtain ⟨h1, h2⟩ := eq_one_of_commute_triangle hcomm (by rw [← map_pow, hx, map_one])
    (by rw [← map_pow, hy, map_one]) hn (by rw [← map_mul, ← map_pow, hxy, map_one])
  exact ⟨(QuotientGroup.eq_one_iff _).mp h1, (QuotientGroup.eq_one_iff _).mp h2⟩

theorem mem_derivedSeries_of_triangle {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 3 = 1) {n : ℕ}
    (hn : n.Coprime 6) (hxy : (x * y) ^ n = 1) (k : ℕ) :
    x ∈ derivedSeries G k ∧ y ∈ derivedSeries G k := by
  induction k with
  | zero => simp [derivedSeries_zero]
  | succ k ih => exact mem_derivedSeries_succ_of_triangle hx hy hn hxy k ih.1 ih.2

theorem eq_one_of_isSolvable_of_triangle [Group.IsSolvable G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ^ 3 = 1) {n : ℕ} (hn : n.Coprime 6) (hxy : (x * y) ^ n = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := Group.IsSolvable.solvable (G := G)
  have := (mem_derivedSeries_of_triangle hx hy hn hxy k).1
  rwa [hk, Subgroup.mem_bot] at this

theorem not_isSolvable_of_triangle (H : Subgroup G) {x y : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hx : x ^ 2 = 1) (hy : y ^ 3 = 1) {n : ℕ} (hn : n.Coprime 6) (hxy : (x * y) ^ n = 1)
    (hne : x ≠ 1) : ¬ Group.IsSolvable ↥H := by
  intro hs
  have := eq_one_of_isSolvable_of_triangle (G := ↥H) (x := ⟨x, hxH⟩) (y := ⟨y, hyH⟩)
    (Subtype.ext (by simpa using hx)) (Subtype.ext (by simpa using hy)) hn
    (Subtype.ext (by simpa using hxy))
  exact hne (congrArg Subtype.val this)

end CFSG.Quasithin.SBd19F
