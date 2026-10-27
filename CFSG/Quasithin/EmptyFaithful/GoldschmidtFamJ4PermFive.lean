module

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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.J4Fam

open Equiv

@[expose] def pa : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def pb : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def Ord3 (x : Perm (Fin 5)) : Prop := x ≠ 1 ∧ x ^ 3 = 1

instance (x : Perm (Fin 5)) : Decidable (Ord3 x) := by unfold Ord3; infer_instance

set_option maxRecDepth 100000 in
theorem exists_word_ord3 : ∀ g : Perm (Fin 5), g 4 ≠ 4 →
    Ord3 g ∨ Ord3 (g * g) ∨ Ord3 (pa * g) ∨ Ord3 (pb * g) ∨ Ord3 (pa * pb * g) ∨
      Ord3 (pa * g * g) ∨ Ord3 (pb * g * g) ∨ Ord3 (pa * pb * g * g) ∨
      Ord3 (pa * g * pa * g) := by
  unfold Ord3 pa pb
  decide

set_option maxRecDepth 100000 in
theorem eq_of_zero_one : ∀ t : Perm (Fin 5), t 4 = 4 → t * t = 1 → t 0 = 1 →
    t = swap 0 1 ∨ t = pa := by
  unfold pa
  decide

set_option maxRecDepth 100000 in
theorem eq_of_zero_two : ∀ t : Perm (Fin 5), t 4 = 4 → t * t = 1 → t 0 = 2 →
    t = swap 0 2 ∨ t = pb := by
  unfold pb
  decide

set_option maxRecDepth 100000 in
theorem comm_cases :
    ¬ ((swap 0 1 : Perm (Fin 5)) * swap 0 2 = swap 0 2 * swap 0 1) ∧
    ¬ ((swap 0 1 : Perm (Fin 5)) * pb = pb * swap 0 1) ∧
    ¬ (pa * (swap 0 2 : Perm (Fin 5)) = swap 0 2 * pa) := by
  unfold pb pa
  decide

theorem pa_pb_mem {V : Subgroup (Perm (Fin 5))} (ha : ∀ v ∈ V, v 4 = 4)
    (hb : ∀ v ∈ V, v * v = 1) (hc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hd : ∀ i : Fin 5, i ≠ 4 → ∃ v ∈ V, v 0 = i) : pa ∈ V ∧ pb ∈ V := by
  obtain ⟨t1, ht1, ht10⟩ := hd 1 (by decide)
  obtain ⟨t2, ht2, ht20⟩ := hd 2 (by decide)
  have h1 := eq_of_zero_one t1 (ha t1 ht1) (hb t1 ht1) ht10
  have h2 := eq_of_zero_two t2 (ha t2 ht2) (hb t2 ht2) ht20
  have hcomm := hc t1 ht1 t2 ht2
  obtain ⟨c1, c2, c3⟩ := comm_cases
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact absurd hcomm c1
  · exact absurd hcomm c2
  · exact absurd hcomm c3
  · exact ⟨ht1, ht2⟩

theorem three_dvd_card_of_klein {G V : Subgroup (Perm (Fin 5))} (hVG : V ≤ G)
    (ha : ∀ v ∈ V, v 4 = 4) (hb : ∀ v ∈ V, v * v = 1) (hc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hd : ∀ i : Fin 5, i ≠ 4 → ∃ v ∈ V, v 0 = i) (he : ∃ g ∈ G, g 4 ≠ 4) :
    3 ∣ Nat.card G := by
  obtain ⟨hpa, hpb⟩ := pa_pb_mem ha hb hc hd
  obtain ⟨g, hg, hg4⟩ := he
  have hpa' : pa ∈ G := hVG hpa
  have hpb' : pb ∈ G := hVG hpb
  have key : ∃ x ∈ G, Ord3 x := by
    rcases exists_word_ord3 g hg4 with h | h | h | h | h | h | h | h | h
    · exact ⟨_, hg, h⟩
    · exact ⟨_, G.mul_mem hg hg, h⟩
    · exact ⟨_, G.mul_mem hpa' hg, h⟩
    · exact ⟨_, G.mul_mem hpb' hg, h⟩
    · exact ⟨_, G.mul_mem (G.mul_mem hpa' hpb') hg, h⟩
    · exact ⟨_, G.mul_mem hpa' (G.mul_mem hg hg), h⟩
    · exact ⟨_, G.mul_mem hpb' (G.mul_mem hg hg), h⟩
    · exact ⟨_, G.mul_mem (G.mul_mem hpa' hpb') (G.mul_mem hg hg), h⟩
    · exact ⟨_, G.mul_mem (G.mul_mem (G.mul_mem hpa' hg) hpa') hg, h⟩
  obtain ⟨x, hx, hx1, hx3⟩ := key
  have ho : orderOf (⟨x, hx⟩ : G) = 3 := by
    have h3 : (⟨x, hx⟩ : G) ^ 3 = 1 := Subtype.ext hx3
    have h1 : (⟨x, hx⟩ : G) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    exact orderOf_eq_prime h3 h1
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem four_dvd_card_of_transitive {V : Subgroup (Perm (Fin 5))} (ha : ∀ v ∈ V, v 4 = 4)
    (hd : ∀ i : Fin 5, i ≠ 4 → ∃ v ∈ V, v 0 = i) : 4 ∣ Nat.card V := by
  have horb : MulAction.orbit V (0 : Fin 5) = {i | i ≠ 4} := by
    ext i
    constructor
    · rintro ⟨⟨v, hv⟩, rfl⟩ h
      have h4 := ha v hv
      have : (0 : Fin 5) = 4 := v.injective (h.trans h4.symm)
      exact absurd this (by decide)
    · intro hi
      obtain ⟨v, hv, hv0⟩ := hd i hi
      exact ⟨⟨v, hv⟩, hv0⟩
  have hcard : (MulAction.orbit V (0 : Fin 5)).ncard = 4 := by
    rw [horb, show ({i : Fin 5 | i ≠ 4} : Set (Fin 5)) = Set.univ \ {4} by ext i; simp,
      Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
    simp
  have h1 := MulAction.index_stabilizer V (0 : Fin 5)
  have h2 := (MulAction.stabilizer V (0 : Fin 5)).card_mul_index
  rw [h1, hcard] at h2
  exact ⟨_, by rw [← h2, mul_comm]⟩

theorem five_dvd_card_of_transitive {G V : Subgroup (Perm (Fin 5))} (hVG : V ≤ G)
    (hd : ∀ i : Fin 5, i ≠ 4 → ∃ v ∈ V, v 0 = i) (he : ∃ g ∈ G, g 4 ≠ 4) :
    5 ∣ Nat.card G := by
  obtain ⟨g, hg, hg4⟩ := he
  have horb : MulAction.orbit G (4 : Fin 5) = Set.univ := by
    ext i
    simp only [Set.mem_univ, iff_true]
    by_cases hi : i = 4
    · subst hi
      exact ⟨1, rfl⟩
    · obtain ⟨v1, hv1, hv10⟩ := hd (g 4) hg4
      obtain ⟨v2, hv2, hv20⟩ := hd i hi
      refine ⟨⟨v2 * v1⁻¹ * g, G.mul_mem (G.mul_mem (hVG hv2) (G.inv_mem (hVG hv1))) hg⟩, ?_⟩
      show (v2 * v1⁻¹ * g) 4 = i
      have h1 : v1⁻¹ (g 4) = 0 := by
        rw [← hv10]
        exact v1.symm_apply_apply 0
      show v2 (v1⁻¹ (g 4)) = i
      rw [h1, hv20]
  have hcard : (MulAction.orbit G (4 : Fin 5)).ncard = 5 := by
    rw [horb, Set.ncard_univ]
    simp
  have h1 := MulAction.index_stabilizer G (4 : Fin 5)
  have h2 := (MulAction.stabilizer G (4 : Fin 5)).card_mul_index
  rw [h1, hcard] at h2
  exact ⟨_, by rw [← h2, mul_comm]⟩

theorem sixty_dvd_card_of_klein {G V : Subgroup (Perm (Fin 5))} (hVG : V ≤ G)
    (ha : ∀ v ∈ V, v 4 = 4) (hb : ∀ v ∈ V, v * v = 1) (hc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v)
    (hd : ∀ i : Fin 5, i ≠ 4 → ∃ v ∈ V, v 0 = i) (he : ∃ g ∈ G, g 4 ≠ 4) :
    60 ∣ Nat.card G := by
  have h3 := three_dvd_card_of_klein hVG ha hb hc hd he
  have h4 : 4 ∣ Nat.card G :=
    (four_dvd_card_of_transitive ha hd).trans (Subgroup.card_dvd_of_le hVG)
  have h5 := five_dvd_card_of_transitive hVG hd he
  have h12 : 12 ∣ Nat.card G :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 4) h3 h4
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 5) h12 h5

end CFSG.Quasithin.J4Fam
