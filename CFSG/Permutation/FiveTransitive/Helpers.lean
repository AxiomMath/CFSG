module

public import CFSG.Permutation.FiveTransitive.FiniteChecks
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace FiveTransitive.Helpers

theorem permCongr_formPerm
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (l : List α) :
    e.permCongr (List.formPerm l) = List.formPerm (l.map e) := by
  induction l with
  | nil =>
      exact e.permCongrHom.map_one
  | cons x l ih =>
      cases l with
      | nil =>
          exact e.permCongrHom.map_one
      | cons y l =>
          simp only [List.formPerm_cons_cons, List.map_cons, e.permCongr_mul, ih]
          congr 1
          ext z
          simp only [Equiv.permCongr_apply, Equiv.swap_apply_def]
          split_ifs <;>
            have hz := e.apply_symm_apply z <;>
            simp_all

private theorem mem_normalCore_of_card_support_le_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hdegree : 5 ≤ Fintype.card X)
    {g : Equiv.Perm X} (hg : g ∈ P) (hcard : g.support.card ≤ 5) :
    g ∈ P.normalCore := by
  classical
  obtain ⟨t, hsupport, ht⟩ :=
    Finset.exists_superset_card_eq hcard hdegree
  let e : Fin 5 ≃ {x // x ∈ t} :=
    (Finset.equivFinOfCardEq ht).symm
  let a : Fin 5 → X := fun i => e i
  have ha : Function.Injective a := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  intro b
  have hba : Function.Injective (fun i => b (a i)) :=
    b.injective.comp ha
  obtain ⟨p, hp⟩ := h5 a (fun i => b (a i)) ha hba
  have hp_on_t : ∀ x ∈ t, (p : Equiv.Perm X) x = b x := by
    intro x hx
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    have hai : a i = x := congrArg Subtype.val hi
    rw [← hai]
    exact hp i
  let q : Equiv.Perm X := (p : Equiv.Perm X)⁻¹ * b
  have hq_fix : ∀ x ∈ t, q x = x := by
    intro x hx
    change (p : Equiv.Perm X)⁻¹ (b x) = x
    rw [← hp_on_t x hx]
    exact (p : Equiv.Perm X).symm_apply_apply x
  have hqg : Equiv.Perm.Disjoint q g := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro x
    by_cases hx : x ∈ g.support
    · exact Or.inl (hq_fix x (hsupport hx))
    · exact Or.inr (Equiv.Perm.notMem_support.mp hx)
  have hb : b = (p : Equiv.Perm X) * q := by
    simp [q]
  have hconj :
      b * g * b⁻¹ =
        (p : Equiv.Perm X) * g * (p : Equiv.Perm X)⁻¹ := by
    rw [hb, mul_inv_rev, mul_assoc (p : Equiv.Perm X) q g, hqg.commute.eq]
    group
  rw [hconj]
  exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)

theorem alternatingGroup_le_of_nontrivial_card_support_le_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hdegree : 5 ≤ Fintype.card X)
    {g : Equiv.Perm X} (hg : g ∈ P) (hgNe : g ≠ 1)
    (hcard : g.support.card ≤ 5) :
    alternatingGroup X ≤ P := by
  have hgcore :=
    mem_normalCore_of_card_support_le_five X P h5 hdegree hg hcard
  have hcoreNe : P.normalCore ≠ ⊥ := by
    intro hcore
    apply hgNe
    simpa [hcore] using hgcore
  have hcore : Nontrivial P.normalCore :=
    P.normalCore.nontrivial_iff_ne_bot.mpr hcoreNe
  exact (Equiv.Perm.alternatingGroup_le_of_normal (by
    rw [Nat.card_eq_fintype_card]
    omega) hcore).trans P.normalCore_le

private theorem exists_controlled_conjugator12
    (P : Subgroup (Equiv.Perm (Fin 12)))
    (h5 : ∀ a b : Fin 5 → Fin 12,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    ∃ p : P,
      (p : Equiv.Perm (Fin 12)) 0 = 0 ∧
      (p : Equiv.Perm (Fin 12)) 1 = 1 ∧
      (p : Equiv.Perm (Fin 12)) 2 = 2 ∧
      (p : Equiv.Perm (Fin 12)) 3 = 3 ∧
      (p : Equiv.Perm (Fin 12)) 7 = 4 := by
  obtain ⟨p, hp⟩ := h5
    FiniteChecks.sourceTuple12 FiniteChecks.targetTuple12
    FiniteChecks.sourceTuple12_injective
    FiniteChecks.targetTuple12_injective
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [FiniteChecks.sourceTuple12, FiniteChecks.targetTuple12,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (0 : Fin 5)
  · simpa [FiniteChecks.sourceTuple12, FiniteChecks.targetTuple12,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (1 : Fin 5)
  · simpa [FiniteChecks.sourceTuple12, FiniteChecks.targetTuple12,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (2 : Fin 5)
  · simpa [FiniteChecks.sourceTuple12, FiniteChecks.targetTuple12,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (3 : Fin 5)
  · simpa [FiniteChecks.sourceTuple12, FiniteChecks.targetTuple12,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (4 : Fin 5)

private theorem five_le_image_of_controlled_conjugator12
    (p : Equiv.Perm (Fin 12))
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 2)
    (hp3 : p 3 = 3) (hp7 : p 7 = 4)
    (i : Fin 12)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (hi3 : i ≠ 3) (hi7 : i ≠ 7) :
    5 ≤ (p i).val := by
  apply FiniteChecks.five_le_of_ne_zero_one_two_three_four12
  · simpa [hp0] using p.injective.ne hi0
  · simpa [hp1] using p.injective.ne hi1
  · simpa [hp2] using p.injective.ne hi2
  · simpa [hp3] using p.injective.ne hi3
  · simpa [hp7] using p.injective.ne hi7

private theorem exists_controlled_conjugator13
    (P : Subgroup (Equiv.Perm (Fin 13)))
    (h5 : ∀ a b : Fin 5 → Fin 13,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    ∃ p : P,
      (p : Equiv.Perm (Fin 13)) 0 = 0 ∧
      (p : Equiv.Perm (Fin 13)) 1 = 1 ∧
      (p : Equiv.Perm (Fin 13)) 2 = 2 ∧
      (p : Equiv.Perm (Fin 13)) 3 = 3 ∧
      (p : Equiv.Perm (Fin 13)) 7 = 4 := by
  obtain ⟨p, hp⟩ := h5
    FiniteChecks.sourceTuple13 FiniteChecks.targetTuple13
    FiniteChecks.sourceTuple13_injective
    FiniteChecks.targetTuple13_injective
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [FiniteChecks.sourceTuple13, FiniteChecks.targetTuple13,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (0 : Fin 5)
  · simpa [FiniteChecks.sourceTuple13, FiniteChecks.targetTuple13,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (1 : Fin 5)
  · simpa [FiniteChecks.sourceTuple13, FiniteChecks.targetTuple13,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (2 : Fin 5)
  · simpa [FiniteChecks.sourceTuple13, FiniteChecks.targetTuple13,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (3 : Fin 5)
  · simpa [FiniteChecks.sourceTuple13, FiniteChecks.targetTuple13,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (4 : Fin 5)

private theorem five_le_image_of_controlled_conjugator13
    (p : Equiv.Perm (Fin 13))
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 2)
    (hp3 : p 3 = 3) (hp7 : p 7 = 4)
    (i : Fin 13)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (hi3 : i ≠ 3) (hi7 : i ≠ 7) :
    5 ≤ (p i).val := by
  apply FiniteChecks.five_le_of_ne_zero_one_two_three_four13
  · simpa [hp0] using p.injective.ne hi0
  · simpa [hp1] using p.injective.ne hi1
  · simpa [hp2] using p.injective.ne hi2
  · simpa [hp3] using p.injective.ne hi3
  · simpa [hp7] using p.injective.ne hi7

private theorem exists_controlled_conjugator14
    (P : Subgroup (Equiv.Perm (Fin 14)))
    (h5 : ∀ a b : Fin 5 → Fin 14,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    ∃ p : P,
      (p : Equiv.Perm (Fin 14)) 0 = 0 ∧
      (p : Equiv.Perm (Fin 14)) 1 = 1 ∧
      (p : Equiv.Perm (Fin 14)) 2 = 2 ∧
      (p : Equiv.Perm (Fin 14)) 3 = 3 ∧
      (p : Equiv.Perm (Fin 14)) 7 = 4 := by
  obtain ⟨p, hp⟩ := h5
    FiniteChecks.sourceTuple14 FiniteChecks.targetTuple14
    FiniteChecks.sourceTuple14_injective
    FiniteChecks.targetTuple14_injective
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [FiniteChecks.sourceTuple14, FiniteChecks.targetTuple14,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (0 : Fin 5)
  · simpa [FiniteChecks.sourceTuple14, FiniteChecks.targetTuple14,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (1 : Fin 5)
  · simpa [FiniteChecks.sourceTuple14, FiniteChecks.targetTuple14,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (2 : Fin 5)
  · simpa [FiniteChecks.sourceTuple14, FiniteChecks.targetTuple14,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (3 : Fin 5)
  · simpa [FiniteChecks.sourceTuple14, FiniteChecks.targetTuple14,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (4 : Fin 5)

private theorem five_le_image_of_controlled_conjugator14
    (p : Equiv.Perm (Fin 14))
    (hp0 : p 0 = 0) (hp1 : p 1 = 1) (hp2 : p 2 = 2)
    (hp3 : p 3 = 3) (hp7 : p 7 = 4)
    (i : Fin 14)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
    (hi3 : i ≠ 3) (hi7 : i ≠ 7) :
    5 ≤ (p i).val := by
  apply FiniteChecks.five_le_of_ne_zero_one_two_three_four14
  · simpa [hp0] using p.injective.ne hi0
  · simpa [hp1] using p.injective.ne hi1
  · simpa [hp2] using p.injective.ne hi2
  · simpa [hp3] using p.injective.ne hi3
  · simpa [hp7] using p.injective.ne hi7

private theorem alternatingGroup_le_of_sevenCycle_mem
    (P : Subgroup (Equiv.Perm (Fin 10)))
    (h5 : ∀ a b : Fin 5 → Fin 10,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.sevenCycle ∈ P) :
    alternatingGroup (Fin 10) ≤ P := by
  classical
  obtain ⟨p, hp⟩ := h5
    FiniteChecks.sourceTuple FiniteChecks.targetTuple
    FiniteChecks.sourceTuple_injective FiniteChecks.targetTuple_injective
  have hp0 : (p : Equiv.Perm (Fin 10)) 0 = 0 := by
    simpa [FiniteChecks.sourceTuple, FiniteChecks.targetTuple,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (0 : Fin 5)
  have hp1 : (p : Equiv.Perm (Fin 10)) 1 = 1 := by
    simpa [FiniteChecks.sourceTuple, FiniteChecks.targetTuple,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (1 : Fin 5)
  have hp2 : (p : Equiv.Perm (Fin 10)) 2 = 2 := by
    simpa [FiniteChecks.sourceTuple, FiniteChecks.targetTuple,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (2 : Fin 5)
  have hp3 : (p : Equiv.Perm (Fin 10)) 3 = 3 := by
    simpa [FiniteChecks.sourceTuple, FiniteChecks.targetTuple,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (3 : Fin 5)
  have hp7 : (p : Equiv.Perm (Fin 10)) 7 = 4 := by
    simpa [FiniteChecks.sourceTuple, FiniteChecks.targetTuple,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (4 : Fin 5)
  have htail (i : Fin 10)
      (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
      (hi3 : i ≠ 3) (hi7 : i ≠ 7) :
      5 ≤ ((p : Equiv.Perm (Fin 10)) i).val := by
    apply FiniteChecks.five_le_of_ne_zero_one_two_three_four
    · simpa [hp0] using (p : Equiv.Perm (Fin 10)).injective.ne hi0
    · simpa [hp1] using (p : Equiv.Perm (Fin 10)).injective.ne hi1
    · simpa [hp2] using (p : Equiv.Perm (Fin 10)).injective.ne hi2
    · simpa [hp3] using (p : Equiv.Perm (Fin 10)).injective.ne hi3
    · simpa [hp7] using (p : Equiv.Perm (Fin 10)).injective.ne hi7
  let x : Fin 10 := (p : Equiv.Perm (Fin 10)) 4
  let y : Fin 10 := (p : Equiv.Perm (Fin 10)) 5
  let z : Fin 10 := (p : Equiv.Perm (Fin 10)) 6
  have hx : 5 ≤ x.val := by
    apply htail <;> decide
  have hy : 5 ≤ y.val := by
    apply htail <;> decide
  have hz : 5 ≤ z.val := by
    apply htail <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 10)).injective.ne (by decide)
  have hxz : x ≠ z :=
    (p : Equiv.Perm (Fin 10)).injective.ne (by decide)
  have hyz : y ≠ z :=
    (p : Equiv.Perm (Fin 10)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 10) :=
    (p : Equiv.Perm (Fin 10)) * FiniteChecks.sevenCycle *
      (p : Equiv.Perm (Fin 10))⁻¹
  have hh :
      h = FiniteChecks.comparisonCycle x y z := by
    change
      (p : Equiv.Perm (Fin 10)) * FiniteChecks.sevenCycle *
          (p : Equiv.Perm (Fin 10))⁻¹ =
        FiniteChecks.comparisonCycle x y z
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.sevenCycle,
      permCongr_formPerm]
    simp [FiniteChecks.comparisonCycle, x, y, z, hp0, hp1, hp2, hp3]
  have hhP : h ∈ P :=
    P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    FiniteChecks.exists_small_mem_closure x y z hx hy hz hxy hxz hyz
  have hclosure :
      Subgroup.closure
          ({FiniteChecks.sevenCycle,
            FiniteChecks.comparisonCycle x y z} :
            Set (Equiv.Perm (Fin 10))) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hg
    · rwa [← hh]
  have hwP : w ∈ P := hclosure hw
  have hwcore : w ∈ P.normalCore :=
    mem_normalCore_of_card_support_le_five (Fin 10) P h5
      (by rw [Fintype.card_fin]; norm_num) hwP hwsupport
  have hcoreNe : P.normalCore ≠ ⊥ := by
    intro hcore
    apply hwNe
    simpa [hcore] using hwcore
  have hcore : Nontrivial P.normalCore :=
    P.normalCore.nontrivial_iff_ne_bot.mpr hcoreNe
  exact (Equiv.Perm.alternatingGroup_le_of_normal
    (by rw [Nat.card_fin]; norm_num) hcore).trans
    P.normalCore_le

private theorem alternatingGroup_le_of_sevenCycle11_mem
    (P : Subgroup (Equiv.Perm (Fin 11)))
    (h5 : ∀ a b : Fin 5 → Fin 11,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.sevenCycle11 ∈ P) :
    alternatingGroup (Fin 11) ≤ P := by
  classical
  obtain ⟨p, hp⟩ := h5
    FiniteChecks.sourceTuple11 FiniteChecks.targetTuple11
    FiniteChecks.sourceTuple11_injective FiniteChecks.targetTuple11_injective
  have hp0 : (p : Equiv.Perm (Fin 11)) 0 = 0 := by
    simpa [FiniteChecks.sourceTuple11, FiniteChecks.targetTuple11,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (0 : Fin 5)
  have hp1 : (p : Equiv.Perm (Fin 11)) 1 = 1 := by
    simpa [FiniteChecks.sourceTuple11, FiniteChecks.targetTuple11,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (1 : Fin 5)
  have hp2 : (p : Equiv.Perm (Fin 11)) 2 = 2 := by
    simpa [FiniteChecks.sourceTuple11, FiniteChecks.targetTuple11,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (2 : Fin 5)
  have hp3 : (p : Equiv.Perm (Fin 11)) 3 = 3 := by
    simpa [FiniteChecks.sourceTuple11, FiniteChecks.targetTuple11,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (3 : Fin 5)
  have hp7 : (p : Equiv.Perm (Fin 11)) 7 = 4 := by
    simpa [FiniteChecks.sourceTuple11, FiniteChecks.targetTuple11,
      Subgroup.smul_def, Equiv.Perm.smul_def] using hp (4 : Fin 5)
  have htail (i : Fin 11)
      (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2)
      (hi3 : i ≠ 3) (hi7 : i ≠ 7) :
      5 ≤ ((p : Equiv.Perm (Fin 11)) i).val := by
    apply FiniteChecks.five_le_of_ne_zero_one_two_three_four11
    · simpa [hp0] using (p : Equiv.Perm (Fin 11)).injective.ne hi0
    · simpa [hp1] using (p : Equiv.Perm (Fin 11)).injective.ne hi1
    · simpa [hp2] using (p : Equiv.Perm (Fin 11)).injective.ne hi2
    · simpa [hp3] using (p : Equiv.Perm (Fin 11)).injective.ne hi3
    · simpa [hp7] using (p : Equiv.Perm (Fin 11)).injective.ne hi7
  let x : Fin 11 := (p : Equiv.Perm (Fin 11)) 4
  let y : Fin 11 := (p : Equiv.Perm (Fin 11)) 5
  let z : Fin 11 := (p : Equiv.Perm (Fin 11)) 6
  have hx : 5 ≤ x.val := by
    apply htail <;> decide
  have hy : 5 ≤ y.val := by
    apply htail <;> decide
  have hz : 5 ≤ z.val := by
    apply htail <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 11)).injective.ne (by decide)
  have hxz : x ≠ z :=
    (p : Equiv.Perm (Fin 11)).injective.ne (by decide)
  have hyz : y ≠ z :=
    (p : Equiv.Perm (Fin 11)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 11) :=
    (p : Equiv.Perm (Fin 11)) * FiniteChecks.sevenCycle11 *
      (p : Equiv.Perm (Fin 11))⁻¹
  have hh :
      h = FiniteChecks.comparisonCycle11 x y z := by
    change
      (p : Equiv.Perm (Fin 11)) * FiniteChecks.sevenCycle11 *
          (p : Equiv.Perm (Fin 11))⁻¹ =
        FiniteChecks.comparisonCycle11 x y z
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.sevenCycle11,
      permCongr_formPerm]
    simp [FiniteChecks.comparisonCycle11, x, y, z, hp0, hp1, hp2, hp3]
  have hhP : h ∈ P :=
    P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    FiniteChecks.exists_small_mem_closure11 x y z hx hy hz hxy hxz hyz
  have hclosure :
      Subgroup.closure
          ({FiniteChecks.sevenCycle11,
            FiniteChecks.comparisonCycle11 x y z} :
            Set (Equiv.Perm (Fin 11))) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hg
    · rwa [← hh]
  have hwP : w ∈ P := hclosure hw
  have hwcore : w ∈ P.normalCore :=
    mem_normalCore_of_card_support_le_five (Fin 11) P h5
      (by rw [Fintype.card_fin]; norm_num) hwP hwsupport
  have hcoreNe : P.normalCore ≠ ⊥ := by
    intro hcore
    apply hwNe
    simpa [hcore] using hwcore
  have hcore : Nontrivial P.normalCore :=
    P.normalCore.nontrivial_iff_ne_bot.mpr hcoreNe
  exact (Equiv.Perm.alternatingGroup_le_of_normal
    (by rw [Nat.card_fin]; norm_num) hcore).trans
    P.normalCore_le

private theorem alternatingGroup_le_of_sevenCycle12_mem
    (P : Subgroup (Equiv.Perm (Fin 12)))
    (h5 : ∀ a b : Fin 5 → Fin 12,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.sevenCycle12 ∈ P) :
    alternatingGroup (Fin 12) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator12 P h5
  let x : Fin 12 := (p : Equiv.Perm (Fin 12)) 4
  let y : Fin 12 := (p : Equiv.Perm (Fin 12)) 5
  let z : Fin 12 := (p : Equiv.Perm (Fin 12)) 6
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator12
      (p : Equiv.Perm (Fin 12)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator12
      (p : Equiv.Perm (Fin 12)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hz : 5 ≤ z.val := by
    apply five_le_image_of_controlled_conjugator12
      (p : Equiv.Perm (Fin 12)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 12)).injective.ne (by decide)
  have hxz : x ≠ z :=
    (p : Equiv.Perm (Fin 12)).injective.ne (by decide)
  have hyz : y ≠ z :=
    (p : Equiv.Perm (Fin 12)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 12) :=
    (p : Equiv.Perm (Fin 12)) * FiniteChecks.sevenCycle12 *
      (p : Equiv.Perm (Fin 12))⁻¹
  have hh : h = FiniteChecks.comparisonCycle12 x y z := by
    change
      (p : Equiv.Perm (Fin 12)) * FiniteChecks.sevenCycle12 *
          (p : Equiv.Perm (Fin 12))⁻¹ =
        FiniteChecks.comparisonCycle12 x y z
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.sevenCycle12,
      permCongr_formPerm]
    simp [FiniteChecks.comparisonCycle12, x, y, z, hp0, hp1, hp2, hp3]
  have hhP : h ∈ P :=
    P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    FiniteChecks.exists_small_mem_closure12 x y z hx hy hz hxy hxz hyz
  have hclosure :
      Subgroup.closure
          ({FiniteChecks.sevenCycle12,
            FiniteChecks.comparisonCycle12 x y z} :
            Set (Equiv.Perm (Fin 12))) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hg
    · rwa [← hh]
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 12) P h5 (by norm_num) (hclosure hw) hwNe hwsupport

private theorem alternatingGroup_le_of_tripleSwap12_mem
    (P : Subgroup (Equiv.Perm (Fin 12)))
    (h5 : ∀ a b : Fin 5 → Fin 12,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.tripleSwap12 ∈ P) :
    alternatingGroup (Fin 12) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator12 P h5
  let x : Fin 12 := (p : Equiv.Perm (Fin 12)) 4
  let y : Fin 12 := (p : Equiv.Perm (Fin 12)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator12
      (p : Equiv.Perm (Fin 12)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator12
      (p : Equiv.Perm (Fin 12)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 12)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 12) :=
    (p : Equiv.Perm (Fin 12)) * FiniteChecks.tripleSwap12 *
      (p : Equiv.Perm (Fin 12))⁻¹
  have hh : h = FiniteChecks.comparisonTripleSwap12 x y := by
    change
      (p : Equiv.Perm (Fin 12)) * FiniteChecks.tripleSwap12 *
          (p : Equiv.Perm (Fin 12))⁻¹ =
        FiniteChecks.comparisonTripleSwap12 x y
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.tripleSwap12,
      Equiv.permCongr_mul, Equiv.permCongr_mul,
      permCongr_formPerm, permCongr_formPerm, permCongr_formPerm]
    simp [FiniteChecks.comparisonTripleSwap12, x, y, hp0, hp1, hp2, hp3]
  have hhP : h ∈ P :=
    P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  let w :=
    FiniteChecks.tripleSwap12 *
      (FiniteChecks.comparisonTripleSwap12 x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.tripleSwap12_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rwa [← hh]
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 12) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_doubleThreeCycle12_mem
    (P : Subgroup (Equiv.Perm (Fin 12)))
    (h5 : ∀ a b : Fin 5 → Fin 12,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.doubleThreeCycle12 ∈ P) :
    alternatingGroup (Fin 12) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator12 P h5
  let x : Fin 12 := (p : Equiv.Perm (Fin 12)) 4
  let y : Fin 12 := (p : Equiv.Perm (Fin 12)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator12
      (p : Equiv.Perm (Fin 12)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator12
      (p : Equiv.Perm (Fin 12)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 12)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 12) :=
    (p : Equiv.Perm (Fin 12)) * FiniteChecks.doubleThreeCycle12 *
      (p : Equiv.Perm (Fin 12))⁻¹
  have hh : h = FiniteChecks.comparisonDoubleThreeCycle12 x y := by
    change
      (p : Equiv.Perm (Fin 12)) * FiniteChecks.doubleThreeCycle12 *
          (p : Equiv.Perm (Fin 12))⁻¹ =
        FiniteChecks.comparisonDoubleThreeCycle12 x y
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.doubleThreeCycle12,
      Equiv.permCongr_mul, permCongr_formPerm, permCongr_formPerm]
    simp [FiniteChecks.comparisonDoubleThreeCycle12, x, y,
      hp0, hp1, hp2, hp3]
  have hhP : h ∈ P :=
    P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  let w :=
    FiniteChecks.doubleThreeCycle12 *
      (FiniteChecks.comparisonDoubleThreeCycle12 x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.doubleThreeCycle12_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rwa [← hh]
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 12) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_sevenCycle13_mem
    (P : Subgroup (Equiv.Perm (Fin 13)))
    (h5 : ∀ a b : Fin 5 → Fin 13,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.sevenCycle13 ∈ P) :
    alternatingGroup (Fin 13) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator13 P h5
  let x : Fin 13 := (p : Equiv.Perm (Fin 13)) 4
  let y : Fin 13 := (p : Equiv.Perm (Fin 13)) 5
  let z : Fin 13 := (p : Equiv.Perm (Fin 13)) 6
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator13
      (p : Equiv.Perm (Fin 13)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator13
      (p : Equiv.Perm (Fin 13)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hz : 5 ≤ z.val := by
    apply five_le_image_of_controlled_conjugator13
      (p : Equiv.Perm (Fin 13)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 13)).injective.ne (by decide)
  have hxz : x ≠ z :=
    (p : Equiv.Perm (Fin 13)).injective.ne (by decide)
  have hyz : y ≠ z :=
    (p : Equiv.Perm (Fin 13)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 13) :=
    (p : Equiv.Perm (Fin 13)) * FiniteChecks.sevenCycle13 *
      (p : Equiv.Perm (Fin 13))⁻¹
  have hh : h = FiniteChecks.comparisonCycle13 x y z := by
    change
      (p : Equiv.Perm (Fin 13)) * FiniteChecks.sevenCycle13 *
          (p : Equiv.Perm (Fin 13))⁻¹ =
        FiniteChecks.comparisonCycle13 x y z
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.sevenCycle13,
      permCongr_formPerm]
    simp [FiniteChecks.comparisonCycle13, x, y, z, hp0, hp1, hp2, hp3]
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    FiniteChecks.exists_small_mem_closure13 x y z hx hy hz hxy hxz hyz
  have hclosure :
      Subgroup.closure
          ({FiniteChecks.sevenCycle13,
            FiniteChecks.comparisonCycle13 x y z} :
            Set (Equiv.Perm (Fin 13))) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hg
    · rw [← hh]
      exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 13) P h5 (by norm_num) (hclosure hw) hwNe hwsupport

private theorem alternatingGroup_le_of_tripleSwap13_mem
    (P : Subgroup (Equiv.Perm (Fin 13)))
    (h5 : ∀ a b : Fin 5 → Fin 13,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.tripleSwap13 ∈ P) :
    alternatingGroup (Fin 13) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator13 P h5
  let x : Fin 13 := (p : Equiv.Perm (Fin 13)) 4
  let y : Fin 13 := (p : Equiv.Perm (Fin 13)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator13
      (p : Equiv.Perm (Fin 13)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator13
      (p : Equiv.Perm (Fin 13)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 13)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 13) :=
    (p : Equiv.Perm (Fin 13)) * FiniteChecks.tripleSwap13 *
      (p : Equiv.Perm (Fin 13))⁻¹
  have hh : h = FiniteChecks.comparisonTripleSwap13 x y := by
    change
      (p : Equiv.Perm (Fin 13)) * FiniteChecks.tripleSwap13 *
          (p : Equiv.Perm (Fin 13))⁻¹ =
        FiniteChecks.comparisonTripleSwap13 x y
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.tripleSwap13,
      Equiv.permCongr_mul, Equiv.permCongr_mul,
      permCongr_formPerm, permCongr_formPerm, permCongr_formPerm]
    simp [FiniteChecks.comparisonTripleSwap13, x, y, hp0, hp1, hp2, hp3]
  let w :=
    FiniteChecks.tripleSwap13 *
      (FiniteChecks.comparisonTripleSwap13 x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.tripleSwap13_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 13) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_doubleThreeCycle13_mem
    (P : Subgroup (Equiv.Perm (Fin 13)))
    (h5 : ∀ a b : Fin 5 → Fin 13,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.doubleThreeCycle13 ∈ P) :
    alternatingGroup (Fin 13) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator13 P h5
  let x : Fin 13 := (p : Equiv.Perm (Fin 13)) 4
  let y : Fin 13 := (p : Equiv.Perm (Fin 13)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator13
      (p : Equiv.Perm (Fin 13)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator13
      (p : Equiv.Perm (Fin 13)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 13)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 13) :=
    (p : Equiv.Perm (Fin 13)) * FiniteChecks.doubleThreeCycle13 *
      (p : Equiv.Perm (Fin 13))⁻¹
  have hh : h = FiniteChecks.comparisonDoubleThreeCycle13 x y := by
    change
      (p : Equiv.Perm (Fin 13)) * FiniteChecks.doubleThreeCycle13 *
          (p : Equiv.Perm (Fin 13))⁻¹ =
        FiniteChecks.comparisonDoubleThreeCycle13 x y
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.doubleThreeCycle13,
      Equiv.permCongr_mul, permCongr_formPerm, permCongr_formPerm]
    simp [FiniteChecks.comparisonDoubleThreeCycle13, x, y,
      hp0, hp1, hp2, hp3]
  let w :=
    FiniteChecks.doubleThreeCycle13 *
      (FiniteChecks.comparisonDoubleThreeCycle13 x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.doubleThreeCycle13_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 13) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_sevenCycle14_mem
    (P : Subgroup (Equiv.Perm (Fin 14)))
    (h5 : ∀ a b : Fin 5 → Fin 14,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.sevenCycle14 ∈ P) :
    alternatingGroup (Fin 14) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator14 P h5
  let x : Fin 14 := (p : Equiv.Perm (Fin 14)) 4
  let y : Fin 14 := (p : Equiv.Perm (Fin 14)) 5
  let z : Fin 14 := (p : Equiv.Perm (Fin 14)) 6
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator14
      (p : Equiv.Perm (Fin 14)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator14
      (p : Equiv.Perm (Fin 14)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hz : 5 ≤ z.val := by
    apply five_le_image_of_controlled_conjugator14
      (p : Equiv.Perm (Fin 14)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 14)).injective.ne (by decide)
  have hxz : x ≠ z :=
    (p : Equiv.Perm (Fin 14)).injective.ne (by decide)
  have hyz : y ≠ z :=
    (p : Equiv.Perm (Fin 14)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 14) :=
    (p : Equiv.Perm (Fin 14)) * FiniteChecks.sevenCycle14 *
      (p : Equiv.Perm (Fin 14))⁻¹
  have hh : h = FiniteChecks.comparisonCycle14 x y z := by
    change
      (p : Equiv.Perm (Fin 14)) * FiniteChecks.sevenCycle14 *
          (p : Equiv.Perm (Fin 14))⁻¹ =
        FiniteChecks.comparisonCycle14 x y z
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.sevenCycle14,
      permCongr_formPerm]
    simp [FiniteChecks.comparisonCycle14, x, y, z, hp0, hp1, hp2, hp3]
  obtain ⟨w, hw, hwNe, hwsupport⟩ :=
    FiniteChecks.exists_small_mem_closure14 x y z hx hy hz hxy hxz hyz
  have hclosure :
      Subgroup.closure
          ({FiniteChecks.sevenCycle14,
            FiniteChecks.comparisonCycle14 x y z} :
            Set (Equiv.Perm (Fin 14))) ≤ P := by
    rw [Subgroup.closure_le]
    intro u hu
    rcases hu with (rfl | rfl)
    · exact hg
    · rw [← hh]
      exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 14) P h5 (by norm_num) (hclosure hw) hwNe hwsupport

private theorem alternatingGroup_le_of_tripleSwap14_mem
    (P : Subgroup (Equiv.Perm (Fin 14)))
    (h5 : ∀ a b : Fin 5 → Fin 14,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.tripleSwap14 ∈ P) :
    alternatingGroup (Fin 14) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator14 P h5
  let x : Fin 14 := (p : Equiv.Perm (Fin 14)) 4
  let y : Fin 14 := (p : Equiv.Perm (Fin 14)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator14
      (p : Equiv.Perm (Fin 14)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator14
      (p : Equiv.Perm (Fin 14)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 14)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 14) :=
    (p : Equiv.Perm (Fin 14)) * FiniteChecks.tripleSwap14 *
      (p : Equiv.Perm (Fin 14))⁻¹
  have hh : h = FiniteChecks.comparisonTripleSwap14 x y := by
    change
      (p : Equiv.Perm (Fin 14)) * FiniteChecks.tripleSwap14 *
          (p : Equiv.Perm (Fin 14))⁻¹ =
        FiniteChecks.comparisonTripleSwap14 x y
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.tripleSwap14,
      Equiv.permCongr_mul, Equiv.permCongr_mul,
      permCongr_formPerm, permCongr_formPerm, permCongr_formPerm]
    simp [FiniteChecks.comparisonTripleSwap14, x, y, hp0, hp1, hp2, hp3]
  let w :=
    FiniteChecks.tripleSwap14 *
      (FiniteChecks.comparisonTripleSwap14 x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.tripleSwap14_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 14) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_doubleThreeCycle14_mem
    (P : Subgroup (Equiv.Perm (Fin 14)))
    (h5 : ∀ a b : Fin 5 → Fin 14,
      Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hg : FiniteChecks.doubleThreeCycle14 ∈ P) :
    alternatingGroup (Fin 14) ≤ P := by
  classical
  obtain ⟨p, hp0, hp1, hp2, hp3, hp7⟩ :=
    exists_controlled_conjugator14 P h5
  let x : Fin 14 := (p : Equiv.Perm (Fin 14)) 4
  let y : Fin 14 := (p : Equiv.Perm (Fin 14)) 5
  have hx : 5 ≤ x.val := by
    apply five_le_image_of_controlled_conjugator14
      (p : Equiv.Perm (Fin 14)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hy : 5 ≤ y.val := by
    apply five_le_image_of_controlled_conjugator14
      (p : Equiv.Perm (Fin 14)) hp0 hp1 hp2 hp3 hp7 <;> decide
  have hxy : x ≠ y :=
    (p : Equiv.Perm (Fin 14)).injective.ne (by decide)
  let h : Equiv.Perm (Fin 14) :=
    (p : Equiv.Perm (Fin 14)) * FiniteChecks.doubleThreeCycle14 *
      (p : Equiv.Perm (Fin 14))⁻¹
  have hh : h = FiniteChecks.comparisonDoubleThreeCycle14 x y := by
    change
      (p : Equiv.Perm (Fin 14)) * FiniteChecks.doubleThreeCycle14 *
          (p : Equiv.Perm (Fin 14))⁻¹ =
        FiniteChecks.comparisonDoubleThreeCycle14 x y
    rw [← Equiv.permCongr_eq_mul, FiniteChecks.doubleThreeCycle14,
      Equiv.permCongr_mul, permCongr_formPerm, permCongr_formPerm]
    simp [FiniteChecks.comparisonDoubleThreeCycle14, x, y,
      hp0, hp1, hp2, hp3]
  let w :=
    FiniteChecks.doubleThreeCycle14 *
      (FiniteChecks.comparisonDoubleThreeCycle14 x y)⁻¹
  obtain ⟨hwNe, hwsupport⟩ :=
    FiniteChecks.doubleThreeCycle14_difference_small x y hx hy hxy
  have hwP : w ∈ P := by
    apply P.mul_mem hg
    apply P.inv_mem
    rw [← hh]
    exact P.mul_mem (P.mul_mem p.prop hg) (P.inv_mem p.prop)
  exact alternatingGroup_le_of_nontrivial_card_support_le_five
    (Fin 14) P h5 (by norm_num) hwP hwNe hwsupport

private theorem alternatingGroup_le_of_cycleType_eq_fin_twelve
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 12)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (c : Equiv.Perm (Fin 12))
    (hcycleType :
      ((Fintype.equivFinOfCardEq hcard).permCongr g).cycleType =
        c.cycleType)
    (hforce :
      ∀ Q : Subgroup (Equiv.Perm (Fin 12)),
        (∀ a b : Fin 5 → Fin 12,
          Function.Injective a → Function.Injective b →
          ∃ q : Q, ∀ i, q • a i = b i) →
        c ∈ Q → alternatingGroup (Fin 12) ≤ Q) :
    alternatingGroup X ≤ P := by
  classical
  let e₀ : X ≃ Fin 12 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 12) := e₀.permCongr g
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let e : X ≃ Fin 12 := e₀.trans k
  let P' : Subgroup (Equiv.Perm (Fin 12)) :=
    P.map e.permCongrHom
  have hemapg : e.permCongr g = c := by
    change k * g₁ * k⁻¹ = c
    exact hk
  have hc : c ∈ P' := by
    rw [Subgroup.mem_map]
    exact ⟨g, hg, hemapg⟩
  have h5P' :
      ∀ a b : Fin 5 → Fin 12,
        Function.Injective a → Function.Injective b →
        ∃ q : P', ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' : Function.Injective (fun i => e.symm (a i)) :=
      e.symm.injective.comp ha
    have hb' : Function.Injective (fun i => e.symm (b i)) :=
      e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := h5
      (fun i => e.symm (a i)) (fun i => e.symm (b i)) ha' hb'
    let q' : Equiv.Perm (Fin 12) := e.permCongr (q : Equiv.Perm X)
    have hq'P : q' ∈ P' := by
      change e.permCongr (q : Equiv.Perm X) ∈ P.map e.permCongrHom
      exact Subgroup.mem_map_of_mem e.permCongrHom.toMonoidHom q.prop
    refine ⟨⟨q', hq'P⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (e.symm (a i)) = e.symm (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      Equiv.permCongr_apply] using congrArg e hqi
  have hAlt' : alternatingGroup (Fin 12) ≤ P' :=
    hforce P' h5P' hc
  intro σ hσ
  let σ' : Equiv.Perm (Fin 12) := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup (Fin 12) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simpa [σ', Equiv.Perm.sign_permCongr] using hσ
  have hmapped : σ' ∈ P' := hAlt' hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ := e.permCongrHom.injective (by
    simpa [σ'] using hτσ)
  rwa [← hτeq]

private theorem alternatingGroup_le_of_cycleType_eq_fin_thirteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 13)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (c : Equiv.Perm (Fin 13))
    (hcycleType :
      ((Fintype.equivFinOfCardEq hcard).permCongr g).cycleType =
        c.cycleType)
    (hforce :
      ∀ Q : Subgroup (Equiv.Perm (Fin 13)),
        (∀ a b : Fin 5 → Fin 13,
          Function.Injective a → Function.Injective b →
          ∃ q : Q, ∀ i, q • a i = b i) →
        c ∈ Q → alternatingGroup (Fin 13) ≤ Q) :
    alternatingGroup X ≤ P := by
  classical
  let e₀ : X ≃ Fin 13 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 13) := e₀.permCongr g
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let e : X ≃ Fin 13 := e₀.trans k
  let P' : Subgroup (Equiv.Perm (Fin 13)) :=
    P.map e.permCongrHom
  have hemapg : e.permCongr g = c := by
    change k * g₁ * k⁻¹ = c
    exact hk
  have hc : c ∈ P' := by
    rw [Subgroup.mem_map]
    exact ⟨g, hg, hemapg⟩
  have h5P' :
      ∀ a b : Fin 5 → Fin 13,
        Function.Injective a → Function.Injective b →
        ∃ q : P', ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' : Function.Injective (fun i => e.symm (a i)) :=
      e.symm.injective.comp ha
    have hb' : Function.Injective (fun i => e.symm (b i)) :=
      e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := h5
      (fun i => e.symm (a i)) (fun i => e.symm (b i)) ha' hb'
    let q' : Equiv.Perm (Fin 13) := e.permCongr (q : Equiv.Perm X)
    have hq'P : q' ∈ P' := by
      change e.permCongr (q : Equiv.Perm X) ∈ P.map e.permCongrHom
      exact Subgroup.mem_map_of_mem e.permCongrHom.toMonoidHom q.prop
    refine ⟨⟨q', hq'P⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (e.symm (a i)) = e.symm (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      Equiv.permCongr_apply] using congrArg e hqi
  have hAlt' : alternatingGroup (Fin 13) ≤ P' :=
    hforce P' h5P' hc
  intro σ hσ
  let σ' : Equiv.Perm (Fin 13) := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup (Fin 13) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simpa [σ', Equiv.Perm.sign_permCongr] using hσ
  have hmapped : σ' ∈ P' := hAlt' hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ := e.permCongrHom.injective (by
    simpa [σ'] using hτσ)
  rwa [← hτeq]

private theorem alternatingGroup_le_of_cycleType_eq_fin_fourteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    (c : Equiv.Perm (Fin 14))
    (hcycleType :
      ((Fintype.equivFinOfCardEq hcard).permCongr g).cycleType =
        c.cycleType)
    (hforce :
      ∀ Q : Subgroup (Equiv.Perm (Fin 14)),
        (∀ a b : Fin 5 → Fin 14,
          Function.Injective a → Function.Injective b →
          ∃ q : Q, ∀ i, q • a i = b i) →
        c ∈ Q → alternatingGroup (Fin 14) ≤ Q) :
    alternatingGroup X ≤ P := by
  classical
  let e₀ : X ≃ Fin 14 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 14) := e₀.permCongr g
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let e : X ≃ Fin 14 := e₀.trans k
  let P' : Subgroup (Equiv.Perm (Fin 14)) :=
    P.map e.permCongrHom
  have hemapg : e.permCongr g = c := by
    change k * g₁ * k⁻¹ = c
    exact hk
  have hc : c ∈ P' := by
    rw [Subgroup.mem_map]
    exact ⟨g, hg, hemapg⟩
  have h5P' :
      ∀ a b : Fin 5 → Fin 14,
        Function.Injective a → Function.Injective b →
        ∃ q : P', ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' : Function.Injective (fun i => e.symm (a i)) :=
      e.symm.injective.comp ha
    have hb' : Function.Injective (fun i => e.symm (b i)) :=
      e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := h5
      (fun i => e.symm (a i)) (fun i => e.symm (b i)) ha' hb'
    let q' : Equiv.Perm (Fin 14) := e.permCongr (q : Equiv.Perm X)
    have hq'P : q' ∈ P' := by
      change e.permCongr (q : Equiv.Perm X) ∈ P.map e.permCongrHom
      exact Subgroup.mem_map_of_mem e.permCongrHom.toMonoidHom q.prop
    refine ⟨⟨q', hq'P⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (e.symm (a i)) = e.symm (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      Equiv.permCongr_apply] using congrArg e hqi
  have hAlt' : alternatingGroup (Fin 14) ≤ P' :=
    hforce P' h5P' hc
  intro σ hσ
  let σ' : Equiv.Perm (Fin 14) := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup (Fin 14) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simpa [σ', Equiv.Perm.sign_permCongr] using hσ
  have hmapped : σ' ∈ P' := hAlt' hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ := e.permCongrHom.injective (by
    simpa [σ'] using hτσ)
  rwa [← hτeq]

private theorem alternatingGroup_le_of_prime_order_support_le_seven13
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 13)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    {p : ℕ} (hp : p.Prime) (hgorder : orderOf g = p)
    (hsupport : g.support.card ≤ 7) :
    alternatingGroup X ≤ P := by
  classical
  have hgNe : g ≠ 1 := by
    intro hgone
    rw [hgone, orderOf_one] at hgorder
    exact hp.ne_one hgorder.symm
  by_cases hsmall : g.support.card ≤ 5
  · exact alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 (by omega) hg hgNe hsmall
  have hsupp : g.support.card = 6 ∨ g.support.card = 7 := by
    omega
  let e₀ : X ≃ Fin 13 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 13) := e₀.permCongr g
  have hg₁order : orderOf g₁ = p := by
    calc
      orderOf g₁ = orderOf g := e₀.permCongrHom.orderOf_eq g
      _ = p := hgorder
  have hg₁prime : (orderOf g₁).Prime := by
    rw [hg₁order]
    exact hp
  have hsupportMap :
      g₁.support = g.support.map e₀.toEmbedding := by
    ext y
    simp [g₁, Equiv.Perm.mem_support, Equiv.permCongr_apply]
    constructor
    · intro h h'
      apply h
      rw [h', e₀.apply_symm_apply]
    · intro h h'
      apply h
      apply e₀.injective
      simpa using h'
  have hg₁support : g₁.support.card = g.support.card := by
    rw [hsupportMap, Finset.card_map]
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order hg₁prime
  have hsum := g₁.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    hg₁order, hg₁support] at hsum
  rcases hsupp with hsupp | hsupp
  · have hp_le : p ≤ 6 := by
      nlinarith [Nat.zero_le m]
    interval_cases p
    all_goals norm_num at hp
    · have hm' : m + 1 = 3 := by omega
      have hcycle :
          g₁.cycleType = FiniteChecks.tripleSwap13.cycleType := by
        rw [hm, hg₁order, hm', FiniteChecks.tripleSwap13_cycleType]
        norm_num
      apply alternatingGroup_le_of_cycleType_eq_fin_thirteen
        X P hcard h5 hg FiniteChecks.tripleSwap13
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_tripleSwap13_mem
    · have hm' : m + 1 = 2 := by omega
      have hcycle :
          g₁.cycleType =
            FiniteChecks.doubleThreeCycle13.cycleType := by
        rw [hm, hg₁order, hm',
          FiniteChecks.doubleThreeCycle13_cycleType]
        norm_num
      apply alternatingGroup_le_of_cycleType_eq_fin_thirteen
        X P hcard h5 hg FiniteChecks.doubleThreeCycle13
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_doubleThreeCycle13_mem
    · omega
  · have hp_le : p ≤ 7 := by
      nlinarith [Nat.zero_le m]
    interval_cases p
    all_goals norm_num at hp
    · omega
    · omega
    · omega
    · have hm' : m + 1 = 1 := by omega
      have hg₁cycle : g₁.IsCycle := by
        rw [← Equiv.Perm.card_cycleType_eq_one, hm,
          Multiset.card_replicate, hm']
      have hcycle :
          g₁.cycleType = FiniteChecks.sevenCycle13.cycleType := by
        rw [hg₁cycle.cycleType,
          FiniteChecks.sevenCycle13_isCycle.cycleType,
          hg₁support, hsupp,
          FiniteChecks.sevenCycle13_card_support]
      apply alternatingGroup_le_of_cycleType_eq_fin_thirteen
        X P hcard h5 hg FiniteChecks.sevenCycle13
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_sevenCycle13_mem

private theorem alternatingGroup_le_of_prime_order_support_le_seven14
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {g : Equiv.Perm X} (hg : g ∈ P)
    {p : ℕ} (hp : p.Prime) (hgorder : orderOf g = p)
    (hsupport : g.support.card ≤ 7) :
    alternatingGroup X ≤ P := by
  classical
  have hgNe : g ≠ 1 := by
    intro hgone
    rw [hgone, orderOf_one] at hgorder
    exact hp.ne_one hgorder.symm
  by_cases hsmall : g.support.card ≤ 5
  · exact alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 (by omega) hg hgNe hsmall
  have hsupp : g.support.card = 6 ∨ g.support.card = 7 := by
    omega
  let e₀ : X ≃ Fin 14 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 14) := e₀.permCongr g
  have hg₁order : orderOf g₁ = p := by
    calc
      orderOf g₁ = orderOf g := e₀.permCongrHom.orderOf_eq g
      _ = p := hgorder
  have hg₁prime : (orderOf g₁).Prime := by
    rw [hg₁order]
    exact hp
  have hsupportMap :
      g₁.support = g.support.map e₀.toEmbedding := by
    ext y
    simp [g₁, Equiv.Perm.mem_support, Equiv.permCongr_apply]
    constructor
    · intro h h'
      apply h
      rw [h', e₀.apply_symm_apply]
    · intro h h'
      apply h
      apply e₀.injective
      simpa using h'
  have hg₁support : g₁.support.card = g.support.card := by
    rw [hsupportMap, Finset.card_map]
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order hg₁prime
  have hsum := g₁.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    hg₁order, hg₁support] at hsum
  rcases hsupp with hsupp | hsupp
  · have hp_le : p ≤ 6 := by
      nlinarith [Nat.zero_le m]
    interval_cases p
    all_goals norm_num at hp
    · have hm' : m + 1 = 3 := by omega
      have hcycle :
          g₁.cycleType = FiniteChecks.tripleSwap14.cycleType := by
        rw [hm, hg₁order, hm', FiniteChecks.tripleSwap14_cycleType]
        norm_num
      apply alternatingGroup_le_of_cycleType_eq_fin_fourteen
        X P hcard h5 hg FiniteChecks.tripleSwap14
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_tripleSwap14_mem
    · have hm' : m + 1 = 2 := by omega
      have hcycle :
          g₁.cycleType =
            FiniteChecks.doubleThreeCycle14.cycleType := by
        rw [hm, hg₁order, hm',
          FiniteChecks.doubleThreeCycle14_cycleType]
        norm_num
      apply alternatingGroup_le_of_cycleType_eq_fin_fourteen
        X P hcard h5 hg FiniteChecks.doubleThreeCycle14
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_doubleThreeCycle14_mem
    · omega
  · have hp_le : p ≤ 7 := by
      nlinarith [Nat.zero_le m]
    interval_cases p
    all_goals norm_num at hp
    · omega
    · omega
    · omega
    · have hm' : m + 1 = 1 := by omega
      have hg₁cycle : g₁.IsCycle := by
        rw [← Equiv.Perm.card_cycleType_eq_one, hm,
          Multiset.card_replicate, hm']
      have hcycle :
          g₁.cycleType = FiniteChecks.sevenCycle14.cycleType := by
        rw [hg₁cycle.cycleType,
          FiniteChecks.sevenCycle14_isCycle.cycleType,
          hg₁support, hsupp,
          FiniteChecks.sevenCycle14_card_support]
      apply alternatingGroup_le_of_cycleType_eq_fin_fourteen
        X P hcard h5 hg FiniteChecks.sevenCycle14
      · simpa [e₀, g₁] using hcycle
      · exact alternatingGroup_le_of_sevenCycle14_mem

private theorem prime_order_support_le_eight_of_not_alternating14
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {g : Equiv.Perm X} (hg : g ∈ P)
    {p : ℕ} (hp : p.Prime) (hgorder : orderOf g = p)
    (hsupport : g.support.card ≤ 8) :
    p = 2 ∧ g.support.card = 8 := by
  have hnotSmall : ¬g.support.card ≤ 7 := by
    intro hsmall
    exact hnotAlt (alternatingGroup_le_of_prime_order_support_le_seven14
      X P hcard h5 hg hp hgorder hsmall)
  have hsuppEq : g.support.card = 8 := by
    omega
  refine ⟨?_, hsuppEq⟩
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    exact hp
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    hgorder, hsuppEq] at hsum
  have hp_le : p ≤ 8 := by
    nlinarith [Nat.zero_le m]
  interval_cases p
  all_goals norm_num at hp
  all_goals omega

private theorem prime_order_support_le_nine_of_not_alternating14
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {g : Equiv.Perm X} (hg : g ∈ P)
    {p : ℕ} (hp : p.Prime) (hgorder : orderOf g = p)
    (hsupport : g.support.card ≤ 9) :
    (p = 2 ∧ g.support.card = 8) ∨
      (p = 3 ∧ g.support.card = 9) := by
  by_cases hsmall : g.support.card ≤ 8
  · exact Or.inl (prime_order_support_le_eight_of_not_alternating14
      X P hcard h5 hnotAlt hg hp hgorder hsmall)
  have hsuppEq : g.support.card = 9 := by
    omega
  right
  refine ⟨?_, hsuppEq⟩
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    exact hp
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    hgorder, hsuppEq] at hsum
  have hp_le : p ≤ 9 := by
    nlinarith [Nat.zero_le m]
  interval_cases p
  all_goals norm_num at hp
  all_goals omega

theorem inf_stabilizer_subsingleton_of_not_alternating14
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5)
    (y z : SubMulAction.ofFixingSubgroup P s) (hyz : y ≠ z) :
    Subsingleton ↥
      (MulAction.stabilizer (fixingSubgroup P s) y ⊓
        MulAction.stabilizer (fixingSubgroup P s) z) := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  let M : Subgroup K :=
    MulAction.stabilizer K y ⊓ MulAction.stabilizer K z
  rw [← not_nontrivial_iff_subsingleton]
  intro hM
  have hMcard : 1 < Nat.card M :=
    Finite.one_lt_card_iff_nontrivial.mpr hM
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (n := Nat.card M) (by omega)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  let g : Equiv.Perm X := (((u : M) : K) : P)
  have hgorder : orderOf g = p := by
    calc
      orderOf g = orderOf (((u : M) : K) : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf ((u : M) : K) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = p := hu
  have hgP : g ∈ P := (((u : M) : K) : P).prop
  have hfix :
      ∀ x ∈ s, (((u : M) : K) : P) • x = x :=
    (mem_fixingSubgroup_iff P).mp ((u : M) : K).prop
  have huStabilizers :
      ((u : M) : K) ∈ MulAction.stabilizer K y ∧
        ((u : M) : K) ∈ MulAction.stabilizer K z :=
    Subgroup.mem_inf.mp u.prop
  have hyfixSubtype : ((u : M) : K) • y = y :=
    MulAction.mem_stabilizer_iff.mp huStabilizers.1
  have hzfixSubtype : ((u : M) : K) • z = z :=
    MulAction.mem_stabilizer_iff.mp huStabilizers.2
  have hyfix :
      (((u : M) : K) : P) • (y : X) = y :=
    congrArg Subtype.val hyfixSubtype
  have hzfix :
      (((u : M) : K) : P) • (z : X) = z :=
    congrArg Subtype.val hzfixSubtype
  have hyNotS : (y : X) ∉ s := y.prop
  have hzNotS : (z : X) ∉ s := z.prop
  have hyzX : (y : X) ≠ (z : X) := by
    intro h
    exact hyz (Subtype.ext h)
  let t : Set X := Set.insert (y : X) (Set.insert (z : X) s)
  have hyNotInsert : (y : X) ∉ Set.insert (z : X) s := by
    intro hy
    change (y : X) = (z : X) ∨ (y : X) ∈ s at hy
    exact hy.elim hyzX hyNotS
  have htcard : t.ncard = 7 := by
    change (Set.insert (y : X) (Set.insert (z : X) s)).ncard = 7
    calc
      _ = (Set.insert (z : X) s).ncard + 1 :=
        Set.ncard_insert_of_notMem hyNotInsert
      _ = (s.ncard + 1) + 1 :=
        congrArg (fun n => n + 1)
          (Set.ncard_insert_of_notMem hzNotS)
      _ = 7 := by omega
  have hsuppSubset : (g.support : Set X) ⊆ tᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    change x ∉ Set.insert (y : X) (Set.insert (z : X) s)
    intro hxt
    change x = (y : X) ∨ x = (z : X) ∨ x ∈ s at hxt
    rcases hxt with rfl | rfl | hxs
    · exact Equiv.Perm.mem_support.mp hx hyfix
    · exact Equiv.Perm.mem_support.mp hx hzfix
    · exact Equiv.Perm.mem_support.mp hx (hfix x hxs)
  have htcomplement : tᶜ.ncard = 7 := by
    have htotal := Set.ncard_add_ncard_compl t
    rw [Nat.card_eq_fintype_card, hcard, htcard] at htotal
    omega
  have hsuppCard : g.support.card ≤ 7 := by
    rw [← Set.ncard_coe_finset]
    exact (Set.ncard_le_ncard hsuppSubset).trans_eq htcomplement
  exact hnotAlt (alternatingGroup_le_of_prime_order_support_le_seven14
    X P hcard h5 hgP hp hgorder hsuppCard)

theorem prime_dvd_five_point_stabilizer_eq_two_or_three_of_not_alternating14
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 14)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    {s : Set X} (hs : s.ncard = 5)
    {p : ℕ} (hp : p.Prime)
    (hpdvd : p ∣ Nat.card (fixingSubgroup P s)) :
    p = 2 ∨ p = 3 := by
  classical
  let K : Subgroup P := fixingSubgroup P s
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  let g : Equiv.Perm X := ((u : K) : P)
  have hgorder : orderOf g = p := by
    calc
      orderOf g = orderOf ((u : K) : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = p := hu
  have hgP : g ∈ P := ((u : K) : P).prop
  have hfix :
      ∀ x ∈ s, ((u : K) : P) • x = x :=
    (mem_fixingSubgroup_iff P).mp u.prop
  have hsuppSubset : (g.support : Set X) ⊆ sᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxs
    apply Equiv.Perm.mem_support.mp hx
    exact hfix x hxs
  have hcomplement : sᶜ.ncard = 9 := by
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hsuppCard : g.support.card ≤ 9 := by
    rw [← Set.ncard_coe_finset]
    exact (Set.ncard_le_ncard hsuppSubset).trans_eq hcomplement
  rcases prime_order_support_le_nine_of_not_alternating14
      X P hcard h5 hnotAlt hgP hp hgorder hsuppCard with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem not_card_eq_five_tuple_mul_small_two_power_of_card_thirteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 13)
    (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8)
    (hPcard : Nat.card P = 154440 * k) :
    False := by
  classical
  rcases hk with rfl | rfl | rfl | rfl
  all_goals
    letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    let S : Sylow 13 P := Sylow.nonempty.some
    have hScard : Nat.card S = 13 := by
      rw [S.card_eq_multiplicity, hPcard]
      rw [show 154440 = 13 * 11880 by norm_num, Nat.mul_assoc,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, (show Nat.Prime 13 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num
    letI : IsCyclic S := isCyclic_of_prime_card hScard
    letI : IsMulCommutative S := IsCyclic.isMulCommutative
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
    have huorder : orderOf u = 13 := hu.trans hScard
    let g : Equiv.Perm X := (u : P)
    have hgorder : orderOf g = 13 := by
      calc
        orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
        _ = orderOf u := Subgroup.orderOf_coe _
        _ = 13 := huorder
    have hgprime : (orderOf g).Prime := by
      rw [hgorder]
      norm_num
    have hgcycle : g.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order' hgprime (by
        rw [hcard, hgorder]
        norm_num)
    have hgsupport : g.support.card = 13 := by
      rw [← hgcycle.orderOf, hgorder]
    have hcentralizerPerm :
        Nat.card (Subgroup.centralizer
          ({g} : Set (Equiv.Perm X))) = 13 := by
      rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
        hgsupport, hcard]
      norm_num
    let C : Subgroup P :=
      Subgroup.centralizer (S : Set P)
    have hSC : (S : Subgroup P) ≤ C := by
      exact Subgroup.le_centralizer (S : Subgroup P)
    let baseMap : C →* Equiv.Perm X :=
      P.subtype.comp C.subtype
    have hbaseMapMem :
        ∀ c : C, baseMap c ∈
          Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
      intro c
      change ((c.1 : P) : Equiv.Perm X) ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((c.2 (u : P) u.prop).symm)
    let centMap :
        C →* Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
      baseMap.codRestrict
        (Subgroup.centralizer ({g} : Set (Equiv.Perm X))) hbaseMapMem
    have hcentMapInjective : Function.Injective centMap := by
      intro a b hab
      have hab' := congrArg Subtype.val hab
      change baseMap a = baseMap b at hab'
      exact C.subtype_injective (P.subtype_injective hab')
    have hCdiv13 : Nat.card C ∣ 13 := by
      rw [← hcentralizerPerm]
      exact Subgroup.card_dvd_of_injective centMap hcentMapInjective
    have h13divC : 13 ∣ Nat.card C := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le hSC
    have hCcard : Nat.card C = 13 := by
      exact Nat.dvd_antisymm hCdiv13 h13divC
    have hAutCard : Nat.card (MulAut S) = 12 := by
      rw [IsCyclic.card_mulAut S, hScard,
        Nat.totient_prime (by norm_num)]
    have hrangeDvd :
        Nat.card S.normalizerMonoidHom.range ∣ 12 := by
      rw [← hAutCard]
      exact Subgroup.card_subgroup_dvd_card _
    have hrEq :
        C.relIndex (Subgroup.normalizer (S : Set P)) =
          Nat.card S.normalizerMonoidHom.range := by
      change
        (Subgroup.centralizer (S : Set P)).relIndex
            (Subgroup.normalizer (S : Set P)) =
          Nat.card S.normalizerMonoidHom.range
      rw [Subgroup.relIndex, ← Subgroup.index_ker,
        S.normalizerMonoidHom_ker]
      simp only [S.coe_coe]
    have hrDvd :
        C.relIndex (Subgroup.normalizer (S : Set P)) ∣ 12 := by
      rwa [hrEq]
    have hsmod :
        (Subgroup.normalizer (S : Set P)).index ≡ 1 [MOD 13] := by
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 13 P
    have hrel :
        C.relIndex (Subgroup.normalizer (S : Set P)) *
            (Subgroup.normalizer (S : Set P)).index =
          C.index := by
      simpa only [C] using Subgroup.relIndex_mul_index
        (Subgroup.centralizer_le_normalizer (S : Set P))
    have hCindex := C.index_mul_card
    rw [hCcard, hPcard, ← hrel] at hCindex
    letI :
        C.IsFiniteRelIndex (Subgroup.normalizer (S : Set P)) :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    have hrpos :
        0 < C.relIndex (Subgroup.normalizer (S : Set P)) :=
      Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
    have hrle :
        C.relIndex (Subgroup.normalizer (S : Set P)) ≤ 12 :=
      Nat.le_of_dvd (by norm_num) hrDvd
    change
      (Subgroup.normalizer (S : Set P)).index % 13 = 1 at hsmod
    interval_cases C.relIndex (Subgroup.normalizer (S : Set P))
    all_goals try norm_num at hrDvd
    all_goals try norm_num at hCindex
    all_goals omega

private theorem card_eq_factorial_of_five_transitive_of_card_le_six
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X) (hcard_le : Fintype.card X ≤ 6)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    ext i
    exact hg i
  letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
  have hdegree : Nat.card X - 1 ≤ 5 := by
    rw [Nat.card_eq_fintype_card]
    omega
  have hfive_card : 5 ≤ Nat.card X := by
    rwa [Nat.card_eq_fintype_card]
  have hPdegree : MulAction.IsMultiplyPretransitive P X (Nat.card X - 1) :=
    MulAction.isMultiplyPretransitive_of_le hdegree hfive_card
  have hPtop : P = ⊤ := Equiv.Perm.eq_top_of_isMultiplyPretransitive hPdegree
  have hφ_surjective : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    exact hPtop
  calc
    Fintype.card G = Fintype.card (Equiv.Perm X) :=
      Fintype.card_congr (Equiv.ofBijective φ ⟨MulAction.toPerm_injective, hφ_surjective⟩)
    _ = (Fintype.card X).factorial := Fintype.card_perm

private theorem alternatingGroup_le_of_five_transitive_of_card_eq_eight
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 8)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ (MulAction.toPermHom G X).range := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    ext i
    exact hg i
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 5) (by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      omega)
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hfixIndex' : (fixingSubgroup P s).index = 6720 := by omega
  have hfixCard := (fixingSubgroup P s).index_mul_card
  rw [hfixIndex'] at hfixCard
  have hPcardLower : 6720 ≤ Nat.card P := by
    calc
      6720 = 6720 * 1 := by norm_num
      _ ≤ 6720 * Nat.card (fixingSubgroup P s) := by
        exact Nat.mul_le_mul_left 6720 Nat.card_pos
      _ = Nat.card P := hfixCard
  have hPcardLower' : 6720 ≤ Fintype.card P := by
    rwa [← Nat.card_eq_fintype_card]
  have hcardNat : Nat.card X = 8 := by
    rwa [Nat.card_eq_fintype_card]
  have hPcard := P.index_mul_card
  rw [Nat.card_perm, hcardNat] at hPcard
  norm_num at hPcard
  have hPindex : P.index ≤ 6 := by
    have hscaled : P.index * 6720 ≤ 6 * 6720 := by
      calc
        P.index * 6720 ≤ P.index * Fintype.card P :=
          Nat.mul_le_mul_left P.index hPcardLower'
        _ = 40320 := hPcard
        _ = 6 * 6720 := by norm_num
    omega
  have hcoreNe : P.normalCore ≠ ⊥ := by
    intro hcore
    let ψ := MulAction.toPermHom (Equiv.Perm X) ((Equiv.Perm X) ⧸ P)
    have hψinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [← P.normalCore_eq_ker, hcore]
    have hcardLe := Nat.card_le_card_of_injective ψ hψinj
    rw [Nat.card_perm, Nat.card_perm, ← P.index_eq_card,
      Nat.card_eq_fintype_card, hcard] at hcardLe
    have hfacLe := Nat.factorial_le hPindex
    norm_num at hcardLe hfacLe
    omega
  have hcore : Nontrivial P.normalCore :=
    P.normalCore.nontrivial_iff_ne_bot.mpr hcoreNe
  exact (Equiv.Perm.alternatingGroup_le_of_normal (by
    rw [Nat.card_eq_fintype_card, hcard]
    omega) hcore).trans P.normalCore_le

theorem alternatingGroup_le_of_five_transitive_of_card_eq_nine
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 9)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ (MulAction.toPermHom G X).range := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg⟩
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5P a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 4) (by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      omega)
  have hcomplement : sᶜ.ncard = 5 := by
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hYcard :
      Nat.card (SubMulAction.ofFixingSubgroup P s) = 5 := by
    change Nat.card ↥(sᶜ : Set X) = 5
    rw [Nat.card_coe_set_eq]
    exact hcomplement
  have hH1 :
      MulAction.IsMultiplyPretransitive
        (fixingSubgroup P s) (SubMulAction.ofFixingSubgroup P s) 1 :=
    SubMulAction.ofFixingSubgroup.isMultiplyPretransitive
      (m := 1) (n := 5) P s (by omega)
  letI : MulAction.IsPretransitive
      (fixingSubgroup P s) (SubMulAction.ofFixingSubgroup P s) :=
    MulAction.is_one_pretransitive_iff.mp hH1
  letI : Nonempty (SubMulAction.ofFixingSubgroup P s) :=
    Finite.card_pos_iff.mp (by omega)
  let y : SubMulAction.ofFixingSubgroup P s := Classical.choice inferInstance
  have hindex := MulAction.index_stabilizer_of_transitive (fixingSubgroup P s) y
  rw [hYcard] at hindex
  have hstabCard := (MulAction.stabilizer (fixingSubgroup P s) y).index_mul_card
  rw [hindex] at hstabCard
  have hdvd : 5 ∣ Nat.card (fixingSubgroup P s) :=
    ⟨Nat.card (MulAction.stabilizer (fixingSubgroup P s) y), hstabCard.symm⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  let g : Equiv.Perm X := ((u : fixingSubgroup P s) : P)
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf ((u : fixingSubgroup P s) : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := hu
  have hgP : g ∈ P := by
    exact ((u : fixingSubgroup P s) : P).prop
  have hfix :
      ∀ x ∈ s, ((u : fixingSubgroup P s) : P) • x = x :=
    (mem_fixingSubgroup_iff P).mp u.prop
  have hsuppSubset : (g.support : Set X) ⊆ sᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxs
    apply Equiv.Perm.mem_support.mp hx
    exact hfix x hxs
  have hsuppCard : g.support.card ≤ 5 := by
    rw [← Set.ncard_coe_finset]
    exact (Set.ncard_le_ncard hsuppSubset).trans_eq hcomplement
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order hgprime (by omega)
  have hgsupport : g.support.card = 5 := by
    rw [← hgcycle.orderOf, hgorder]
  have hgcore : g ∈ P.normalCore :=
    mem_normalCore_of_card_support_le_five X P h5P (by omega) hgP (by omega)
  have hgNe : g ≠ 1 := by
    intro hg
    rw [hg] at hgsupport
    norm_num at hgsupport
  have hcoreNe : P.normalCore ≠ ⊥ := by
    intro hcore
    apply hgNe
    simpa [hcore] using hgcore
  have hcore : Nontrivial P.normalCore :=
    P.normalCore.nontrivial_iff_ne_bot.mpr hcoreNe
  exact (Equiv.Perm.alternatingGroup_le_of_normal (by
    rw [Nat.card_eq_fintype_card, hcard]
    omega) hcore).trans P.normalCore_le

theorem alternatingGroup_le_of_five_transitive_of_card_eq_ten
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 10)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ (MulAction.toPermHom G X).range := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg⟩
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5P a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 5) (by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      norm_num)
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hfixIndex' : (fixingSubgroup P s).index = 30240 := by omega
  have hPcard := (fixingSubgroup P s).index_mul_card
  rw [hfixIndex'] at hPcard
  have hdvd : 7 ∣ Nat.card P := by
    refine ⟨4320 * Nat.card (fixingSubgroup P s), ?_⟩
    calc
      Nat.card P = 30240 * Nat.card (fixingSubgroup P s) := hPcard.symm
      _ = 7 * (4320 * Nat.card (fixingSubgroup P s)) := by ring
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 7 hdvd
  let g : Equiv.Perm X := (u : P)
  have hgP : g ∈ P := u.prop
  have hgorder : orderOf g = 7 :=
    (Subgroup.orderOf_coe u).trans hu
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' hgprime (by
      rw [hcard, hgorder]
      norm_num)
  let e₀ : X ≃ Fin 10 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 10) := e₀.permCongr g
  have hg₁order : orderOf g₁ = 7 := by
    calc
      orderOf g₁ = orderOf g := e₀.permCongrHom.orderOf_eq g
      _ = 7 := hgorder
  have hg₁prime : (orderOf g₁).Prime := by
    rw [hg₁order]
    norm_num
  have hg₁cycle : g₁.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' hg₁prime (by
      rw [Fintype.card_fin, hg₁order]
      norm_num)
  have hg₁support : g₁.support.card = 7 := by
    rw [← hg₁cycle.orderOf, hg₁order]
  have hcycleType :
      g₁.cycleType = FiniteChecks.sevenCycle.cycleType := by
    rw [hg₁cycle.cycleType, FiniteChecks.sevenCycle_isCycle.cycleType,
      hg₁support, FiniteChecks.sevenCycle_card_support]
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let e : X ≃ Fin 10 := e₀.trans k
  let P' : Subgroup (Equiv.Perm (Fin 10)) :=
    P.map e.permCongrHom
  have hemapg : e.permCongr g = FiniteChecks.sevenCycle := by
    change k * g₁ * k⁻¹ = FiniteChecks.sevenCycle
    exact hk
  have hseven : FiniteChecks.sevenCycle ∈ P' := by
    rw [Subgroup.mem_map]
    exact ⟨g, hgP, hemapg⟩
  have h5P' :
      ∀ a b : Fin 5 → Fin 10,
        Function.Injective a → Function.Injective b →
        ∃ q : P', ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' : Function.Injective (fun i => e.symm (a i)) :=
      e.symm.injective.comp ha
    have hb' : Function.Injective (fun i => e.symm (b i)) :=
      e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := h5P
      (fun i => e.symm (a i)) (fun i => e.symm (b i)) ha' hb'
    let q' : Equiv.Perm (Fin 10) := e.permCongr (q : Equiv.Perm X)
    have hq'P : q' ∈ P' := by
      change e.permCongr (q : Equiv.Perm X) ∈ P.map e.permCongrHom
      exact Subgroup.mem_map_of_mem e.permCongrHom.toMonoidHom q.prop
    refine ⟨⟨q', hq'P⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (e.symm (a i)) = e.symm (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      Equiv.permCongr_apply] using congrArg e hqi
  have hAlt' : alternatingGroup (Fin 10) ≤ P' :=
    alternatingGroup_le_of_sevenCycle_mem P' h5P' hseven
  intro σ hσ
  let σ' : Equiv.Perm (Fin 10) := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup (Fin 10) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simpa [σ', Equiv.Perm.sign_permCongr] using hσ
  have hmapped : σ' ∈ P' := hAlt' hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ := e.permCongrHom.injective (by
    simpa [σ'] using hτσ)
  rwa [← hτeq]

theorem alternatingGroup_le_of_five_transitive_of_card_eq_eleven
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 11)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    alternatingGroup X ≤ (MulAction.toPermHom G X).range := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg⟩
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5P a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 5) (by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      norm_num)
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hfixIndex' : (fixingSubgroup P s).index = 55440 := by omega
  have hPcard := (fixingSubgroup P s).index_mul_card
  rw [hfixIndex'] at hPcard
  have hdvd : 7 ∣ Nat.card P := by
    refine ⟨7920 * Nat.card (fixingSubgroup P s), ?_⟩
    calc
      Nat.card P = 55440 * Nat.card (fixingSubgroup P s) := hPcard.symm
      _ = 7 * (7920 * Nat.card (fixingSubgroup P s)) := by ring
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 7 hdvd
  let g : Equiv.Perm X := (u : P)
  have hgP : g ∈ P := u.prop
  have hgorder : orderOf g = 7 :=
    (Subgroup.orderOf_coe u).trans hu
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' hgprime (by
      rw [hcard, hgorder]
      norm_num)
  let e₀ : X ≃ Fin 11 := Fintype.equivFinOfCardEq hcard
  let g₁ : Equiv.Perm (Fin 11) := e₀.permCongr g
  have hg₁order : orderOf g₁ = 7 := by
    calc
      orderOf g₁ = orderOf g := e₀.permCongrHom.orderOf_eq g
      _ = 7 := hgorder
  have hg₁prime : (orderOf g₁).Prime := by
    rw [hg₁order]
    norm_num
  have hg₁cycle : g₁.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' hg₁prime (by
      rw [Fintype.card_fin, hg₁order]
      norm_num)
  have hg₁support : g₁.support.card = 7 := by
    rw [← hg₁cycle.orderOf, hg₁order]
  have hcycleType :
      g₁.cycleType = FiniteChecks.sevenCycle11.cycleType := by
    rw [hg₁cycle.cycleType, FiniteChecks.sevenCycle11_isCycle.cycleType,
      hg₁support, FiniteChecks.sevenCycle11_card_support]
  obtain ⟨k, hk⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq hcycleType)
  let e : X ≃ Fin 11 := e₀.trans k
  let P' : Subgroup (Equiv.Perm (Fin 11)) :=
    P.map e.permCongrHom
  have hemapg : e.permCongr g = FiniteChecks.sevenCycle11 := by
    change k * g₁ * k⁻¹ = FiniteChecks.sevenCycle11
    exact hk
  have hseven : FiniteChecks.sevenCycle11 ∈ P' := by
    rw [Subgroup.mem_map]
    exact ⟨g, hgP, hemapg⟩
  have h5P' :
      ∀ a b : Fin 5 → Fin 11,
        Function.Injective a → Function.Injective b →
        ∃ q : P', ∀ i, q • a i = b i := by
    intro a b ha hb
    have ha' : Function.Injective (fun i => e.symm (a i)) :=
      e.symm.injective.comp ha
    have hb' : Function.Injective (fun i => e.symm (b i)) :=
      e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := h5P
      (fun i => e.symm (a i)) (fun i => e.symm (b i)) ha' hb'
    let q' : Equiv.Perm (Fin 11) := e.permCongr (q : Equiv.Perm X)
    have hq'P : q' ∈ P' := by
      change e.permCongr (q : Equiv.Perm X) ∈ P.map e.permCongrHom
      exact Subgroup.mem_map_of_mem e.permCongrHom.toMonoidHom q.prop
    refine ⟨⟨q', hq'P⟩, ?_⟩
    intro i
    have hqi :
        (q : Equiv.Perm X) (e.symm (a i)) = e.symm (b i) := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hq i
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def, q',
      Equiv.permCongr_apply] using congrArg e hqi
  have hAlt' : alternatingGroup (Fin 11) ≤ P' :=
    alternatingGroup_le_of_sevenCycle11_mem P' h5P' hseven
  intro σ hσ
  let σ' : Equiv.Perm (Fin 11) := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup (Fin 11) := by
    rw [Equiv.Perm.mem_alternatingGroup] at hσ ⊢
    simpa [σ', Equiv.Perm.sign_permCongr] using hσ
  have hmapped : σ' ∈ P' := hAlt' hσ'
  rw [Subgroup.mem_map] at hmapped
  obtain ⟨τ, hτ, hτσ⟩ := hmapped
  have hτeq : τ = σ := e.permCongrHom.injective (by
    simpa [σ'] using hτσ)
  rwa [← hτeq]

theorem card_classification_of_alternatingGroup_le
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 7 ≤ Fintype.card X)
    (hAlt : alternatingGroup X ≤ (MulAction.toPermHom G X).range) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  letI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hPindex : P.index ≤ 2 := by
    calc
      P.index ≤ (alternatingGroup X).index := Subgroup.index_antitone hAlt
      _ = 2 := alternatingGroup.index_eq_two
  have hPindexNe : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcardRange : Fintype.card G = Fintype.card P :=
    Fintype.card_congr (Equiv.ofInjective φ MulAction.toPerm_injective)
  rcases (show P.index = 1 ∨ P.index = 2 by omega) with hindex | hindex
  · have hPtop : P = ⊤ := Subgroup.index_eq_one.mp hindex
    left
    calc
      Fintype.card G = Fintype.card P := hcardRange
      _ = Fintype.card (Equiv.Perm X) := by simp [hPtop]
      _ = (Fintype.card X).factorial := Fintype.card_perm
  · have hPalt : P = alternatingGroup X :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
    right
    refine ⟨hcard, ?_⟩
    calc
      Fintype.card G = Fintype.card P := hcardRange
      _ = Fintype.card (alternatingGroup X) :=
        Fintype.card_congr (MulEquiv.subgroupCongr hPalt).toEquiv
      _ = (Fintype.card X).factorial / 2 := card_alternatingGroup

theorem classification_of_five_transitive_of_card_eq_twelve
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 12)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) ∨
      (Fintype.card X = 12 ∧ Fintype.card G = 95040) := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg⟩
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5P a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 5) (by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      norm_num)
  have hcomplement : sᶜ.ncard = 7 := by
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hfixIndex' : (fixingSubgroup P s).index = 95040 := by
    omega
  by_cases hK : Nontrivial (fixingSubgroup P s)
  · have hKcard : 1 < Nat.card (fixingSubgroup P s) :=
      Finite.one_lt_card_iff_nontrivial.mpr hK
    obtain ⟨p, hp, hpdvd⟩ :=
      Nat.exists_prime_and_dvd (n := Nat.card (fixingSubgroup P s)) (by omega)
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ :=
      exists_prime_orderOf_dvd_card' p hpdvd
    let g : Equiv.Perm X := ((u : fixingSubgroup P s) : P)
    have hgorder : orderOf g = p := by
      calc
        orderOf g = orderOf ((u : fixingSubgroup P s) : P) :=
          Subgroup.orderOf_coe _
        _ = orderOf u := Subgroup.orderOf_coe _
        _ = p := hu
    have hgprime : (orderOf g).Prime := by
      rw [hgorder]
      exact hp
    have hgP : g ∈ P := ((u : fixingSubgroup P s) : P).prop
    have hfix :
        ∀ x ∈ s, ((u : fixingSubgroup P s) : P) • x = x :=
      (mem_fixingSubgroup_iff P).mp u.prop
    have hsuppSubset : (g.support : Set X) ⊆ sᶜ := by
      intro x hx
      rw [Set.mem_compl_iff]
      intro hxs
      apply Equiv.Perm.mem_support.mp hx
      exact hfix x hxs
    have hsuppCard : g.support.card ≤ 7 := by
      rw [← Set.ncard_coe_finset]
      exact (Set.ncard_le_ncard hsuppSubset).trans_eq hcomplement
    have hgNe : g ≠ 1 := by
      intro hg
      rw [hg, orderOf_one] at hgorder
      exact hp.ne_one hgorder.symm
    have hAlt : alternatingGroup X ≤ P := by
      by_cases hsmall : g.support.card ≤ 5
      · exact alternatingGroup_le_of_nontrivial_card_support_le_five
          X P h5P (by omega) hgP hgNe hsmall
      have hsupp : g.support.card = 6 ∨ g.support.card = 7 := by
        omega
      let e₀ : X ≃ Fin 12 := Fintype.equivFinOfCardEq hcard
      let g₁ : Equiv.Perm (Fin 12) := e₀.permCongr g
      have hg₁order : orderOf g₁ = p := by
        calc
          orderOf g₁ = orderOf g := e₀.permCongrHom.orderOf_eq g
          _ = p := hgorder
      have hg₁prime : (orderOf g₁).Prime := by
        rw [hg₁order]
        exact hp
      have hsupportMap :
          g₁.support = g.support.map e₀.toEmbedding := by
        ext y
        simp [g₁, Equiv.Perm.mem_support, Equiv.permCongr_apply]
        constructor
        · intro h h'
          apply h
          rw [h', e₀.apply_symm_apply]
        · intro h h'
          apply h
          apply e₀.injective
          simpa using h'
      have hg₁support : g₁.support.card = g.support.card := by
        rw [hsupportMap, Finset.card_map]
      obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order hg₁prime
      have hsum := g₁.sum_cycleType
      rw [hm, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
        hg₁order, hg₁support] at hsum
      rcases hsupp with hsupp | hsupp
      · have hp_le : p ≤ 6 := by nlinarith [Nat.zero_le m]
        interval_cases p
        all_goals norm_num at hp
        · have hm' : m + 1 = 3 := by omega
          have hcycle :
              g₁.cycleType = FiniteChecks.tripleSwap12.cycleType := by
            rw [hm, hg₁order, hm', FiniteChecks.tripleSwap12_cycleType]
            norm_num
          apply alternatingGroup_le_of_cycleType_eq_fin_twelve
            X P hcard h5P hgP FiniteChecks.tripleSwap12
          · simpa [e₀, g₁] using hcycle
          · exact alternatingGroup_le_of_tripleSwap12_mem
        · have hm' : m + 1 = 2 := by omega
          have hcycle :
              g₁.cycleType =
                FiniteChecks.doubleThreeCycle12.cycleType := by
            rw [hm, hg₁order, hm',
              FiniteChecks.doubleThreeCycle12_cycleType]
            norm_num
          apply alternatingGroup_le_of_cycleType_eq_fin_twelve
            X P hcard h5P hgP FiniteChecks.doubleThreeCycle12
          · simpa [e₀, g₁] using hcycle
          · exact alternatingGroup_le_of_doubleThreeCycle12_mem
        · omega
      · have hp_le : p ≤ 7 := by nlinarith [Nat.zero_le m]
        interval_cases p
        all_goals norm_num at hp
        · omega
        · omega
        · omega
        · have hm' : m + 1 = 1 := by omega
          have hg₁cycle : g₁.IsCycle := by
            rw [← Equiv.Perm.card_cycleType_eq_one, hm,
              Multiset.card_replicate, hm']
          have hcycle :
              g₁.cycleType = FiniteChecks.sevenCycle12.cycleType := by
            rw [hg₁cycle.cycleType,
              FiniteChecks.sevenCycle12_isCycle.cycleType,
              hg₁support, hsupp,
              FiniteChecks.sevenCycle12_card_support]
          apply alternatingGroup_le_of_cycleType_eq_fin_twelve
            X P hcard h5P hgP FiniteChecks.sevenCycle12
          · simpa [e₀, g₁] using hcycle
          · exact alternatingGroup_le_of_sevenCycle12_mem
    rcases card_classification_of_alternatingGroup_le G X (by omega) hAlt with
      hfull | hhalf
    · exact Or.inl hfull
    · exact Or.inr (Or.inl hhalf)
  · haveI : Subsingleton (fixingSubgroup P s) :=
      not_nontrivial_iff_subsingleton.mp hK
    have hKcard : Nat.card (fixingSubgroup P s) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    have hPcard := (fixingSubgroup P s).index_mul_card
    rw [hfixIndex', hKcard] at hPcard
    have hcardRange : Fintype.card G = Fintype.card P :=
      Fintype.card_congr (Equiv.ofInjective φ MulAction.toPerm_injective)
    right
    right
    refine ⟨hcard, ?_⟩
    rw [hcardRange, ← Nat.card_eq_fintype_card]
    omega

theorem classification_of_five_transitive_of_card_eq_thirteen
    (G X : Type) [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : Fintype.card X = 13)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have h5P :
      ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g, hg⟩ := h5 a b ha hb
    exact ⟨⟨φ g, ⟨g, rfl⟩⟩, hg⟩
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5P a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  obtain ⟨s, _, hs⟩ := Set.exists_subset_card_eq
    (s := (Set.univ : Set X)) (n := 5) (by
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
      norm_num)
  have hcomplement : sᶜ.ncard = 8 := by
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hfixIndex' : (fixingSubgroup P s).index = 154440 := by
    omega
  by_cases hAlt : alternatingGroup X ≤ P
  · exact card_classification_of_alternatingGroup_le G X (by omega) hAlt
  · exfalso
    let K : Subgroup P := fixingSubgroup P s
    let Y := SubMulAction.ofFixingSubgroup P s
    have hYcard : Nat.card Y = 8 := by
      change Nat.card ↥(sᶜ : Set X) = 8
      rw [Nat.card_coe_set_eq]
      exact hcomplement
    letI : Nonempty Y := Finite.card_pos_iff.mp (by omega)
    let y : Y := Classical.choice inferInstance
    let L : Subgroup K := MulAction.stabilizer K y
    have hLsubsingleton : Subsingleton L := by
      rw [← not_nontrivial_iff_subsingleton]
      intro hL
      have hLcard : 1 < Nat.card L :=
        Finite.one_lt_card_iff_nontrivial.mpr hL
      obtain ⟨p, hp, hpdvd⟩ :=
        Nat.exists_prime_and_dvd (n := Nat.card L) (by omega)
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpdvd
      let g : Equiv.Perm X := (((u : L) : K) : P)
      have hgorder : orderOf g = p := by
        calc
          orderOf g = orderOf (((u : L) : K) : P) :=
            Subgroup.orderOf_coe _
          _ = orderOf ((u : L) : K) := Subgroup.orderOf_coe _
          _ = orderOf u := Subgroup.orderOf_coe _
          _ = p := hu
      have hgP : g ∈ P := (((u : L) : K) : P).prop
      have hfix :
          ∀ x ∈ s, (((u : L) : K) : P) • x = x :=
        (mem_fixingSubgroup_iff P).mp ((u : L) : K).prop
      have hsuppSubset : (g.support : Set X) ⊆ sᶜ := by
        intro x hx
        rw [Set.mem_compl_iff]
        intro hxs
        apply Equiv.Perm.mem_support.mp hx
        exact hfix x hxs
      have hyfixSubtype : ((u : L) : K) • y = y :=
        MulAction.mem_stabilizer_iff.mp u.prop
      have hyfix : (((u : L) : K) : P) • (y : X) = y := by
        exact congrArg Subtype.val hyfixSubtype
      have hyNotSupport : (y : X) ∉ (g.support : Set X) := by
        intro hy
        apply Equiv.Perm.mem_support.mp hy
        exact hyfix
      have hsuppProper : (g.support : Set X) ⊂ sᶜ := by
        rw [Set.ssubset_iff_subset_ne]
        refine ⟨hsuppSubset, ?_⟩
        intro heq
        apply hyNotSupport
        rw [heq]
        exact y.prop
      have hsuppLt :=
        Set.ncard_lt_ncard hsuppProper
      rw [Set.ncard_coe_finset, hcomplement] at hsuppLt
      have hsuppCard : g.support.card ≤ 7 := by
        omega
      exact hAlt (alternatingGroup_le_of_prime_order_support_le_seven13
        X P hcard h5P hgP hp hgorder hsuppCard)
    letI : Subsingleton L := hLsubsingleton
    have hLcard : Nat.card L = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    have hLindex : L.index = Nat.card K := by
      rw [Nat.card_eq_fintype_card] at hLcard ⊢
      simpa [hLcard] using L.index_mul_card
    have hindexOrbit :
        L.index = (MulAction.orbit K y).ncard := by
      simpa only [L] using MulAction.index_stabilizer K y
    have hKcardLe : Nat.card K ≤ 8 := by
      calc
        Nat.card K = L.index := hLindex.symm
        _ = (MulAction.orbit K y).ncard := hindexOrbit
        _ ≤ (Set.univ : Set Y).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
        _ = Nat.card Y := Set.ncard_univ Y
        _ = 8 := hYcard
    have hprimeDivTwo :
        ∀ {p : ℕ}, p.Prime → p ∣ Nat.card K → p = 2 := by
      intro p hp hpdvd
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpdvd
      let g : Equiv.Perm X := ((u : K) : P)
      have hgorder : orderOf g = p := by
        calc
          orderOf g = orderOf ((u : K) : P) := Subgroup.orderOf_coe _
          _ = orderOf u := Subgroup.orderOf_coe _
          _ = p := hu
      have hgP : g ∈ P := ((u : K) : P).prop
      have hfix :
          ∀ x ∈ s, ((u : K) : P) • x = x :=
        (mem_fixingSubgroup_iff P).mp u.prop
      have hsuppSubset : (g.support : Set X) ⊆ sᶜ := by
        intro x hx
        rw [Set.mem_compl_iff]
        intro hxs
        apply Equiv.Perm.mem_support.mp hx
        exact hfix x hxs
      have hsuppCard : g.support.card ≤ 8 := by
        rw [← Set.ncard_coe_finset]
        exact (Set.ncard_le_ncard hsuppSubset).trans_eq hcomplement
      by_cases hsuppSmall : g.support.card ≤ 7
      · exact (hAlt (alternatingGroup_le_of_prime_order_support_le_seven13
          X P hcard h5P hgP hp hgorder hsuppSmall)).elim
      have hsuppEq : g.support.card = 8 := by
        omega
      have hgprime : (orderOf g).Prime := by
        rw [hgorder]
        exact hp
      obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order hgprime
      have hsum := g.sum_cycleType
      rw [hm, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
        hgorder, hsuppEq] at hsum
      have hp_le : p ≤ 8 := by
        nlinarith [Nat.zero_le m]
      interval_cases p
      all_goals norm_num at hp
      all_goals omega
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hKne3 : Nat.card K ≠ 3 := by
      intro hKcard
      have hp := hprimeDivTwo (p := 3) (by norm_num) (by
        rw [hKcard])
      norm_num at hp
    have hKne5 : Nat.card K ≠ 5 := by
      intro hKcard
      have hp := hprimeDivTwo (p := 5) (by norm_num) (by
        rw [hKcard])
      norm_num at hp
    have hKne6 : Nat.card K ≠ 6 := by
      intro hKcard
      have hp := hprimeDivTwo (p := 3) (by norm_num) (by
        rw [hKcard]
        norm_num)
      norm_num at hp
    have hKne7 : Nat.card K ≠ 7 := by
      intro hKcard
      have hp := hprimeDivTwo (p := 7) (by norm_num) (by
        rw [hKcard])
      norm_num at hp
    have hKcases :
        Nat.card K = 1 ∨ Nat.card K = 2 ∨
          Nat.card K = 4 ∨ Nat.card K = 8 := by
      omega
    have hPcard : Nat.card P = 154440 * Nat.card K := by
      have hKindex := K.index_mul_card
      change (fixingSubgroup P s).index * Nat.card K = Nat.card P at hKindex
      rw [hfixIndex'] at hKindex
      exact hKindex.symm
    exact not_card_eq_five_tuple_mul_small_two_power_of_card_thirteen
      X P hcard (Nat.card K) hKcases hPcard

private theorem classification_of_five_transitive_of_card_le_seven
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X) (hcard_le : Fintype.card X ≤ 7)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  by_cases hcard_six : Fintype.card X ≤ 6
  · exact Or.inl (card_eq_factorial_of_five_transitive_of_card_le_six
      G X hcard hcard_six h5)
  have hcard_eq : Fintype.card X = 7 := by omega
  letI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let φ : G →* Equiv.Perm X := MulAction.toPermHom G X
  let P : Subgroup (Equiv.Perm X) := φ.range
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨⟨φ g, ⟨g, rfl⟩⟩, ?_⟩
    ext i
    exact hg i
  have hdegree : Nat.card X - 2 = 5 := by
    rw [Nat.card_eq_fintype_card, hcard_eq]
  have hPdegree : MulAction.IsMultiplyPretransitive P X (Nat.card X - 2) := by
    rwa [hdegree]
  have hAlt : alternatingGroup X ≤ P :=
    IsMultiplyPretransitive.alternatingGroup_le X P hPdegree
  have hPindex : P.index ≤ 2 := by
    calc
      P.index ≤ (alternatingGroup X).index := Subgroup.index_antitone hAlt
      _ = 2 := alternatingGroup.index_eq_two
  have hPindex_ne : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard_range : Fintype.card G = Fintype.card P := by
    exact Fintype.card_congr (Equiv.ofInjective φ MulAction.toPerm_injective)
  rcases (show P.index = 1 ∨ P.index = 2 by omega) with hindex | hindex
  · have hPtop : P = ⊤ := Subgroup.index_eq_one.mp hindex
    left
    calc
      Fintype.card G = Fintype.card P := hcard_range
      _ = Fintype.card (Equiv.Perm X) := by simp [hPtop]
      _ = (Fintype.card X).factorial := Fintype.card_perm
  · have hPalt : P = alternatingGroup X :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
    right
    refine ⟨by omega, ?_⟩
    calc
      Fintype.card G = Fintype.card P := hcard_range
      _ = Fintype.card (alternatingGroup X) :=
        Fintype.card_congr (MulEquiv.subgroupCongr hPalt).toEquiv
      _ = (Fintype.card X).factorial / 2 := card_alternatingGroup

theorem classification_of_five_transitive_of_card_le_eleven
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X) (hcard_le : Fintype.card X ≤ 11)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    Fintype.card G = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧
        Fintype.card G = (Fintype.card X).factorial / 2) := by
  classical
  by_cases hcard_seven : Fintype.card X ≤ 7
  · exact classification_of_five_transitive_of_card_le_seven
      G X hcard hcard_seven h5
  have hAlt :
      alternatingGroup X ≤ (MulAction.toPermHom G X).range := by
    rcases (show Fintype.card X = 8 ∨ Fintype.card X = 9 ∨
        Fintype.card X = 10 ∨ Fintype.card X = 11 by omega) with
      hcard_eq | hcard_eq | hcard_eq | hcard_eq
    · exact alternatingGroup_le_of_five_transitive_of_card_eq_eight
        G X hcard_eq h5
    · exact alternatingGroup_le_of_five_transitive_of_card_eq_nine
        G X hcard_eq h5
    · exact alternatingGroup_le_of_five_transitive_of_card_eq_ten
        G X hcard_eq h5
    · exact alternatingGroup_le_of_five_transitive_of_card_eq_eleven
        G X hcard_eq h5
  exact FiveTransitive.Helpers.card_classification_of_alternatingGroup_le G X (by omega) hAlt

end FiveTransitive.Helpers

end CFSG
