module

public import CFSG.Permutation.FiveTransitive.Degree20SevenFiniteChecks
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
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

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

theorem nineteen_dvd_card_of_large_normal_subgroup
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (Q : Subgroup P) [Q.Normal]
    (hQlarge : 20 < Nat.card Q) :
    19 ∣ Nat.card Q := by
  classical
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP2 : MulAction.IsMultiplyPretransitive P X 2 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 2) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  letI : MulAction.IsPreprimitive P X :=
    MulAction.isPreprimitive_of_is_two_pretransitive hP2
  have hQfixedNe :
      MulAction.fixedPoints Q X ≠ Set.univ := by
    intro hfixed
    have hsubsingleton : Subsingleton Q := by
      constructor
      intro a b
      apply Subtype.ext
      apply P.subtype_injective
      ext z
      have ha :
          a • z = z :=
        MulAction.mem_fixedPoints.mp
          ((Set.eq_univ_iff_forall.mp hfixed) z) a
      have hb :
          b • z = z :=
        MulAction.mem_fixedPoints.mp
          ((Set.eq_univ_iff_forall.mp hfixed) z) b
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def]
        using ha.trans hb.symm
    have hQcardOne : Nat.card Q = 1 :=
      @Nat.card_unique Q inferInstance hsubsingleton
    omega
  have hQtrans :
      MulAction.IsPretransitive Q X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
      hQfixedNe
  letI : MulAction.IsPretransitive Q X := hQtrans
  have hxNonempty : Nonempty X :=
    Fintype.card_pos_iff.mp (by omega)
  let x : X := Classical.choice hxNonempty
  let K : Subgroup P := MulAction.stabilizer P x
  let Y := SubMulAction.ofStabilizer P x
  have hP3 : MulAction.IsMultiplyPretransitive P X 3 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 3) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hK2 :
      MulAction.IsMultiplyPretransitive K Y 2 := by
    simpa only [K, Y] using
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := P) (α := X) (a := x) (n := 2)).mp hP3
  letI : MulAction.IsPreprimitive K Y :=
    MulAction.isPreprimitive_of_is_two_pretransitive hK2
  let L : Subgroup K := Subgroup.comap K.subtype Q
  letI : L.Normal :=
    Subgroup.Normal.comap (inferInstance : Q.Normal) K.subtype
  have hLfixedNe :
      MulAction.fixedPoints L Y ≠ Set.univ := by
    intro hfixed
    have hLsubsingleton : Subsingleton L := by
      constructor
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      apply P.subtype_injective
      ext z
      by_cases hz : z = x
      · subst z
        have ha :
            a.1.1 • x = x :=
          MulAction.mem_stabilizer_iff.mp a.1.prop
        have hb :
            b.1.1 • x = x :=
          MulAction.mem_stabilizer_iff.mp b.1.prop
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def]
          using ha.trans hb.symm
      · let y : Y := ⟨z, by
          simpa only [Y,
            SubMulAction.mem_ofStabilizer_iff] using hz⟩
        have ha :
            a • y = y :=
          MulAction.mem_fixedPoints.mp
            ((Set.eq_univ_iff_forall.mp hfixed) y) a
        have hb :
            b • y = y :=
          MulAction.mem_fixedPoints.mp
            ((Set.eq_univ_iff_forall.mp hfixed) y) b
        have ha' := congrArg Subtype.val ha
        have hb' := congrArg Subtype.val hb
        change ((a.1.1 : P) : Equiv.Perm X) z = z at ha'
        change ((b.1.1 : P) : Equiv.Perm X) z = z at hb'
        exact ha'.trans hb'.symm
    let stabilizerToL :
        MulAction.stabilizer Q x → L :=
      fun q =>
        ⟨⟨q.1.1, by
            exact MulAction.mem_stabilizer_iff.mpr
              (MulAction.mem_stabilizer_iff.mp q.prop)⟩,
          q.1.prop⟩
    have hstabilizerSubsingleton :
        Subsingleton (MulAction.stabilizer Q x) := by
      constructor
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun q : L => q.1.1)
        (hLsubsingleton.elim
          (stabilizerToL a) (stabilizerToL b))
    letI : Subsingleton (MulAction.stabilizer Q x) :=
      hstabilizerSubsingleton
    have hstabilizerCard :
        Nat.card (MulAction.stabilizer Q x) = 1 :=
      Nat.card_unique
    have hindex :
        (MulAction.stabilizer Q x).index = 20 := by
      rw [MulAction.index_stabilizer_of_transitive,
        Nat.card_eq_fintype_card, hcard]
    have hindexCard :=
      (MulAction.stabilizer Q x).index_mul_card
    have hQcard : Nat.card Q = 20 := by
      calc
        Nat.card Q =
            (MulAction.stabilizer Q x).index *
              Nat.card (MulAction.stabilizer Q x) :=
          hindexCard.symm
        _ = 20 := by
          rw [hindex, hstabilizerCard]
    exact (Nat.ne_of_gt hQlarge) hQcard
  have hLtrans :
      MulAction.IsPretransitive L Y :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
      hLfixedNe
  letI : MulAction.IsPretransitive L Y := hLtrans
  have hYcard : Nat.card Y = 19 := by
    rw [SubMulAction.nat_card_ofStabilizer_eq P x,
      Nat.card_eq_fintype_card, hcard]
  have hyNonempty : Nonempty Y :=
    (Nat.card_pos_iff.mp (by
      rw [hYcard]
      norm_num)).1
  let y : Y := Classical.choice hyNonempty
  have hLindex :
      (MulAction.stabilizer L y).index = 19 := by
    rw [MulAction.index_stabilizer_of_transitive,
      hYcard]
  have hLindexCard :=
    (MulAction.stabilizer L y).index_mul_card
  have hnineteenL : 19 ∣ Nat.card L := by
    rw [hLindex] at hLindexCard
    exact ⟨Nat.card (MulAction.stabilizer L y),
      hLindexCard.symm⟩
  let inclusion : L →* Q := {
    toFun := fun q => ⟨q.1.1, by exact q.prop⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    exact Subtype.ext (Subtype.ext
      (congrArg (fun q : Q => (q : P)) hab))
  exact hnineteenL.trans
    (Subgroup.card_dvd_of_injective inclusion hinclusion)

end FiveTransitive.Degree20

end CFSG
