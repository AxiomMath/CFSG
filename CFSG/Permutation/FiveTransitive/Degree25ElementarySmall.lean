module

public import CFSG.Permutation.FiveTransitive.Degree25ThirteenFiniteChecks
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
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace FiveTransitive.Degree25

abbrev ThreeCycle := Multiplicative (ZMod 3)

abbrev TwoThreeBase := Fin 2 → ThreeCycle

abbrev TwoThreePoints :=
  (Fin 2 × ThreeCycle) ⊕ Fin 19

instance : SMul TwoThreeBase TwoThreePoints where
  smul a
    | Sum.inl x => Sum.inl ⟨x.1, a x.1 * x.2⟩
    | Sum.inr i => Sum.inr i

instance : MulAction TwoThreeBase TwoThreePoints where
  one_smul
    | Sum.inl x => by
        change
          Sum.inl (x.1, (1 : ThreeCycle) * x.2) =
            Sum.inl x
        congr 2
        exact one_mul x.2
    | Sum.inr _ => rfl
  mul_smul a b
    | Sum.inl x => by
        change
          Sum.inl (x.1, (a x.1 * b x.1) * x.2) =
            Sum.inl (x.1, a x.1 * (b x.1 * x.2))
        congr 2
        exact mul_assoc _ _ _
    | Sum.inr _ => rfl

instance : FaithfulSMul TwoThreeBase TwoThreePoints where
  eq_of_smul_eq_smul {a b} h := by
    funext i
    have hi :=
      h (Sum.inl (i, (1 : ThreeCycle)))
    injection hi with hi
    have hi' := congrArg Prod.snd hi
    change a i * 1 = b i * 1 at hi'
    simpa using hi'

theorem card_twoThreePoints :
    Fintype.card TwoThreePoints = 25 := by
  rw [Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  norm_num [ZMod.card]

theorem twoThreeBase_support_le_six
    (a : TwoThreeBase) :
    ((MulAction.toPermHom TwoThreeBase TwoThreePoints) a).support.card ≤ 6 := by
  decide +revert

abbrev TwoCycle := Multiplicative (ZMod 2)

abbrev TwoTwoBase := Fin 2 → TwoCycle

abbrev TwoTwoPoints :=
  (Fin 2 × TwoCycle) ⊕ Fin 21

instance : SMul TwoTwoBase TwoTwoPoints where
  smul a
    | Sum.inl x => Sum.inl ⟨x.1, a x.1 * x.2⟩
    | Sum.inr i => Sum.inr i

instance : MulAction TwoTwoBase TwoTwoPoints where
  one_smul
    | Sum.inl x => by
        change
          Sum.inl (x.1, (1 : TwoCycle) * x.2) =
            Sum.inl x
        congr 2
        exact one_mul x.2
    | Sum.inr _ => rfl
  mul_smul a b
    | Sum.inl x => by
        change
          Sum.inl (x.1, (a x.1 * b x.1) * x.2) =
            Sum.inl (x.1, a x.1 * (b x.1 * x.2))
        congr 2
        exact mul_assoc _ _ _
    | Sum.inr _ => rfl

instance : FaithfulSMul TwoTwoBase TwoTwoPoints where
  eq_of_smul_eq_smul {a b} h := by
    funext i
    have hi :=
      h (Sum.inl (i, (1 : TwoCycle)))
    injection hi with hi
    have hi' := congrArg Prod.snd hi
    change a i * 1 = b i * 1 at hi'
    simpa using hi'

theorem card_twoTwoPoints :
    Fintype.card TwoTwoPoints = 25 := by
  rw [Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  norm_num [ZMod.card]

theorem twoTwoBase_support_le_four
    (a : TwoTwoBase) :
    ((MulAction.toPermHom TwoTwoBase TwoTwoPoints) a).support.card ≤ 4 := by
  decide +revert

abbrev ThreeTwoBase := Fin 3 → TwoCycle

abbrev ThreeTwoPoints :=
  (Fin 3 × TwoCycle) ⊕ Fin 19

instance : SMul ThreeTwoBase ThreeTwoPoints where
  smul a
    | Sum.inl x => Sum.inl ⟨x.1, a x.1 * x.2⟩
    | Sum.inr i => Sum.inr i

instance : MulAction ThreeTwoBase ThreeTwoPoints where
  one_smul
    | Sum.inl x => by
        change
          Sum.inl (x.1, (1 : TwoCycle) * x.2) =
            Sum.inl x
        congr 2
        exact one_mul x.2
    | Sum.inr _ => rfl
  mul_smul a b
    | Sum.inl x => by
        change
          Sum.inl (x.1, (a x.1 * b x.1) * x.2) =
            Sum.inl (x.1, a x.1 * (b x.1 * x.2))
        congr 2
        exact mul_assoc _ _ _
    | Sum.inr _ => rfl

instance : FaithfulSMul ThreeTwoBase ThreeTwoPoints where
  eq_of_smul_eq_smul {a b} h := by
    funext i
    have hi :=
      h (Sum.inl (i, (1 : TwoCycle)))
    injection hi with hi
    have hi' := congrArg Prod.snd hi
    change a i * 1 = b i * 1 at hi'
    simpa using hi'

theorem card_threeTwoPoints :
    Fintype.card ThreeTwoPoints = 25 := by
  rw [Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  norm_num [ZMod.card]

theorem threeTwoBase_support_le_six
    (a : ThreeTwoBase) :
    ((MulAction.toPermHom ThreeTwoBase ThreeTwoPoints) a).support.card ≤ 6 := by
  decide +revert

instance : SMul (DihedralGroup 4) (ZMod 4) where
  smul
    | DihedralGroup.r i, x => x - i
    | DihedralGroup.sr i, x => i - x

instance : MulAction (DihedralGroup 4) (ZMod 4) where
  one_smul x := by
    change x - 0 = x
    exact sub_zero x
  mul_smul a b x := by
    rcases a with i | i <;> rcases b with j | j
    · change x - (i + j) = (x - j) - i
      ring
    · change (j - i) - x = (j - x) - i
      ring
    · change (i + j) - x = i - (x - j)
      ring
    · change x - (j - i) = i - (j - x)
      ring

instance : FaithfulSMul (DihedralGroup 4) (ZMod 4) where
  eq_of_smul_eq_smul {a b} h := by
    rcases a with i | i <;> rcases b with j | j
    · have hzero := h 0
      change -i = -j at hzero
      exact congrArg DihedralGroup.r (neg_injective hzero)
    · revert i j
      decide
    · revert i j
      decide
    · have hzero := h 0
      change i - 0 = j - 0 at hzero
      simp only [sub_zero] at hzero
      exact congrArg DihedralGroup.sr hzero

abbrev FourTwoBase :=
  DihedralGroup 4 × TwoCycle

abbrev FourTwoPoints :=
  ((ZMod 4) ⊕ TwoCycle) ⊕ Fin 19

instance : SMul FourTwoBase FourTwoPoints where
  smul a
    | Sum.inl (Sum.inl x) =>
        Sum.inl (Sum.inl (a.1 • x))
    | Sum.inl (Sum.inr x) =>
        Sum.inl (Sum.inr (a.2 * x))
    | Sum.inr i => Sum.inr i

instance : MulAction FourTwoBase FourTwoPoints where
  one_smul
    | Sum.inl (Sum.inl x) => by
        change Sum.inl (Sum.inl ((1 : DihedralGroup 4) • x)) =
          Sum.inl (Sum.inl x)
        rw [one_smul]
    | Sum.inl (Sum.inr x) => by
        change
          Sum.inl (Sum.inr ((1 : TwoCycle) * x)) =
            Sum.inl (Sum.inr x)
        rw [one_mul]
    | Sum.inr _ => rfl
  mul_smul a b
    | Sum.inl (Sum.inl x) => by
        change
          Sum.inl (Sum.inl ((a.1 * b.1) • x)) =
            Sum.inl (Sum.inl (a.1 • (b.1 • x)))
        rw [mul_smul]
    | Sum.inl (Sum.inr x) => by
        change
          Sum.inl (Sum.inr ((a.2 * b.2) * x)) =
            Sum.inl (Sum.inr (a.2 * (b.2 * x)))
        rw [mul_assoc]
    | Sum.inr _ => rfl

instance : FaithfulSMul FourTwoBase FourTwoPoints where
  eq_of_smul_eq_smul {a b} h := by
    apply Prod.ext
    · apply FaithfulSMul.eq_of_smul_eq_smul
        (M := DihedralGroup 4) (α := ZMod 4)
      intro x
      have hx := h (Sum.inl (Sum.inl x))
      exact Sum.inl.inj (Sum.inl.inj hx)
    · have hx :=
        h (Sum.inl (Sum.inr (1 : TwoCycle)))
      injection hx with hx
      injection hx with hx
      change a.2 * 1 = b.2 * 1 at hx
      simpa using hx

theorem card_fourTwoPoints :
    Fintype.card FourTwoPoints = 25 := by
  rw [Fintype.card_sum, Fintype.card_sum,
    Fintype.card_fin]
  change
    Fintype.card (ZMod 4) +
      Fintype.card (ZMod 2) + 19 = 25
  norm_num [ZMod.card]

theorem fourTwoBase_support_le_six
    (a : FourTwoBase) :
    ((MulAction.toPermHom FourTwoBase FourTwoPoints) a).support.card ≤ 6 := by
  decide +revert

end FiveTransitive.Degree25

end CFSG
