module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG

theorem exists_unit_orderOf_eq_of_isAlgClosed {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) : ∃ ζ : kˣ, orderOf ζ = n := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : k) := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  have hu : IsUnit ζ := hζ.isUnit hn0
  exact ⟨hu.unit, (IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)).eq_orderOf.symm⟩

end CFSG

namespace CFSG.RankThree.PartOne.KLCE

theorem odd_orderOf_of_charTwo {L : Type*} [Field L] [CharP L 2] (a : Lˣ) (ha : IsOfFinOrder a) :
    Odd (orderOf a) := by
  by_contra hodd
  have heven : Even (orderOf a) := Nat.not_odd_iff_even.1 hodd
  obtain ⟨k, hk⟩ := heven
  have hpos : 0 < orderOf a := ha.orderOf_pos
  have hk0 : 0 < k := by omega
  set b : Lˣ := a ^ k with hb
  have hb1 : b ≠ 1 := pow_ne_one_of_lt_orderOf hk0.ne' (by omega)
  have hb2 : b ^ 2 = 1 := by
    rw [hb, ← pow_mul, show k * 2 = orderOf a by omega]
    exact pow_orderOf_eq_one a
  have hb2' : ((b : Lˣ) : L) ^ 2 = 1 := by
    have := congrArg (fun u : Lˣ => (u : L)) hb2
    simpa using this
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h3 : (((b : Lˣ) : L) - 1) ^ 2 = 0 := by
    linear_combination hb2' + (1 - ((b : Lˣ) : L)) * h2
  have h4 : ((b : Lˣ) : L) - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h3
  exact hb1 (Units.ext (sub_eq_zero.1 h4))

theorem isOfFinOrder_of_isAlgebraic {K L : Type*} [Field K] [Finite K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (a : Lˣ) : IsOfFinOrder a := by
  have hint : IsIntegral K (a : L) := (Algebra.IsAlgebraic.isAlgebraic (a : L)).isIntegral
  have : FiniteDimensional K (IntermediateField.adjoin K {(a : L)}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin K {(a : L)}) := Module.finite_of_finite K
  have : Fintype (IntermediateField.adjoin K {(a : L)}) := Fintype.ofFinite _
  let b : IntermediateField.adjoin K {(a : L)} := ⟨a, IntermediateField.subset_adjoin K _ rfl⟩
  have hb : b ≠ 0 := fun h => a.ne_zero (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one b hb
  have h2 : (a : L) ^ (Fintype.card (IntermediateField.adjoin K {(a : L)}) - 1) = 1 :=
    congrArg Subtype.val h1
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨Fintype.card (IntermediateField.adjoin K {(a : L)}) - 1, ?_, Units.ext ?_⟩
  · have := Fintype.one_lt_card (α := IntermediateField.adjoin K {(a : L)})
    omega
  · simpa using h2

end CFSG.RankThree.PartOne.KLCE

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e

theorem odd_card_sub_one {K : Type*} [Field K] [Finite K] [CharP K 2] :
    Odd (Nat.card K - 1) := by
  have : Fintype K := Fintype.ofFinite K
  have h0 : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two (ringChar.eq K 2)
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  rw [← Nat.card_eq_fintype_card] at h0 h1
  exact Nat.odd_iff.mpr (by omega)

theorem exists_odd_pow_eq_one {K L : Type*} [Field K] [Finite K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] (hK2 : ringChar K = 2) {ι : Type*} [Finite ι]
    (b : ι → Lˣ) : ∃ N : ℕ, Odd N ∧ ∀ i, b i ^ N = 1 := by
  classical
  have : CharP K 2 := hK2 ▸ ringChar.charP K
  let F : IntermediateField K L :=
    IntermediateField.adjoin K (Set.range fun i => (b i : L))
  have : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have : Finite F := Module.finite_of_finite K
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  refine ⟨Nat.card F - 1, odd_card_sub_one, fun i => Units.ext ?_⟩
  have hmem : (b i : L) ∈ F := IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  let y : F := ⟨b i, hmem⟩
  have hy0 : y ≠ 0 := fun h => (b i).ne_zero (congrArg Subtype.val h)
  have : Fintype F := Fintype.ofFinite F
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy0
  rw [← Nat.card_eq_fintype_card] at h1
  simpa using congrArg Subtype.val h1

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e

end
