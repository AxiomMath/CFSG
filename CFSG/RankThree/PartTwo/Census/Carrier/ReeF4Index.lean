module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Model

public noncomputable section

namespace CFSG.TauCetiBridge.ReeF4

open TauCeti TauCeti.F4ShortRoot.PrimeField

theorem isReeSteinberg_reeF4 (d : ReeF4LieIndex) :
    IsReeSteinberg d.toSuzukiReeIndex.halfExponent d.steinberg := by
  intro k u
  have hyy : ∀ t, d.halfFrobenius (d.halfFrobenius (rootSubgroupPoints
      (TauCeti.F4ShortRoot.isogenyReverse k) d.1.Closure (Multiplicative.ofAdd t))) =
        rootSubgroupPoints (TauCeti.F4ShortRoot.isogenyReverse k) d.1.Closure
          (Multiplicative.ofAdd (t ^ d.1.characteristic)) := fun t => by
    refine (d.halfFrobenius_halfFrobenius _).trans ?_
    rw [ReeF4LieIndex.primeFrobenius_def, frobenius_rootSubgroupPoints, toAdd_ofAdd, pow_one]
    exact congrArg (fun n => rootSubgroupPoints (TauCeti.F4ShortRoot.isogenyReverse k)
      d.1.Closure (Multiplicative.ofAdd (t ^ n))) d.characteristic_eq_two.symm
  have h := d.toSuzukiReeIndex.pow_fieldExponent_apply_pow (τ := d.halfFrobenius)
    (x := fun t => rootSubgroupPoints k d.1.Closure (Multiplicative.ofAdd t))
    (y := fun t => rootSubgroupPoints (TauCeti.F4ShortRoot.isogenyReverse k) d.1.Closure
      (Multiplicative.ofAdd t))
    (c := TauCeti.F4ShortRoot.isogenyExponent k)
    (fun t => by
      rw [ReeF4LieIndex.halfFrobenius_def]
      exact specialIsogeny_rootSubgroupPoints _ k (Multiplicative.ofAdd t)) hyy u
  rw [ReeF4LieIndex.steinberg_def]
  refine h.trans ?_
  exact congrArg (fun n => rootSubgroupPoints (TauCeti.F4ShortRoot.isogenyReverse k) d.1.Closure
    (Multiplicative.ofAdd (u ^ (n ^ d.toSuzukiReeIndex.halfExponent *
      TauCeti.F4ShortRoot.isogenyExponent k)))) d.characteristic_eq_two

theorem isReeSteinberg_tits (d : TitsLieIndex) : IsReeSteinberg 0 d.steinberg := by
  intro k u
  rw [TitsLieIndex.steinberg_def, specialIsogeny_rootSubgroupPoints, pow_zero, one_mul]
  rfl

theorem card_fixedField_reeF4 (d : ReeF4LieIndex) :
    Nat.card d.1.fixedField = 2 ^ (2 * d.toSuzukiReeIndex.halfExponent + 1) := by
  rw [ValidLieTypeIndex.card_fixedField, d.fieldOrder_eq_two_pow,
    d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one]

theorem card_fixedField_tits (d : TitsLieIndex) : Nat.card d.1.fixedField = 2 := by
  rw [ValidLieTypeIndex.card_fixedField, d.fieldOrder_eq_two]

theorem zerosInAdjoint_reeF4 (d : ReeF4LieIndex) : ZerosInAdjoint d.1.Closure := by
  have : CharP d.1.Closure d.1.characteristic :=
    charP_of_injective_algebraMap (algebraMap (ZMod d.1.characteristic) d.1.Closure).injective _
  exact fun H hCH hH => CFSG.TauCetiBridge.Even.le_adjointGroup_F4_two_rankThree
    (p := d.1.characteristic) d.characteristic_eq_two H hCH hH

theorem zerosInAdjoint_tits (d : TitsLieIndex) : ZerosInAdjoint d.1.Closure := by
  have : CharP d.1.Closure d.1.characteristic :=
    charP_of_injective_algebraMap (algebraMap (ZMod d.1.characteristic) d.1.Closure).injective _
  exact fun H hCH hH => CFSG.TauCetiBridge.Even.le_adjointGroup_F4_two_rankThree
    (p := d.1.characteristic) d.characteristic_eq_two H hCH hH

theorem nonempty_candidate_equiv_reeF4 (d : ReeF4LieIndex) :
    Nonempty (FixedPointCandidate d.steinberg ≃*
      FixedPointCandidate (reeF d.1.fixedField d.toSuzukiReeIndex.halfExponent)) := by
  have hSS : ∀ g, d.steinberg (d.steinberg g) =
      frobenius (2 * d.toSuzukiReeIndex.halfExponent + 1) d.1.Closure g := fun g => by
    rw [d.steinberg_steinberg, ReeF4LieIndex.frobenius_def,
      d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one]
  exact nonempty_candidate_equiv (zerosInAdjoint_reeF4 d) (isReeSteinberg_reeF4 d) hSS
    (card_fixedField_reeF4 d)

theorem nonempty_candidate_equiv_tits (d : TitsLieIndex) :
    Nonempty (FixedPointCandidate d.steinberg ≃* FixedPointCandidate (reeF d.1.fixedField 0)) := by
  have hSS : ∀ g, d.steinberg (d.steinberg g) = frobenius (2 * 0 + 1) d.1.Closure g := fun g => by
    rw [d.steinberg_steinberg, TitsLieIndex.frobenius_def]
  exact nonempty_candidate_equiv (zerosInAdjoint_tits d) (isReeSteinberg_tits d) hSS
    (card_fixedField_tits d)

end CFSG.TauCetiBridge.ReeF4
