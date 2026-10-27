module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOn
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.Adapters.TauCetiExceptional.TwistedTransfer
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.RootWeightFiltrationData

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem exists_rootWeightDatum_untwisted {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : TauCetiBridge.UntwistedBridge τ c) (q : TauCeti.PrimePower) (hv : (c q).Valid)
    (hq : q.p ≠ 2) :
    ∃ D : RootWeightDatum (TauCetiBridge.fieldOf q 1),
      Nonempty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃* ↥D.group) := by
  have hK : Nat.card (TauCetiBridge.fieldOf q 1) = q.card := by
    simpa using TauCetiBridge.card_fieldOf q Nat.one_pos
  obtain ⟨φ⟩ := hB q hv hq (TauCetiBridge.fieldOf q 1) hK
  have hψ : AdjointQuotient τ (TauCetiBridge.fieldOf q 1) ≃*
      ↥(adjointGroup τ (TauCetiBridge.fieldOf q 1)) :=
    (QuotientGroup.quotientMulEquivOfEq
        (center_adjointGroup_eq_bot (τ := τ) (K := TauCetiBridge.fieldOf q 1))).trans
      QuotientGroup.quotientBot
  exact ⟨.ordinary τ, ⟨φ.symm.trans hψ⟩⟩

theorem exists_rootWeightDatum_twisted {t : TwistTag}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex} (hB : TauCetiBridge.TwistedBridge t c)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (hq : q.p ≠ 2) :
    ∃ D : RootWeightDatum (TauCetiBridge.fieldOf q t.order),
      Nonempty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃* ↥D.group) := by
  have hm : 0 < t.order := by cases t <;> decide
  have hKcard : Nat.card (TauCetiBridge.fieldOf q t.order) = q.card ^ t.order :=
    TauCetiBridge.card_fieldOf q hm
  obtain ⟨φ⟩ := hB q hv hq (TauCetiBridge.fieldOf q t.order) hKcard
    (TauCetiBridge.frobOf q t.order) (TauCetiBridge.frobOf_apply q t.order)
  have hK' : Nat.card (TauCetiBridge.fieldOf q t.order) =
      (q.p ^ q.exponent) ^ t.order := by
    rw [← TauCeti.PrimePower.card_def]
    exact hKcard
  have hσ' : ∀ x, TauCetiBridge.frobOf q t.order x = x ^ (q.p ^ q.exponent) := by
    intro x
    rw [TauCetiBridge.frobOf_apply q t.order, TauCeti.PrimePower.card_def]
  have hν := TauCetiBridge.Twisted.nativeEquiv (t := t)
    (K := TauCetiBridge.fieldOf q t.order) (σ := TauCetiBridge.frobOf q t.order)
    (p := q.p) (f := q.exponent) q.prime_p q.exponent_pos hK' hσ'
  set τ' : TauCetiBridge.fieldOf q t.order ≃+* TauCetiBridge.fieldOf q t.order :=
    TauCetiBridge.Twisted.sigmaEquiv (TauCetiBridge.frobOf q t.order) with hτ'
  have hτ'_apply : ∀ y : TauCetiBridge.fieldOf q t.order, τ' y = y ^ q.card := by
    intro y
    rw [hτ']
    exact TauCetiBridge.frobOf_apply q t.order y
  have hpow : ∀ n : ℕ, ∀ x : TauCetiBridge.fieldOf q t.order,
      (τ' ^ n) x = x ^ (q.card ^ n) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ', RingAut.mul_apply, ih x, map_pow, hτ'_apply, ← pow_mul, pow_succ']
  have hσm : τ' ^ t.order = 1 := by
    haveI : Fintype (TauCetiBridge.fieldOf q t.order) :=
      Fintype.ofFinite (TauCetiBridge.fieldOf q t.order)
    ext x
    rw [hpow t.order x, show (1 : TauCetiBridge.fieldOf q t.order ≃+* _) x = x from rfl,
      ← hKcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  refine ⟨.fixed t τ' hσm, ?_⟩
  show Nonempty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃*
    ↥(graphFixedRootGroup t (TauCetiBridge.fieldOf q t.order) τ'.toRingHom))
  rw [hτ', TauCetiBridge.Twisted.sigmaEquiv_toRingHom]
  exact ⟨φ.symm.trans hν⟩

theorem exists_rootWeightDatum_of_not_open (d : TauCeti.ValidLieTypeIndex)
    (hd : ¬ GGLieParabolicOpenIndex d) (h2 : d.1.characteristic ≠ 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K d.1.characteristic)
      (D : RootWeightDatum K), Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* ↥D.group) := by
  obtain ⟨i, hv⟩ := d
  cases i with
  | A n q => exact absurd trivial hd
  | twistedA n q => exact absurd trivial hd
  | B n q => exact absurd trivial hd
  | C n q => exact absurd trivial hd
  | D n q => exact absurd trivial hd
  | twistedD n q => exact absurd trivial hd
  | reeG2 n => exact absurd trivial hd
  | suzuki n => exact absurd (TauCeti.LieTypeIndex.characteristic_suzuki n) h2
  | reeF4 n => exact absurd (TauCeti.LieTypeIndex.characteristic_reeF4 n) h2
  | tits => exact absurd TauCeti.LieTypeIndex.characteristic_tits h2
  | G2 q =>
      have hq : q.p ≠ 2 := by
        simpa [TauCeti.LieTypeIndex.characteristic_G2] using h2
      obtain ⟨D, hD⟩ :=
        exists_rootWeightDatum_untwisted TauCetiBridge.chevalleyBridges.g2 q hv hq
      exact ⟨TauCetiBridge.fieldOf q 1, inferInstance, inferInstance,
        by rw [TauCeti.LieTypeIndex.characteristic_G2]; infer_instance, D, hD⟩
  | F4 q =>
      have hq : q.p ≠ 2 := by
        simpa [TauCeti.LieTypeIndex.characteristic_F4] using h2
      obtain ⟨D, hD⟩ :=
        exists_rootWeightDatum_untwisted TauCetiBridge.chevalleyBridges.f4 q hv hq
      exact ⟨TauCetiBridge.fieldOf q 1, inferInstance, inferInstance,
        by rw [TauCeti.LieTypeIndex.characteristic_F4]; infer_instance, D, hD⟩
  | E6 q =>
      have hq : q.p ≠ 2 := by
        simpa [TauCeti.LieTypeIndex.characteristic_E6] using h2
      obtain ⟨D, hD⟩ :=
        exists_rootWeightDatum_untwisted TauCetiBridge.chevalleyBridges.e6 q hv hq
      exact ⟨TauCetiBridge.fieldOf q 1, inferInstance, inferInstance,
        by rw [TauCeti.LieTypeIndex.characteristic_E6]; infer_instance, D, hD⟩
  | E7 q =>
      have hq : q.p ≠ 2 := by
        simpa [TauCeti.LieTypeIndex.characteristic_E7] using h2
      obtain ⟨D, hD⟩ :=
        exists_rootWeightDatum_untwisted TauCetiBridge.chevalleyBridges.e7 q hv hq
      exact ⟨TauCetiBridge.fieldOf q 1, inferInstance, inferInstance,
        by rw [TauCeti.LieTypeIndex.characteristic_E7]; infer_instance, D, hD⟩
  | E8 q =>
      have hq : q.p ≠ 2 := by
        simpa [TauCeti.LieTypeIndex.characteristic_E8] using h2
      obtain ⟨D, hD⟩ :=
        exists_rootWeightDatum_untwisted TauCetiBridge.chevalleyBridges.e8 q hv hq
      exact ⟨TauCetiBridge.fieldOf q 1, inferInstance, inferInstance,
        by rw [TauCeti.LieTypeIndex.characteristic_E8]; infer_instance, D, hD⟩
  | twistedE6 q =>
      have hq : q.p ≠ 2 := by
        simpa [TauCeti.LieTypeIndex.characteristic_twistedE6] using h2
      obtain ⟨D, hD⟩ := exists_rootWeightDatum_twisted (t := .E6)
        TauCetiBridge.chevalleyBridges.twistedE6 q hv hq
      exact ⟨TauCetiBridge.fieldOf q 2, inferInstance, inferInstance,
        by rw [TauCeti.LieTypeIndex.characteristic_twistedE6]; infer_instance, D, hD⟩
  | trialityD4 q =>
      have hq : q.p ≠ 2 := by
        simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using h2
      obtain ⟨D, hD⟩ := exists_rootWeightDatum_twisted (t := .D4)
        TauCetiBridge.chevalleyBridges.trialityD4 q hv hq
      exact ⟨TauCetiBridge.fieldOf q 3, inferInstance, inferInstance,
        by rw [TauCeti.LieTypeIndex.characteristic_trialityD4]; infer_instance, D, hD⟩

end CFSG.StandardType
