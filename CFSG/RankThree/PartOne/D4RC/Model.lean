module

public import CFSG.RankThree.PartOne.SEITZ7.D4MaxArith
public import CFSG.RankThree.PartOne.SEITZ3.D4Even

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.SEITZ7
open CFSG.RankThree.PartOne.Census3 (IsoLie)



theorem rcg_exists_model {q : TauCeti.PrimePower} (hq : q.p = 2) {K : Type} [Group K] [Finite K]
    (hiso : IsoLie K (.trialityD4 q)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (σ : X →+* X) (_ : CharP X 2)
      (e₀ : K ≃* graphFixedRootGroup TwistTag.D4 X σ) (e : K ≃* twistedGroup σ),
      (∀ c, σ (σ (σ c)) = c) ∧ (∀ c, σ c = c ^ q.card) ∧ Nat.card X = q.card ^ 3 ∧
      Nat.card (fixedField σ) = q.card ∧
      graphFixedRootGroup TwistTag.D4 X σ = (twistedGroup σ).map (adjointGroup d4 X).subtype ∧
      (∀ k, (((e k : twistedGroup σ) : adjointGroup d4 X) : ModGL d4 X) =
        ((e₀ k : graphFixedRootGroup TwistTag.D4 X σ) : ModGL d4 X)) ∧
      Nat.card (twistedGroup σ) = d4Order q.exponent := by
  classical
  have hQ : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
  obtain ⟨X, _, _, σ, hX, hσ', hσ3, ⟨e⟩⟩ := exists_trialityD4_model hq hiso
  have : CharP X 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := q.exponent * 3) (Nat.mul_pos q.exponent_pos (by norm_num)) (by rw [hX, ← pow_mul])
  set σ' : X →+* X := σ.toRingHom with hσ'def
  have hσq : ∀ c, σ' c = c ^ (2 ^ q.exponent) := hσ'
  have hσ3' : ∀ c, σ' (σ' (σ' c)) = c := sigma_three_of_card hX hσq
  have hq2' : 2 ≤ 2 ^ q.exponent := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
  have hXD : Nat.card X = (2 ^ q.exponent) ^ TwistTag.D4.order := hX
  have hC0 : graphFixedRootGroup TwistTag.D4 X σ' =
      (twistedGroup σ').map (adjointGroup d4 X).subtype :=
    (finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two q.exponent_pos X hXD σ'
      hσq).2.2.1.symm.trans (commutator_twistedFixedGroup_eq_map σ' hq2' hX hσq)
  let eΓ : K ≃* twistedGroup σ' := e.trans ((MulEquiv.subgroupCongr hC0).trans
    (Subgroup.equivMapOfInjective _ (adjointGroup d4 X).subtype
      (adjointGroup d4 X).subtype_injective).symm)
  have hF : Nat.card (fixedField σ') = 2 ^ q.exponent := by
    obtain ⟨σ₀, -, -, -, -, k, hk, hkc, -⟩ := finite_graph_field_parameter_fields TwistTag.D4
      Nat.prime_two q.exponent_pos X hXD
    have hfk : fixedField σ' = k := by
      apply SetLike.coe_injective
      rw [hk]
      ext c
      simp [fixedField, RingHom.eqLocusField, hσq]
    rw [hfk]
    exact hkc
  have hΓ : Nat.card (twistedGroup σ') = d4Order q.exponent := by
    rw [← Nat.card_congr eΓ.toEquiv, card_isoLie_trialityD4 hq hiso, hQ]
    rfl
  have hcompat : ∀ k, (((eΓ k : twistedGroup σ') : adjointGroup d4 X) : ModGL d4 X) =
      ((e k : graphFixedRootGroup TwistTag.D4 X σ') : ModGL d4 X) := by
    intro k
    let φ := Subgroup.equivMapOfInjective (twistedGroup σ') (adjointGroup d4 X).subtype
      (adjointGroup d4 X).subtype_injective
    set y := MulEquiv.subgroupCongr hC0 (e k) with hy
    have h1 : φ (φ.symm y) = y := φ.apply_symm_apply y
    have h3 : ((φ (φ.symm y) : (twistedGroup σ').map (adjointGroup d4 X).subtype) : ModGL d4 X) =
        (((φ.symm y : twistedGroup σ') : adjointGroup d4 X) : ModGL d4 X) :=
      Subgroup.coe_equivMapOfInjective_apply _ _ _ _
    rw [h1] at h3
    exact h3.symm
  refine ⟨X, inferInstance, inferInstance, σ', inferInstance, e, eΓ, hσ3', ?_, ?_, ?_, hC0,
    hcompat, hΓ⟩
  · intro c
    rw [hσq, hQ]
  · rw [hX, hQ]
  · rw [hF, hQ]

end CFSG.RankThree.PartOne.D4RC
