module

public import CFSG.RankThree.PartOne.SEITZ7.D4Odd
public import CFSG.RankThree.PartOne.SEITZ3.D4Even

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem transport_max {K Γ : Type} [Group K] [Group Γ] (e : K ≃* Γ) {A B : Subgroup Γ}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hmax : ∀ N : Subgroup Γ, A ⊔ B ≤ N → N = A ⊔ B ∨ N = ⊤) :
    ∃ A' B' : Subgroup K, Nonempty (A' ≃* A) ∧ Nonempty (B' ≃* B) ∧
      (∀ a ∈ A', ∀ b ∈ B', a * b = b * a) ∧ A' ⊓ B' = ⊥ ∧
      ∀ N : Subgroup K, A' ⊔ B' ≤ N → N = A' ⊔ B' ∨ N = ⊤ := by
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  refine ⟨A.map e.symm.toMonoidHom, B.map e.symm.toMonoidHom,
    ⟨(MulEquiv.subgroupMap e.symm A).symm⟩, ⟨(MulEquiv.subgroupMap e.symm B).symm⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e.symm a * e.symm b = e.symm b * e.symm a
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [← Subgroup.map_inf_eq A B e.symm.toMonoidHom hinj, hinf, Subgroup.map_bot]
  · intro N hN
    have hle : A ⊔ B ≤ N.map e.toMonoidHom := by
      intro x hx
      refine ⟨e.symm x, hN ?_, by simp⟩
      rw [← Subgroup.map_sup]
      exact ⟨x, hx, rfl⟩
    rcases hmax _ hle with h | h
    · left
      have : N = (N.map e.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map]
        ext x
        simp
      rw [this, h, Subgroup.map_sup]
    · right
      have : N = (N.map e.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map]
        ext x
        simp
      rw [this, h, Subgroup.map_top_of_surjective _ e.symm.surjective]

theorem max3D4A1A1Big_of_top
    (hgold : CFSG.Goldschmidt.TopStatement) : Max3D4A1A1Big := by
  intro q hq h4 K _ _ _ hiso
  have hQ : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
  have hexp : 2 ≤ q.exponent := by
    by_contra h
    have h1 := q.exponent_pos
    have : q.exponent = 1 := by omega
    rw [hQ, this] at h4
    norm_num at h4
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
  have hmaxΓ : ∀ N : Subgroup (twistedGroup σ'),
      Asub σ' hσ3' ⊔ Bsub σ' hσ3' ≤ N → N = Asub σ' hσ3' ⊔ Bsub σ' hσ3' ∨ N = ⊤ := fun N hN =>
    core_max_tw hgold hσ3' hexp hX hF N hN ((Subgroup.card_subgroup_dvd_card N).trans hΓ.dvd)
      (fun R _ hRn hodd => odd_core_trivial_tw hσ3' hexp hX hF hN hRn hodd)
  obtain ⟨A', B', hA', hB', hcomm', hinf', hmax'⟩ := transport_max eΓ
    (Asub_Bsub_commute σ' hσ3') (Asub_inf_Bsub σ' hσ3') hmaxΓ
  refine ⟨A', B', X, fixedField σ', inferInstance, inferInstance, by rw [hQ]; exact hX,
    by rw [hQ]; exact hF, ⟨hA'.some.trans (MonoidHom.ofInjective (slShort_injective hσ3')).symm⟩,
    ⟨hB'.some.trans (MonoidHom.ofInjective (psiB_injective σ' hσ3')).symm⟩, hcomm', hinf', hmax'⟩

end CFSG.RankThree.PartOne.SEITZ7
