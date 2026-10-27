module

public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_surj_of_quotient_center {Y C : Type*} [Group Y] [Group C]
    (hZ : Subgroup.center C = ⊥) (e : Y ⧸ Subgroup.center Y ≃* C ⧸ Subgroup.center C) :
    ∃ φ : Y →* C, Function.Surjective φ ∧ φ.ker = Subgroup.center Y := by
  let E : Y ⧸ Subgroup.center Y ≃* C :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  refine ⟨E.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y)),
    E.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ E.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem exists_surj_graphFixedRootGroup_of_model {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (h : TwistedChevalleyModel (Y ⧸ Subgroup.center Y) .E6 (p ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (p ^ f) ^ 2 ∧
      ∃ σ : K →+* K, (∀ c, σ c = c ^ (p ^ f)) ∧
        ∃ φ : Y →* graphFixedRootGroup TwistTag.E6 K σ, Function.Surjective φ ∧
          φ.ker = Subgroup.center Y := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hsurjσ : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hΓ := (finite_fixed_root_group_perfect TwistTag.E6 hp hf K hK σ hσ).2.2.1
  have hcong : ∀ A B : Subgroup (ModGL TwistTag.E6.tag K), A = B →
      Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) := by
    rintro A B rfl
    exact ⟨MulEquiv.refl _⟩
  obtain ⟨e₁⟩ := hcong _ _ hΓ
  exact ⟨K, inferInstance, inferInstance, hK, σ, hσ,
    exists_surj_of_quotient_center (center_graphFixedRootGroup_eq_bot hsurjσ) (e.trans e₁)⟩

theorem exists_surj_adjointGroup_of_model {Y : Type} [Group Y] {τ : Tag} {q : ℕ}
    (h : UntwistedChevalleyModel (Y ⧸ Subgroup.center Y) τ q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
      ∃ φ : Y →* adjointGroup τ K, Function.Surjective φ ∧ φ.ker = Subgroup.center Y := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK,
    exists_surj_of_quotient_center center_adjointGroup_eq_bot e⟩

theorem card_eqLocusField_of_pow {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (p ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Nat.card (RingHom.eqLocusField σ (RingHom.id K)) = p ^ f := by
  obtain ⟨-, -, -, -, -, k, hk, hkcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 hp hf K hK
  have e : RingHom.eqLocusField σ (RingHom.id K) = k := by
    ext c
    rw [RingHom.mem_eqLocusField, RingHom.id_apply, hσ, ← SetLike.mem_coe, hk]
    rfl
  rw [e, hkcard]

theorem ringChar_eq_of_card {K : Type} [Field K] {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hK : Nat.card K = p ^ n) : ringChar K = p := by
  have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hn hK
  exact ringChar.eq K p

end CFSG.RankThree.Chevalley
