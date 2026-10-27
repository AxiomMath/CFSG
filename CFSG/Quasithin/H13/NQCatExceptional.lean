module

public import CFSG.Quasithin.H13.NQCatOuter
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

theorem outer_isCyclic_of_ker_eq_inner {C F : Type*} [Group C] [Group F] [IsCyclic F]
    (Θ : MulAut C →* F) (hker : Θ.ker = inner C) : IsCyclic (Outer C) :=
  isCyclic_of_injective ((QuotientGroup.kerLift Θ).comp
      (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom)
    ((QuotientGroup.kerLift_injective Θ).comp
      (QuotientGroup.quotientMulEquivOfEq hker.symm).injective)

theorem outer_isCyclic_of_even_G2_model
    {S : Type} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : IsCyclic (Outer S) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨Θ, -, -, hΘker, -⟩ :=
    (ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK).2
  obtain ⟨σ, -, -, hσ, -, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩
  have : IsCyclic (Outer (adjointGroup .G2 K)) := outer_isCyclic_of_ker_eq_inner Θ hΘker
  let e' : S ≃* adjointGroup .G2 K := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  exact isCyclic_of_injective (equivalence e').toMonoidHom (equivalence e').injective

theorem outer_isCyclic_of_even_trialityD4_model
    {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) : IsCyclic (Outer S) := by
  obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  let σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : σ'.toRingHom = σ := RingHom.ext fun _ => rfl
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, -, -, -, ⟨e₀⟩⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK3 σ' hσ
  have : IsCyclic (Outer (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) :=
    outer_isCyclic_of_ker_eq_inner Θ hΘker
  rw [hσ'] at e₀ this
  let e' := e.trans e₀
  exact isCyclic_of_injective (equivalence e').toMonoidHom (equivalence e').injective

theorem sqt_exceptional_central_quotient_outer_prime_control
    (J : Type) [Group J] [Finite J]
    [Group.IsPerfect J] (hSQT : CFSG.IsStronglyQuasithin (J ⧸ Subgroup.center J))
    (hrep : ExceptionalRep (J ⧸ Subgroup.center J)) :
    (IsCyclic (Outer J) ∨ IsPGroup 2 (Outer J)) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 →
        (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1 := by
  have hinj := (LocalAnalysis.ComponentInitial.perfect_central_quotient_Schreier J).1
  have hcyc : IsCyclic (Outer (J ⧸ Subgroup.center J)) → IsCyclic (Outer J) := fun h =>
    isCyclic_of_injective _ hinj
  have hJ : IsCyclic (Outer J) ∨ IsPGroup 2 (Outer J) := by
    rcases SectionRank.sqt_exceptional_restriction (SectionRank.isStronglyQuasithin_iff.1 hSQT)
        hrep with ⟨f, hf, hG2⟩ | ⟨f, hf, hD4⟩ | ⟨f, -, -, hF4⟩ | hTits | ⟨f, -, -, hSz⟩
    · exact Or.inl (hcyc (outer_isCyclic_of_even_G2_model hf hG2))
    · exact Or.inl (hcyc (outer_isCyclic_of_even_trialityD4_model hf hD4))
    · exact Or.inl (hcyc
        (large_Ree_model_field_outer_group_and_inner_involutions _ 2 f hF4).2.2.2.1)
    · exact Or.inr ((Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ 2 1 hTits).1.of_injective _
        hinj)
    · exact Or.inl ((LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity _ 2 f hSz).2 J
        ⟨MulEquiv.refl _⟩).1
  refine ⟨hJ, fun ℓ hℓ hℓ2 => ?_⟩
  have : Finite (MulAut J) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut J))
  rcases hJ with h | h
  · exact sylow_isCyclic_pRank_le_one_of_isCyclic hℓ
  · exact sylow_isCyclic_pRank_le_one_of_isPGroup_two h hℓ hℓ2

end CFSG.Quasithin.H13.NQCat
