module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

namespace AutSt

theorem exists_orth_E8 : ∀ j : Fin (Tag.rank .E8), ∃ k, k ≠ j ∧ Tag.cartan .E8 k j = 0 := by
  intro j
  fin_cases j <;> decide


variable {K : Type} [Field K]

theorem isSimpleGroup_fixSub_E8 {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    IsSimpleGroup (fixSub (entrywiseAdjointAut .E8 σ)) := by
  obtain ⟨-, -, -, hmap, ⟨-, hsimple, -⟩, -⟩ :=
    even_E7_E8_canonical_field_full_centralizer .E8 (Or.inr rfl) he K hK σ hσ
  let e₁ : fixSub (entrywiseAdjointAut .E8 σ) ≃* fixedFieldImage .E8 σ :=
    (Subgroup.equivMapOfInjective _ (adjointGroup .E8 K).subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have : Nontrivial (fixSub (entrywiseAdjointAut .E8 σ)) := e₁.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e₁.symm.toMonoidHom e₁.symm.surjective

theorem goodAut_E8 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K}
    (hσ2 : entrywiseAdjointAut .E8 σ ^ 2 = 1) (hσ1 : entrywiseAdjointAut .E8 σ ≠ 1)
    {r : adjointGroup .E8 K} (hr : GGModelRoot (e8Datum K) .E8 (MonoidHom.id _) r) :
    GGGoodAut r (entrywiseAdjointAut .E8 σ) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, Θ, hΘ, -, -, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E8 (Or.inr rfl)
  have hΘσ : Θ (entrywiseAdjointAut .E8 σ) = σ := hΘ _ 1 σ fun h => by
    rw [coe_entrywiseAdjointAut]
    simp
  rcases hinv _ hσ2 with h1 | ⟨heven, hpow⟩
  · exfalso
    rw [hΘσ] at h1
    exact hσ1 (by rw [h1, entrywiseAdjointAut_one])
  obtain ⟨e, rfl⟩ : ∃ e, f = 2 * e := by
    obtain ⟨e, he⟩ := heven
    exact ⟨e, by omega⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => by
    rw [← hΘσ, hpow c, show 2 * e / 2 = e by omega]
  have hJ := isSimpleGroup_fixSub_E8 (by omega) hK σ hσ
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, z, hz, hrz⟩ := hr
  rw [MonoidHom.id_apply] at hrz
  subst hrz
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  obtain ⟨g, j, hg⟩ := exists_conj_xPar_single (F := rootOperatorFamily .E8) hγ' hz hz1
  obtain ⟨k, hkj, h0⟩ := exists_orth_E8 j
  obtain ⟨l, hkl, -⟩ := CFSG.LieType.Steinberg.Adjoint.neighbour_E8 k
  have ha3 := orderOf_xPar_mul_xPar_neg (F := rootOperatorFamily .E8) (K := K) hkl
  have hcomm := commute_xPar_single_xy (F := rootOperatorFamily .E8) e8Data_valid noG2_E8
    hkj.symm h0 (1 : K)
  have hconj : g * u⁻¹ * (u * z * u⁻¹) * (g * u⁻¹)⁻¹ = g * z * g⁻¹ := by group
  refine goodAut_of_fixed_simple hJ (g * u⁻¹) ?_
    (xPar (rootOperatorFamily .E8) (Pi.single k 1) 1 *
      xPar (rootOperatorFamily .E8) (-Pi.single k 1) 1)
    ?_ ?_ ?_ ?_
  · rw [hconj, hg, entrywiseAdjointAut_xPar_one]
  · rw [map_mul, entrywiseAdjointAut_xPar_one, entrywiseAdjointAut_xPar_one]
  · rw [hconj, hg]
    exact hcomm.eq.symm
  · intro h
    rw [h, orderOf_one] at ha3
    exact absurd ha3 (by norm_num)
  · rw [ha3]
    decide

theorem autModel_E8 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    GGAutModel (adjointGroup .E8 K) (GGModelRoot (e8Datum K) .E8 (MonoidHom.id _)) := by
  obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E8 (Or.inr rfl)
  have hΘσ : ∀ σ, Θ (entrywiseAdjointAut .E8 σ) = σ := fun σ => hΘ _ 1 σ fun h => by
    rw [coe_entrywiseAdjointAut]
    simp
  refine autModel_of_hom Θ (entrywiseAdjointAutHom (τ := .E8) (K := K)).range (by rw [hker])
    (by rw [hker, Subgroup.relIndex_self]; exact odd_one)
    (fun σ => ⟨entrywiseAdjointAut .E8 (Θ σ), ⟨Θ σ, rfl⟩, hΘσ _⟩) ?_ ?_
  · rintro _ ⟨σ, rfl⟩ h1
    change Θ (entrywiseAdjointAut .E8 σ) = 1 at h1
    change entrywiseAdjointAut .E8 σ = 1
    rw [hΘσ] at h1
    rw [h1, entrywiseAdjointAut_one]
  · rintro r hr _ ⟨σ, rfl⟩ hc2 hc1 e he
    rw [hker] at he
    exact goodAut_conj_inner (goodAut_E8 hf hK hc2 hc1 hr) he

end AutSt

section Family


theorem ggAutModelAt_E8 : GGAutModelAt .E8 := by
  intro n f hadm _ _
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨(ggU .E8 n f).K, inferInstance, MonoidHom.id _, Function.surjective_id, ?_,
    AutSt.autModel_E8 hf hK⟩
  rw [MonoidHom.ker_id]
  exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).symm

theorem ggAutStructureAt_E8 : GGAutStructureAt .E8 :=
  ggAutStructureAt_of_autModelAt ggAutModelAt_E8

end Family

end CFSG.StandardType
