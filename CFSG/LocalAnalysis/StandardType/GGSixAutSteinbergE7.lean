module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergF4
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.Steinberg.Adjoint.CertE7
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

namespace AutSt

theorem exists_orth_E7 : ∀ j : Fin (Tag.rank .E7), ∃ k, k ≠ j ∧ Tag.cartan .E7 k j = 0 := by
  intro j
  fin_cases j <;> decide

theorem exists_nbr_E7 : ∀ k : Fin (Tag.rank .E7), ∃ l, Tag.cartan .E7 k l = -1 := by
  intro k
  fin_cases k <;> decide


variable {K : Type} [Field K]

theorem isSimpleGroup_fixSub_E7 {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 2 ^ (2 * e))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e) :
    IsSimpleGroup (fixSub (entrywiseAdjointAut .E7 σ)) := by
  obtain ⟨-, -, -, hmap, ⟨-, hsimple, -⟩, -⟩ :=
    even_E7_E8_canonical_field_full_centralizer .E7 (Or.inl rfl) he K hK σ hσ
  let e₁ : fixSub (entrywiseAdjointAut .E7 σ) ≃* fixedFieldImage .E7 σ :=
    (Subgroup.equivMapOfInjective _ (adjointGroup .E7 K).subtype Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have : Nontrivial (fixSub (entrywiseAdjointAut .E7 σ)) := e₁.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e₁.symm.toMonoidHom e₁.symm.surjective

theorem autModel_E7 [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    GGAutModel (adjointGroup .E7 K) (GGModelRoot (e7Datum K) .E7 (e7Isogeny K)) := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E7 (Or.inl rfl)
  have hΘσ : ∀ σ, Θ (entrywiseAdjointAut .E7 σ) = σ := fun σ => hΘ _ 1 σ fun h => by
    rw [coe_entrywiseAdjointAut]
    simp
  refine autModel_of_hom Θ (entrywiseAdjointAutHom (τ := .E7) (K := K)).range (by rw [hker])
    (by rw [hker, Subgroup.relIndex_self]; exact odd_one)
    (fun σ => ⟨entrywiseAdjointAut .E7 (Θ σ), ⟨Θ σ, rfl⟩, hΘσ _⟩) ?_ ?_
  · rintro _ ⟨σ, rfl⟩ h1
    change Θ (entrywiseAdjointAut .E7 σ) = 1 at h1
    change entrywiseAdjointAut .E7 σ = 1
    rw [hΘσ] at h1
    rw [h1, entrywiseAdjointAut_one]
  · rintro r hr _ ⟨σ, rfl⟩ hc2 hc1 e he
    rw [hker] at he
    refine goodAut_conj_inner ?_ he
    change entrywiseAdjointAut .E7 σ ^ 2 = 1 at hc2
    change entrywiseAdjointAut .E7 σ ≠ 1 at hc1
    change GGGoodAut r (entrywiseAdjointAut .E7 σ)
    rcases hinv _ hc2 with h1 | ⟨heven, hpow⟩
    · exfalso
      rw [hΘσ] at h1
      exact hc1 (by rw [h1, entrywiseAdjointAut_one])
    obtain ⟨e, rfl⟩ : ∃ e, f = 2 * e := by
      obtain ⟨e, he⟩ := heven
      exact ⟨e, by omega⟩
    have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => by
      rw [← hΘσ σ, hpow c, show 2 * e / 2 = e by omega]
    have hJ := isSimpleGroup_fixSub_E7 (by omega) hK σ hσ
    obtain ⟨hr2, γ, ⟨hγ, -⟩, u, z, hz, rfl⟩ := hr
    have hγ' : IsRoot .E7 γ := e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hz
    rw [map_mul, map_mul, map_inv, e7Isogeny_xm] at hr2 ⊢
    have hz' := xPar_mem (F := rootOperatorFamily .E7) (K := K) hγ' ((e7Eps γ : K) * c)
    have hz1 : xPar (rootOperatorFamily .E7) γ ((e7Eps γ : K) * c) ≠ 1 := by
      intro h
      rw [h, mul_one, mul_inv_cancel, orderOf_one] at hr2
      exact absurd hr2 (by norm_num)
    exact goodAut_of_entrywise e7AdjData_valid noG2_E7 exists_orth_E7 exists_nbr_E7 hJ hγ' hz' hz1

end AutSt

section Family


theorem ggAutModelAt_E7 : GGAutModelAt .E7 := by
  intro n f hadm _ _
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact ⟨adjointGroup .E7 (GaloisField 2 f), inferInstance, e7Isogeny (GaloisField 2 f),
    e7Isogeny_surjective _, CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center,
    AutSt.autModel_E7 hf hK⟩

theorem ggAutStructureAt_E7 : GGAutStructureAt .E7 :=
  ggAutStructureAt_of_autModelAt ggAutModelAt_E7

end Family

end CFSG.StandardType
