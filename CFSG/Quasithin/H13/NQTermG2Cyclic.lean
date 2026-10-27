module

public import CFSG.Quasithin.H13.NQTermCommonSylow
public import CFSG.Quasithin.SteinbergCDEvenOrdinaryThreeFreeBorel
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup pairAutRestrict)
open scoped Pointwise

theorem threeFreeBorelDatum_adjoint
    (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2] :
    ThreeFreeBorelDatum ((posUnipotent τ K).subgroupOf (adjointGroup τ K))
      ((borelGroup τ K).subgroupOf (adjointGroup τ K)) where
  le := fun x hx => (le_sup_right : posUnipotent τ K ≤ borelGroup τ K) hx
  commutator_le := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_subgroupOf]
    have h := commutator_borelGroup_le (τ := τ) (K := K)
      (Subgroup.commutator_mem_commutator hg₁ hg₂)
    simpa [commutatorElement_def] using h
  normalizer_le := by
    intro g hg
    rw [← Subgroup.subgroupOf_normalizer_eq posUnipotent_le_adjointGroup,
      Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_subgroupOf, ← (borel_self_normalizers τ K).1]
    exact ⟨g.2, hg⟩
  isPGroup := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
    obtain ⟨⟨P, hP⟩, -⟩ := exceptional_ordinary_Sylow_opposition τ K 2 w₀ hw₀
    rw [← hP]
    exact P.isPGroup'
  three_free D hUD h3 := by
    have hle := Quasithin.SteinbergCD.even_ordinary_three_free_posUnipotent_overgroups_le_borelGroup
      (τ := τ) (K := K) (D := D.map (adjointGroup τ K).subtype) (Subgroup.map_subtype_le D)
      (fun u hu => ⟨⟨u, posUnipotent_le_adjointGroup hu⟩, hUD hu, rfl⟩)
      (by rwa [Subgroup.card_map_of_injective (adjointGroup τ K).subtype_injective])
    intro x hx
    exact hle ⟨x, hx, rfl⟩

theorem even_G2_common_sylow_odd_subgroup_normalizer_action_is_cyclic
    {f : ℕ} (hf : 2 ≤ f)
    (k : Type) [Field k] (hk : Nat.card k = 2 ^ f) (U : Sylow 2 (adjointGroup .G2 k))
    (A : Subgroup (adjointGroup .G2 k)) (hAodd : Odd (Nat.card A)) (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set (adjointGroup .G2 k)) * (U : Set (adjointGroup .G2 k)) =
      (U : Set (adjointGroup .G2 k)) * (A : Set (adjointGroup .G2 k))) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
    (∀ α ∈ pairAutSubgroup A (U : Subgroup (adjointGroup .G2 k)) ⊓
        (MulAut.conj : adjointGroup .G2 k →* MulAut (adjointGroup .G2 k)).range,
      ∀ a ∈ A, α a = a) ∧
    (IsCyclic (pairAutRestrict A (U : Subgroup (adjointGroup .G2 k))).range ∧
      Nat.card (pairAutRestrict A (U : Subgroup (adjointGroup .G2 k))).range ∣ f) ∧
    ∀ Δ : Subgroup (pairAutSubgroup A (U : Subgroup (adjointGroup .G2 k))),
      IsCyclic (Δ.map (pairAutRestrict A (U : Subgroup (adjointGroup .G2 k)))) ∧
        Nat.card (Δ.map (pairAutRestrict A (U : Subgroup (adjointGroup .G2 k)))) ∣ f := by
  classical
  have hp : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have hf1 : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf1 hk
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem .G2).length
  obtain ⟨⟨P₀, hP₀⟩, -⟩ := exceptional_ordinary_Sylow_opposition .G2 k 2 w₀ hw₀
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (adjointGroup .G2 k) P₀ U
  have hUc : (U : Subgroup (adjointGroup .G2 k)) =
      ((posUnipotent .G2 k).subgroupOf (adjointGroup .G2 k)).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, coe_smul_sylow_eq_map, hP₀]
  have hdat := (threeFreeBorelDatum_adjoint .G2 k).map (MulAut.conj c)
  rw [← hUc] at hdat
  obtain ⟨-, -, hcomm, hfix⟩ := hdat.commute_of_permutable A hAodd hA3 hAU
  have hinner : ∀ α ∈ pairAutSubgroup A (U : Subgroup (adjointGroup .G2 k)) ⊓
      (MulAut.conj : adjointGroup .G2 k →* MulAut (adjointGroup .G2 k)).range,
        ∀ a ∈ A, α a = a := by
    rintro α ⟨hαΓ, g, rfl⟩ a ha
    exact hfix g (mem_normalizer_of_map_conj_eq hαΓ.2) (mem_normalizer_of_map_conj_eq hαΓ.1) a ha
  refine ⟨hcomm, hinner, ?_⟩
  obtain ⟨Θ, -, -, hΘker, -⟩ :=
    (ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf k hk).2
  obtain ⟨σ, -, -, hσ, hcard, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf1 hk
  have : Finite (k ≃+* k) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have : IsCyclic (k ≃+* k) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩
  set Γ := pairAutSubgroup A (U : Subgroup (adjointGroup .G2 k))
  set ρ := pairAutRestrict A (U : Subgroup (adjointGroup .G2 k))
  have hker : (Θ.comp Γ.subtype).ker ≤ ρ.ker := by
    intro α hα
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hΘker] at hα
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    exact hinner α ⟨α.2, hα⟩ a a.2
  have hΔ := map_isCyclic_of_ker_le (Θ.comp Γ.subtype) ρ hker
  rw [hcard] at hΔ
  refine ⟨?_, hΔ⟩
  rw [MonoidHom.range_eq_map]
  exact hΔ ⊤

end CFSG.Quasithin.H13.NQTerm
