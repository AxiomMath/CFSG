module

public import CFSG.Quasithin.H13.NQTermCommonSylow
public import CFSG.Quasithin.SteinbergCDEvenFixedThreeFreeBorel
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (pairAutSubgroup pairAutRestrict)
open scoped Pointwise commutatorElement

theorem threeFreeBorelDatum_fixed
    (t : TwistTag) (K : Type) [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) :
    ThreeFreeBorelDatum
      ((graphFixedPosUnipotent t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom))
      ((graphFixedRootBorel t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom)) where
  le := fun x hx => graphFixedPosUnipotent_le_graphFixedRootBorel hx
  commutator_le := by
    obtain ⟨-, hBUH, -, -, -, hUnorm, -, hHab, -⟩ := fixed_root_Bruhat_decomposition t K σ
    have hN : ∀ x ∈ graphFixedRootTorus t K σ.toRingHom,
        ∀ u ∈ graphFixedPosUnipotent t K σ.toRingHom,
          x * u * x⁻¹ ∈ graphFixedPosUnipotent t K σ.toRingHom := by
      intro x hx u hu
      have hxB := graphFixedRootTorus_le_graphFixedRootBorel hx
      have huB := graphFixedPosUnipotent_le_graphFixedRootBorel hu
      have := hUnorm.conj_mem ⟨u, huB⟩ hu ⟨x, hxB⟩
      exact this
    have hcomm := commutator_le_of_coe_eq_mul hBUH hHab hN
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_subgroupOf]
    have h := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hg₁)
      (Subgroup.mem_subgroupOf.1 hg₂))
    have e : ((⁅g₁, g₂⁆ : graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K) =
        ⁅(g₁ : ModGL t.tag K), (g₂ : ModGL t.tag K)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact h
  normalizer_le := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
    obtain ⟨-, -, -, -, -, -, hNU, -⟩ := fixed_Borel_self_normalizers t K σ w₀ hw₀
    intro g hg
    rw [← Subgroup.subgroupOf_normalizer_eq
      (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom),
      Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_subgroupOf, ← hNU]
    exact ⟨g.2, hg⟩
  isPGroup := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
    obtain ⟨⟨P, hP⟩, -⟩ := exceptional_fixed_Sylow_opposition t K 2 σ w₀ hw₀
    rw [← hP]
    exact P.isPGroup'
  three_free D hUD h3 := by
    have hle := Quasithin.SteinbergCD.even_diagram_fixed_three_free_posUnipotent_overgroups_le_borel
      t K σ (D := D.map (graphFixedRootGroup t K σ.toRingHom).subtype) (Subgroup.map_subtype_le D)
      (fun u hu => ⟨⟨u, graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom hu⟩,
        hUD hu, rfl⟩)
      (by rwa [Subgroup.card_map_of_injective
        (graphFixedRootGroup t K σ.toRingHom).subtype_injective])
    intro x hx
    exact hle ⟨x, hx, rfl⟩

theorem even_triality_common_sylow_odd_subgroup_normalizer_action_is_cyclic
    {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (U : Sylow 2 (graphFixedRootGroup TwistTag.D4 K σ))
    (A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)) (hAodd : Odd (Nat.card A))
    (hA3 : ¬ 3 ∣ Nat.card A)
    (hAU : (A : Set (graphFixedRootGroup TwistTag.D4 K σ)) *
        (U : Set (graphFixedRootGroup TwistTag.D4 K σ)) =
      (U : Set (graphFixedRootGroup TwistTag.D4 K σ)) *
        (A : Set (graphFixedRootGroup TwistTag.D4 K σ))) :
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
    (∀ α ∈ pairAutSubgroup A (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)) ⊓
        (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ →*
          MulAut (graphFixedRootGroup TwistTag.D4 K σ)).range,
      ∀ a ∈ A, α a = a) ∧
    (IsCyclic (pairAutRestrict A (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ))).range ∧
      Nat.card (pairAutRestrict A (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ))).range ∣
        3 * f) ∧
    ∀ Δ : Subgroup (pairAutSubgroup A (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ))),
      IsCyclic (Δ.map (pairAutRestrict A (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)))) ∧
        Nat.card (Δ.map (pairAutRestrict A
          (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ)))) ∣ 3 * f := by
  classical
  have hp : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩, rfl⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨⟨P₀, hP₀⟩, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ' w₀ hw₀
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) P₀ U
  have hUc : (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) =
      ((graphFixedPosUnipotent TwistTag.D4 K σ'.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, coe_smul_sylow_eq_map, hP₀]
  have hdat := (threeFreeBorelDatum_fixed TwistTag.D4 K σ').map (MulAut.conj c)
  rw [← hUc] at hdat
  obtain ⟨-, -, hcomm, hfix⟩ := hdat.commute_of_permutable A hAodd hA3 hAU
  have hinner : ∀ α ∈ pairAutSubgroup A
      (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) ⊓
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ'.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)).range,
        ∀ a ∈ A, α a = a := by
    rintro α ⟨hαΓ, g, rfl⟩ a ha
    exact hfix g (mem_normalizer_of_map_conj_eq hαΓ.2) (mem_normalizer_of_map_conj_eq hαΓ.1) a ha
  refine ⟨hcomm, hinner, ?_⟩
  obtain ⟨-, -, ⟨Θ, -, -, hΘker, -⟩, hcyc, hcard, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ' hσ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  set Λ := pairAutSubgroup A (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom))
  set ρ := pairAutRestrict A (U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom))
  have hker : (Θ.comp Λ.subtype).ker ≤ ρ.ker := by
    intro α hα
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hΘker] at hα
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    exact hinner α ⟨α.2, hα⟩ a a.2
  have hΔ := map_isCyclic_of_ker_le (Θ.comp Λ.subtype) ρ hker
  rw [hcard] at hΔ
  refine ⟨?_, hΔ⟩
  rw [MonoidHom.range_eq_map]
  exact hΔ ⊤

end CFSG.Quasithin.H13.NQTerm
