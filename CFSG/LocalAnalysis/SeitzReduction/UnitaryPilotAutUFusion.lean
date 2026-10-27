module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAutUCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.FusionGenericAutU2

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 f K)

theorem exists_conj_eq_mul_transvection_twoSided {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n) (hn : 4 ≤ n) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hnot : ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsUnitaryTransvection h (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsUnitaryTransvection h (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hLt : L ≤ centralizer ({t} : Set G) := SeitzQ2.le_centralizer_singleton_of_mem_centralizer htC
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  obtain ⟨x, z, hz, hxz, hz1, ⟨U, hU⟩, ⟨U', hU'⟩, hact⟩ :=
    exists_conj_eq_mul_twoSided_of_commutator_eq_top_of_autU2
      (SeitzQ2.commutator_eq_top_of_standardSetting hset.standardSetting) ht hLt hCN hKt hnot
      (fun U β hβ2 hβ => mem_range_conj_of_fix_sylow_of_sq_of_mulEquiv h e hn U β hβ2 hβ)
      (commutator_mem_of_sylow_le_centralizer h hset e (by omega) hq ht hKt)
  refine ⟨x, z, hz, hxz, ⟨hz.1, ?_⟩, ⟨hz.2, ?_⟩, hact⟩
  · refine isUnitaryTransvection_of_commute_sylow_of_mulEquiv h e (by omega) U
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext ?_
    exact hU u hu
  · refine isUnitaryTransvection_of_commute_sylow_of_mulEquiv h
      ((conjugateMulEquiv L x).symm.trans e) (by omega) U'
      (fun h1 => hz1 (congrArg Subtype.val h1)) fun u hu => Subtype.ext ?_
    exact hU' u hu

end CFSG.SeitzReduction.UnitaryPilot
