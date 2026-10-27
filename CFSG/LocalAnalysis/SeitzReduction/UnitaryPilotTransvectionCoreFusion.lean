module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreConj
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvection
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAutUFusion

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}
  {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_isUnitaryTransvection_conj (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n)
    (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G)
    (hgL : g⁻¹ * t * g ∈ L) : ¬ IsUnitaryTransvection h (e ⟨g⁻¹ * t * g, hgL⟩) := by
  intro hz
  have := finite_unitaryPSU h n
  set w : L := ⟨g⁻¹ * t * g, hgL⟩ with hw
  have hcore := mem_perfectCore_centralizer_of_isUnitaryTransvection h hn hz
  set φ : unitaryPSU h n →* G := L.subtype.comp e.symm.toMonoidHom with hφ
  have hφw : φ (e w) = g⁻¹ * t * g := by simp [hφ, hw]
  have hq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  refine LinearPilot.conj_not_mem_perfect hset.standardSetting
    (isSolvable_outer_of_mulEquiv h (by omega) hq e) hset.center_eq_bot htC ht g
    (P := (perfectCore (centralizer ({e w} : Set (unitaryPSU h n)))).map φ) ?_ ?_ ?_
    ⟨e w, hcore, hφw⟩
  · rw [← map_commutator, perfectCore_perfect]
  · rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := mem_centralizer_singleton_iff.1 (perfectCore_le _ hx)
    rw [mem_centralizer_singleton_iff, ← hφw, ← map_mul, ← map_mul, h1]

theorem not_forall_commute_sylow_conj (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h n)
    (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hcomm
  refine not_isUnitaryTransvection_conj h hset e hn htC ht g hgL
    (isUnitaryTransvection_of_commute_sylow_of_mulEquiv h e (by omega) U (fun h1 => ?_)
      fun u hu => Subtype.ext (hcomm u hu))
  have h2 : g⁻¹ * t * g = 1 := congrArg Subtype.val h1
  have ht1 : t = 1 := by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  rw [ht1, orderOf_one] at ht
  exact absurd ht (by decide)

theorem exists_conj_eq_mul_transvection_twoSided_of_six_le (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsUnitaryTransvection h (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsUnitaryTransvection h (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htC : t ∈ centralizer (L : Set G) :=
    (show t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) from hKt ▸ mem_zpowers t).1
  exact exists_conj_eq_mul_transvection_twoSided h hset e (by omega) ht hKt
    (not_forall_commute_sylow_conj h hset e hn htC ht)

end CFSG.SeitzReduction.UnitaryPilot
