module

public import CFSG.Quasithin.SteinbergBMPerfectSubnormalSignalizer
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra
public import CFSG.LocalAnalysis.ComponentClassification.LBalancePrimeCore

public section

namespace CFSG.LocalAnalysis

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open scoped commutatorElement

namespace CentralQuotientLift

theorem ne_bot_of_isComponent {C : Type*} [Group C] {L : Subgroup C} (hL : IsComponent L) :
    ⁅L, L⁆ ≠ ⊥ := by
  intro hLL
  obtain ⟨hperf, -, a, b, hab⟩ := hL.1
  have hL' : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperf
  rw [hLL] at hL'
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have h1 : ∀ x : L, x = 1 := fun x =>
    Subtype.ext ((Subgroup.eq_bot_iff_forall L).mp hL'.symm (x : C) x.2)
  rw [h1 a, h1 b]

theorem component_eq_of_quasisimple_normal {C : Type*} [Group C] [Finite C] (Q : Subgroup C)
    [Q.Normal] (hQ : IsQuasisimple Q) (hsolv : Group.IsSolvable (C ⧸ Q)) {L : Subgroup C}
    (hL : IsComponent L) : L = Q := by
  have hLQ : L ≤ Q := by
    have hLp : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
    have himage : ⁅L.map (QuotientGroup.mk' Q), L.map (QuotientGroup.mk' Q)⁆ =
        L.map (QuotientGroup.mk' Q) := by
      rw [← Subgroup.map_commutator, hLp]
    have := CFSG.Quasithin.SteinbergBM.eq_bot_of_commutator_self_eq_of_isSolvable himage
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at this
  have hQc : IsComponent Q := ⟨hQ, Subgroup.Normal.isSubnormal inferInstance⟩
  rcases CFSG.LocalCores.distinct_components_commute hL hQc with h | h
  · exact h
  · exfalso
    apply ne_bot_of_isComponent hL
    exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hLQ)

end CentralQuotientLift

end CFSG.LocalAnalysis
