module

public import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld.Bridge.OddLocal

variable {G : Type} [Group G] {D : Set G}

theorem closure_le_normalizer_of_isMaxOrbit (hS : Asc72.Setup G D) {c : G} {E : Set G}
    (hE : IsMaxOrbit D c E) : Subgroup.closure E ≤ Subgroup.normalizer E :=
  (Subgroup.closure_mono (subset_commSet hS.normal hE)).trans (closure_commSet_le_normalizer hE)

theorem hClass_closure_eq (hS : Asc72.Setup G D) {c d : G} {E : Set G}
    (hE : IsMaxOrbit D c E) (hd : d ∈ E) : hClass (Subgroup.closure E) d = E := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact orbit_subset (closure_le_normalizer_of_isMaxOrbit hS hE) hd ⟨k, hk, rfl⟩
  · intro hx
    obtain ⟨k, hk, rfl⟩ := orbitGen hS hE hd x hx
    exact ⟨k, hk, rfl⟩

end CFSG.Timmesfeld.Bridge.OddRoot
