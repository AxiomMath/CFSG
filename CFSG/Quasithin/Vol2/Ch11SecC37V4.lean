module

public import CFSG.Quasithin.Vol2.Ch11SecC37V3
public import CFSG.Quasithin.Vol2.Ch11SecC37B5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem point_of_u (i : Inp37) (hTVS : FactTransvPointSL3) (hTVP : FactTransvPointSp4)
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {u : G} (hu : u ∈ VZ T H)
    (huA : u ∉ Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G)) :
    ∃ y : G, (∀ x : G, x ∈ conjSubgroup (fsuV T I) g ↔ y⁻¹ * x * y ∈ fsuV T I) ∧
      ∀ x : G, (∃ a ∈ conjSubgroup (fsuV T I) g, x = u * a * u⁻¹ * a⁻¹) ↔
        y⁻¹ * x * y ∈ V₁ := by
  obtain ⟨l, hl, hpt⟩ := s.exists_point i hTVS hTVP hVL hu huA
  have hV₁eq := s.V₁_eq_inf i hVL
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV s.hyp
  have hl' : ∀ w, w ∈ fsuV T I ↔ l⁻¹ * w * l ∈ fsuV T I := fun w => by
    have := Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hl)) w
    rwa [inv_inv] at this
  have hN := conj_mem_normalizer (s.VZ_le_normalizer_A i.hAS i.hF i.h1102 i.hKF.2.2.2 i.h1122
    i.h1134 i.h1135 i.h1136 hu)
  refine ⟨g⁻¹ * l, fun x => ?_, fun x => ?_⟩
  · rw [mem_conjSubgroup_iff, hl']
    have e : (g⁻¹ * l)⁻¹ * x * (g⁻¹ * l) = l⁻¹ * (g * x * g⁻¹) * l := by group
    rw [e]
  · have e : (g⁻¹ * l)⁻¹ * x * (g⁻¹ * l) = l⁻¹ * (g * x * g⁻¹) * l := by group
    rw [e, hV₁eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hga : g * a * g⁻¹ ∈ fsuV T I := mem_conjSubgroup_iff.mp ha
      have hw : g * (u * a * u⁻¹ * a⁻¹) * g⁻¹ =
          g * u * g⁻¹ * (g * a * g⁻¹) * (g * u * g⁻¹)⁻¹ * (g * a * g⁻¹)⁻¹ := by group
      have hwV : g * (u * a * u⁻¹ * a⁻¹) * g⁻¹ ∈ fsuV T I := by
        rw [hw]
        exact (fsuV T I).mul_mem ((Subgroup.mem_normalizer_iff.mp hN _).mp hga)
          ((fsuV T I).inv_mem hga)
      exact ⟨(hl' _).mp hwV, (hpt _ hwV).mp ⟨_, hga, hw⟩⟩
    · rintro ⟨hxV, hxC⟩
      have hwV : g * x * g⁻¹ ∈ fsuV T I := (hl' _).mpr hxV
      obtain ⟨w', hw', hww⟩ := (hpt _ hwV).mpr hxC
      have hw'A : g⁻¹ * w' * g ∈ conjSubgroup (fsuV T I) g := by
        rw [mem_conjSubgroup_iff]
        have e2 : g * (g⁻¹ * w' * g) * g⁻¹ = w' := by group
        rw [e2]
        exact hw'
      refine ⟨g⁻¹ * w' * g, hw'A, ?_⟩
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * u * g⁻¹ * w' * (g * u * g⁻¹)⁻¹ * w'⁻¹) * g := by rw [hww]
        _ = u * (g⁻¹ * w' * g) * u⁻¹ * (g⁻¹ * w' * g)⁻¹ := by group

theorem exists_u : ∃ u ∈ VZ T H,
    u ∉ Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G) := by
  have h := s.hAC
  rw [IsConcreteLE.not_le_iff_exists] at h
  obtain ⟨a, ha, haC⟩ := h
  rw [Subgroup.mem_centralizer_iff] at haC
  push Not at haC
  obtain ⟨u, hu, hua⟩ := haC
  refine ⟨u, hu, fun huC => hua ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp huC a ha).symm

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
