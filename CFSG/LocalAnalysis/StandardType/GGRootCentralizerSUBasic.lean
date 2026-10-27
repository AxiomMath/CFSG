module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent

public section

namespace CFSG.StandardType

namespace OTwoGen

open Subgroup

section OTwoPrime

variable {G : Type*} [Group G]

theorem le_ggOTwoPrime_of_isPGroup {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    P ≤ ggOTwoPrime H := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  refine Subgroup.subset_closure ⟨hPH hx, k, ?_⟩
  have h := congrArg Subtype.val hk
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at h

theorem range_le_ggOTwoPrime {M : Type*} [Group M] (φ : M →* G) {H : Subgroup G}
    (hφH : φ.range ≤ H)
    (hM : (⊤ : Subgroup M) ≤ Subgroup.closure {x : M | ∃ k : ℕ, x ^ (2 ^ k) = 1}) :
    φ.range ≤ ggOTwoPrime H := by
  rw [MonoidHom.range_eq_map]
  refine (Subgroup.map_mono hM).trans ?_
  rw [MonoidHom.map_closure, ggOTwoPrime]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
  exact ⟨hφH ⟨x, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩

theorem top_le_closure_of_surjective {M N : Type*} [Group M] [Group N] (φ : M →* N)
    (hφ : Function.Surjective φ)
    (hM : (⊤ : Subgroup M) ≤ Subgroup.closure {x : M | ∃ k : ℕ, x ^ (2 ^ k) = 1}) :
    (⊤ : Subgroup N) ≤ Subgroup.closure {x : N | ∃ k : ℕ, x ^ (2 ^ k) = 1} := by
  rw [← MonoidHom.range_eq_top.mpr hφ, MonoidHom.range_eq_map]
  refine (Subgroup.map_mono hM).trans ?_
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem centralizer_conj_eq_map (x g : G) :
    centralizer ({g * x * g⁻¹} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mem_centralizer_singleton_iff]
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group
  · rintro ⟨z, hz, rfl⟩
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hz]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group

theorem centralizer_conj_le_ggOTwoPrime {x : G}
    (h : centralizer ({x} : Set G) ≤ ggOTwoPrime (centralizer ({x} : Set G))) (g : G) :
    centralizer ({g * x * g⁻¹} : Set G) ≤ ggOTwoPrime (centralizer ({g * x * g⁻¹} : Set G)) := by
  rw [centralizer_conj_eq_map]
  exact (Subgroup.map_mono h).trans (LinFusion.map_ggOTwoPrime_le _ _)

theorem inf_centralizer_le_ggOTwoPrime {U : Type*} [Group U] (ψ : U →* G)
    (hψ : Function.Injective ψ) {z : U}
    (hz : centralizer ({z} : Set U) ≤ ggOTwoPrime (centralizer ({z} : Set U))) :
    ψ.range ⊓ centralizer ({ψ z} : Set G) ≤
      ggOTwoPrime (ψ.range ⊓ centralizer ({ψ z} : Set G)) := by
  intro y hy
  obtain ⟨⟨s, rfl⟩, hs⟩ := Subgroup.mem_inf.mp hy
  have hs2 : ψ s * ψ z = ψ z * ψ s := mem_centralizer_singleton_iff.mp hs
  have hs' : s ∈ centralizer ({z} : Set U) :=
    mem_centralizer_singleton_iff.mpr (hψ (by rw [map_mul, map_mul, hs2]))
  refine LinFusion.ggOTwoPrime_mono ?_
    (LinFusion.map_ggOTwoPrime_le ψ _ (Subgroup.mem_map_of_mem ψ (hz hs')))
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
  have hv2 : v * z = z * v := mem_centralizer_singleton_iff.mp hv
  exact Subgroup.mem_inf.mpr ⟨⟨v, rfl⟩,
    mem_centralizer_singleton_iff.mpr (by rw [← map_mul, hv2, map_mul])⟩

end OTwoPrime

end OTwoGen

end CFSG.StandardType
