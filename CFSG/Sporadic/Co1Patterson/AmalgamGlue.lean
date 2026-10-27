module

public import CFSG.Sporadic.Co1Patterson.AmalgamIso
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Defs

variable {G : Type*} [Group G]

@[expose] def AutInnerModAt (x y : G) : Prop :=
  ∀ ψ : ↥(C[x] ⊓ C[y]) ≃* ↥(C[x] ⊓ C[y]),
    (∀ g : ↥(C[x] ⊓ C[y]), (g : G) = x → ψ g = g) →
    (∀ g : ↥(C[x] ⊓ C[y]), (g : G) = y → ψ g = g) →
    (∀ g : ↥(C[x] ⊓ C[y]), ψ g * g⁻¹ ∈ CFSG.pCore 2 ↥(C[x] ⊓ C[y])) →
      ∃ h ∈ C[x] ⊓ C[y], ∀ g : ↥(C[x] ⊓ C[y]), (ψ g : G) = h * g * h⁻¹

@[expose] def AutRigidAt (a e w : G) : Prop :=
  ∀ ψ : ↥(C[a] ⊓ C[e]) ≃* ↥(C[a] ⊓ C[e]),
    (∀ g : ↥(C[a] ⊓ C[e]), (g : G) ∈ C[w] → ψ g = g) →
      (∀ g : ↥(C[a] ⊓ C[e]), ψ g = g) ∨ (∀ g : ↥(C[a] ⊓ C[e]), (ψ g : G) = w * g * w⁻¹)

end Defs

section Cent

variable {G : Type*} [Group G]

theorem mem_cent_iff {x y : G} : x ∈ C[y] ↔ x * y = y * x := mem_centralizer_singleton_iff

theorem mem_cent_conj_iff (c x y : G) : x ∈ C[y] ↔ c * x * c⁻¹ ∈ C[c * y * c⁻¹] := by
  rw [mem_cent_iff, mem_cent_iff]
  constructor
  · intro h
    calc c * x * c⁻¹ * (c * y * c⁻¹) = c * (x * y) * c⁻¹ := by group
      _ = c * (y * x) * c⁻¹ := by rw [h]
      _ = c * y * c⁻¹ * (c * x * c⁻¹) := by group
  · intro h
    have : c * (x * y) * c⁻¹ = c * (y * x) * c⁻¹ := by
      calc c * (x * y) * c⁻¹ = c * x * c⁻¹ * (c * y * c⁻¹) := by group
        _ = c * y * c⁻¹ * (c * x * c⁻¹) := h
        _ = c * (y * x) * c⁻¹ := by group
    simpa using this

theorem mem_cent_inf_mul_iff (x a e : G) : x ∈ C[a] ⊓ C[e] ↔ x ∈ C[e] ⊓ C[a * e] := by
  simp only [mem_inf, mem_cent_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    calc x * (a * e) = (x * a) * e := by group
      _ = a * (x * e) := by rw [h1]; group
      _ = a * e * x := by rw [h2]; group
  · rintro ⟨h2, h3⟩
    refine ⟨?_, h2⟩
    calc x * a = x * (a * e) * e⁻¹ := by group
      _ = a * e * (x * e⁻¹) := by rw [h3]; group
      _ = a * x := by
        have : x * e⁻¹ = e⁻¹ * x := by
          calc x * e⁻¹ = e⁻¹ * (e * x) * e⁻¹ := by group
            _ = e⁻¹ * (x * e) * e⁻¹ := by rw [h2]
            _ = e⁻¹ * x := by group
        rw [this]; group

variable {X : Type*} [Group X] {A : G → X} {H : Subgroup G} {H' : Subgroup X}

theorem IsoOn.inf_cent (hA : IsoOn A H H') {y : G} (hy : y ∈ H) :
    IsoOn A (H ⊓ C[y]) (H' ⊓ C[A y]) := by
  refine hA.restrict inf_le_left (fun x hx => mem_inf.2 ⟨hA.map_mem x hx.1, ?_⟩)
    (fun x hx => ?_)
  · rw [mem_cent_iff, ← hA.map_mul x hx.1 y hy, ← hA.map_mul y hy x hx.1,
      (mem_cent_iff.1 hx.2)]
  · obtain ⟨z, hz, rfl⟩ := hA.surjOn x hx.1
    refine ⟨z, mem_inf.2 ⟨hz, ?_⟩, rfl⟩
    rw [mem_cent_iff]
    refine hA.injOn (H.mul_mem hz hy) (H.mul_mem hy hz) ?_
    rw [hA.map_mul z hz y hy, hA.map_mul y hy z hz]
    exact mem_cent_iff.1 hx.2

end Cent

end CFSG.Sporadic.Co1Patterson
