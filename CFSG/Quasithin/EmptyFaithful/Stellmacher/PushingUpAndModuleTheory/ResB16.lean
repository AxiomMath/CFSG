module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB12

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace OrthFrame

variable {δ μ : Geo H M} (fr : OrthFrame δ μ)

theorem comm_map (A : Subgroup G) (hA : A ≤ stab δ) (Y : Subgroup orth.W) :
    ⁅A, Y.map fr.γ⁆ = (commW orth (fr.img A) Y).map fr.γ := by
  apply le_antisymm
  · refine Subgroup.commutator_le.mpr fun a ha y hy => ?_
    obtain ⟨u, hu, rfl⟩ := hy
    have h1 := fr.equiv ⟨a, hA ha⟩ u
    have hb : fr.Ψ ⟨a, hA ha⟩ ∈ fr.img A := ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    refine ⟨orth.act (fr.Ψ ⟨a, hA ha⟩) u * u⁻¹, Subgroup.subset_closure ⟨_, hb, u, hu, rfl⟩, ?_⟩
    rw [map_mul, map_inv, h1]
    simp [commutatorElement_def]
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨b, ⟨k, hk, rfl⟩, u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv, fr.equiv]
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hk)
      (Subgroup.mem_map_of_mem fr.γ hu)
    simpa [commutatorElement_def] using this

theorem conj_map (k : ↥(stab δ)) (Y : Subgroup orth.W) :
    conjSub (k : G) (Y.map fr.γ) = (actSub (fr.Ψ k) Y).map fr.γ := by
  ext x
  constructor
  · intro hx
    have hx' : (k : G)⁻¹ * x * k ∈ Y.map fr.γ := mem_conjSub.mp hx
    obtain ⟨u, hu, hux⟩ := hx'
    refine ⟨orth.act (fr.Ψ k) u, ⟨u, hu, rfl⟩, ?_⟩
    rw [fr.equiv, hux]
    group
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rw [mem_conjSub]
    refine ⟨u, hu, ?_⟩
    have := fr.equiv k u
    simp only [MulEquiv.coe_toMonoidHom] at *
    rw [this]; group

end OrthFrame

end CFSG.Quasithin.F53
