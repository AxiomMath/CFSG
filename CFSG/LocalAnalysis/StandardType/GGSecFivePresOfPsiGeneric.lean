module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresOfPsiFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

section Generic

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {X : Type*} [Group X]

@[expose] def ggRootsFamily (D : UniversalRootDatum U) : Unit → Set (Fin D.rank → ℤ) :=
  fun _ => D.roots

@[expose] noncomputable def ggRootsHom (D : UniversalRootDatum U) (ψ : U →* X) :
    ∀ k : Unit, ggSub D (ggRootsFamily D k) →* X :=
  fun _ => ψ.comp (ggSub D D.roots).subtype

theorem ggExt_ggRootsHom_of_mem (ψ : U →* X) {u : U} (hu : u ∈ ggSub D D.roots) :
    ggExt (ggRootsHom D ψ ()) u = ψ u := by
  rw [ggExt_of_mem (ggRootsHom D ψ ()) hu]
  rfl

theorem ggExt_ggRootsHom (hU2 : GGRootsGenerate D) (ψ : U →* X) (u : U) :
    ggExt (ggRootsHom D ψ ()) u = ψ u :=
  ggExt_ggRootsHom_of_mem ψ (by rw [hU2]; exact Subgroup.mem_top u)

theorem range_ggRootsHom (hU2 : GGRootsGenerate D) (ψ : U →* X) :
    (ggRootsHom D ψ ()).range = ψ.range := by
  ext x
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(y : U), hy⟩
  · rintro ⟨u, hu⟩
    refine ⟨⟨u, ?_⟩, hu⟩
    show u ∈ ggSub D D.roots
    rw [hU2]
    exact Subgroup.mem_top u

theorem ggActsLikeHom_roots {ν : GGWeyl D →* U} (hν : GGWeylLift D ν) (ψ : U →* X) :
    GGActsLikeHom D (ggRootsFamily D) (ggRootsHom D ψ) ν (ψ.comp ν) := by
  intro v k l α hα hαl z hz
  cases k
  cases l
  have hzS : z ∈ ggSub D D.roots := rootGroup_le_ggSub (S := D.roots) hα hz
  have hconj : ν v * z * (ν v)⁻¹ ∈ ggSub D D.roots :=
    rootGroup_le_ggSub (S := D.roots)
      (CFSG.LieType.CurtisTits.weylAction_mem_roots hα v)
      (hν.conj_mem v α hα z hz)
  rw [ggExt_ggRootsHom_of_mem ψ hzS, ggExt_ggRootsHom_of_mem ψ hconj]
  simp only [MonoidHom.comp_apply, map_mul, map_inv]

theorem ggWeylInRHom_roots {ν : GGWeyl D →* U} (hU2 : GGRootsGenerate D) (ψ : U →* X) :
    GGWeylInRHom D (ggRootsFamily D) (ggRootsHom D ψ) ν (ψ.comp ν) := by
  intro k v j h
  cases k
  rw [ggExt_ggRootsHom hU2 ψ]
  rfl

theorem ggOrbit_roots : GGOrbit D (ggRootsFamily D) := by
  intro J hJ
  refine ⟨1, (), fun γ hγ => ?_⟩
  rw [map_one, Module.End.one_apply]
  simpa [ggRootsFamily] using hγ.1

theorem injective_comp_of_rigid {ν : GGWeyl D →* U} (hν : GGWeylLift D ν)
    (hU3 : GGSimpleRootGroupsRigid D) {ψ : U →* X} (hker : ψ.ker ≤ Subgroup.center U) :
    Function.Injective (ψ.comp ν) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hw' : ψ (ν w) = 1 := hw
  have hmem : ν w ∈ ψ.ker := MonoidHom.mem_ker.mpr hw'
  have hcenter : ν w ∈ Subgroup.center U := hker hmem
  have hc : ∀ u : U, ν w * u * (ν w)⁻¹ = u := fun u => by
    rw [← Subgroup.mem_center_iff.mp hcenter u]
    group
  have hci : ∀ u : U, (ν w)⁻¹ * u * (ν w) = u := fun u => by
    rw [← Subgroup.mem_center_iff.mp (inv_mem hcenter) u]
    group
  have hfix : ∀ i : Fin D.rank,
      D.rootGroup (weylAction D.isFiniteType w (Pi.single i 1)) =
        D.rootGroup (Pi.single i 1) := by
    intro i
    refine le_antisymm ?_ ?_
    · intro x hx
      have hroot : weylAction D.isFiniteType w (Pi.single i 1) ∈ D.roots :=
        CFSG.LieType.CurtisTits.weylAction_mem_roots (single_mem_roots i) w
      have hconj := hν.conj_mem w⁻¹ (weylAction D.isFiniteType w (Pi.single i 1)) hroot x hx
      simp only [map_inv, inv_inv,
        CFSG.LieType.RootSystem.weylAction_inv_apply_apply] at hconj
      rwa [hci x] at hconj
    · intro x hx
      have hconj := hν.conj_mem w (Pi.single i 1) (single_mem_roots i) x hx
      rwa [hc x] at hconj
  exact ggWeyl_eq_one_of_fixes_simple (fun i => hU3 i w (hfix i))

theorem exists_ne_one_ggRootsHom (hU2 : GGRootsGenerate D) (hU4 : GGRootNotCentral D) {ψ : U →* X}
    (hker : ψ.ker ≤ Subgroup.center U) :
    ∃ k, ∃ γ ∈ ggRootsFamily D k, ∃ z ∈ D.rootGroup γ, ggExt (ggRootsHom D ψ k) z ≠ 1 := by
  obtain ⟨γ, hγ, hnotle⟩ := hU4
  obtain ⟨z, hz, hzc⟩ : ∃ z ∈ D.rootGroup γ, z ∉ Subgroup.center U := by
    by_contra h
    exact hnotle fun z hz => by
      by_contra hzc
      exact h ⟨z, hz, hzc⟩
  refine ⟨(), γ, hγ, z, hz, ?_⟩
  rw [ggExt_ggRootsHom_of_mem ψ (rootGroup_le_ggSub (S := D.roots) hγ hz)]
  intro hz1
  exact hzc (hker (MonoidHom.mem_ker.mpr hz1))

end Generic

end CFSG.StandardType

end
