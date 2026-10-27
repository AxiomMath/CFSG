module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.ActualKernelInclusion

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType.LieCore

variable {Ω : Type} [Field Ω]

theorem kernelRoots_joint_subset_of_closure
    {X : Type} [Group X] {B1 D : Subgroup X} (hDB : D ≤ B1)
    (Θ : B1 →* ModGL .F4 Ω)
    (coord : D → Fin Tag.F4.rank → Ωˣ)
    (hcoord : ∀ b : D, Θ (Subgroup.inclusion hDB b) = rootDiagUnit .F4 (coord b))
    {x d : X} (hxD : x ∈ D) (hdD : d ∈ D)
    (hgen : Subgroup.closure ({x, d} : Set X) = D)
    (e : D) :
    kernelRoots (jointChar (coord ⟨x, hxD⟩) (coord ⟨d, hdD⟩)) ⊆
      kernelRoots (rootCharHom (coord e)) := by
  intro γ hγ
  rw [kernelRoots] at hγ ⊢
  obtain ⟨hγroot, hγchar⟩ := hγ
  have hxchar : rootChar (coord ⟨x, hxD⟩) γ = 1 := by
    have h := congrArg Prod.fst hγchar
    simpa [jointChar, rootCharHom] using h
  have hdchar : rootChar (coord ⟨d, hdD⟩) γ = 1 := by
    have h := congrArg Prod.snd hγchar
    simpa [jointChar, rootCharHom] using h
  let ΘD : D →* ModGL .F4 Ω := Θ.comp (Subgroup.inclusion hDB)
  let P : Subgroup D :=
    (Subgroup.centralizer ({pinnedX .F4 Ω γ 1} : Set (ModGL .F4 Ω))).comap ΘD
  have hxP : (⟨x, hxD⟩ : D) ∈ P := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h := rootDiagUnit_conj_pinnedX (coord ⟨x, hxD⟩) hγroot 1
    rw [hxchar, Units.val_one, one_mul] at h
    have h' := mul_inv_eq_iff_eq_mul.1 h
    simpa only [ΘD, MonoidHom.comp_apply, hcoord ⟨x, hxD⟩] using h'
  have hdP : (⟨d, hdD⟩ : D) ∈ P := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h := rootDiagUnit_conj_pinnedX (coord ⟨d, hdD⟩) hγroot 1
    rw [hdchar, Units.val_one, one_mul] at h
    have h' := mul_inv_eq_iff_eq_mul.1 h
    simpa only [ΘD, MonoidHom.comp_apply, hcoord ⟨d, hdD⟩] using h'
  have hsub : ({x, d} : Set X) ⊆ (P.map D.subtype : Subgroup X) := by
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]
      exact Subgroup.mem_map.mpr ⟨⟨x, hxD⟩, hxP, rfl⟩
    · rw [h]
      exact Subgroup.mem_map.mpr ⟨⟨d, hdD⟩, hdP, rfl⟩
  have hDle : D ≤ P.map D.subtype := by
    have h := (Subgroup.closure_le (P.map D.subtype)).mpr hsub
    rwa [hgen] at h
  obtain ⟨p, hpP, hpval⟩ := Subgroup.mem_map.mp (hDle e.2)
  have heP : e ∈ P := (Subtype.ext hpval) ▸ hpP
  have heMem : ΘD e ∈ Subgroup.centralizer ({pinnedX .F4 Ω γ 1} : Set (ModGL .F4 Ω)) :=
    Subgroup.mem_comap.mp heP
  have hcomm : Θ (Subgroup.inclusion hDB e) * pinnedX .F4 Ω γ 1 =
      pinnedX .F4 Ω γ 1 * Θ (Subgroup.inclusion hDB e) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp heMem
    simpa only [ΘD, MonoidHom.comp_apply] using h
  have hstep : rootDiagUnit .F4 (coord e) * pinnedX .F4 Ω γ 1 *
      (rootDiagUnit .F4 (coord e))⁻¹ = pinnedX .F4 Ω γ 1 := by
    rw [← hcoord e, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hconj := rootDiagUnit_conj_pinnedX (coord e) hγroot 1
  rw [hstep] at hconj
  have hparam : (((rootChar (coord e) γ : Ωˣ) : Ω) * 1) = 1 :=
    (pinnedX_injective .F4 Ω γ hconj).symm
  refine ⟨hγroot, ?_⟩
  have hroot : rootChar (coord e) γ = 1 := Units.ext (by simpa using hparam)
  simpa [rootCharHom] using hroot

end CFSG.StandardType.F4ExplicitPos.ActualKernelInclusion

end

end
