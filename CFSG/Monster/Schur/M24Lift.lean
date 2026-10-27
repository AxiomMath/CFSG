module

public import CFSG.Monster.Schur.M24Cast
public import CFSG.Monster.Schur.M24.Words
public import CFSG.Sporadic.Presentation.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Monster.Schur.M24

open TauCeti

private theorem pres_eq : pres = Sporadic.m24Presentation := rfl

theorem relatorLetters_eq : pres.relatorLetters =
    [a2, b3, ab23, r4, r5, r6, r7].map (List.map fun x => (x.1.val, x.2)) := by
  rw [pres_eq, GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    Sporadic.m24Presentation_transcribed]
  simp only [List.map_cons, List.map_nil, Relator.toWord_pow, Relator.toWord_mul,
    Relator.toWord_inv, Relator.toWord_gen, Relator.toWord_comm, FreeGroup.invRev]
  decide +kernel

theorem map_val_injective :
    Function.Injective
      (List.map fun x : Fin pres.generatorCount × Bool => (x.1.val, x.2)) :=
  List.map_injective_iff.2 fun a b hab => by
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (Fin.ext hab.1) hab.2

theorem castTo_mem_relators {w : List (Fin 2 × Bool)}
    (h : w.map (fun x => (x.1.val, x.2)) ∈ pres.relatorLetters) : castTo w ∈ pres.relators := by
  rw [GroupPresentation.relatorLetters_def] at h
  obtain ⟨v, hv, e⟩ := List.mem_map.1 h
  have hv' : v = castTo w := map_val_injective (by
    rw [e]
    simp [castTo, idx, List.map_map, Function.comp_def])
  rw [← hv']
  exact hv

theorem exists_castTo_of_mem
    {v : List (Fin pres.generatorCount × Bool)} (hv : v ∈ pres.relators) :
    ∃ w ∈ [a2, b3, ab23, r4, r5, r6, r7], v = castTo w := by
  have hl : v.map (fun x => (x.1.val, x.2)) ∈ pres.relatorLetters := by
    rw [GroupPresentation.relatorLetters_def]
    exact List.mem_map_of_mem hv
  rw [relatorLetters_eq] at hl
  obtain ⟨w, hw, e⟩ := List.mem_map.1 hl
  refine ⟨w, hw, map_val_injective ?_⟩
  rw [← e]
  simp [castTo, idx, List.map_map, Function.comp_def]

@[expose] noncomputable def liftHom {G : Type*} [Group G]
    (f : Fin 2 → G)
    (hf : ∀ w ∈ [a2, b3, ab23, r4, r5, r6, r7], FreeGroup.lift f (FreeGroup.mk w) = 1) :
    SporadicName.M24.Group →* G :=
  PresentedGroup.toGroup (f := fun j => f (Fin.cast generatorCount_eq j)) (by
    rw [CFSG.Sporadic.Presentation.relatorSet_eq]
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
    obtain ⟨w, hw, rfl⟩ := exists_castTo_of_mem hv
    have e : FreeGroup.lift (fun j => f (Fin.cast generatorCount_eq j)) (FreeGroup.mk (castTo w)) =
        FreeGroup.lift f (FreeGroup.mk w) := by
      simp [castTo, idx, FreeGroup.lift_mk, List.map_map, Function.comp_def]
    rw [e]
    exact hf w hw)

theorem liftHom_of {G : Type*} [Group G] (f : Fin 2 → G)
    (hf : ∀ w ∈ [a2, b3, ab23, r4, r5, r6, r7], FreeGroup.lift f (FreeGroup.mk w) = 1)
    (i : Fin 2) : liftHom f hf (PresentedGroup.of (idx i)) = f i := by
  rw [liftHom, PresentedGroup.toGroup.of]
  simp [idx]

end CFSG.Monster.Schur.M24
