module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoLen
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoGen
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4Datum

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley
open scoped commutatorElement

private abbrev datumCS {U : Type} [Group U] (D : UniversalRootDatum U) :=
  (CFSG.LieType.RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem

private theorem f4_perm_val_le_one (i : Fin 4) :
    (ReeTag.F4.perm i).val ≤ 1 ↔ ¬ i.val ≤ 1 := by
  fin_cases i <;> decide +kernel

theorem finiteExceptionalAut_F4_map_rootGroup
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {β : Fin (f4Datum K).rank → ℤ}
    (hβ : β ∈ (f4Datum K).roots) :
    ∃ β' ∈ (f4Datum K).roots,
      ((f4Datum K).rootGroup β).map (ReeTag.F4.finiteExceptionalAut K).toMonoidHom =
          (f4Datum K).rootGroup β' ∧
        ((f4Datum K).rootGroup (-β)).map (ReeTag.F4.finiteExceptionalAut K).toMonoidHom =
          (f4Datum K).rootGroup (-β') ∧
        (GGLongRoot (f4Datum K) β' ↔ ¬ GGLongRoot (f4Datum K) β) := by
  change β ∈ CFSG.LieType.RootSystem.roots (f4Datum K).isFiniteType
    (f4Datum K).divisible at hβ
  simp only [CFSG.LieType.RootSystem.roots, Set.mem_union, Set.mem_setOf_eq] at hβ
  obtain ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩ := hβ
  · obtain ⟨ω, rfl⟩ := (datumCS (f4Datum K)).wordProd_surjective w
    let ρ : Fin (f4Datum K).rank → Fin (f4Datum K).rank := fun j => ReeTag.F4.perm j
    let n : Fin (f4Datum K).rank → adjointGroup .F4 K :=
      CFSG.LieType.Chevalley.weylElement .F4 K
    let g : adjointGroup .F4 K := (ω.map n).prod
    let g' : adjointGroup .F4 K := ((ω.map ρ).map n).prod
    let β' : Fin (f4Datum K).rank → ℤ :=
      weylAction (f4Datum K).isFiniteType ((datumCS (f4Datum K)).wordProd (ω.map ρ))
        (Pi.single (ρ i) 1)
    have hct := f4_isCTGroupDatum_exact K
    have hacts := CFSG.LieType.Steinberg.actsAs_list_prod hct ω
    have hacts' := CFSG.LieType.Steinberg.actsAs_list_prod hct (ω.map ρ)
    have hsingle : Pi.single i 1 ∈ (f4Datum K).roots :=
      mem_adjDatum_roots.2 (isRoot_single .F4 i)
    have hnegsingle : -(Pi.single i 1) ∈ (f4Datum K).roots :=
      mem_adjDatum_roots.2 (isRoot_neg_single .F4 i)
    have hsingle' : Pi.single (ρ i) 1 ∈ (f4Datum K).roots :=
      mem_adjDatum_roots.2 (isRoot_single .F4 (ρ i))
    have hnegsingle' : -(Pi.single (ρ i) 1) ∈ (f4Datum K).roots :=
      mem_adjDatum_roots.2 (isRoot_neg_single .F4 (ρ i))
    let φ : adjointGroup .F4 K →* adjointGroup .F4 K :=
      (ReeTag.F4.finiteExceptionalAut K).toMonoidHom
    have hφg : φ g = g' := by
      change (ReeTag.F4.finiteExceptionalAut K).toMonoidHom (List.prod (ω.map n)) =
        List.prod ((ω.map ρ).map n)
      rw [map_list_prod]
      have hmap : (ω.map n).map φ = (ω.map ρ).map n := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left fun j _ => finiteExceptionalAut_F4_weylElement K j
      exact congrArg List.prod hmap
    have hφcomp :
        φ.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj g').toMonoidHom.comp φ := by
      rw [← hφg]
      ext x
      simp [MulAut.conj_apply]
    have hsingle_map :
        ((f4Datum K).rootGroup (Pi.single i 1)).map φ =
          (f4Datum K).rootGroup (Pi.single (ρ i) 1) :=
      (finiteExceptionalAut_F4_map_rootGroup_single K i).1
    have hnegsingle_map :
        ((f4Datum K).rootGroup (-(Pi.single i 1))).map φ =
          (f4Datum K).rootGroup (-(Pi.single (ρ i) 1)) :=
      (finiteExceptionalAut_F4_map_rootGroup_single K i).2
    have hβmap : (f4Datum K).rootGroup (weylAction (f4Datum K).isFiniteType
          ((datumCS (f4Datum K)).wordProd ω) (Pi.single i 1)) =
        ((f4Datum K).rootGroup (Pi.single i 1)).map (MulAut.conj g).toMonoidHom :=
      (hacts (Pi.single i 1) hsingle).symm
    have hβmapφ : ((f4Datum K).rootGroup (weylAction (f4Datum K).isFiniteType
          ((datumCS (f4Datum K)).wordProd ω) (Pi.single i 1))).map φ =
        (f4Datum K).rootGroup β' := by
      rw [hβmap, Subgroup.map_map, hφcomp, ← Subgroup.map_map, hsingle_map]
      exact hacts' (Pi.single (ρ i) 1) hsingle'
    have hnegβ : -(weylAction (f4Datum K).isFiniteType ((datumCS (f4Datum K)).wordProd ω)
          (Pi.single i 1)) =
        weylAction (f4Datum K).isFiniteType ((datumCS (f4Datum K)).wordProd ω)
          (-(Pi.single i 1)) :=
      (map_neg (weylAction (f4Datum K).isFiniteType ((datumCS (f4Datum K)).wordProd ω))
        (Pi.single i 1)).symm
    have hβnegmap : (f4Datum K).rootGroup
          (-(weylAction (f4Datum K).isFiniteType
              ((datumCS (f4Datum K)).wordProd ω) (Pi.single i 1))) =
        ((f4Datum K).rootGroup (-(Pi.single i 1))).map (MulAut.conj g).toMonoidHom := by
      rw [hnegβ]
      exact (hacts (-(Pi.single i 1)) hnegsingle).symm
    have hnegβ' : -(weylAction (f4Datum K).isFiniteType
          ((datumCS (f4Datum K)).wordProd (ω.map ρ))
          (Pi.single (ρ i) 1)) =
        weylAction (f4Datum K).isFiniteType ((datumCS (f4Datum K)).wordProd (ω.map ρ))
          (-(Pi.single (ρ i) 1)) :=
      (map_neg (weylAction (f4Datum K).isFiniteType
        ((datumCS (f4Datum K)).wordProd (ω.map ρ))) (Pi.single (ρ i) 1)).symm
    have hβnegmapφ : ((f4Datum K).rootGroup
          (-(weylAction (f4Datum K).isFiniteType
              ((datumCS (f4Datum K)).wordProd ω) (Pi.single i 1)))).map φ =
        (f4Datum K).rootGroup (-β') := by
      rw [hβnegmap, Subgroup.map_map, hφcomp, ← Subgroup.map_map, hnegsingle_map]
      rw [show -β' = weylAction (f4Datum K).isFiniteType
            ((datumCS (f4Datum K)).wordProd (ω.map ρ))
            (-(Pi.single (ρ i) 1)) from hnegβ']
      exact hacts' (-(Pi.single (ρ i) 1)) hnegsingle'
    have hβ'mem : β' ∈ (f4Datum K).roots :=
      CFSG.LieType.RootSystem.weylAction_mem_roots (f4Datum K).isFiniteType
        ((datumCS (f4Datum K)).wordProd (ω.map ρ)) hsingle'
    have hlong : GGLongRoot (f4Datum K) β' ↔
        ¬ GGLongRoot (f4Datum K)
          (weylAction (f4Datum K).isFiniteType ((datumCS (f4Datum K)).wordProd ω)
            (Pi.single i 1)) := by
      rw [show β' = weylAction (f4Datum K).isFiniteType
            ((datumCS (f4Datum K)).wordProd (ω.map ρ))
            (Pi.single (ρ i) 1) from rfl]
      rw [ggLongRoot_weylAction_iff (f4Datum K)
          ((datumCS (f4Datum K)).wordProd (ω.map ρ)) (Pi.single (ρ i) 1),
        f4_ggLongRoot_single_iff K (ρ i),
        ggLongRoot_weylAction_iff (f4Datum K)
          ((datumCS (f4Datum K)).wordProd ω) (Pi.single i 1),
        f4_ggLongRoot_single_iff K i]
      exact f4_perm_val_le_one i
    exact ⟨β', hβ'mem, hβmapφ, hβnegmapφ, hlong⟩
  · exact absurd hi (Set.notMem_empty i)

end CFSG.StandardType.LieKnownR2.Short
