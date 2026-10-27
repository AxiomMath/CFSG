module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusStdFrame
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizer
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaMinusLevi
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2Map
public import CFSG.Quasithin.Background.B6Sections
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Spin (quadMinus)

private lemma stdP0_e_eq_single_T2J6b {F : Type} [Field F] (b c : F) :
    (stdP0 F b c).e = (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1))) 1 :
      Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := by
  rw [stdP0, minusPair_e]

private lemma map_lineStab_eq_pointStabilizer_T2J6b {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (KTabD.lineStab (StatedOmega (StatedQuadMinus 3 F b c))
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1))) 1 :
          Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)).map
        (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr).toMonoidHom =
      pointStabilizer (quadMinus 3 F b c)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1))) 1 :
          Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := by
  let v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F :=
    Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1))) 1
  change (KTabD.lineStab (StatedOmega (StatedQuadMinus 3 F b c)) v).map
      (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr).toMonoidHom =
    pointStabilizer (quadMinus 3 F b c) v
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [KTabD.mem_lineStab] at hA
    obtain ⟨d, hd⟩ := hA
    refine ⟨d, ?_⟩
    change ((statedOmegaMinusEquiv (m := 3) (by norm_num) hirr) A).app v = d • v
    rw [statedOmegaMinusEquiv_app]
    exact hd
  · intro hg
    rw [mem_pointStabilizer] at hg
    obtain ⟨d, hd⟩ := hg
    obtain ⟨A, hA⟩ := (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr).surjective g
    refine ⟨A, ?_, hA⟩
    rw [KTabD.mem_lineStab]
    refine ⟨d, ?_⟩
    rw [← statedOmegaMinusEquiv_app (m := 3) (by norm_num) hirr A v]
    rw [hA]
    exact hd

theorem nonempty_bar2_derInf_pointStabilizer_std {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (Bar2 (F07.DerInf (pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e)) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 F b c))) := by
  haveI : Finite (Gom (quadMinus 3 F b c)) := instFiniteGomQuadMinusThree F b c
  haveI : Finite ↥(StatedOmega (StatedQuadMinus 3 F b c)) := inferInstance
  obtain ⟨g⟩ := KTabD.nonempty_bar2_hinf_lineStab_statedOmegaMinus (K := F) hirr 0
  have hmap := KTabD.nonempty_bar2_hinf_map
    (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr)
    (KTabD.lineStab (StatedOmega (StatedQuadMinus 3 F b c))
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1))) 1 :
        Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
  rw [map_lineStab_eq_pointStabilizer_T2J6b hirr] at hmap
  obtain ⟨f⟩ := hmap
  rw [stdP0_e_eq_single_T2J6b b c]
  exact ⟨f.symm.trans g⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
