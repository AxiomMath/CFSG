module

public import CFSG.LieType.Chevalley.GraphFixedParabolicPCore
public import CFSG.LieType.Chevalley.GraphFixedParabolicIntersection
public import CFSG.LieType.Chevalley.CLSEvenTrialityFourGroup
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite

public section

namespace CFSG.StandardType.LieKnownR2.TriD4HighRootParabolic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis CFSG.StandardType.RootCentExc

theorem graphFixedRootGroup_inf_normalizer_highRootFixed_D4
    (K : Type) [Field K] [CharP K 2] (σ : K ≃+* K) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.normalizer ((rootSubgroup TwistTag.D4.tag K (highRoot TwistTag.D4.tag) ⊓
          twistedFixedGroup TwistTag.D4 K σ.toRingHom : Subgroup (ModGL TwistTag.D4.tag K)) :
            Set (ModGL TwistTag.D4.tag K)) =
      graphFixedParabolic TwistTag.D4 K σ.toRingHom
        ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank)) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hJ : TwistTag.D4.orbitUnion
      ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank)) = Jθ TwistTag.D4.tag := by
    ext i
    rw [mem_orbitUnion_iff_orbitIndex]
    have key : ∀ i : Fin 4, (![0, 0, 1, 0] : Fin 4 → Fin 2) i = 0 ↔ i ≠ 2 := by decide
    exact key i
  have hP := (diagram_fixed_parabolic_intersection TwistTag.D4 K σ
    ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank))).2.1
  rw [hJ] at hP
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
    have hgΓ : g ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
      graphFixedRootGroup_le _ K σ.toRingHom hgC
    have hgG : g ∈ adjointGroup TwistTag.D4.tag K :=
      ((mem_twistedFixedGroup_iff_twistHom _ K σ.toRingHom).1 hgΓ).1
    have hx : pinnedX TwistTag.D4.tag K (highRoot TwistTag.D4.tag) 1 ∈
        (rootSubgroup TwistTag.D4.tag K (highRoot TwistTag.D4.tag) ⊓
          twistedFixedGroup TwistTag.D4 K σ.toRingHom) :=
      Subgroup.mem_inf.2 ⟨mem_rootSubgroup.2 ⟨1, rfl⟩,
        (mem_twistedFixedGroup_iff_twistHom _ K σ.toRingHom).2 ⟨pinnedX_mem_adjointGroup _ 1,
          twistHom_pinnedX_one_of_fixed h2 σ.toRingHom (isRoot_highRoot _)
            permLattice_d4TrialityHighestRoot⟩⟩
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1
      (Subgroup.mem_inf.1 ((Subgroup.mem_normalizer_iff.1 hgN _).1 hx)).1
    rw [← hP]
    exact Subgroup.mem_inf.2 ⟨mem_parabolicSubgroup_of_conj h2 (isMaxHeight_highRoot _)
      (fun w hw => mem_parabolicWeylGroup_of_smul_highRoot _ hw) hgG hc.symm, hgC⟩
  · rw [← hP] at hg
    obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.1 hg
    have hgΓ : g ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
      graphFixedRootGroup_le _ K σ.toRingHom hgC
    exact Subgroup.mem_inf.2 ⟨hgC, Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
      ⟨Pθ_le_normalizer_Uθ _ K hgP, Subgroup.le_normalizer hgΓ⟩)⟩

theorem pCore_graphFixedParabolic_D4
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) :
    (CFSG.pCore (ringChar K) (graphFixedParabolic TwistTag.D4 K σ.toRingHom
        ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank)))).map
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom
          ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank))).subtype =
      graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
        ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank)) := by
  refine le_antisymm (pCore_graphFixedParabolic_le_of_word TwistTag.D4 K σ _
    [(0 : Fin 2)] ?_ ?_) (graphFixedParabolicRadical_le_pCore TwistTag.D4 K σ _)
  · intro a ha
    exact List.mem_singleton.1 ha
  · intro α hα
    have hw : ∀ a : Fin TwistTag.D4.foldedTag.rank,
        (([a] : List (Fin TwistTag.D4.foldedTag.rank)).map TwistTag.D4.orbitReflection).prod =
          TwistTag.D4.orbitReflection a := fun a => by simp
    rw [hw (0 : Fin 2)]
    have hmem := orbitReflection_mem_parabolicWeylGroup (t := TwistTag.D4)
      (J := ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank))) (a := (0 : Fin 2))
      (Set.mem_singleton _)
    have hw0 : TwistTag.D4.orbitReflection (0 : Fin 2) =
        simple TwistTag.D4.tag (0 : Fin 4) * (simple TwistTag.D4.tag (1 : Fin 4) *
          (simple TwistTag.D4.tag (3 : Fin 4) * 1)) := rfl
    have hneg : ∀ i ∈ TwistTag.D4.orbitUnion
        ({(0 : Fin 2)} : Set (Fin TwistTag.D4.foldedTag.rank)),
        height (TwistTag.D4.orbitReflection (0 : Fin 2) •
          (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) < 0 := by
      intro i hi
      rw [mem_orbitUnion_iff_orbitIndex] at hi
      have key : ∀ i : Fin 4, (![0, 0, 1, 0] : Fin 4 → Fin 2) i = 0 → i = 0 ∨ i = 1 ∨ i = 3 := by
        decide
      rw [hw0]
      rcases key i hi with rfl | rfl | rfl <;>
      · simp only [mul_smul, simple_smul, one_smul]
        decide +kernel
    have h1 := (neg_mem_parabolicPosRoots_of_simple_neg hmem hneg hα).2.2
    rw [height_neg] at h1
    omega

end CFSG.StandardType.LieKnownR2.TriD4HighRootParabolic
