module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel
public import CFSG.Adapters.LieModelSimple
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem s16c167_cfg2_simple_alt {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (h : UC22.IsAlt X n) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  exact e.isSimpleGroup

theorem s16c167_cfg2_simple_ln {X : Type} [Group X] {m : ℕ} (h : IsLn X m 1) :
    IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem s16c167_cfg2_simple_sp {X : Type} [Group X] (h : IsSpn X 6 1) : IsSimpleGroup X := by
  obtain ⟨-, K, instK, instFin, hK, ⟨e⟩⟩ := h
  letI : Field K := instK
  letI : Finite K := instFin
  have hK2 : Nat.card K = 2 := by simpa using hK
  haveI : IsSimpleGroup (StatedProj (StatedSp 3 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 3 (by norm_num)
      (Or.inr (Or.inr ⟨hK2, le_rfl⟩))
  have hscal : (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK2, Subgroup.bot_subgroupOf]
  let eP : StatedProj (StatedSp 3 K) ≃* StatedSp 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
  exact (e.trans eP.symm).isSimpleGroup

theorem s16c167_cfg2_simple_omegaMinus_eight {X : Type} [Group X] (h : IsOmegaMinus X 8 1) :
    IsSimpleGroup X := by
  obtain ⟨-, K, instK, instFin, b, c, -, hirr, ⟨e⟩⟩ := h
  letI : Field K := instK
  letI : Finite K := instFin
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
      (by norm_num) hirr
  exact e.isSimpleGroup

theorem s16c167_cfg2_simple {G : Type} [Group G] [Finite G] (D : Data G)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
    (h2 : Case168_2 D V₀ V hV L) : IsSimpleGroup ↥(lBar V₀ V hV L) := by
  obtain ⟨-, ⟨L₀, -, hfam⟩, -⟩ := h2
  rcases hfam with ⟨n, hn5, -, -, hA, -⟩ | ⟨m, -, -, -, hL, -⟩ | ⟨-, hS, -⟩ | ⟨-, hO, -⟩ |
    ⟨-, hO, -⟩
  · exact s16c167_cfg2_simple_alt hn5 hA
  · exact s16c167_cfg2_simple_ln hL
  · exact s16c167_cfg2_simple_sp hS
  · exact s16c1_isSimpleGroup_of_isOmegaMinus_six hO
  · exact s16c167_cfg2_simple_omegaMinus_eight hO

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
