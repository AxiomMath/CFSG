module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Cases

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

theorem asch54Case_of_sectionalTwoRankLE (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X], P X → CFSG.GH74.SectionalTwoRankLE X 2) :
    Asch54Case P := by
  intro Q _ _ L T hK hLn hLs hLnab hC hPL _ hT hnu
  left
  have hE : CFSG.GH74.SectionalTwoRankLE ↥L 2 := hP _ hPL
  have hKL : CFSG.Open.IsKGroup ↥L := hK.of_injective L.subtype L.subtype_injective
  have hcat := hKL.isCatalogGroup_of_surjective ⊤ hLnab (Subgroup.subtype ⊤)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hq : Group.IsSolvable (Q ⧸ L) :=
    isSolvable_quotient_of_outSolvable L (by rw [hC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer (hS _ hLs hLnab hcat))
  exact lGen_eq_top_of_not_hasUniqueMaxOver (fun X _ _ =>
    not_hasCompFactor_of_sectionalTwoRankLE isCalL0_nonabelian_not_sectionalTwoRankLE hq hE X)
    (lt_top_of_isSylowIn_of_not_isSolvable hT (not_isSolvable_of_simple_normal L hLs hLnab)) hnu

theorem asch54ChevOdd_of (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hRee : Asch54Case fun X _ => ∃ f : ℕ, CFSG.Models.LieModel X .twistedG2 0 3 f)
    (hRest : Asch54Case fun X _ => CFSG.Models.OddLieType X ∧
      ¬ CFSG.GH74.SectionalTwoRankLE X 2 ∧ ¬ ∃ f : ℕ, CFSG.Models.LieModel X .twistedG2 0 3 f) :
    Asch54ChevOdd := by
  intro Q _ _ L T hK hLn hLs hLnab hC hP hL0 hT hnu
  by_cases hsec : CFSG.GH74.SectionalTwoRankLE ↥L 2
  · exact asch54Case_of_sectionalTwoRankLE hS (P := fun X _ => CFSG.GH74.SectionalTwoRankLE X 2)
      (fun _ _ _ h => h) Q L T hK hLn hLs hLnab hC hsec hL0 hT hnu
  by_cases hree : ∃ f : ℕ, CFSG.Models.LieModel ↥L .twistedG2 0 3 f
  · exact hRee Q L T hK hLn hLs hLnab hC hree hL0 hT hnu
  · exact hRest Q L T hK hLn hLs hLnab hC ⟨hP, hsec, hree⟩ hL0 hT hnu

end CFSG.LocalAnalysis.WeakClosure81
