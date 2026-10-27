module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_calC_cover_of_l5_component
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (h125 : Hyp125 D V₀ V) (h127 : R127 D) (h119 : F11.R119 D)
    {Lbar : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : CFSG.Open.IsComponentOf Lbar (Mbar D.M V₀ V hV))
    (hL : IsLn Lbar 5 1) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧
      barSub V₀ V hV K = Lbar ∧ IsLn (Bar2 K) 5 1 := by
  obtain ⟨K, hKmem, hbarK, ⟨e⟩⟩ :=
    exists_calC_cover_of_simple_component (hV := hV) h125 h127 h119 hcomp
      (s16c167_cfg2_simple_ln hL)
  exact ⟨K, hKmem, hbarK,
    s15k_schur_l5 hKmem.2.2 (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
