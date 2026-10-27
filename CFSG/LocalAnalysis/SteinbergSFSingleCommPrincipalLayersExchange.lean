module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommPrincipalLayersCover
public import CFSG.Foundations.Basic
public import CFSG.Assembly.Defs
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBJEvenLinearTwoSquareField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace PrincipalLayers

open Subgroup TorusLayer CFSG.RankThree.PartOne.KCRootAxis
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoSquareField
  (even_linear_two_fixed_SL2_subgroup_determines_square_field)
open scoped MatrixGroups

variable {F : Type} [Group F] [Finite F] {K : Type} [Field K] {n : ℕ}
  {S J Y V U : Subgroup F} {t : F} {hk : SL₂ K → F}

set_option quotPrecheck false in
local notation "𝐑" => CFSG.Open.standardComponentOddCore F
set_option quotPrecheck false in
local notation "θ" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)
set_option quotPrecheck false in
local notation "𝐒𝐛" => S.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F))
set_option quotPrecheck false in
local notation "𝐃" => normalClosure ((S.map (QuotientGroup.mk'
  (CFSG.Open.standardComponentOddCore F)) : Subgroup (F ⧸ CFSG.Open.standardComponentOddCore F)) :
    Set (F ⧸ CFSG.Open.standardComponentOddCore F))
set_option quotPrecheck false in
local notation "𝐚" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F) t
set_option quotPrecheck false in
local notation "α" => (MulAut.conjNormal (H := 𝐃) 𝐚 : MulAut ↥𝐃)

end PrincipalLayers

end CFSG.LocalAnalysis.SymplecticFourStandard
