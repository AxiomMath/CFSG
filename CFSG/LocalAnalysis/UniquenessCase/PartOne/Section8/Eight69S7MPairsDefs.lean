module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2PermSound
public import CFSG.RankThree.Native.HSMcLSmallData
public import Certificates.Data.McLFivePairs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs

open CFSG.AGLEmbedding.FusD2 CFSG.AGLEmbedding.MaxD2 CFSG.RankThree.Native
open Certificates.MaxD2Heis (mclFiveDataP)

noncomputable abbrev mclAB : List (Equiv.Perm (Fin 275)) := [mcl275A, mcl275B]

noncomputable abbrev mclU5 : Equiv.Perm (Fin 275) := wordVal mclAB mclFiveDataP.uW

noncomputable abbrev mclV5 : Equiv.Perm (Fin 275) := wordVal mclAB mclFiveDataP.vW

noncomputable abbrev mclR5 : Subgroup (Equiv.Perm (Fin 275)) := Rsub mclFiveDataP mclAB

noncomputable abbrev mclNGens5 : List (Equiv.Perm (Fin 275)) :=
  mclFiveDataP.nW.map (wordVal mclAB)

noncomputable abbrev mclN5 : Subgroup (Equiv.Perm (Fin 275)) := Nsub mclFiveDataP mclAB

noncomputable abbrev mclRep5 (i : ℕ) : Equiv.Perm (Fin 275) :=
  (repElts mclFiveDataP mclAB).getD i 1

noncomputable abbrev mclH5 (k : ℕ) : Equiv.Perm (Fin 275) :=
  (Certificates.McLFivePairs.conjWords.map (wordVal mclNGens5)).getD k 1

noncomputable abbrev mclB0Gens : List (Equiv.Perm (Fin 275)) :=
  [mclU5, mclV5, (mclRep5 95)⁻¹ * mclU5 * mclRep5 95, (mclRep5 95)⁻¹ * mclV5 * mclRep5 95]

noncomputable abbrev mclBGens5 (k : ℕ) : List (Equiv.Perm (Fin 275)) :=
  mclB0Gens.map fun x => (mclH5 k)⁻¹ * x * mclH5 k

noncomputable abbrev mclB5 (k : Fin 3) : Subgroup (Equiv.Perm (Fin 275)) :=
  Subgroup.closure {g | g ∈ mclBGens5 k}

theorem mcl_repW_length : mclFiveDataP.repW.length = 113 := by decide

theorem mclNGens5_length : mclNGens5.length = 4 := by
  simp only [mclNGens5, List.length_map]
  decide

theorem mclRep5_zero : mclRep5 0 = 1 := rfl

theorem mclH5_zero : mclH5 0 = 1 := rfl

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs
