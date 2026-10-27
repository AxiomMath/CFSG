module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumD
public import CFSG.Quasithin.EmptyFaithful.Insp7NumP
public import CFSG.Quasithin.EmptyFaithful.Insp7NumQ
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

@[expose] def SmallRest (L : Type) [Group L] : Prop :=
  StatedClassicalModel L .PSL 3 2 2 ∨
    StatedClassicalModel L .PSU 3 2 2 ∨ StatedClassicalModel L .PSp 2 2 2 ∨
    StatedClassicalModel L .PSL 4 2 1 ∨ Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
    StatedClassicalModel L .PSU 3 3 1 ∨ SuzukiModel L 2 3 ∨
    (Subgroup.center L ≠ ⊥ ∧ Subgroup.center L = CFSG.pCore 2 L ∧
      StatedClassicalModel (L ⧸ CFSG.pCore 2 L) .PSL 3 2 2)

@[expose] def L33Fam (L : Type) [Group L] : Prop :=
  StatedClassicalModel L .PSL 3 3 1

theorem numFactAt_of_cover {F G H : ∀ (L : Type) [Group L], Prop}
    (hFGH : ∀ (L : Type) [Group L], F L → G L ∨ H L) (hG : NumFactAt G) (hH : NumFactAt H) :
    NumFactAt F := by
  intro L _ _ hq hFL z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  rcases hFGH L hFL with h | h
  · exact hG L hq h z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  · exact hH L hq h z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard

theorem numFactAt_psl32 : NumFactAt (fun L _ => StatedClassicalModel L .PSL 3 2 1) :=
  numFactAt_of_cover (G := OddL2Fam) (H := OddL2Fam)
    (fun _ _ h => Or.inl ⟨7, ⟨by norm_num, Or.inr ⟨3, by norm_num, by norm_num⟩⟩,
      CFSG.QuasithinUnique.Id2519.psl2_seven_of_psl3_two h⟩) numFactAt_oddL2 numFactAt_oddL2

theorem numFactAt_smallLie (hS : NumFactAt SmallRest) : NumFactAt SmallLie :=
  numFactAt_of_cover (G := EvenL2Fam)
    (H := fun L _ => StatedClassicalModel L .PSL 3 2 1 ∨ SmallRest L)
    (fun L _ h => by
      unfold SmallLie at h
      unfold EvenL2Fam SmallRest
      tauto) numFactAt_evenL2
    (numFactAt_of_cover (G := fun L _ => StatedClassicalModel L .PSL 3 2 1) (H := SmallRest)
      (fun _ _ h => h) numFactAt_psl32 hS)

theorem numFactAt_oddFam (hO : NumFactAt L33Fam) : NumFactAt OddFam :=
  numFactAt_of_cover (fun L _ h => by
    unfold OddFam at h
    unfold L33Fam OddL2Fam
    tauto) hO numFactAt_oddL2

theorem lemma14320Inspect_of_small
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hS : NumFactAt SmallRest) (hT : NumFactAt LargeReeTits) (hO : NumFactAt L33Fam)
    (hP : NumFactAt SporSmall) : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_residuals hbig (numFactAt_smallLie hS) hT (numFactAt_oddFam hO) hP

end Insp7

end CFSG.Quasithin
