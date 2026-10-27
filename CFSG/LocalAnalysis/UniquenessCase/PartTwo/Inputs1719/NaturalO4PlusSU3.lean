module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NaturalO4PlusSubnormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem false_of_isSubnormal_isNaturalO4Plus_of_isSU3
    {W : Type} [CommGroup W] [Finite W] {Kc Y : Subgroup (MulAut W)} {e n : ℕ}
    (hSU : IsSU3 ↥Kc n) (hsub : CFSG.Open.IsSubnormal Kc Y)
    (hnat : IsNaturalO4Plus Y e) : False := by
  obtain ⟨K, hKfield, hKfinite, hKcard, -, ⟨eK⟩⟩ :=
    exists_mulEquiv_sl2_of_isSubnormal_isNaturalO4Plus hSU.1 hsub hnat
  have hKq : CFSG.IsQuasisimple Kc := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hSU.1
  have : Nontrivial ↥Kc := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hKcSL : Kc ≃* CFSG.Open.StatedSL 2 K :=
    eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
  have hmSL : CFSG.Blueprint.LieModel ↥Kc .PSL 2 2 e :=
    CFSG.Quasithin.H13.lieModel_psl_two_of_mulEquiv hKq.1 hKcard hKcSL
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.not_lieModel_psl2_of_isSU3 (n := n) hSU hmSL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
