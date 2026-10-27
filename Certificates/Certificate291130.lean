module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.RankThree.PartOne.KS.ScalFiveBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BFiveData
import Certificates.Kernel.BabyMonster.Scal.Glue
import Certificates.Kernel.BabyMonster.Seeds

public section

namespace Certificates

open CFSG.Blueprint

open CFSG.RankThree.PartOne.KS.ScalFive
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BScal in
theorem certificate291130 : ∃ (q : Fin 4 → CFSG.Blueprint.NativeSporadic.B) (z s t : CFSG.Blueprint.NativeSporadic.B),
    ScalRel q z s t fiveM fiveSm 0 1 fiveCs (2 : ZMod 5) fiveCt :=
  CFSG.KC.BM.ScalGlue.certificate291130_of_seeds
    (by rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert _ _))
    (by rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))

end Certificates
