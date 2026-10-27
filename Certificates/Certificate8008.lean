module

public import Certificates.Data.CoverCenterThreeJ3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CoverCenter.J3Facts
import Certificates.Kernel.CoverCenter.J3Cov

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.CosetTable CFSG.Blueprint
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest in
open scoped commutatorElement in
theorem certificate8008 : (∃ g : Fin 6 → NativeSporadic.J3,
      (∀ i, j3CoverE i ≠ 0 → g i ^ j3CoverE i = 1) ∧
      (∀ i, j3CoverE i = 0 → g i = ⁅evalW g (j3CoverCWf i).1, evalW g (j3CoverCWf i).2⁆) ∧
      (∀ w ∈ j3CoverRels, evalW g w = 1) ∧
      Nat.card (Subgroup.closure ({g 0, g 1} : Set NativeSporadic.J3)) = 1944) ∧
    (Finite (PG 6 j3GammaWords) ∧ Nat.card (PG 6 j3GammaWords) ≤ 729 * 8) :=
  ⟨KernelCover.J3.witness, KernelCover.J3Cov.gamma_card⟩

end Certificates
