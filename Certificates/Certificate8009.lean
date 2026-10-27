module

public import Certificates.Data.CoverCenterThreeMcL
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.CoverCenter.McLFacts
import Certificates.Kernel.CoverCenter.McCov
import Certificates.Kernel.CoverCenter.C8009A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.CosetTable CFSG.KC.MiscCoset

theorem mcl_gamma_card :
    Finite (PG 7 mclGammaWords) ∧ Nat.card (PG 7 mclGammaWords) ≤ 87480 * 4 := by
  have h := TableFact.card_restrict (n := 29160) (N := 12) mclGammaWords (by norm_num)
    (subsetOf 7 [0, 6]) (by decide) CFSG.KBFact.F8009a CFSG.KBFact.F8009b
  exact ⟨h.1, h.2.trans (by norm_num)⟩

open CFSG.SectionRank.Native CFSG.CosetTable CFSG.Blueprint
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest in
open scoped commutatorElement in
theorem certificate8009 : (∃ g : Fin 7 → NativeSporadic.McL,
      (∀ i, mclCoverE i ≠ 0 → g i ^ mclCoverE i = 1) ∧
      (∀ i, mclCoverE i = 0 → g i = ⁅evalW g (mclCoverCWf i).1, evalW g (mclCoverCWf i).2⁆) ∧
      (∀ w ∈ mclCoverRels, evalW g w = 1) ∧
      58320 ≤ Nat.card (Subgroup.closure (Set.range g))) ∧
    (Finite (PG 7 mclPresWords) ∧ Nat.card (PG 7 mclPresWords) ≤ 14580 * 4) ∧
    (Finite (PG 7 mclGammaWords) ∧ Nat.card (PG 7 mclGammaWords) ≤ 87480 * 4) :=
  ⟨CFSG.KD.CoverMcL.witness, KernelCover.McCov.pres_card, mcl_gamma_card⟩

end Certificates
