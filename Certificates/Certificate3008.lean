module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUniqueData
import Certificates.Kernel.Misc.Coset.C3008

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.SympSix CFSG.LieType.Multipliers CFSG.CosetTable in
theorem certificate3008 : (((rels.all fun r => decide (wordPerm r = 1)) && ((List.finRange 3).all fun i =>
      decide (wordPerm (commWords (coverPairs i)) = sympGen i)) && decide (wordPerm wordSB =
      CFSG.EvenSmallLie.Sp6.sp6B)) = true)
    ∧ ((genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 3 [0, 1])).FiniteIndex ∧
      (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 3 [0, 1])).index ≤ 56)
    ∧ ((Subgroup.zpowers (PresentedGroup.mk {r | r ∈ relsY.map FreeGroup.mk}
        (FreeGroup.mk [(1, true)]))).FiniteIndex ∧
      (Subgroup.zpowers (PresentedGroup.mk {r | r ∈ relsY.map FreeGroup.mk}
        (FreeGroup.mk [(1, true)]))).index ≤ 5184)
    ∧ ((genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 3 [0, 1])).FiniteIndex ∧
      (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 3 [0, 1])).index ≤ 56)
    ∧ (Finite (PG _ cover₁) ∧ Nat.card (PG _ cover₁) ≤ 51840) :=
  ⟨KernelMiscCoset.C3008.model, KernelMiscCoset.C3008.pres, KernelMiscCoset.C3008.presY,
    KernelMiscCoset.C3008.cover, KernelMiscCoset.C3008.cover₁_card⟩

end Certificates
