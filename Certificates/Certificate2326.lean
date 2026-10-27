module

public import CFSG.Alternating.Multipliers.Carmichael
import Certificates.Kernel.Misc.Coset.C2326

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Alternating CFSG.Alternating.Multipliers Subgroup CFSG.LieType.Multipliers CFSG.LocalAnalysis.ComponentInitial CFSG.CosetTable in
theorem certificate2326 :
    (Finite (PG 3 (coverWords (carmichaelWords 3) fun i => commWords (carmichaelPairs 3 i))) ∧
      Nat.card (PG 3 (coverWords (carmichaelWords 3) fun i => commWords (carmichaelPairs 3 i))) ≤
        120 ∧
      2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ (coverWords (carmichaelWords 3)
        fun i => commWords (carmichaelPairs 3 i)).map FreeGroup.mk}
        (FreeGroup.mk (carmichaelRel01 1))))
    ∧ (Finite (PG 4 (coverWords (carmichaelWords 4) fun i => commWords (carmichaelPairs 4 i))) ∧
      Nat.card (PG 4 (coverWords (carmichaelWords 4) fun i => commWords (carmichaelPairs 4 i))) ≤
        2160 ∧
      6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ (coverWords (carmichaelWords 4)
        fun i => commWords (carmichaelPairs 4 i)).map FreeGroup.mk}
        (FreeGroup.mk (carmichaelRel01 2))))
    ∧ (Finite (PG 5 (coverWords (carmichaelWords 5) fun i => commWords (carmichaelPairs 5 i))) ∧
      Nat.card (PG 5 (coverWords (carmichaelWords 5) fun i => commWords (carmichaelPairs 5 i))) ≤
        15120 ∧
      6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 5) | r ∈ (coverWords (carmichaelWords 5)
        fun i => commWords (carmichaelPairs 5 i)).map FreeGroup.mk}
        (FreeGroup.mk (carmichaelRel01 3)))) :=
  ⟨KernelMiscCoset.C2326.five, KernelMiscCoset.C2326.six, KernelMiscCoset.C2326.seven⟩

end Certificates
