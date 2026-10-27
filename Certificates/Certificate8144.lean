module

public import CFSG.RankThree.Native.ONTriplePresInputs
import Certificates.Kernel.Misc.Coset.C8144Index

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple CFSG.CosetTable in
theorem certificate8144 : (Finite (PG (subsetOf 8 [0, 1, 2, 3, 4, 5]).length C1) ∧
      Nat.card (PG (subsetOf 8 [0, 1, 2, 3, 4, 5]).length C1) ≤ 3753792)
    ∧ (Finite (PG 8 (coverRels 1 1 1)) ∧ Nat.card (PG 8 (coverRels 1 1 1)) ≤ 1382446517760)
    ∧ (Finite (PG 8 (coverRels 0 0 0)) ∧ Nat.card (PG 8 (coverRels 0 0 0)) ≤ 1382446517760)
    ∧ ((genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
        (subsetOf 8 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
        (subsetOf 8 [0, 1, 2, 3, 4, 5])).index ≤ 368280) :=
  ⟨KernelMiscCoset.C8144.card_coxeter_le, KernelMiscCoset.C8144.card_one_le,
    KernelMiscCoset.C8144.card_zero_le, KernelMiscCoset.C8144.index_one_le⟩

end Certificates
