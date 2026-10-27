module

public import CFSG.RankThree.OddKernel.SporadicKernelTh
public import Certificates.Certificate291390
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Cover

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.CosetTable CFSG.AGLEmbedding CFSG.Blueprint

theorem kernelTrivialAt_three_Th :
    KernelTrivialAt (NativeSporadic.Carrier .Th) 3 := by
  have hcard : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.OddKernel.card_Th_eq
  have hsyl : (Nat.card (NativeSporadic.Carrier .Th)).factorization 3 ≤
      thULocal3.n.factorization 3 := by
    rw [hcard]
    change (Nat.factorization 90745943887872000) 3 ≤ (Nat.factorization 236196) 3
    rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three]
    decide +kernel
  obtain ⟨⟨g, hR, hpow, hn⟩, hfin, hle⟩ := Certificates.certificate291390
  have : Finite (NativeSporadic.Carrier .Th) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact kernelTrivialAt_three_of_local_card g hR hpow (fun i => by fin_cases i <;> decide)
    ⟨hfin, hle⟩ hn hsyl

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
