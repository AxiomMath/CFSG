module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3F2
public import CFSG.Sporadic.Co1
public import Certificates.Certificate291362

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.CosetTable CFSG.AGLEmbedding CFSG.Blueprint

theorem exists_co1Local3 :
    ∃ x : Fin 3 → NativeSporadic.Co1,
      (∀ r ∈ co1Local3.rels, FreeGroup.lift x (FreeGroup.mk r) = 1) ∧
      (∀ i : Fin 3, x i ^ co1Local3.ords.getD i 0 = 1) ∧
      157464 ≤ Nat.card (Subgroup.closure (Set.range x)) :=
  Certificates.certificate291362.1

theorem card_co1Cover_le :
    Finite (PG 3 co1Cover) ∧ Nat.card (PG 3 co1Cover) ≤ 157464 :=
  Certificates.certificate291362.2

theorem kernelTrivialAt_three_Co1 :
    KernelTrivialAt (NativeSporadic.Carrier .Co1) 3 := by
  have hcard : Nat.card (NativeSporadic.Carrier .Co1) = 4157776806543360000 :=
    CFSG.Sporadic.Co1.card_Co1
  have hsyl : (Nat.card (NativeSporadic.Carrier .Co1)).factorization 3 ≤
      (157464 : ℕ).factorization 3 := by
    rw [hcard]
    exact factorization_three_le (k := 9) (b := 211236945920000) (c := 8) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨x, hR, hpow, hn⟩ := exists_co1Local3
  have : Finite (NativeSporadic.Carrier .Co1) := Finite.of_injective _
    (CFSG.SectionRank.LocalWitness.valHom_injective (NativeSporadic.seedMonoid 2 24 1
      NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2))
  exact kernelTrivialAt_three_of_local_card x hR hpow (by decide) card_co1Cover_le hn hsyl

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
