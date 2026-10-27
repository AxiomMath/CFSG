module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3F2
public import CFSG.Sporadic.Co2Cert.Order
public import Certificates.Certificate291361

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.CosetTable CFSG.AGLEmbedding CFSG.Blueprint

theorem exists_co2Local3 :
    ∃ x : Fin 3 → NativeSporadic.Co2,
      (∀ r ∈ co2Local3.rels, FreeGroup.lift x (FreeGroup.mk r) = 1) ∧
      (∀ i : Fin 3, x i ^ co2Local3.ords.getD i 0 = 1) ∧
      23328 ≤ Nat.card (Subgroup.closure (Set.range x)) :=
  Certificates.certificate291361.1

theorem card_co2Cover_le :
    Finite (PG 3 co2Cover) ∧ Nat.card (PG 3 co2Cover) ≤ 23328 :=
  Certificates.certificate291361.2

theorem kernelTrivialAt_three_Co2 :
    KernelTrivialAt (NativeSporadic.Carrier .Co2) 3 := by
  have hcard : Nat.card (NativeSporadic.Carrier .Co2) = 42305421312000 :=
    CFSG.Sporadic.Co2Cert.natCard_Co2
  have hsyl : (Nat.card (NativeSporadic.Carrier .Co2)).factorization 3 ≤
      (23328 : ℕ).factorization 3 := by
    rw [hcard]
    exact factorization_three_le (k := 6) (b := 58032128000) (c := 32) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨x, hR, hpow, hn⟩ := exists_co2Local3
  have : Finite (NativeSporadic.Carrier .Co2) := Finite.of_injective _
    (CFSG.SectionRank.LocalWitness.valHom_injective (NativeSporadic.seedMonoid 2 22 1
      NativeSporadic.Co2Seed1 NativeSporadic.Co2Seed2))
  exact kernelTrivialAt_three_of_local_card x hR hpow (by decide) card_co2Cover_le hn hsyl

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
