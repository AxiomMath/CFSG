module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3F2
public import CFSG.Sporadic.Schreier.Co3Order
public import Certificates.Certificate291360

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.CosetTable CFSG.AGLEmbedding CFSG.Blueprint

theorem exists_co3Local3 :
    ∃ x : Fin 3 → NativeSporadic.Co3,
      (∀ r ∈ co3Local3.rels, FreeGroup.lift x (FreeGroup.mk r) = 1) ∧
      (∀ i : Fin 3, x i ^ co3Local3.ords.getD i 0 = 1) ∧
      69984 ≤ Nat.card (Subgroup.closure (Set.range x)) :=
  Certificates.certificate291360.1

theorem card_co3Cover_le :
    Finite (PG 3 co3Cover) ∧ Nat.card (PG 3 co3Cover) ≤ 69984 :=
  Certificates.certificate291360.2

theorem kernelTrivialAt_three_Co3 :
    KernelTrivialAt (NativeSporadic.Carrier .Co3) 3 := by
  have hcard : Nat.card (NativeSporadic.Carrier .Co3) = 495766656000 :=
    CFSG.Sporadic.Schreier.Co3.card_Co3_of_perm
  have hsyl : (Nat.card (NativeSporadic.Carrier .Co3)).factorization 3 ≤
      (69984 : ℕ).factorization 3 := by
    rw [hcard]
    exact factorization_three_le (k := 7) (b := 226688000) (c := 32) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨x, hR, hpow, hn⟩ := exists_co3Local3
  have : Finite (NativeSporadic.Carrier .Co3) := Finite.of_injective _
    (CFSG.SectionRank.LocalWitness.valHom_injective (NativeSporadic.seedMonoid 2 22 1
      NativeSporadic.Co3Seed1 NativeSporadic.Co3Seed2))
  exact kernelTrivialAt_three_of_local_card x hR hpow (by decide) card_co3Cover_le hn hsyl

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
