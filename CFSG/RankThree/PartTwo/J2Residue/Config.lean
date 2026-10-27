module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G]

structure J2Config (L : Subgroup G) (d : G) (LB : Subgroup G) : Prop where
  perfect : Group.IsPerfect L
  j2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* J2)
  mem_d : d ∈ L
  orderOf_d : orderOf d = 3
  threeCentral : ∃ S : Sylow 3 ↥L, (⟨d, mem_d⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
    (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, mem_d⟩ : ↥L)}
  lB_eq : LB = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))
  tripleCover : Sec4.IsTripleCover (↥LB ⧸ CFSG.pCore 2 ↥LB) (alternatingGroup (Fin 6))
  mem_lB : d ∈ LB
  pCoreOf_le : CFSG.Open.pCoreOf 2 LB ≤ CFSG.Open.pCoreOf 2 L

end CFSG.RankThree.PartTwo.J2Residue
