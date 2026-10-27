module

public import CFSG.Quasithin.AppendixH.H9.H92.OrthoCard.OrthogonalAction

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem card_centralizer_swap_le :
    Nat.card ↥(Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5)))) ≤ 720 :=
  (Nat.card_le_card_of_injective _
    (orthBasisPerm_injective.comp orthMatOfMem_injective)).trans card_perm_orthonormalBasis5_le

end CFSG.ASVolI.ChH
