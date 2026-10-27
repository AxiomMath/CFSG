module

public import CFSG.Quasithin.AppendixH.H9.H93.H93Defs

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem psiExt_coe (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) (x : ↥(Mg 4)) :
    psiExt ψ (x : MulAut (PairN 4)) = ψ x :=
  psiExt_of_mem ψ x.2

theorem psiExt_mul (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {x y : MulAut (PairN 4)}
    (hx : x ∈ Mg 4) (hy : y ∈ Mg 4) : psiExt ψ (x * y) = psiExt ψ x * psiExt ψ y := by
  rw [psiExt_of_mem ψ ((Mg 4).mul_mem hx hy), psiExt_of_mem ψ hx, psiExt_of_mem ψ hy,
    ← map_mul]
  rfl

theorem orderOf_psiExt (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {t : MulAut (PairN 4)}
    (ht : t ∈ Mg 4) : orderOf (psiExt ψ t) = orderOf t := by
  rw [psiExt_of_mem ψ ht, MulEquiv.orderOf_eq]
  exact Subgroup.orderOf_mk t ht

end CFSG.ASVolI.ChH
