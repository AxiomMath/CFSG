module

public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddTranspositions.PartThree.Wong

structure WongHyp {G : Type} [Group G] (t : G) (L₁ L₂ : Subgroup G) : Prop where
  orderOf_t : orderOf t = 2
  equiv₁ : Nonempty (L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
  equiv₂ : Nonempty (L₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
  commute : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b
  inf_eq : L₁ ⊓ L₂ = Subgroup.zpowers t
  relIndex_eq : (L₁ ⊔ L₂).relIndex (Subgroup.centralizer {t}) = 2
  sup_oddCore_ne_top : Subgroup.centralizer {t} ⊔ CFSG.oddCore G ≠ ⊤

end CFSG.OddTranspositions.PartThree.Wong
