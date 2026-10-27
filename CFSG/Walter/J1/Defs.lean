module

public import CFSG.Walter.Defs

public section

namespace CFSG.Walter.J1

structure JankoHyp (G : Type) [Group G] [Finite G] where
  isSimpleGroup : IsSimpleGroup G
  abelian_sylow : HasAbelianSylowTwo G
  t : G
  orderOf_t : orderOf t = 2
  F : Subgroup G
  le_centralizer : F ≤ Subgroup.centralizer ({t} : Set G)
  t_not_mem : t ∉ F
  centralizer_eq : Subgroup.centralizer ({t} : Set G) = Subgroup.zpowers t ⊔ F
  iso : F ≃* alternatingGroup (Fin 5)

end CFSG.Walter.J1
