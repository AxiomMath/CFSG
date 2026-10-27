module

public import CFSG.Quasithin.Vol2.Ch11SecDSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem mem_normalizer_zpowers_of_mem_centralizer {z g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  have h : Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer (Subgroup.zpowers z : Set G) :=
    by rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact Subgroup.centralizer_le_normalizer _ (h ▸ hg)

variable [Finite G]

end CFSG.Quasithin.Vol2.Ch11.SecD
