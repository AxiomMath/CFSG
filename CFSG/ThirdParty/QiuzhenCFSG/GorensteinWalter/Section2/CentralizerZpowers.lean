module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- Centralizing an element implies centralizing, and hence normalizing, the
cyclic subgroup it generates. -/
public theorem centralizer_singleton_le_normalizer_zpowers
    {G : Type u} [Group G] (t : G) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  have hcent : Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have htx : t * x = x * t :=
      Subgroup.mem_centralizer_iff.mp hx t (by simp)
    exact ((show Commute x t from htx.symm).zpow_right n).symm
  exact hcent.trans
    (Subgroup.centralizer_le_normalizer
      ((Subgroup.zpowers t : Subgroup G) : Set G))

end CFSG.GorensteinWalter
