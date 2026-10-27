module

public import CFSG.RankThree.PartOne.Mult.Sporadic
public import CFSG.Sporadic.Recognition.HNMult3Cert

public section

namespace CFSG.RankThree.PartOne.MultRes

open CFSG.Blueprint CFSG.RankThree.PartOne.Mult

theorem sporadicKernelTrivial_hn_three :
    SporadicKernelTrivial .HN 3 := by
  intro E _ _ hE S _ π hS hπ hC hpg
  obtain ⟨e⟩ := hS
  have : Group.IsPerfect E := hE
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact map_eq_one_iff e e.injective
  have h := CFSG.Sporadic.Recognition.HNMult3.ker_eq_bot_of_certificate (E := E)
    (e.toMonoidHom.comp π) (e.surjective.comp hπ) (hker ▸ hC) (hker ▸ hpg)
  exact hker.symm.trans h

end CFSG.RankThree.PartOne.MultRes
