module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeW
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictDefs

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native


theorem burnsideJ4NP_openReachP_of_tree (htop : burnsideJ4NP_TopFacts)
    (hv : ∀ k, 1 ≤ k → k ≤ treeN → burnsideJ4NP_VerdictWH (burnsideJ4NP_Wv k)) :
    burnsideJ4NP_OpenReachP := by
  have hN : treeN = 1327 := rfl
  refine burnsideJ4NP_openReachP_of_data (fun k => burnsideJ4NP_Rep (k + 1)) treeN
    ⟨0, by omega, 1, Hj.one_mem, ?_⟩ ?_ ?_
  · show Subgroup.zpowers CFSG.Quasithin.J4Loc.z0 =
      (burnsideJ4NP_Rep 1).map (MulAut.conj (1 : J)).toMonoidHom
    rw [burnsideJ4NP_map_conj_one]
    exact burnsideJ4NP_tree_h0
  · intro k hk x hx h2A hxA B hB hB10 hBE
    obtain ⟨k', hk1, hkN, h, hh, hBe⟩ :=
      burnsideJ4NP_treeStep htop (k := k + 1) (by omega) (by omega) x hx h2A hxA B hB hB10 hBE
    refine ⟨k' - 1, by omega, h, hh, ?_⟩
    show B = (burnsideJ4NP_Rep (k' - 1 + 1)).map (MulAut.conj h).toMonoidHom
    rw [show k' - 1 + 1 = k' by omega]
    exact hBe
  · refine burnsideJ4NP_hverdict_of_verdictWH (fun k => burnsideJ4NP_Rep (k + 1))
      (fun k => burnsideJ4NP_Wv (k + 1)) treeN (fun k hk => ⟨1, Hj.one_mem, ?_⟩)
      (fun k hk => hv (k + 1) (by omega) (by omega))
    show Subgroup.closure {x | x ∈ burnsideJ4NP_Rep (k + 1) ∧ burnsideJ4NP_Is2A x} =
      (burnsideJ4NP_Wv (k + 1)).map (MulAut.conj (1 : J)).toMonoidHom
    rw [burnsideJ4NP_map_conj_one]
    exact burnsideJ4NP_closure2A_Rep (by omega) (by omega)

end CFSG.ASVolI
