module

public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.Monster.B.TwoA.Fischer.SliceOrderPSU
public import CFSG.Monster.B.E6.StdF4LeviUnitary

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LieType.Chevalley.C2E6Std CFSG.Assembly.LowTwoRank

@[expose] noncomputable def stdLeviIn : Subgroup stdGroup := (stdLevi firstJ).subgroupOf stdGroup

@[expose] noncomputable def stdLeviEquiv :
    stdLeviIn ≃* StatedProj (StatedSU 6 (2 ^ 1) CFSG.Fischer.F4) :=
  (Subgroup.subgroupOfEquivOfLe
    ((stdLevi_le_nativeParabolic (by simp [firstJ] : (2 : Fin 4) ∈ firstJ)).trans
      (nativeParabolic_le_stdGroup firstJ))).trans
    (CFSG.Monster.B.E6.StdF4.leviPSU.trans CFSG.Monster.B.TwoA.Fischer.projSUStatedEquiv)

theorem exists_elementary_two_nine :
    ∃ U : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) CFSG.Fischer.F4)),
      IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 9 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -, hmax, -⟩ :=
    CFSG.Monster.B.TwoA.Unitary.Clique.unitary_six_maximal_clique_unipotent_kernel
  obtain ⟨hU, hc, -⟩ := h10 _ hmax
  obtain ⟨h1, h2⟩ :=
    CFSG.RankThree.Coprime.isElementaryAbelian_map_mulEquiv
      CFSG.Monster.B.TwoA.Fischer.projSUStatedEquiv hU
  exact ⟨_, h1, h2.trans hc⟩

end CFSG.RankThree.PartOne
