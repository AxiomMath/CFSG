module

public import CFSG.Timmesfeld.Bridge.OddLocalCommon
public import CFSG.Timmesfeld.Bridge.OddTranspMain

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddLocal

theorem npcDischarge : NPCDischarge := fun _ _ _ _ hS hperf hB =>
  OddTransp.noPerfectCentralExt_of_isBenderGroup hS hperf hB

theorem commonNeighbour : CommonNeighbourStmt :=
  commonNeighbour_of OddTransp.oddTranspSimple OddTransp.oddTranspSecondKind
    OddTransp.oddTranspThirdKind OddTransp.oddTranspZStar npcDischarge

theorem rootGen_quotient_bender_or_dihedral {G : Type} [Group G] [Finite G] {D : Set G}
    (hD : IsOddTransp D) (hN : IsNormalSet D) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) :
    (∃ n, 2 ≤ n ∧
      Nonempty (rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x) ≃* CFSG.Theory.Comparator.PSL2Model n)) ∨
    (∃ n, 1 ≤ n ∧
      Nonempty (rootGen D d x ⧸ CFSG.pCore 2 (rootGen D d x) ≃* CFSG.Theory.Comparator.SzModel n)) ∨
    (let π := QuotientGroup.mk' (CFSG.pCore 2 (rootGen D d x))
     let dbar := π ⟨d, mem_rootGen_of_mem (mem_rootSet_self hd)⟩
     let xbar := π ⟨x, mem_rootGen_left d x⟩
     Subgroup.closure {dbar, xbar} = ⊤ ∧ orderOf dbar = 2 ∧ orderOf xbar = 2 ∧
       Odd (orderOf (dbar * xbar)) ∧ 1 < orderOf (dbar * xbar) ∧
       ∀ e ∈ rootSet D d,
         e⁻¹ * d ∈ (CFSG.pCore 2 (rootGen D d x)).map (rootGen D d x).subtype) :=
  rootGen_quotient OddTransp.oddTranspZStar commonNeighbour hD hN hd hx hdx

end CFSG.Timmesfeld.Bridge
