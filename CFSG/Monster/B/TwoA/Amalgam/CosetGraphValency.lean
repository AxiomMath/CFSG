module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphPoints
public import CFSG.Monster.B.TwoA.Amalgam.Deck

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Geometry CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.CosetBuilding

theorem natCard_neighborSet_cv0_eq :
    Nat.card (cgraph.neighborSet cv0) = 3968055 := by
  rw [natCard_neighborSet_cv0]
  exact short_F4_deck_triviality_and_native_order.2.2.2.2.2.2.2.2.2

theorem short_F4_native_coset_graph_valency_and_cliques :
    cgraph.Connected ∧
    (∀ s : Shat, (∀ v, cvMul v s = v) → s = 1) ∧
    (∀ v w : CVert, ∃ s : Shat, cvMul v s = w) ∧
    (∀ v w v' w' : CVert, cgraph.Adj v w → cgraph.Adj v' w' →
      ∃ s : Shat, cvMul v s = v' ∧ cvMul w s = w') ∧
    (∀ s : Shat, cvMul cv0 s = cv0 ↔ (s : Dfull) ∈ Eam) ∧
    (∀ (a : Dfull) (ha : a ∈ Ehat) (hn : a ∉ N1),
      (∀ e : Eam, (nbrEquiv ha hn (Quotient.mk _ e) : CVert) = cvOf (elS ha * toS e)) ∧
      ∀ e f : Eam, (nbrEquiv ha hn (Quotient.mk _ (e * f)) : CVert) =
        cvMul (nbrEquiv ha hn (Quotient.mk _ e)) (toS f)) ∧
    Nat.card (cgraph.neighborSet cv0) = 3968055 ∧
    (∃ δ : Chamber → Chamber → WeylGroup .F4,
      IsWeylDistanceBuilding (coxeterSystem .F4) δ ∧
      ∀ (i : Fin Tag.F4.rank) (x y : Chamber),
        chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) ∧
    (∀ e : Eam, (ptEquiv (Quotient.mk _ e) : Set Chamber) = vtx 0 (chamberOf e)) ∧
    (∀ e f : Eam, (ptEquiv (Quotient.mk _ (e * f)) : Set Chamber) =
      chamberMulPerm f '' ptEquiv (Quotient.mk _ e)) ∧
    Set.range clabel = {y | ∃ s : Shat, ((s : Dfull))⁻¹ * cQ * s = y} ∧
    (∀ v : CVert, Set.InjOn clabel (cgraph.neighborSet v)) ∧
    (∀ v w : CVert, cgraph.Adj v w →
      clabel v ≠ clabel w ∧ clabel v * clabel w = clabel w * clabel v ∧
      clabel v * clabel v = 1 ∧ clabel w * clabel w = 1 ∧
      ∃ s : Shat, clabel v * clabel w = (s : Dfull)⁻¹ * xhat * s) ∧
    (∀ v : CVert,
      Nat.card (clabel ⁻¹' {clabel v}) = ((Eam.subgroupOf Shat).subgroupOf CSc).index) ∧
    (cSigma 1).ncard = 120 ∧
    (∀ v ∈ cSigma 1, ∀ w ∈ cSigma 1, v ≠ w → cgraph.Adj v w) ∧
    (∀ (a : Dfull) (ha : a ∈ Ehat) (hn : a ∉ N1) (e : Eam) (u : P1Cos),
      nbr ha hn u ∈ cSigma (toS e) \ {cv0} ↔ (ptMap u ∩ vtx 3 (chamberOf e)).Nonempty) ∧
    (∀ x : Chamber, ∃ e : Eam, vtx 3 x = vtx 3 (chamberOf e)) ∧
    (cSigma 1 \ {cv0}).ncard = 119 ∧
    (∀ (a : Dfull) (ha : a ∈ Ehat) (hn : a ∉ N1) (u w : P1Cos), u ≠ w → ∀ x : Chamber,
      (ptMap u ∩ vtx 3 x).Nonempty → (ptMap w ∩ vtx 3 x).Nonempty →
      cgraph.Adj (nbr ha hn u) (nbr ha hn w)) := by
  obtain ⟨-, -, -, -, ⟨δ, hδ, hadj, -⟩, -⟩ := short_F4_deck_triviality_and_native_order
  refine ⟨cgraph_connected, cvMul_faithful, cvMul_transitive,
    fun _ _ _ _ h h' => cvMul_edge_transitive h h', cvMul_cv0_iff,
    fun _ ha hn => ⟨fun _ => rfl, fun e f => nbr_mk_mul ha hn e f⟩, natCard_neighborSet_cv0_eq,
    ⟨δ, hδ, hadj⟩, fun _ => rfl, ptMap_mk_mul, range_clabel, clabel_injOn_neighborSet,
    fun _ _ h => clabel_adj h, natCard_fiber, ncard_cSigma,
    fun _ hv _ hw hne => cSigma_isClique hv hw hne,
    fun _ ha hn e u => nbr_mem_cSigma_diff_iff ha hn e u, fun x => ?_, ncard_cSigma_diff,
    fun _ ha hn _ _ huw x hu hw => nbr_adj_of_common_vtx ha hn huw x hu hw⟩
  obtain ⟨e, rfl⟩ := chamberOf_surjective x
  exact ⟨e, rfl⟩

end CFSG.Monster.B.TwoA.Amalgam
