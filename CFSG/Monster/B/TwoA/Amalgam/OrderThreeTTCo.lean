module

public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTTCore
public import CFSG.Monster.B.Generic.CoConnected
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeType

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Classical.UnitarySix (IsoPt isoGraph)

theorem exists_adj_of_isSRGWith {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n) (hk : 0 < k) :
    ∃ p q, G.Adj p q := by
  have hV : Nonempty V := Fintype.card_pos_iff.1 (h.card ▸ hn)
  obtain ⟨p⟩ := hV
  obtain ⟨q, hq⟩ : (G.neighborFinset p).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree, h.regular p]
    exact hk
  exact ⟨p, q, (G.mem_neighborFinset p q).1 hq⟩

theorem compl_connected_of_isSRGWith {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n k ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (hn : 0 < n) (hk : n < 2 * (n - 1 - k)) : Gᶜ.Connected := by
  have hcard := h.card
  have hreg := h.regular.compl
  rw [hcard] at hreg
  have hV : Nonempty V := Fintype.card_pos_iff.1 (hcard ▸ hn)
  refine SimpleGraph.Connected.mk fun p q => ?_
  by_cases hpq : p = q
  · exact hpq ▸ SimpleGraph.Reachable.refl p
  · obtain ⟨r, hr⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ (Gᶜ.neighborFinset p)) (Finset.subset_univ (Gᶜ.neighborFinset q)) (by
        rw [Finset.card_univ, hcard, Gᶜ.card_neighborFinset_eq_degree,
          Gᶜ.card_neighborFinset_eq_degree, hreg p, hreg q]
        omega)
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hr
    exact hr.1.reachable.trans hr.2.reachable.symm

theorem isoGraph_exists_adj : ∃ p q : IsoPt, isoGraph.Adj p q :=
  exists_adj_of_isSRGWith
    CFSG.Monster.B.Classical.UnitarySix.unitary_six_isotropic_point_graph.1 (by norm_num)
    (by norm_num)

theorem isoGraph_compl_connected : isoGraphᶜ.Connected := by
  classical
  exact compl_connected_of_isSRGWith
    CFSG.Monster.B.Classical.UnitarySix.unitary_six_isotropic_point_graph.1 (by norm_num)
    (by norm_num)

@[expose] def nbrInduceIso
    (C : Set CVert) (x : C) :
    (cgraph.induce C).induce ((cgraph.induce C).neighborSet x) ≃g
      cgraph.induce (cgraph.neighborSet x ∩ C) where
  toFun y := ⟨y.1.1, y.2, y.1.2⟩
  invFun z := ⟨⟨z.1, z.2.2⟩, z.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem compl_connected_commonNeighbors
    {v w : CVert} (hw : w ∈ sphereThree v) :
    (cgraph.induce (cgraph.commonNeighbors v w))ᶜ.Connected := by
  have h1 := native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw
  have hC : Nonempty (cgraph.commonNeighbors v w) := h1.1.to_subtype
  have hiso : ∀ x : cgraph.commonNeighbors v w,
      Nonempty ((cgraph.induce (cgraph.commonNeighbors v w)).induce
        ((cgraph.induce (cgraph.commonNeighbors v w)).neighborSet x) ≃g isoGraph) :=
    fun x => ⟨(nbrInduceIso _ x).trans (h1.2.2.2.2 x x.2).2.2.2.choose⟩
  refine CFSG.Monster.B.Generic.locally_coconnected_graph_complement_connected _
    (fun x => ?_) (fun x => ?_)
  · obtain ⟨e⟩ := hiso x
    obtain ⟨p, q, hpq⟩ := isoGraph_exists_adj
    exact ⟨s(e.symm p, e.symm q), (SimpleGraph.mem_edgeSet _).2 ((e.symm.map_adj_iff).2 hpq)⟩
  · obtain ⟨e⟩ := hiso x
    let ec : ((cgraph.induce (cgraph.commonNeighbors v w)).induce
        ((cgraph.induce (cgraph.commonNeighbors v w)).neighborSet x))ᶜ ≃g isoGraphᶜ :=
      { toEquiv := e.toEquiv
        map_rel_iff' := fun {a b} => by
          simp only [SimpleGraph.compl_adj, ne_eq, RelIso.coe_fn_toEquiv, e.map_adj_iff,
            e.injective.eq_iff] }
    exact ec.symm.connected_iff.mp isoGraph_compl_connected

theorem conj_eq_of_orderOf_mul_eq_three {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (h3 : orderOf (a * b) = 3) : (b * a)⁻¹ * a * (b * a) = b := by
  have hc : (a * b) ^ 3 = 1 := by
    rw [← h3]
    exact pow_orderOf_eq_one _
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc (b * a)⁻¹ * a * (b * a) = a⁻¹ * b⁻¹ * a * b * a := by group
    _ = a * b * a * b * a := by rw [ha', hb']
    _ = (a * b) ^ 3 * b⁻¹ := by rw [pow_three]; group
    _ = b := by rw [hc, one_mul, hb']

section Class

variable (H : ∀ x : CVert, LocalHom x)
include H

theorem conj_clabelS_mem_cnLabels {v w u : CVert} (hu : u ∈ cgraph.commonNeighbors v w)
    {h : Shat} (hh : h ∈ cnGroup v w) : h⁻¹ * clabelS u * h ∈ cnLabels v w := by
  have hq := Subgroup.mem_inf.1 (cnGroup_le H v w hh)
  exact ⟨cvMul u h, cvMul_mem_commonNeighbors (mem_vStab.1 hq.1) (mem_vStab.1 hq.2) hu,
    clabelS_cvMul u h⟩

theorem cnLabels_eq_conj
    {v w : CVert} (hw : w ∈ sphereThree v) {u : CVert}
    (hu : u ∈ cgraph.commonNeighbors v w) :
    cnLabels v w = {y | ∃ h ∈ cnGroup v w, y = h⁻¹ * clabelS u * h} := by
  have key : ∀ b : cgraph.commonNeighbors v w,
      Relation.ReflTransGen (cgraph.induce (cgraph.commonNeighbors v w))ᶜ.Adj ⟨u, hu⟩ b →
        ∃ h ∈ cnGroup v w, clabelS b = h⁻¹ * clabelS u * h := by
    intro b hb
    induction hb with
    | refl => exact ⟨1, one_mem _, by rw [inv_one, one_mul, mul_one]⟩
    | @tail b c _ hbc ih =>
      obtain ⟨h, hh, he⟩ := ih
      rw [SimpleGraph.compl_adj] at hbc
      have hne : (b : CVert) ≠ c := fun e => hbc.1 (Subtype.ext e)
      have h3 : orderOf (clabelS b * clabelS c) = 3 := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_clabel_mul_of_not_adj hw b.2 c.2 hne hbc.2
      refine ⟨h * (clabelS c * clabelS b),
        mul_mem hh (mul_mem (clabelS_mem_cnGroup c.2) (clabelS_mem_cnGroup b.2)), ?_⟩
      calc clabelS c = (clabelS c * clabelS b)⁻¹ * clabelS b * (clabelS c * clabelS b) :=
            (conj_eq_of_orderOf_mul_eq_three (clabelS_mul_self H _) (clabelS_mul_self H _)
              h3).symm
        _ = (clabelS c * clabelS b)⁻¹ * (h⁻¹ * clabelS u * h) * (clabelS c * clabelS b) := by
            rw [← he]
        _ = (h * (clabelS c * clabelS b))⁻¹ * clabelS u * (h * (clabelS c * clabelS b)) := by
            group
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    show ∃ h ∈ cnGroup v w, clabelS z = h⁻¹ * clabelS u * h
    refine key ⟨z, hz⟩ ?_
    rw [← SimpleGraph.reachable_iff_reflTransGen]
    exact (compl_connected_commonNeighbors hw).preconnected _ _
  · rintro ⟨h, hh, rfl⟩
    exact conj_clabelS_mem_cnLabels H hu hh

end Class

end CFSG.Monster.B.TwoA.Amalgam
