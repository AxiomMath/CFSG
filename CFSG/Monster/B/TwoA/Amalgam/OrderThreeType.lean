module

public import CFSG.Monster.B.TwoA.Amalgam.OrderThree
public import CFSG.Monster.B.TwoA.Amalgam.OrderFour

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

theorem pow_four_eq_one_of_sq_conj {G : Type*} [Group G] {g p x : G} (hx : x * x = 1)
    (h : (g⁻¹ * p * g) ^ 2 = x) : p ^ 4 = 1 := by
  have h1 : g⁻¹ * (p * p) * g = x := by
    rw [← h, sq]
    group
  have h2 : p * p = g * x * g⁻¹ := by
    rw [← h1]
    group
  calc p ^ 4 = p * p * (p * p) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    _ = g * (x * x) * g⁻¹ := by rw [h2]; group
    _ = 1 := by rw [hx, mul_one, mul_inv_cancel]

theorem orderOf_clabel_mul_of_adj
    {u z : CVert} (h : cgraph.Adj u z) :
    clabel u ≠ clabel z ∧ Commute (clabel u) (clabel z) ∧ orderOf (clabel u * clabel z) = 2 := by
  obtain ⟨hne, hc, hu, hz, -⟩ := clabel_adj h
  refine ⟨hne, hc, orderOf_eq_prime ?_ fun h1 => hne ?_⟩
  · calc (clabel u * clabel z) ^ 2 = clabel u * (clabel z * clabel u) * clabel z := by
          rw [sq]
          group
      _ = clabel u * (clabel u * clabel z) * clabel z := by rw [← hc]
      _ = clabel u * clabel u * (clabel z * clabel z) := by group
      _ = 1 := by rw [hu, hz, one_mul]
  · exact (eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right hz)

theorem mem_sphereThree_of_mem_commonNeighbors
    {v w u z : CVert} (hw : w ∈ sphereThree v)
    (hu : u ∈ cgraph.commonNeighbors v w) (hz : z ∈ cgraph.commonNeighbors v w) (huz : u ≠ z)
    (hna : ¬cgraph.Adj u z) : z ∈ sphereThree u := by
  have hd : cgraph.dist u z = 2 :=
    cgraph_dist_eq_two_iff.2 ⟨huz, hna, v, (hu.1 : cgraph.Adj v u).symm, hz.1⟩
  have hmem : z ∈ sphereThree u ∪ sphereFour u := by
    rw [← (native_coset_graph_two_distance_two_orbits.2.2.1 u).1]
    exact hd
  rcases hmem with h3 | h4
  · exact h3
  · exfalso
    obtain ⟨hvw, hvwa, -⟩ := cgraph_dist_eq_two_iff.1 hw.1
    obtain ⟨-, -, ⟨s, hus, hzs⟩, -, hsub⟩ := native_coset_graph_order_four_common_neighbors.1 u z h4
    have hvu : cgraph.Adj u v := (hu.1 : cgraph.Adj v u).symm
    have hzv : cgraph.Adj z v := (hz.1 : cgraph.Adj v z).symm
    have hwu : cgraph.Adj u w := (hu.2 : cgraph.Adj w u).symm
    have hzw : cgraph.Adj z w := (hz.2 : cgraph.Adj w z).symm
    have hvs : v ∈ cPi s := hsub s hus hzs ⟨hvu, hzv⟩
    have hws : w ∈ cPi s := hsub s hus hzs ⟨hwu, hzw⟩
    have hv0 := mem_cPi_iff.1 hvs
    have hw0 := mem_cPi_iff.1 hws
    have hne : (⟨cvMul v s⁻¹, hv0⟩ : cPi0) ≠ ⟨cvMul w s⁻¹, hw0⟩ := fun h =>
      hvw (cvMul_injective s⁻¹ (congrArg Subtype.val h))
    have hnadj : ¬cgraphPi.Adj ⟨cvMul v s⁻¹, hv0⟩ ⟨cvMul w s⁻¹, hw0⟩ := fun h =>
      hvwa ((cgraph_adj_cvMul v w s⁻¹).1 h)
    have h2 := (native_coset_graph_order_four_common_neighbors.2.2 _ _ hne hnadj).1
    have e : clabel (cvMul v s⁻¹) * clabel (cvMul w s⁻¹) =
        ((s⁻¹ : Shat) : Dfull)⁻¹ * (clabel v * clabel w) * ((s⁻¹ : Shat) : Dfull) := by
      rw [clabel_cvMul, clabel_cvMul]
      group
    have h4 : (clabel v * clabel w) ^ 4 = 1 :=
      pow_four_eq_one_of_sq_conj xhat_mul_self (e ▸ h2)
    have hdvd := orderOf_dvd_of_pow_eq_one h4
    rcases hw.2 with h | h
    · rw [show orderOf (clabel v * clabel w) = 3 from h] at hdvd
      exact absurd hdvd (by decide)
    · rw [show orderOf (clabel v * clabel w) = 6 from h] at hdvd
      exact absurd hdvd (by decide)

theorem orderOf_clabel_mul_of_not_adj
    {v w u z : CVert} (hw : w ∈ sphereThree v)
    (hu : u ∈ cgraph.commonNeighbors v w) (hz : z ∈ cgraph.commonNeighbors v w) (huz : u ≠ z)
    (hna : ¬cgraph.Adj u z) : orderOf (clabel u * clabel z) = 3 :=
  ((native_order_three_label_products_and_dihedral_triples u).1 z
    (mem_sphereThree_of_mem_commonNeighbors hw hu hz huz hna)).1

end CFSG.Monster.B.TwoA.Amalgam
