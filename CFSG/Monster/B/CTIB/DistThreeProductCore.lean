module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentOrbits
public import CFSG.Monster.B.TwoA.Amalgam.DiameterThree

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem distThreeLocalOrbits_of_inputs
    (hL : DistThreeLabelsInput) (hO : DistThreeOuterInput)
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) : DistThreeLocalOrbits := by
  intro v u hvu
  have h := native_distance_three_pair_two_local_root_orbits hL hO hP hT hvu
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

theorem dist_le_three_of_inputs
    (hL : DistThreeLabelsInput) (hO : DistThreeOuterInput)
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) (v w : CVert) :
    cgraph.dist v w ≤ 3 :=
  dist_le_three (distThreeLocalOrbits_of_inputs hL hO hP hT)
    (fun v w u hw hwu h => hT v w u hw hwu (mem_sphereDistThree.2 h)) v w

theorem clabel_injective_of_inputs
    (hL : DistThreeLabelsInput) (hO : DistThreeOuterInput)
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) : Function.Injective clabel :=
  clabel_injective_of (dist_le_three_of_inputs hL hO hP hT) fun v u hvu he =>
    (hL v u hvu).2.2.1 (Subtype.ext he.symm)

theorem commute_clabelS_iff
    (hinj : Function.Injective clabel) (p : CVert) (s : Shat) :
    Commute s (clabelS p) ↔ s ∈ vStab p :=
  Subtype.ext_iff.trans (commute_clabel_iff_of_injective hinj p s)

theorem exists_clabelS_eq_of_isConj
    {v : CVert} {a : Shat} (h : IsConj (clabelS v) a) :
    ∃ x : CVert, clabelS x = a := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  exact ⟨cvMul v g⁻¹, by rw [clabelS_cvMul, inv_inv, hg]⟩

theorem isConj_clabelS
    (v w : CVert) : IsConj (clabelS v) (clabelS w) := by
  obtain ⟨g, hg⟩ := cvMul_transitive v w
  refine isConj_iff.2 ⟨g⁻¹, ?_⟩
  rw [← hg, clabelS_cvMul, inv_inv]

theorem orderOf_clabelS_mul
    (p q : CVert) :
    orderOf (clabelS p * clabelS q) = orderOf (clabel p * clabel q) :=
  (Subgroup.orderOf_coe (clabelS p * clabelS q)).symm

theorem commute_clabelS_of_adj
    {p q : CVert} (h : cgraph.Adj p q) :
    Commute (clabelS p) (clabelS q) :=
  Subtype.ext (clabel_adj h).2.1

theorem sq_clabelS_mul_of_commute
    {p q : CVert} (h : Commute (clabelS p) (clabelS q)) :
    (clabelS p * clabelS q) ^ 2 = 1 := by
  rw [h.mul_pow, sq, sq, clabelS_mul_clabelS, clabelS_mul_clabelS, one_mul]

theorem commute_or_three_or_four
    (hdiam : ∀ v w : CVert, cgraph.dist v w ≤ 3)
    (hL : DistThreeLabelsInput) (p q : CVert) :
    Commute (clabelS p) (clabelS q) ∨ (q ∈ sphereThree p ∧ orderOf (clabelS p * clabelS q) = 3) ∨
      (q ∈ sphereFour p ∧ orderOf (clabelS p * clabelS q) = 4) := by
  have hle := hdiam p q
  rcases (show cgraph.dist p q = 0 ∨ cgraph.dist p q = 1 ∨ cgraph.dist p q = 2 ∨
    cgraph.dist p q = 3 by omega) with h0 | h1 | h2 | h3
  · left
    have hpq : p = q := by
      by_contra hne
      exact absurd h0 (cgraph_connected.pos_dist_of_ne hne).ne'
    rw [hpq]
  · exact Or.inl (commute_clabelS_of_adj (SimpleGraph.dist_eq_one_iff_adj.1 h1))
  · rcases labelThree_or_labelFour_of_dist exists_rootModel h2 with h | h
    · have hq : q ∈ sphereThree p := ⟨h2, h.1⟩
      refine Or.inr (Or.inl ⟨hq, ?_⟩)
      rw [orderOf_clabelS_mul]
      exact ((native_order_three_label_products_and_dihedral_triples p).1 q hq).1
    · have hq : q ∈ sphereFour p := ⟨h2, h.1⟩
      refine Or.inr (Or.inr ⟨hq, ?_⟩)
      rw [orderOf_clabelS_mul]
      exact (native_coset_graph_order_four_common_neighbors.1 p q hq).1
  · exact Or.inl (hL p q h3).2.2.2.symm

theorem adj_or_dist_three_of_commute
    (hdiam : ∀ v w : CVert, cgraph.dist v w ≤ 3)
    {p q : CVert} (hne : p ≠ q) (hc : Commute (clabelS p) (clabelS q)) :
    cgraph.Adj p q ∨ cgraph.dist p q = 3 := by
  have hle := hdiam p q
  have hpos : 0 < cgraph.dist p q := cgraph_connected.pos_dist_of_ne hne
  have hdvd : orderOf (clabelS p * clabelS q) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (sq_clabelS_mul_of_commute hc)
  rcases (show cgraph.dist p q = 1 ∨ cgraph.dist p q = 2 ∨ cgraph.dist p q = 3 by omega) with
    h1 | h2 | h3
  · exact Or.inl (SimpleGraph.dist_eq_one_iff_adj.1 h1)
  · exfalso
    rcases labelThree_or_labelFour_of_dist exists_rootModel h2 with h | h
    · have h3 := ((native_order_three_label_products_and_dihedral_triples p).1 q ⟨h2, h.1⟩).1
      rw [← orderOf_clabelS_mul] at h3
      rw [h3] at hdvd
      exact absurd hdvd (by decide)
    · have h4 := (native_coset_graph_order_four_common_neighbors.1 p q ⟨h2, h.1⟩).1
      rw [← orderOf_clabelS_mul] at h4
      rw [h4] at hdvd
      exact absurd hdvd (by decide)
  · exact Or.inr h3

theorem sq_clabel_mul_of_mem_cPi
    {p q : CVert} (hq : q ∈ sphereFour p) {s : Shat}
    (hp : p ∈ cPi s) (hqs : q ∈ cPi s) :
    (clabel p * clabel q) ^ 2 = ((s : Dfull))⁻¹ * xhat * s := by
  have hp' := mem_cPi_iff.1 hp
  have hq' := mem_cPi_iff.1 hqs
  have hpq : p ≠ q := (cgraph_dist_eq_two_iff.1 hq.1).1
  have hna : ¬ cgraph.Adj p q := (cgraph_dist_eq_two_iff.1 hq.1).2.1
  have hne : (⟨cvMul p s⁻¹, hp'⟩ : cPi0) ≠ ⟨cvMul q s⁻¹, hq'⟩ := fun h =>
    hpq (cvMul_injective s⁻¹ (congrArg Subtype.val h))
  have hna' : ¬ cgraphPi.Adj (⟨cvMul p s⁻¹, hp'⟩ : cPi0) ⟨cvMul q s⁻¹, hq'⟩ := fun h =>
    hna ((cgraph_adj_cvMul p q s⁻¹).1 h)
  have h := (native_coset_graph_order_four_common_neighbors.2.2 _ _ hne hna').1
  have e : clabel (cvMul p s⁻¹) * clabel (cvMul q s⁻¹) =
      (s : Dfull) * (clabel p * clabel q) * (s : Dfull)⁻¹ := by
    rw [clabel_cvMul, clabel_cvMul, Subgroup.coe_inv, inv_inv]
    group
  have h' : (s : Dfull) * (clabel p * clabel q) ^ 2 * (s : Dfull)⁻¹ = xhat := by
    rw [← conj_pow, ← e]
    exact h
  rw [← h']
  group

theorem dist_le_two_of_sq_eq
    {v w x : CVert} (hvx : x ∈ sphereFour v) (hwx : x ∈ sphereFour w)
    (hsq : (clabel v * clabel x) ^ 2 = (clabel w * clabel x) ^ 2) : cgraph.dist v w ≤ 2 := by
  obtain ⟨s, hvs, hxs⟩ := (native_coset_graph_order_four_common_neighbors.1 v x hvx).2.2.1
  obtain ⟨t, hwt, hxt⟩ := (native_coset_graph_order_four_common_neighbors.1 w x hwx).2.2.1
  have h1 := sq_clabel_mul_of_mem_cPi hvx hvs hxs
  have h2 := sq_clabel_mul_of_mem_cPi hwx hwt hxt
  have hJ : ((t * s⁻¹ : Shat) : Dfull) ∈ Jhat := by
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul,
      Subgroup.coe_inv]
    have e : (s : Dfull)⁻¹ * xhat * s = (t : Dfull)⁻¹ * xhat * t := by rw [← h1, ← h2, hsq]
    calc (t : Dfull) * (s : Dfull)⁻¹ * xhat =
          (t : Dfull) * ((s : Dfull)⁻¹ * xhat * s) * (s : Dfull)⁻¹ := by group
      _ = (t : Dfull) * ((t : Dfull)⁻¹ * xhat * t) * (s : Dfull)⁻¹ := by rw [e]
      _ = xhat * ((t : Dfull) * (s : Dfull)⁻¹) := by group
  have hts : cPi t = cPi s := by
    have h := cPi_mul_left hJ s
    rwa [inv_mul_cancel_right] at h
  rw [hts] at hwt
  have hv' := mem_cPi_iff.1 hvs
  have hw' := mem_cPi_iff.1 hwt
  rw [← dist_cvMul v w s⁻¹]
  by_cases hvw : (⟨cvMul v s⁻¹, hv'⟩ : cPi0) = ⟨cvMul w s⁻¹, hw'⟩
  · rw [show cvMul v s⁻¹ = cvMul w s⁻¹ from congrArg Subtype.val hvw, SimpleGraph.dist_self]
    omega
  · by_cases ha : cgraphPi.Adj (⟨cvMul v s⁻¹, hv'⟩ : cPi0) ⟨cvMul w s⁻¹, hw'⟩
    · rw [SimpleGraph.dist_eq_one_iff_adj.2
        (show cgraph.Adj (cvMul v s⁻¹) (cvMul w s⁻¹) from ha)]
      omega
    · rw [dist_eq_two_of_pi hvw ha]

theorem betaGroup_mul_eq_one
    {r r' : betaGroup} (h : r ≠ 1) (h' : r' ≠ 1) : r * r' = 1 := by
  have e : ∀ x : betaGroup, x ≠ 1 → (x : MulAut stdGroup) = betaG := fun x hx =>
    (mem_betaGroup_iff.1 x.2).resolve_left fun e => hx (Subtype.ext e)
  apply Subtype.ext
  rw [Subgroup.coe_mul, e r h, e r' h', OneMemClass.coe_one]
  exact betaG_mul_self

end CFSG.Monster.B.CTIB
