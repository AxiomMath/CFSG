module

public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeAmbCore
public import CFSG.Monster.B.TwoA.Amalgam.Exact3510Std
public import CFSG.Monster.B.TwoA.Amalgam.DistTwo
public import CFSG.Monster.B.Generic.Exact3510Spectral
public import CFSG.Monster.B.Generic.LocallyUnitary
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate16022
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3025
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16040
public import Certificates.Certificate16951
public import Certificates.Certificate3027
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import CFSG.Monster.B.TwoA.Amalgam.StdIso
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Generic
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

local notation "𝕄" v:max w:max => cgraph.induce (cgraph.commonNeighbors v w)

@[expose] def cnLocalIso
    (v w : CVert) (z : cgraph.commonNeighbors v w) :
    (cgraph.induce (cgraph.commonNeighbors v w)).induce
        ((cgraph.induce (cgraph.commonNeighbors v w)).neighborSet z) ≃g
      cgraph.induce (cgraph.neighborSet z ∩ cgraph.commonNeighbors v w) where
  toFun y := ⟨y.1.1, y.2, y.1.2⟩
  invFun y := ⟨⟨y.1, y.2.2⟩, y.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[expose] def cnHom
    {v w : CVert} (s : Shat) (hv : cvMul v s = v) (hw : cvMul w s = w) :
    cgraph.induce (cgraph.commonNeighbors v w) →g cgraph.induce (cgraph.commonNeighbors v w) where
  toFun z := ⟨cvMul z s, by
    have h1 := (cgraph_adj_cvMul v z s).2 z.2.1
    have h2 := (cgraph_adj_cvMul w z s).2 z.2.2
    rw [hv] at h1
    rw [hw] at h2
    exact ⟨h1, h2⟩⟩
  map_rel' h := (cgraph_adj_cvMul _ _ s).2 h

theorem coe_cnHom
    {v w : CVert} (s : Shat) (hv : cvMul v s = v) (hw : cvMul w s = w)
    (z : cgraph.commonNeighbors v w) : ((cnHom s hv hw z : cgraph.commonNeighbors v w) : CVert) =
      cvMul z s := rfl

theorem conj_eq_of_braid {G : Type*} [Group G] {d e : G} (hd : d * d = 1) (he : e * e = 1)
    (h : d * e * d = e * d * e) : (d * e * d)⁻¹ * d * (d * e * d) = e := by
  have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  calc (d * e * d)⁻¹ * d * (d * e * d) = d⁻¹ * e⁻¹ * d * e * d := by group
    _ = d * e * d * e * d := by rw [hd', he']
    _ = (e * d * e) * e * d := by rw [h]
    _ = e * d * (e * e) * d := by group
    _ = e * (d * d) := by rw [he, mul_one]; group
    _ = e := by rw [hd, mul_one]

theorem natCard_subgroup_eq_mul
    (K : Subgroup Shat) (u : CVert) :
    Nat.card K = {x | ∃ s ∈ K, cvMul u s = x}.ncard * Nat.card ↥(K ⊓ vStab u) := by
  let f : K → {x | ∃ s ∈ K, cvMul u s = x} := fun s => ⟨cvMul u s.1, s.1, s.2, rfl⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), ← Nat.card_coe_set_eq]
  refine natCard_sigma_const fun y => ?_
  obtain ⟨_, s₀, hs₀, rfl⟩ := y
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1 * s₀⁻¹, Subgroup.mem_inf.2 ⟨K.mul_mem x.1.2 (K.inv_mem hs₀), ?_⟩⟩
      invFun := fun t => ⟨⟨t.1 * s₀, K.mul_mem (Subgroup.mem_inf.1 t.2).1 hs₀⟩, ?_⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (inv_mul_cancel_right _ _))
      right_inv := fun t => Subtype.ext (mul_inv_cancel_right _ _) }
  · have hx : cvMul u x.1.1 = cvMul u s₀ := congrArg Subtype.val x.2
    rw [mem_vStab, cvMul_mul, hx, cvMul_inv_cancel]
  · apply Subtype.ext
    show cvMul u (t.1 * s₀) = cvMul u s₀
    rw [cvMul_mul, mem_vStab.1 (Subgroup.mem_inf.1 t.2).2]

section Main

variable (hType : ∀ ⦃v w u z : CVert⦄, w ∈ sphereThree v → u ∈ cgraph.commonNeighbors v w →
  z ∈ cgraph.commonNeighbors v w → u ≠ z → ¬cgraph.Adj u z → z ∈ sphereThree u)

@[expose] def cnPt
    {v w : CVert} (M : RootModel v) (z : cgraph.commonNeighbors v w) : Pts :=
  M.iv ⟨z, z.2.1⟩

include hType in
theorem relIdx_cnPt
    {v w : CVert} (hw : w ∈ sphereThree v) (M : RootModel v)
    [DecidableEq (cgraph.commonNeighbors v w)]
    [DecidableRel (cgraph.induce (cgraph.commonNeighbors v w)).Adj]
    (a b : cgraph.commonNeighbors v w) :
    relIdx (cnPt M a) (cnPt M b) =
      if a = b then 0 else if (𝕄 v w).Adj a b then 2 else 4 := by
  by_cases hab : a = b
  · rw [ite_eq_left hab, hab, (relIdx_eq_zero_iff _ _).2 rfl]
  · rw [ite_eq_right hab]
    have hne : (⟨a, a.2.1⟩ : cgraph.neighborSet v) ≠ ⟨b, b.2.1⟩ := fun e =>
      hab (Subtype.ext (congrArg (fun z : cgraph.neighborSet v => (z : CVert)) e))
    have h := M.orbSize_of_mem_commonNeighbors hType hw (u := ⟨a, a.2.1⟩) (z := ⟨b, b.2.1⟩) a.2 b.2
      hne
    by_cases hadj : (cgraph.induce (cgraph.commonNeighbors v w)).Adj a b
    · rw [ite_eq_left hadj]
      exact relIdx_eq_two_of_orbSize (h.1 hadj)
    · rw [ite_eq_right hadj]
      exact relIdx_eq_four_of_orbSize (h.2 hadj)

include hType in
theorem posSemidef_levelMat_zero
    {v w : CVert} (hw : w ∈ sphereThree v) (M : RootModel v)
    [DecidableEq (cgraph.commonNeighbors v w)]
    [DecidableRel (cgraph.induce (cgraph.commonNeighbors v w)).Adj] :
    (levelMat (cgraph.induce (cgraph.commonNeighbors v w)) (1 / 8) (1 / 64)).PosSemidef :=
  posSemidef_levelMat_of_relIdx_zero _ (cnPt M) (relIdx_cnPt hType hw M)

include hType in
theorem posSemidef_levelMat_one
    {v w : CVert} (hw : w ∈ sphereThree v) (M : RootModel v)
    [DecidableEq (cgraph.commonNeighbors v w)]
    [DecidableRel (cgraph.induce (cgraph.commonNeighbors v w)).Adj] :
    (levelMat (cgraph.induce (cgraph.commonNeighbors v w)) (1 / 528) (-1 / 4096)).PosSemidef :=
  posSemidef_levelMat_of_relIdx_one _ (cnPt M) (relIdx_cnPt hType hw M)

theorem cn_regular
    {v w : CVert} (hw : w ∈ sphereThree v) [Fintype (cgraph.commonNeighbors v w)]
    [DecidableRel (cgraph.induce (cgraph.commonNeighbors v w)).Adj] :
    (cgraph.induce (cgraph.commonNeighbors v w)).IsRegularOfDegree 693 := by
  intro z
  have hval := ((native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.2.2 z
    z.2).1
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_congr (cnLocalIso v w z).toEquiv, Nat.card_coe_set_eq, hval]

theorem cn_local_isSRGWith
    {v w : CVert} (hw : w ∈ sphereThree v)
    [Fintype (cgraph.commonNeighbors v w)]
    [DecidableRel (cgraph.induce (cgraph.commonNeighbors v w)).Adj]
    (z : cgraph.commonNeighbors v w) :
    ((cgraph.induce (cgraph.commonNeighbors v w)).induce
      ((cgraph.induce (cgraph.commonNeighbors v w)).neighborSet z)).IsSRGWith 693 180 51 45 := by
  classical
  obtain ⟨ι, -⟩ := ((native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.2.2 z
    z.2).2.2.2
  have : Fintype ↥(cgraph.neighborSet z ∩ cgraph.commonNeighbors v w) := Fintype.ofFinite _
  exact isSRGWith_of_iso (cnLocalIso v w z).symm
    (isSRGWith_of_iso ι.symm native_order_three_common_neighbor_local_unitary_graph.1)

include hType in
theorem cvMul_clabel_braid
    {v w : CVert} (hw : w ∈ sphereThree v)
    {x y : CVert} (hx : x ∈ cgraph.commonNeighbors v w) (hy : y ∈ cgraph.commonNeighbors v w)
    (hne : x ≠ y) (hna : ¬cgraph.Adj x y) :
    cvMul (cvMul (cvMul x (clabelS x)) (clabelS y)) (clabelS x) = y := by
  have H : ∀ z : CVert, LocalHom z := fun z => (nonempty_localHom z).some
  have h3 : orderOf (clabel x * clabel y) = 3 :=
    ((native_order_three_label_products_and_dihedral_triples x).1 y (hType hw hx hy hne hna)).1
  have hbr := mul_mul_eq_of_orderOf_mul (clabel_mul_self H x) (clabel_mul_self H y) h3
  have hvx : cvMul v (clabelS x) = v :=
    cvMul_clabelS_of_mem H ((cgraph.mem_neighborSet _ _).2 (hx.1 : cgraph.Adj v x).symm)
  have hvy : cvMul v (clabelS y) = v :=
    cvMul_clabelS_of_mem H ((cgraph.mem_neighborSet _ _).2 (hy.1 : cgraph.Adj v y).symm)
  have hmem : cvMul (cvMul (cvMul x (clabelS x)) (clabelS y)) (clabelS x) ∈
      cgraph.neighborSet v := by
    have h1 := (cgraph_adj_cvMul v x (clabelS x)).2 hx.1
    rw [hvx] at h1
    have h2 := (cgraph_adj_cvMul v _ (clabelS y)).2 h1
    rw [hvy] at h2
    have h3' := (cgraph_adj_cvMul v _ (clabelS x)).2 h2
    rw [hvx] at h3'
    exact h3'
  refine clabel_injOn_neighborSet v hmem hy.1 ?_
  rw [← cvMul_mul, ← cvMul_mul, clabel_cvMul]
  have e : ((clabelS x * (clabelS y * clabelS x) : Shat) : Dfull) =
      clabel x * clabel y * clabel x := by
    simp only [Subgroup.coe_mul, coe_clabelS, mul_assoc]
  rw [e]
  exact conj_eq_of_braid (clabel_mul_self H x) (clabel_mul_self H y) hbr

include hType in
theorem cn_connected
    {v w : CVert} (hw : w ∈ sphereThree v) :
    (cgraph.induce (cgraph.commonNeighbors v w)).Connected := by
  classical
  have : Fintype (cgraph.commonNeighbors v w) := Fintype.ofFinite _
  have H : ∀ z : CVert, LocalHom z := fun z => (nonempty_localHom z).some
  obtain ⟨M, -⟩ := exists_rootModel v
  have hreg := cn_regular hw (v := v) (w := w)
  have heig := neg_nine_le_of_posSemidef (𝕄 v w) hreg (posSemidef_levelMat_zero hType hw M)
  have hcard := card_le_of_posSemidef (𝕄 v w) hreg (posSemidef_levelMat_one hType hw M)
  obtain ⟨hcomp, -⟩ :=
    locally_unitary_graph_least_eigenvalue_rigidity (𝕄 v w) (cn_local_isSRGWith hw) heig
  have hcc : ∀ x : cgraph.commonNeighbors v w, {y | (𝕄 v w).Reachable x y}.ncard = 3510 := by
    intro x
    have h := (hcomp ((𝕄 v w).connectedComponentMk x)).2.card
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
    rw [← h]
    congr 1
    ext y
    simp only [Set.mem_ofPred_eq, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact SimpleGraph.reachable_comm
  have hne : Nonempty (cgraph.commonNeighbors v w) := by
    obtain ⟨u, hu⟩ := (native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).1
    exact ⟨⟨u, hu⟩⟩
  refine connected_of_conj (𝕄 v w) (reachable_of_three (𝕄 v w) hcc hcard) fun x y hxy => ?_
  have hne' : (x : CVert) ≠ y := fun e => hxy (by rw [Subtype.ext e])
  have hna : ¬cgraph.Adj x y := fun h => hxy (SimpleGraph.Adj.reachable h)
  have hxv : cvMul v (clabelS x) = v := cvMul_clabelS_of_mem H
    ((cgraph.mem_neighborSet _ _).2 (x.2.1 : cgraph.Adj v x).symm)
  have hxw : cvMul w (clabelS x) = w := cvMul_clabelS_of_mem H
    ((cgraph.mem_neighborSet _ _).2 (x.2.2 : cgraph.Adj w x).symm)
  have hyv : cvMul v (clabelS y) = v := cvMul_clabelS_of_mem H
    ((cgraph.mem_neighborSet _ _).2 (y.2.1 : cgraph.Adj v y).symm)
  have hyw : cvMul w (clabelS y) = w := cvMul_clabelS_of_mem H
    ((cgraph.mem_neighborSet _ _).2 (y.2.2 : cgraph.Adj w y).symm)
  refine ⟨cnHom (clabelS x) hxv hxw, cnHom (clabelS y) hyv hyw, Subtype.ext ?_, Subtype.ext ?_,
    fun p => Subtype.ext ?_, Subtype.ext ?_⟩
  · exact cvMul_clabelS_self H x
  · exact cvMul_clabelS_self H y
  · show cvMul (cvMul p (clabelS y)) (clabelS y) = p
    rw [← cvMul_mul, clabelS_mul_self H y, cvMul_one]
  · exact cvMul_clabel_braid hType hw x.2 y.2 hne' hna

include hType in
theorem cn_isSRGWith
    {v w : CVert} (hw : w ∈ sphereThree v) [Fintype (cgraph.commonNeighbors v w)]
    [DecidableRel (cgraph.induce (cgraph.commonNeighbors v w)).Adj] :
    (cgraph.induce (cgraph.commonNeighbors v w)).IsSRGWith 3510 693 180 126 := by
  classical
  obtain ⟨M, -⟩ := exists_rootModel v
  have hreg := cn_regular hw (v := v) (w := w)
  have heig := neg_nine_le_of_posSemidef (𝕄 v w) hreg (posSemidef_levelMat_zero hType hw M)
  obtain ⟨hcomp, -⟩ :=
    locally_unitary_graph_least_eigenvalue_rigidity (𝕄 v w) (cn_local_isSRGWith hw) heig
  have hconn := cn_connected hType hw (v := v) (w := w)
  obtain ⟨x₀⟩ := hconn.nonempty
  have hmem : ∀ y : cgraph.commonNeighbors v w, y ∈ ((𝕄 v w).connectedComponentMk x₀).supp :=
    fun y => (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
      (SimpleGraph.ConnectedComponent.sound (hconn.preconnected y x₀))
  let e : (𝕄 v w).induce ((𝕄 v w).connectedComponentMk x₀).supp ≃g (𝕄 v w) :=
    { toFun := fun y => y.1
      invFun := fun y => ⟨y, hmem y⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  convert isSRGWith_of_iso e (hcomp _).2

include hType in
theorem ncard_commonNeighbors_eq_3510
    {v w : CVert} (hw : w ∈ sphereThree v) :
    (cgraph.commonNeighbors v w).ncard = 3510 := by
  classical
  have : Fintype (cgraph.commonNeighbors v w) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (cn_isSRGWith hType hw).card

include hType in
theorem ncard_sphereThree_eq
    (v : CVert) : (sphereThree v).ncard = 2370830336 := by
  have h := ncard_sphereThree_mul exists_rootModel natCard_neighborSet_cv0_eq v
    (μ := 3510) fun w hw => ncard_commonNeighbors_eq_3510 hType hw
  omega

include hType in
theorem natCard_pairStab_eq
    {v w : CVert} (hw : w ∈ sphereThree v) :
    Nat.card (vStab v ⊓ vStab w : Subgroup Shat) = 129123503308800 := by
  have hU := native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw
  obtain ⟨u, hu⟩ := hU.1
  have horb : {x | ∃ s ∈ vStab v ⊓ vStab w, cvMul u s = x} = cgraph.commonNeighbors v w := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h1 := (cgraph_adj_cvMul v u s).2 hu.1
      have h2 := (cgraph_adj_cvMul w u s).2 hu.2
      rw [mem_vStab.1 (Subgroup.mem_inf.1 hs).1] at h1
      rw [mem_vStab.1 (Subgroup.mem_inf.1 hs).2] at h2
      exact ⟨h1, h2⟩
    · intro hx
      exact hU.2.2.2.1 u hu x hx
  rw [natCard_subgroup_eq_mul _ u, horb, ncard_commonNeighbors_eq_3510 hType hw,
    (hU.2.2.2.2 u hu).2.2.1]

end Main

end CFSG.Monster.B.TwoA.Amalgam
