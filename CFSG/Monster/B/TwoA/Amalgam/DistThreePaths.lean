module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeDefs
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsPres
public import CFSG.Monster.B.TwoA.Amalgam.TypeFour
public import CFSG.Monster.B.TwoA.Amalgam.TriangleCore
public import CFSG.Monster.B.TwoA.Amalgam.Exact3510Core
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoInst
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
public import Certificates.Certificate3079
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16028
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16040
public import Certificates.Certificate16951
public import Certificates.Certificate3027
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import CFSG.Monster.B.E6.StdF4Fiber
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsQuot

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

private theorem mem_sphereFour_symm
    {v w : CVert} : w ∈ sphereFour v ↔ v ∈ sphereFour w := by
  have hord : ∀ a b : CVert, LabelFour a b → LabelFour b a := by
    intro a b h
    have e : lblOrd b a = lblOrd a b := by
      rw [lblOrd, lblOrd, ← MulEquiv.orderOf_eq (MulAut.conj (clabel a)) (clabel b * clabel a),
        MulAut.conj_apply]
      congr 1
      group
    rw [LabelFour, e]
    exact h
  exact ⟨fun h => ⟨SimpleGraph.dist_comm.trans h.1, hord v w h.2⟩,
    fun h => ⟨SimpleGraph.dist_comm.trans h.1, hord w v h.2⟩⟩

theorem exists_adj_dist_two_of_dist_three
    {v u : CVert} (h : cgraph.dist v u = 3) :
    ∃ w, cgraph.Adj w u ∧ cgraph.dist v w = 2 := by
  obtain ⟨p, hp⟩ := cgraph_connected.exists_walk_length_eq_dist v u
  rw [h] at hp
  have hadj := p.adj_getVert_succ (i := 2) (by omega)
  rw [show 2 + 1 = p.length by omega, SimpleGraph.Walk.getVert_length] at hadj
  refine ⟨p.getVert 2, hadj, le_antisymm ?_ ?_⟩
  · have h1 := SimpleGraph.dist_le (p.take 2)
    rw [SimpleGraph.Walk.take_length, hp] at h1
    exact h1
  · have h1 : cgraph.dist v u ≤ cgraph.dist v (p.getVert 2) + cgraph.dist (p.getVert 2) u :=
      cgraph_connected.dist_triangle
    rw [h, SimpleGraph.dist_eq_one_iff_adj.2 hadj] at h1
    omega

theorem xSet_nonempty_of
    (hT3 : ∀ ⦃v w : CVert⦄, w ∈ sphereThree v → ∀ u, cgraph.Adj w u → cgraph.dist v u ≠ 3)
    {v u : CVert} (hu : u ∈ sphereDistThree v) : (xSet v u).Nonempty := by
  obtain ⟨w, hwu, hvw⟩ := exists_adj_dist_two_of_dist_three hu
  have hw : w ∈ sphereThree v ∪ sphereFour v := by
    rw [← setOf_dist_eq_two_eq_union exists_rootModel]
    exact hvw
  rcases hw with h3 | h4
  · exact absurd hu (hT3 h3 u hwu)
  · exact ⟨w, (cgraph.adj_comm _ _).1 hwu, h4⟩

theorem pairStabOrbit_eq_setOf
    (a b c : CVert) :
    pairStabOrbit a b c = {x | ∃ s ∈ vStab a ⊓ vStab b, cvMul c s = x} := by
  ext x
  constructor
  · rintro ⟨s, ha, hb, rfl⟩
    exact ⟨s, Subgroup.mem_inf.2 ⟨ha, hb⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, (Subgroup.mem_inf.1 hs).1, (Subgroup.mem_inf.1 hs).2, rfl⟩

theorem mem_vStab_cvMul_iff
    {x : CVert} {s y : Shat} :
    y ∈ vStab (cvMul x s) ↔ s * y * s⁻¹ ∈ vStab x := by
  rw [mem_vStab, mem_vStab, ← cvMul_mul, cvMul_mul x (s * y) s⁻¹]
  constructor
  · intro h
    rw [h, cvMul_inv_cancel]
  · intro h
    have h1 : cvMul (cvMul (cvMul x (s * y)) s⁻¹) s = cvMul x s := by rw [h]
    rwa [cvMul_inv_cancel'] at h1

theorem natCard_pairStab_cvMul
    (a b : CVert) (s : Shat) :
    Nat.card ↥(vStab (cvMul a s) ⊓ vStab (cvMul b s)) = Nat.card ↥(vStab a ⊓ vStab b) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨s * y * s⁻¹, mem_vStab_cvMul_iff.1 (Subgroup.mem_inf.1 y.2).1,
        mem_vStab_cvMul_iff.1 (Subgroup.mem_inf.1 y.2).2⟩
      invFun := fun z => ⟨s⁻¹ * z * s, mem_vStab_cvMul_iff.2 (by
          rw [show s * (s⁻¹ * (z : Shat) * s) * s⁻¹ = z by group]
          exact (Subgroup.mem_inf.1 z.2).1), mem_vStab_cvMul_iff.2 (by
          rw [show s * (s⁻¹ * (z : Shat) * s) * s⁻¹ = z by group]
          exact (Subgroup.mem_inf.1 z.2).2)⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun z => Subtype.ext (by simp only; group) }

theorem natCard_pairStab_base
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) :
    Nat.card ↥(vStab cv0 ⊓ vStab (cvOf (jhatS k))) = Nat.card (Q4 k) := by
  have hiff := (native_type_four_pair_stabilizer_parabolic_projection k hk0 hk).1
  refine Nat.card_congr
    { toFun := fun y => ⟨((y : Shat) : Dfull), (hiff y).1 ⟨(Subgroup.mem_inf.1 y.2).1,
        (Subgroup.mem_inf.1 y.2).2⟩⟩
      invFun := fun z => ⟨⟨z, Jhat_le_Shat (Q4_le_Jhat z.2)⟩, Subgroup.mem_inf.2
        ((hiff ⟨z, Jhat_le_Shat (Q4_le_Jhat z.2)⟩).2 z.2)⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }

theorem natCard_pairStab_sphereFour
    {v w : CVert} (hw : w ∈ sphereFour v) :
    Nat.card ↥(vStab v ⊓ vStab w) = 27396522639360 := by
  obtain ⟨s, k, hv, hwk, hk0, hk, -⟩ := exists_base_presentation hw
  rw [← hv, ← hwk, natCard_pairStab_cvMul, natCard_pairStab_base hk0 hk, natCard_Q4 hk0 hk]
  norm_num

section Main

variable
  (hT3 : ∀ ⦃v w : CVert⦄, w ∈ sphereThree v → ∀ u, cgraph.Adj w u → cgraph.dist v u ≠ 3)
  (hT4 : ∀ ⦃v w : CVert⦄, w ∈ sphereFour v → ∀ u ∈ cgraph.neighborSet v ∩ sphereDistThree w,
    pairStabOrbit v w u = cgraph.neighborSet v ∩ sphereDistThree w ∧
      (cgraph.neighborSet v ∩ sphereDistThree w).ncard = 8064)

theorem cvMul_mem_neighborSet_inter
    {v w u : CVert} {s : Shat} (hv : cvMul v s = v)
    (hu : u ∈ cgraph.neighborSet w ∩ sphereDistThree v) :
    cvMul u s ∈ cgraph.neighborSet (cvMul w s) ∩ sphereDistThree v := by
  refine ⟨(cgraph_adj_cvMul w u s).2 hu.1, ?_⟩
  have h := sphereDistThree_cvMul hu.2 s
  rwa [hv] at h

theorem neighborSet_inter_cvMul
    {v w : CVert} {s : Shat} (hv : cvMul v s = v) :
    cgraph.neighborSet (cvMul w s) ∩ sphereDistThree v =
      (fun x => cvMul x s) '' (cgraph.neighborSet w ∩ sphereDistThree v) := by
  have hv' : cvMul v s⁻¹ = v := by
    conv_lhs => rw [← hv]
    exact cvMul_inv_cancel v s
  ext x
  constructor
  · intro hx
    refine ⟨cvMul x s⁻¹, ?_, cvMul_inv_cancel' x s⟩
    have h := cvMul_mem_neighborSet_inter hv' hx
    rwa [cvMul_inv_cancel] at h
  · rintro ⟨y, hy, rfl⟩
    exact cvMul_mem_neighborSet_inter hv hy

include hT3 in
theorem exists_sphereFour_adj_sphereDistThree
    (hne : ∀ v : CVert, (sphereDistThree v).Nonempty)
    (v : CVert) : ∃ w ∈ sphereFour v, (cgraph.neighborSet w ∩ sphereDistThree v).Nonempty := by
  obtain ⟨u, hu⟩ := hne v
  obtain ⟨w, hwu, hw⟩ := xSet_nonempty_of hT3 hu
  exact ⟨w, hw, u, (cgraph.adj_comm _ _).1 hwu, hu⟩

include hT3 hT4 in
theorem ncard_neighborSet_inter_sphereDistThree
    (hne : ∀ v : CVert, (sphereDistThree v).Nonempty) {v w : CVert} (hw : w ∈ sphereFour v) :
    (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 8064 ∧
      ∀ u ∈ cgraph.neighborSet w ∩ sphereDistThree v,
        pairStabOrbit w v u = cgraph.neighborSet w ∩ sphereDistThree v := by
  obtain ⟨w₀, hw₀, u₀, hu₀⟩ := exists_sphereFour_adj_sphereDistThree hT3 hne v
  have hw₀' := mem_sphereFour_symm.1 hw₀
  have horb : w ∈ vStabOrbit v w₀ := by
    rw [vStabOrbit_eq_sphereFour exists_rootModel hw₀]
    exact hw
  obtain ⟨s, hsv, rfl⟩ := horb
  have hcard : (cgraph.neighborSet (cvMul w₀ s) ∩ sphereDistThree v).ncard = 8064 := by
    rw [neighborSet_inter_cvMul hsv, Set.ncard_image_of_injective _ (cvMul_injective s)]
    exact (hT4 hw₀' u₀ hu₀).2
  refine ⟨hcard, fun u hu => (hT4 (mem_sphereFour_symm.1 hw) u hu).1⟩

include hT3 hT4 in
theorem exists_smul_eq_sphereDistThree
    (hne : ∀ v : CVert, (sphereDistThree v).Nonempty)
    {v u u' : CVert} (hu : u ∈ sphereDistThree v) (hu' : u' ∈ sphereDistThree v) :
    ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u' := by
  obtain ⟨w, hwu, hw⟩ := xSet_nonempty_of hT3 hu
  obtain ⟨w', hwu', hw'⟩ := xSet_nonempty_of hT3 hu'
  have horb : w' ∈ vStabOrbit v w := by
    rw [vStabOrbit_eq_sphereFour exists_rootModel hw]
    exact hw'
  obtain ⟨s, hsv, rfl⟩ := horb
  have hus : cvMul u s ∈ cgraph.neighborSet (cvMul w s) ∩ sphereDistThree v :=
    cvMul_mem_neighborSet_inter hsv ⟨(cgraph.adj_comm _ _).1 hwu, hu⟩
  have h := (ncard_neighborSet_inter_sphereDistThree hT3 hT4 hne hw').2 _ hus
  have hu'm : u' ∈ pairStabOrbit (cvMul w s) v (cvMul u s) := by
    rw [h]
    exact ⟨(cgraph.adj_comm _ _).1 hwu', hu'⟩
  obtain ⟨q, -, hqv, hqu⟩ := hu'm
  exact ⟨s * q, by rw [cvMul_mul, hsv, hqv], by rw [cvMul_mul, hqu]⟩

include hT3 hT4 in
theorem exists_smul_eq_xSet
    (hne : ∀ v : CVert, (sphereDistThree v).Nonempty) {v u w w' : CVert}
    (hu : u ∈ sphereDistThree v) (hw : w ∈ xSet v u) (hw' : w' ∈ xSet v u) :
    ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w' := by
  have horb : w' ∈ vStabOrbit v w := by
    rw [vStabOrbit_eq_sphereFour exists_rootModel hw.2]
    exact hw'.2
  obtain ⟨s, hsv, hsw⟩ := horb
  have hus : cvMul u s ∈ cgraph.neighborSet (cvMul w s) ∩ sphereDistThree v :=
    cvMul_mem_neighborSet_inter hsv ⟨(cgraph.adj_comm _ _).1 hw.1, hu⟩
  rw [hsw] at hus
  have h := (ncard_neighborSet_inter_sphereDistThree hT3 hT4 hne hw'.2).2 _ hus
  have hum : u ∈ pairStabOrbit w' v (cvMul u s) := by
    rw [h]
    exact ⟨(cgraph.adj_comm _ _).1 hw'.1, hu⟩
  obtain ⟨q, hqw, hqv, hqu⟩ := hum
  exact ⟨s * q, by rw [cvMul_mul, hsv, hqv], by rw [cvMul_mul, hqu],
    by rw [cvMul_mul, hsw, hqw]⟩

include hT3 hT4 in
theorem natCard_stab_xSet
    (hne : ∀ v : CVert, (sphereDistThree v).Nonempty) {v u w : CVert}
    (hu : u ∈ sphereDistThree v) (hw : w ∈ xSet v u) :
    Nat.card ↥(vStab v ⊓ vStab u ⊓ vStab w) = 3397386240 := by
  have huw : u ∈ cgraph.neighborSet w ∩ sphereDistThree v := ⟨(cgraph.adj_comm _ _).1 hw.1, hu⟩
  have horb := (ncard_neighborSet_inter_sphereDistThree hT3 hT4 hne hw.2)
  have hK := natCard_subgroup_eq_mul (vStab w ⊓ vStab v) u
  rw [← pairStabOrbit_eq_setOf, horb.2 u huw, horb.1, inf_comm,
    natCard_pairStab_sphereFour hw.2] at hK
  have e : vStab v ⊓ vStab u ⊓ vStab w = vStab v ⊓ vStab w ⊓ vStab u := by
    rw [inf_assoc, inf_comm (vStab u), ← inf_assoc]
  rw [e]
  omega

end Main

theorem native_distance_three_single_orbit_and_8064_paths
    (hne : ∀ v : CVert, (sphereDistThree v).Nonempty)
    (hT3 : ∀ ⦃v w : CVert⦄, w ∈ sphereThree v → ∀ u, cgraph.Adj w u → cgraph.dist v u ≠ 3)
    (hT4 : ∀ ⦃v w : CVert⦄, w ∈ sphereFour v → ∀ u ∈ cgraph.neighborSet v ∩ sphereDistThree w,
      pairStabOrbit v w u = cgraph.neighborSet v ∩ sphereDistThree w ∧
        (cgraph.neighborSet v ∩ sphereDistThree w).ncard = 8064) :
    (∀ v u u' : CVert, u ∈ sphereDistThree v → u' ∈ sphereDistThree v →
      ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u') ∧
    (∀ v w : CVert, w ∈ sphereFour v →
      (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 8064 ∧
        ∀ u ∈ cgraph.neighborSet w ∩ sphereDistThree v,
          pairStabOrbit w v u = cgraph.neighborSet w ∩ sphereDistThree v) ∧
    (∀ v w : CVert, w ∈ sphereThree v → Disjoint (cgraph.neighborSet w) (sphereDistThree v)) ∧
    (∀ v u : CVert, u ∈ sphereDistThree v → (xSet v u).Nonempty ∧
      (∀ w ∈ xSet v u, ∀ w' ∈ xSet v u,
        ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w') ∧
      ∀ w ∈ xSet v u, Nat.card ↥(vStab v ⊓ vStab u ⊓ vStab w) = 3397386240) ∧
    (∀ v u : CVert, u ∈ sphereDistThree v → (xSet u v).Nonempty ∧
      (∀ w ∈ xSet u v, ∀ w' ∈ xSet u v,
        ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w') ∧
      ∀ w ∈ xSet u v, Nat.card ↥(vStab v ⊓ vStab u ⊓ vStab w) = 3397386240) := by
  have hpart : ∀ v u : CVert, u ∈ sphereDistThree v → (xSet v u).Nonempty ∧
      (∀ w ∈ xSet v u, ∀ w' ∈ xSet v u,
        ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w') ∧
      ∀ w ∈ xSet v u, Nat.card ↥(vStab v ⊓ vStab u ⊓ vStab w) = 3397386240 :=
    fun v u hu => ⟨xSet_nonempty_of hT3 hu,
      fun w hw w' hw' => exists_smul_eq_xSet hT3 hT4 hne hu hw hw',
      fun w hw => natCard_stab_xSet hT3 hT4 hne hu hw⟩
  refine ⟨fun v u u' hu hu' => exists_smul_eq_sphereDistThree hT3 hT4 hne hu hu',
    fun v w hw => ncard_neighborSet_inter_sphereDistThree hT3 hT4 hne hw,
    fun v w hw => Set.disjoint_left.2 fun u hwu hu => hT3 hw u hwu hu, hpart,
    fun v u hu => ?_⟩
  have huv : v ∈ sphereDistThree u := by
    rw [mem_sphereDistThree, SimpleGraph.dist_comm]
    exact hu
  obtain ⟨h1, h2, h3⟩ := hpart u v huv
  refine ⟨h1, fun w hw w' hw' => ?_, fun w hw => ?_⟩
  · obtain ⟨g, hgu, hgv, hgw⟩ := h2 w hw w' hw'
    exact ⟨g, hgv, hgu, hgw⟩
  · rw [show vStab v ⊓ vStab u = vStab u ⊓ vStab v from inf_comm _ _]
    exact h3 w hw

end CFSG.Monster.B.TwoA.Amalgam
