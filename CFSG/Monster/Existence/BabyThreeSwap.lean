module

public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyThreeSwapIndex
public import CFSG.Monster.Existence.BabyThreeSwapScheme
public import CFSG.Monster.GMS.DoubleCoverOf
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeOuterFinal
public import CFSG.Monster.B.TwoA.Amalgam.RankFiveMatrix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.GMS CFSG.Blueprint

theorem mem_rankFiveOrbit_comm
    (v w : CVert) (i : Fin 5) :
    w ∈ rankFiveOrbit v i ↔ v ∈ rankFiveOrbit w i := by
  fin_cases i
  · exact ⟨fun h => (show w = v from h).symm ▸ rfl, fun h => (show v = w from h).symm ▸ rfl⟩
  · exact ⟨fun h => cgraph.adj_symm h, fun h => cgraph.adj_symm h⟩
  · exact mem_sphereThree_comm
  · exact mem_sphereFour_comm
  · exact ⟨fun h => show cgraph.dist w v = 3 by rw [SimpleGraph.dist_comm]; exact h,
      fun h => show cgraph.dist v w = 3 by rw [SimpleGraph.dist_comm]; exact h⟩

theorem ncard_sphereDistThree_inter_of_mem_sphereThree
    {v w : CVert} (hw : w ∈ sphereThree v) :
    (sphereDistThree v ∩ sphereDistThree w).ncard = 61776 := by
  have : Finite CVert := short_F4_involution_coset_graph_data.1
  obtain ⟨hpart, -, hmat⟩ := native_rank_five_exact_neighbor_matrix_of_ambient ambientRootOrbitsHyp
  exact ncard_inter_four_of_neighbour_matrix rankFiveOrbit (fun _ => rfl)
    mem_rankFiveOrbit_comm hpart (fun v' i j w' hw' => hmat v' i j w' hw') v w hw

theorem exists_mem_sphereDistThree_inter
    {v w : CVert} (hw : w ∈ sphereThree v) :
    ∃ u, u ∈ sphereDistThree v ∧ u ∈ sphereDistThree w := by
  obtain ⟨u, hu⟩ := Set.nonempty_of_ncard_ne_zero
    (by rw [ncard_sphereDistThree_inter_of_mem_sphereThree hw]; norm_num)
  exact ⟨u, hu.1, hu.2⟩

theorem mem_centralizer_iff_mem_vStab
    {r : NativeSporadic.B} {v : CVert}
    (hv : clabelS v = babyToShat r) (x : NativeSporadic.B) :
    x ∈ Subgroup.centralizer ({r} : Set NativeSporadic.B) ↔ babyToShat x ∈ vStab v := by
  have hcoe : clabel v = ((babyToShat r : Shat) : Dfull) := by
    rw [← coe_clabelS, hv]
  constructor
  · intro h
    have h1 : babyToShat r * babyToShat x = babyToShat x * babyToShat r := by
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 h]
    refine mem_vStab.2 ((centralizerInput_B v (babyToShat x)).1 ?_)
    rw [hcoe]
    exact congrArg Subtype.val h1.symm
  · intro h
    have h1 := (centralizerInput_B v (babyToShat x)).2 (mem_vStab.1 h)
    rw [hcoe] at h1
    have h2 : babyToShat x * babyToShat r = babyToShat r * babyToShat x := Subtype.ext h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply babyToShat.injective
    rw [map_mul, map_mul]
    exact h2

theorem exists_swap_of_mem_sphereDistThree
    {r t : NativeSporadic.B} {v u : CVert}
    (hv : clabelS v = babyToShat r) (hu : u ∈ sphereDistThree v) (ht : clabelS u = babyToShat t) :
    t ∈ Subgroup.centralizer ({r} : Set NativeSporadic.B) ∧
      ∀ K : Subgroup NativeSporadic.B, K.relIndex (Subgroup.centralizer {r}) = 2 → t ∉ K := by
  obtain ⟨hmem, hout, -⟩ := native_distance_three_label_is_outer_local_involution_final hu
  have htH : t ∈ Subgroup.centralizer ({r} : Set NativeSporadic.B) :=
    (mem_centralizer_iff_mem_vStab hv t).2 (by rw [← ht]; exact hmem)
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  refine ⟨htH, fun K hK => ?_⟩
  with_reducible_and_instances
    exact not_mem_of_relIndex_eq_two babyToShat (Subgroup.centralizer {r}) (vStab v)
      (mem_centralizer_iff_mem_vStab hv) (index_commutator_vStab hs) htH
      (fun y hy => hout y (hy.trans ht.symm)) hK

theorem mem_sphereThree_of_orderOf_eq_three
    {r s : NativeSporadic.B} {v w : CVert}
    (hr : orderOf r = 2) (hv : clabelS v = babyToShat r) (hw : clabelS w = babyToShat s)
    (h3 : orderOf (r * s) = 3) : w ∈ sphereThree v := by
  have hprod : orderOf (clabelS v * clabelS w) = 3 := by
    rw [hv, hw, ← map_mul, MulEquiv.orderOf_eq]
    exact h3
  have hord : ∀ {a b : Shat}, IsConj a b → orderOf a = orderOf b := fun h => by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  rcases labelSphere_cover v w with rfl | ⟨k, hk⟩
  · have hr2 : r * r = 1 := by
      rw [← pow_two]
      have := pow_orderOf_eq_one r
      rwa [hr] at this
    have h1 : clabelS w * clabelS w = 1 := by
      rw [hv, ← map_mul, hr2, map_one]
    rw [h1, orderOf_one] at hprod
    omega
  · match k, hk with
    | 0, hk =>
      have h0 := hord (isConj_clabelS_mul_of_mem_zero hk)
      rw [hprod, ← babyToShat_babyRep_zero, MulEquiv.orderOf_eq,
        orderOf_babyRep (by norm_num)] at h0
      omega
    | 1, hk =>
      have h0 := hord (isConj_clabelS_mul_of_mem_one hk)
      rw [hprod, ← babyToShat_babyRep, MulEquiv.orderOf_eq, orderOf_babyRep (by norm_num)] at h0
      omega
    | 2, hk => exact hk
    | 3, hk =>
      have h0 := orderOf_clabelS_mul_of_mem_three hk
      omega

theorem babyThreeSwap_of_ne_rep_three
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0) :
    BabyThreeSwap := by
  intro r s hr hs hrs
  have hcls : ∀ t : NativeSporadic.B, BabyInv 0 t → IsConj t (babyRep 1) := fun t ht =>
    isConj_babyRep_one_of_babyInv_zero h3 ht
  obtain ⟨v, hv⟩ := (babyInv_zero_iff_clabelS hcls r).1 hr
  obtain ⟨w, hw⟩ := (babyInv_zero_iff_clabelS hcls s).1 hs
  obtain ⟨u, huv, huw⟩ := exists_mem_sphereDistThree_inter
    (mem_sphereThree_of_orderOf_eq_three hr.1 hv hw hrs)
  obtain ⟨t, ht⟩ : ∃ t, clabelS u = babyToShat t := ⟨babyToShat.symm (clabelS u), by simp⟩
  obtain ⟨h1, h1'⟩ := exists_swap_of_mem_sphereDistThree hv huv ht
  obtain ⟨h2, h2'⟩ := exists_swap_of_mem_sphereDistThree hw huw ht
  exact ⟨t, Subgroup.mem_inf.2 ⟨h1, h2⟩, fun K _ hK => h1' K hK, fun K _ hK => h2' K hK⟩

theorem babyThreeSwap_of
    (hT3 : BabyTableIII) : BabyThreeSwap :=
  babyThreeSwap_of_ne_rep_three (natCard_centralizer_rep_three_ne_of_babyTableIII hT3)

end CFSG.Monster.Existence
