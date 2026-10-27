module

public import CFSG.Monster.B.CTIB.DistThreeProductCore
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeSplit

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

section Group

variable {G : Type*} [Group G]

theorem commute_of_mul_self {d a : G} (hd : d * d = 1) (ha : a * a = 1)
    (hda : d * a * (d * a) = 1) : Commute d a := by
  have h1 : d * a = (d * a)⁻¹ := eq_inv_of_mul_eq_one_left hda
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_left ha, inv_eq_of_mul_eq_one_left hd] at h1
  exact h1

theorem mul_eq_mul_mul {c e a : G} (hc : c * c = 1) (hce : Commute c e) :
    e * a = c * e * (c * a) := by
  calc e * a = c * c * e * a := by rw [hc, one_mul]
    _ = c * (c * e) * a := by group
    _ = c * (e * c) * a := by rw [hce.eq]
    _ = c * e * (c * a) := by group

theorem sq_mul_of_commute {d p : G} (hdp : Commute d p) (hd : d * d = 1) :
    (d * p) ^ 2 = p ^ 2 := by
  rw [hdp.mul_pow, sq d, hd, one_mul]

end Group

theorem dist_le_two_of_adj_adj
    {v x w : CVert} (h1 : cgraph.Adj v x) (h2 : cgraph.Adj x w) :
    cgraph.dist v w ≤ 2 := by
  have h := cgraph_connected.dist_triangle (u := v) (v := x) (w := w)
  rw [SimpleGraph.dist_eq_one_iff_adj.2 h1, SimpleGraph.dist_eq_one_iff_adj.2 h2] at h
  exact h

theorem false_of_adj_of_mul_eq
    (hL : DistThreeLabelsInput) (hO : DistThreeOuterInput)
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) {v w x y : CVert}
    (hvw : cgraph.dist v w = 3) (hx : cgraph.Adj v x) (hxw : Commute (clabelS w) (clabelS x))
    (hy : clabelS y = clabelS v * clabelS w * clabelS x) : False := by
  have hdiam := dist_le_three_of_inputs hL hO hP hT
  have hinj := clabel_injective_of_inputs hL hO hP hT
  have hwv : cgraph.dist w v = 3 := by rw [SimpleGraph.dist_comm]; exact hvw
  have hN3 := (native_distance_three_pair_two_local_root_orbits hL hO hP hT hwv).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hev, ρ, iu, hcomp, hρe, -, hfour, hroot⟩ := hN3
  have hex : cvMul x (clabelS w) = x := (commute_clabelS_iff hinj x (clabelS w)).1 hxw
  have hx4 : x ∉ sphereFour w := fun h => ((hfour ⟨x, hx⟩).1 h) hex
  have hj := (hroot ⟨x, hx⟩).1 hx4
  obtain ⟨j, hj, hjx⟩ := hj
  have hxv : clabelS x ∈ vStab v :=
    (commute_clabelS_iff hinj v (clabelS x)).1 (commute_clabelS_of_adj hx).symm
  have hρa : ρ ⟨clabelS x, hxv⟩ = SemidirectProduct.inl (iu ⟨x, hx⟩ : stdGroup) :=
    hcomp.2.2.2.2 ⟨x, hx⟩ ⟨clabelS x, hxv⟩ rfl
  have hyv : clabelS y ∈ vStab v := by
    rw [hy]
    exact (vStab v).mul_mem ((vStab v).mul_mem (clabelS_mem_vStab_self v) hev) hxv
  have hb : (⟨clabelS y, hyv⟩ : vStab v) = cStab v * ⟨clabelS w, hev⟩ * ⟨clabelS x, hxv⟩ :=
    Subtype.ext hy
  have hρc : ρ (cStab v) = 1 := (hcomp.2.1 _).2 (Subgroup.mem_zpowers _)
  have hρb : ρ ⟨clabelS y, hyv⟩ =
      betaStarElt * SemidirectProduct.inl (j * rootInv * j⁻¹) := by
    calc ρ ⟨clabelS y, hyv⟩ = ρ (cStab v * ⟨clabelS w, hev⟩ * ⟨clabelS x, hxv⟩) := congrArg ρ hb
      _ = ρ (cStab v) * ρ ⟨clabelS w, hev⟩ * ρ ⟨clabelS x, hxv⟩ :=
          (map_mul ρ _ _).trans (congrArg (· * ρ ⟨clabelS x, hxv⟩) (map_mul ρ _ _))
      _ = 1 * betaStarElt * SemidirectProduct.inl (iu ⟨x, hx⟩ : stdGroup) :=
          congrArg₂ (· * ·) (congrArg₂ (· * ·) hρc hρe) hρa
      _ = betaStarElt * SemidirectProduct.inl (j * rootInv * j⁻¹) := by rw [one_mul, hjx]
  have hcj : Commute (SemidirectProduct.inl j : GStar) betaStarElt :=
    (mem_groupJ_iff_commute j).1 (Subgroup.mem_subgroupOf.1 hj)
  have hct : Commute (SemidirectProduct.inl rootInv : GStar) betaStarElt :=
    (mem_groupJ_iff_commute rootInv).1 (Subgroup.mem_subgroupOf.1 rootInv_mem_groupJ)
  have hconj : ρ ⟨clabelS y, hyv⟩ = SemidirectProduct.inl j *
      CFSG.Monster.B.E6.FieldInvF4.tStar * (SemidirectProduct.inl j)⁻¹ := by
    rw [hρb, map_mul, map_mul, map_inv]
    have hc1 : Commute (SemidirectProduct.inl j * SemidirectProduct.inl rootInv *
        (SemidirectProduct.inl j)⁻¹ : GStar) betaStarElt := (hcj.mul_left hct).mul_left hcj.inv_left
    calc betaStarElt * (SemidirectProduct.inl j * SemidirectProduct.inl rootInv *
          (SemidirectProduct.inl j)⁻¹) = SemidirectProduct.inl j * SemidirectProduct.inl rootInv *
          (SemidirectProduct.inl j)⁻¹ * betaStarElt := hc1.symm.eq
      _ = SemidirectProduct.inl j * SemidirectProduct.inl rootInv *
          ((SemidirectProduct.inl j)⁻¹ * betaStarElt) := by rw [mul_assoc]
      _ = SemidirectProduct.inl j * SemidirectProduct.inl rootInv *
          (betaStarElt * (SemidirectProduct.inl j)⁻¹) := by rw [hcj.inv_left.eq]
      _ = SemidirectProduct.inl j * CFSG.Monster.B.E6.FieldInvF4.tStar *
          (SemidirectProduct.inl j)⁻¹ := by
        rw [CFSG.Monster.B.E6.FieldInvF4.tStar, rootStar]
        group
  have hle := natCard_centralizer_le (ker_eq_zpowers_cStab hcomp.2.1) ⟨clabelS y, hyv⟩
  have hcard : Nat.card (Subgroup.centralizer {ρ ⟨clabelS y, hyv⟩}) = 95126814720 := by
    rw [hconj]
    exact (CFSG.Monster.B.E6.FieldInvF4.card_centralizer_conj _ _).trans
      CFSG.Monster.B.E6.FieldInvF4.card_centralizer_tStar
  have hr : (ρ ⟨clabelS y, hyv⟩).right ≠ 1 := by
    rw [hρb, SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one]
    exact betaStarElt_right_ne_one
  have hyne : v ≠ y := by
    intro h
    apply hr
    have e : (⟨clabelS y, hyv⟩ : vStab v) = cStab v :=
      Subtype.ext (show clabelS y = clabelS v by rw [h])
    rw [e, hρc]
    rfl
  rcases adj_or_dist_three_of_commute hdiam hyne (commute_clabelS_of_mem_vStab hyv).symm with
    hadj | h3
  · exact hr (by rw [hcomp.2.2.2.2 ⟨y, hadj⟩ ⟨clabelS y, hyv⟩ rfl]; rfl)
  · have hI := native_distance_three_canonical_F4_centralizer_image hL hO hP hT h3
    obtain ⟨s, -, hs, -, -, -, -, hC, -⟩ := hI
    have hs' : s = ⟨clabelS y, hyv⟩ := Subtype.ext hs
    rw [hs'] at hC
    omega

theorem adj_of_dist_three_mul
    (hO : DistThreeOuterInput)
    (hdiam : ∀ v w : CVert, cgraph.dist v w ≤ 3) {v w x y : CVert} (hvw : cgraph.dist v w = 3)
    (hvx : cgraph.dist v x = 3) (hwv : clabelS w ∈ vStab v) (hxv : clabelS x ∈ vStab v)
    (hy : clabelS y = clabelS v * clabelS w * clabelS x) (hyne : y ≠ v) : cgraph.Adj v y := by
  have hc := exists_isCompatLocal v
  obtain ⟨ρ, iv, hc⟩ := hc
  have h1 : (ρ ⟨clabelS w, hwv⟩).right ≠ 1 := hO v w hvw ρ iv hc _ rfl
  have h2 : (ρ ⟨clabelS x, hxv⟩).right ≠ 1 := hO v x hvx ρ iv hc _ rfl
  have hyv : clabelS y ∈ vStab v := by
    rw [hy]
    exact (vStab v).mul_mem ((vStab v).mul_mem (clabelS_mem_vStab_self v) hwv) hxv
  have hb : (⟨clabelS y, hyv⟩ : vStab v) = cStab v * ⟨clabelS w, hwv⟩ * ⟨clabelS x, hxv⟩ :=
    Subtype.ext hy
  have hρc : ρ (cStab v) = 1 := (hc.2.1 _).2 (Subgroup.mem_zpowers _)
  have hr : (ρ ⟨clabelS y, hyv⟩).right = 1 := by
    have h3 : ρ ⟨clabelS y, hyv⟩ = ρ (cStab v) * (ρ ⟨clabelS w, hwv⟩ * ρ ⟨clabelS x, hxv⟩) :=
      (congrArg ρ hb).trans ((map_mul ρ _ _).trans ((congrArg (· * ρ ⟨clabelS x, hxv⟩)
        (map_mul ρ _ _)).trans (mul_assoc _ _ _)))
    calc (ρ ⟨clabelS y, hyv⟩).right =
          (ρ (cStab v) * (ρ ⟨clabelS w, hwv⟩ * ρ ⟨clabelS x, hxv⟩)).right :=
          congrArg SemidirectProduct.right h3
      _ = (ρ (cStab v)).right * ((ρ ⟨clabelS w, hwv⟩).right * (ρ ⟨clabelS x, hxv⟩).right) := rfl
      _ = 1 * ((ρ ⟨clabelS w, hwv⟩).right * (ρ ⟨clabelS x, hxv⟩).right) :=
          congrArg (· * _) (congrArg SemidirectProduct.right hρc)
      _ = 1 := by rw [one_mul]; exact betaGroup_mul_eq_one h1 h2
  rcases adj_or_dist_three_of_commute hdiam (Ne.symm hyne)
    (commute_clabelS_of_mem_vStab hyv).symm with h | h
  · exact h
  · exact absurd hr (hO v y h ρ iv hc _ rfl)

theorem eq_or_eq_of_clabelS_eq_mul
    (hL : DistThreeLabelsInput) (hO : DistThreeOuterInput)
    (hP : DistThreePathInput) (hT : TypeThreeBoundInput) {v w x y : CVert}
    (hvw : cgraph.dist v w = 3) (hy : clabelS y = clabelS v * clabelS w * clabelS x) :
    clabelS x = clabelS v ∨ clabelS x = clabelS w := by
  have hdiam := dist_le_three_of_inputs hL hO hP hT
  have hwv : cgraph.dist w v = 3 := by rw [SimpleGraph.dist_comm]; exact hvw
  have hLvw := hL v w hvw
  obtain ⟨hev, hcw, hne, hce⟩ := hLvw
  have hc2 := clabelS_mul_clabelS v
  have he2 := clabelS_mul_clabelS w
  have hd2 : clabelS v * clabelS w * (clabelS v * clabelS w) = 1 := by
    calc clabelS v * clabelS w * (clabelS v * clabelS w) =
          clabelS v * (clabelS w * clabelS v) * clabelS w := by group
      _ = clabelS v * (clabelS v * clabelS w) * clabelS w := by rw [hce.eq]
      _ = 1 := by rw [← mul_assoc, hc2, one_mul, he2]
  have hd1 : clabelS v * clabelS w ≠ 1 := fun h =>
    hne (by rw [← inv_eq_of_mul_eq_one_left hc2, eq_inv_of_mul_eq_one_left h, inv_inv])
  have hod : orderOf (clabelS v * clabelS w) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hd2) hd1
  have hdc : Commute (clabelS v * clabelS w) (clabelS v) := (Commute.refl _).mul_left hce
  have ha2 := clabelS_mul_clabelS x
  have hda : Commute (clabelS v * clabelS w) (clabelS x) :=
    commute_of_mul_self hd2 ha2 (by rw [← hy]; exact clabelS_mul_clabelS y)
  have hdp : Commute (clabelS v * clabelS w) (clabelS v * clabelS x) := hdc.mul_right hda
  have hea := mul_eq_mul_mul (a := clabelS x) hc2 hce.symm
  have hac : Commute (clabelS x) (clabelS v) := by
    rcases commute_or_three_or_four hdiam hL v x with h | ⟨-, h3⟩ | ⟨hx4, h4⟩
    · exact h.symm
    · exfalso
      have h6 : orderOf (clabelS w * clabelS x) = 6 := by
        rw [hea, hdp.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hod, h3]; decide), hod, h3]
      rcases commute_or_three_or_four hdiam hL w x with h | ⟨-, h'⟩ | ⟨-, h'⟩
      · have hdvd := orderOf_dvd_of_pow_eq_one (sq_clabelS_mul_of_commute h)
        rw [h6] at hdvd
        exact absurd hdvd (by decide)
      · rw [h6] at h'
        exact absurd h' (by decide)
      · rw [h6] at h'
        exact absurd h' (by decide)
    · exfalso
      have hsq : (clabelS w * clabelS x) ^ 2 = (clabelS v * clabelS x) ^ 2 := by
        rw [hea, sq_mul_of_commute hdp hd2]
      have hsq1 : (clabelS v * clabelS x) ^ 2 ≠ 1 := fun h => by
        have hdvd := orderOf_dvd_of_pow_eq_one h
        rw [h4] at hdvd
        exact absurd hdvd (by decide)
      rcases commute_or_three_or_four hdiam hL w x with h | ⟨-, h'⟩ | ⟨hx4', -⟩
      · exact hsq1 (hsq.symm.trans (sq_clabelS_mul_of_commute h))
      · have h44 : (clabelS w * clabelS x) ^ 4 = 1 := by
          have h0 := pow_orderOf_eq_one (clabelS v * clabelS x)
          rw [h4] at h0
          calc (clabelS w * clabelS x) ^ 4 = ((clabelS w * clabelS x) ^ 2) ^ 2 := by
                rw [← pow_mul]
            _ = ((clabelS v * clabelS x) ^ 2) ^ 2 := by rw [hsq]
            _ = (clabelS v * clabelS x) ^ 4 := by rw [← pow_mul]
            _ = 1 := h0
        have hdvd := orderOf_dvd_of_pow_eq_one h44
        rw [h'] at hdvd
        exact absurd hdvd (by decide)
      · have hsqD : (clabel v * clabel x) ^ 2 = (clabel w * clabel x) ^ 2 := by
          have h := congrArg (fun z : Shat => (z : Dfull)) hsq.symm
          simpa only [Subgroup.coe_pow, Subgroup.coe_mul, coe_clabelS] using h
        have := dist_le_two_of_sq_eq hx4 hx4' hsqD
        omega
  have hae : Commute (clabelS x) (clabelS w) := by
    have h := hac.mul_right hda.symm
    rwa [← mul_assoc, hc2, one_mul] at h
  by_contra hcon
  push Not at hcon
  obtain ⟨hxc, hxe⟩ := hcon
  have hxv : x ≠ v := fun h => hxc (by rw [h])
  have hxw : x ≠ w := fun h => hxe (by rw [h])
  have hy' : clabelS y = clabelS w * clabelS v * clabelS x := by rw [hy, hce.eq]
  rcases adj_or_dist_three_of_commute hdiam (Ne.symm hxv) hac.symm with h1 | h1 <;>
    rcases adj_or_dist_three_of_commute hdiam (Ne.symm hxw) hae.symm with h2 | h2
  · have := dist_le_two_of_adj_adj h1 h2.symm
    omega
  · exact false_of_adj_of_mul_eq hL hO hP hT hvw h1 hae.symm hy
  · exact false_of_adj_of_mul_eq hL hO hP hT hwv h2 hac.symm hy'
  · have hyv : y ≠ v := by
      intro h
      apply hxe
      rw [h] at hy
      have h' : clabelS v * (clabelS w * clabelS x) = clabelS v * 1 := by
        rw [← mul_assoc, ← hy, mul_one]
      have h'' := mul_left_cancel h'
      rw [← inv_eq_of_mul_eq_one_left he2]
      exact eq_inv_of_mul_eq_one_right h''
    have hyw : y ≠ w := by
      intro h
      apply hxc
      rw [h] at hy'
      have h' : clabelS w * (clabelS v * clabelS x) = clabelS w * 1 := by
        rw [← mul_assoc, ← hy', mul_one]
      have h'' := mul_left_cancel h'
      rw [← inv_eq_of_mul_eq_one_left hc2]
      exact eq_inv_of_mul_eq_one_right h''
    have h3 := adj_of_dist_three_mul hO hdiam hvw h1 hev (hL v x h1).1 hy hyv
    have h4 := adj_of_dist_three_mul hO hdiam hwv h2 hcw (hL w x h2).1 hy' hyw
    have := dist_le_two_of_adj_adj h3 h4.symm
    omega

theorem distance_three_product_determines_endpoints
    (hL : DistThreeLabelsInput)
    (hO : DistThreeOuterInput) (hP : DistThreePathInput) (hT : TypeThreeBoundInput)
    {v w : CVert} (hvw : cgraph.dist v w = 3) :
    {a : Shat | IsConj (clabelS v) a ∧ IsConj (clabelS v) (clabelS v * clabelS w * a)} =
      {clabelS v, clabelS w} ∧
    ∀ a b : Shat, IsConj (clabelS v) a → IsConj (clabelS v) b →
      clabelS v * clabelS w = a * b → ({a, b} : Set Shat) = {clabelS v, clabelS w} := by
  have hLvw := hL v w hvw
  obtain ⟨-, -, -, hce⟩ := hLvw
  have hc2 := clabelS_mul_clabelS v
  have he2 := clabelS_mul_clabelS w
  have key : ∀ x y : CVert, clabelS y = clabelS v * clabelS w * clabelS x →
      clabelS x = clabelS v ∨ clabelS x = clabelS w := fun x y hy =>
    eq_or_eq_of_clabelS_eq_mul hL hO hP hT hvw hy
  have hcomm : clabelS v * clabelS w * clabelS v = clabelS w := by
    rw [mul_assoc, hce.eq, ← mul_assoc, hc2, one_mul]
  have hcomm' : clabelS v * clabelS w * clabelS w = clabelS v := by
    rw [mul_assoc, he2, mul_one]
  have hmem : ∀ a : Shat, IsConj (clabelS v) a → IsConj (clabelS v) (clabelS v * clabelS w * a) →
      a ∈ ({clabelS v, clabelS w} : Set Shat) := by
    intro a ha hb
    obtain ⟨x, rfl⟩ := exists_clabelS_eq_of_isConj ha
    obtain ⟨y, hy⟩ := exists_clabelS_eq_of_isConj hb
    rcases key x y hy with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨Set.ext fun a => ⟨fun h => hmem a h.1 h.2, fun h => ?_⟩, fun a b ha hb hab => ?_⟩
  · rcases h with h | h
    · rw [h]
      refine ⟨IsConj.refl _, ?_⟩
      rw [hcomm]
      exact isConj_clabelS v w
    · rw [Set.mem_singleton_iff.1 h]
      exact ⟨isConj_clabelS v w, isConj_iff.2 ⟨1, by rw [hcomm', one_mul, inv_one, mul_one]⟩⟩
  · obtain ⟨x, rfl⟩ := exists_clabelS_eq_of_isConj ha
    have hainv : (clabelS x)⁻¹ = clabelS x := inv_eq_of_mul_eq_one_left (clabelS_mul_clabelS x)
    have hb' : IsConj (clabelS v) (clabelS v * clabelS w * clabelS x) := by
      have e1 : clabelS v * clabelS w * clabelS x = clabelS x * b * (clabelS x)⁻¹ := by
        rw [hab, hainv]
      rw [e1]
      exact hb.trans (isConj_iff.2 ⟨clabelS x, rfl⟩)
    have hbeq : b = (clabelS x)⁻¹ * (clabelS v * clabelS w) := by rw [hab, inv_mul_cancel_left]
    rcases hmem _ ha hb' with h | h
    · have h' : clabelS x = clabelS v := h
      rw [h', inv_eq_of_mul_eq_one_left hc2, ← mul_assoc, hc2, one_mul] at hbeq
      rw [h', hbeq]
    · have h' : clabelS x = clabelS w := h
      rw [h', inv_eq_of_mul_eq_one_left he2, ← mul_assoc, hce.eq, mul_assoc, he2, mul_one]
        at hbeq
      rw [h', hbeq, Set.pair_comm]

end CFSG.Monster.B.CTIB
