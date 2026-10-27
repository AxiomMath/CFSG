module

public import CFSG.Monster.GMS.S37Three
public import CFSG.Monster.GMS.Facts.Section4Coh
import CFSG.Monster.GMS.Coxeter
import CFSG.Monster.GMS.NotConj

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic S36Lines

namespace S37

section Reach

variable {G : Type*} [Group G] {a x y : G}

@[expose] def VReach (a x y : G) : Prop :=
  ∃ (hx : IsConj a x) (hy : IsConj a y), (twoAGraph a).Reachable ⟨x, hx⟩ ⟨y, hy⟩

theorem VReach.refl (hx : IsConj a x) : VReach a x x :=
  ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

theorem VReach.symm (h : VReach a x y) : VReach a y x := by
  obtain ⟨hx, hy, h⟩ := h
  exact ⟨hy, hx, h.symm⟩

theorem VReach.trans {z : G} (h₁ : VReach a x y) (h₂ : VReach a y z) : VReach a x z := by
  obtain ⟨hx, hy, h₁⟩ := h₁
  obtain ⟨_, hz, h₂⟩ := h₂
  exact ⟨hx, hz, h₁.trans h₂⟩

theorem VReach.of_mem_twoANbr (ha : orderOf a = 2) (hx : IsConj a x) (hy : y ∈ twoANbr a x) :
    VReach a x y :=
  ⟨hx, hy.1, ((S57.adj_iff_mem_twoANbr ha ⟨x, hx⟩ ⟨y, hy.1⟩).mpr hy).reachable⟩

theorem VReach.of_commonNbr (ha : orderOf a = 2) (hx : IsConj a x) (hy : IsConj a y) {c : G}
    (hcx : c ∈ twoANbr a x) (hcy : c ∈ twoANbr a y) : VReach a x y :=
  (VReach.of_mem_twoANbr ha hx hcx).trans (VReach.of_mem_twoANbr ha hy hcy).symm

end Reach

section Paths

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y : G}

theorem vreach_of_mem_cent
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hx : IsConj a x)
    (hy : IsConj a y) (hc : y ∈ Subgroup.centralizer ({x} : Set G)) : VReach a x y := by
  have ha : orderOf a = 2 := hG.1.1
  by_cases hyx : y = x
  · subst hyx
    exact VReach.refl hy
  have hxx := sq_eq_one_of_isConj ha hx
  have hyy := sq_eq_one_of_isConj ha hy
  have hxy : x * y = y * x := (mem_cent_iff.mp hc).symm
  have hxy1 : x * y ≠ 1 := fun h =>
    hyx (by rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hxx])
  have hxysq : (x * y) * (x * y) = 1 :=
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  have hxy2 : orderOf (x * y) = 2 := orderOf_eq_two_of_mul_self hxysq hxy1
  rcases s31_five I.sls I.tableV I.leech hG I.leechInv hxy2 with hA | hB
  · exact VReach.of_mem_twoANbr ha hx ⟨hy, hA⟩
  · have hn := ncard_commonNbr_twoB I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG hx (show y ∈ twoBNbr a z₀ x from ⟨hy, hB⟩)
    obtain ⟨c, hc1, hc2⟩ : (twoANbr a x ∩ twoANbr a y).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    exact VReach.of_commonNbr ha hx hy hc1 hc2

theorem exists_commonNbr_threeA
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hx : IsConj a x) (hy : y ∈ typeSet a z₀ x .threeA) :
    (twoANbr a x ∩ twoANbr a y).Nonempty := by
  obtain ⟨c₀, hc₀⟩ :=
    table7_nonempty I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx .two_A
  have hpos : (tableVIOrbit a z₀ x c₀ .three_A).ncard ≠ 0 := by
    rw [s341_ncard I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx hc₀ .three_A]
    norm_num [tableVISize]
  obtain ⟨y', hy'⟩ := Set.nonempty_of_ncard_ne_zero hpos
  have hy'c : y' ∈ twoANbr a c₀ := hy'.1.1
  have hy'x : y' ≠ x := hy'.1.2.1
  have hord3 : orderOf (x * y') = 3 := hy'.2
  have hy'A : IsConj a y' := hy'c.1
  obtain ⟨w, hw, hwB⟩ := hCN x y' c₀ hx hc₀ hy'c hord3
  have hy'odd : y' ∈ oddNbr a z₀ x := ⟨hy'A, hy'x, by rw [hord3]; decide, w, hw, hwB⟩
  obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hy'odd
  have hc₀y' : c₀ ∈ twoANbr a x ∩ twoANbr a y' :=
    ⟨hc₀, (S57.mem_twoANbr_comm hy'A hc₀.1).mpr hy'c⟩
  have hk0 : OddNbrType z₀ x y' 0 := by
    have hok := (s348_card hk hw hwB).1
    rw [hord3] at hok
    match k, hk, hok with
    | 0, hk, _ => exact hk
    | 1, hk, _ =>
      exfalso
      have hemp := commonNbr_threeC_eq_empty I.sls I.tableV I.leech I.tableIII I.tableIVBaby
        I.threeSwap I.leechPair I.leechOddPair I.tableIV hG hx
        (show y' ∈ typeSet a z₀ x .threeC from ⟨hy'odd, hk⟩)
      exact (Set.eq_empty_iff_forall_notMem.mp hemp) c₀ hc₀y'
    | 2, _, hok => exact absurd hok (by decide)
  obtain ⟨g, hg, hgy⟩ := s348_orbit I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hy'odd
    hy.1 hk0 hy.2
  have := S57.conj_mem_inter (a := a) hg hc₀y'
  rw [hgy] at this
  exact ⟨_, this⟩

theorem vreach_of_mem_gammaNbr_aux
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hF5 : FiveATwoA a z₀) (hx : IsConj a x)
    (hy : y ∈ gammaNbr a z₀ x) (h3C : y ∉ typeSet a z₀ x .threeC) : VReach a x y := by
  have ha : orderOf a = 2 := hG.1.1
  rcases mem_gammaNbr_iff.mp hy with rfl | ⟨K, hK⟩
  · exact VReach.refl hx
  have hyA : IsConj a y := isConj_of_mem_typeSet hK
  have common : (twoANbr a x ∩ twoANbr a y).Nonempty → VReach a x y := fun ⟨c, hc1, hc2⟩ =>
    VReach.of_commonNbr ha hx hyA hc1 hc2
  cases K with
  | twoA => exact VReach.of_mem_twoANbr ha hx hK
  | twoB =>
    refine common (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_commonNbr_twoB I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG hx hK]
    norm_num
  | fourA =>
    refine common (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_commonNbr_fourA I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG hx hK]
    norm_num
  | fourB =>
    refine common (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_commonNbr_fourB I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx hK]
    norm_num
  | sixA =>
    refine common (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_commonNbr_sixA I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hx hK]
    norm_num
  | threeA => exact common (exists_commonNbr_threeA I hG hCN hx hK)
  | threeC => exact absurd hK h3C
  | fiveA =>
    obtain ⟨t, ht, htA⟩ := hF5 x y hx hK
    obtain ⟨htx, hty⟩ := Subgroup.mem_inf.mp ht
    exact (vreach_of_mem_cent I hG hx htA htx).trans
      (vreach_of_mem_cent I hG hyA htA hty).symm

end Paths

section Cover

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y z : G}

theorem vreach_of_mem_gammaNbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hES : EdgeSquares a) (hEC : EightCentOrders a z₀)
    (hE1 : EightOneOddOrder a z₀) (hF4 : FourAOddOrder a z₀) (hLO : LineOddOrder a)
    (hOD : OddTypeDvd a z₀) (hF5 : FiveATwoA a z₀) (hx : IsConj a x)
    (hy : y ∈ gammaNbr a z₀ x) : VReach a x y := by
  by_cases h3C : y ∈ typeSet a z₀ x .threeC
  swap
  · exact vreach_of_mem_gammaNbr_aux I hG hCN hF5 hx hy h3C
  have ha : orderOf a = 2 := hG.1.1
  have hz₀ : orderOf z₀ = 2 := hG.2.1
  have hyA : IsConj a y := isConj_of_mem_typeSet h3C
  have hxx := sq_eq_one_of_isConj ha hx
  have hyy := sq_eq_one_of_isConj ha hyA
  obtain ⟨z, hz⟩ : (twoANbr a y).Nonempty :=
    table7_nonempty I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hyA .two_A
  have hzz := sq_eq_one_of_isConj ha hz.1
  have hzg : z ∈ gammaNbr a z₀ x := (s372_one I hG hCN hES hEC hE1 hF4 hLO hOD hx hy hz).2
  have hyz : y * z ∈ twoANbr a y :=
    ⟨hz.2, by rw [← mul_assoc, hyy, one_mul]; exact hz.1⟩
  have hyzg : y * z ∈ gammaNbr a z₀ x := (s372_one I hG hCN hES hEC hE1 hF4 hLO hOD hx hy hyz).2
  have hnot : z ∉ typeSet a z₀ x .threeC ∨ y * z ∉ typeSet a z₀ x .threeC := by
    by_contra hboth
    push Not at hboth
    obtain ⟨h1, h2⟩ := hboth
    have hxz : orderOf (x * z) = 3 := orderOf_mul_of_mem_typeSet ha hz₀ h1
    have hxyz : orderOf (x * (y * z)) = 3 := orderOf_mul_of_mem_typeSet ha hz₀ h2
    have hxy : orderOf (x * y) = 3 := orderOf_mul_of_mem_typeSet ha hz₀ h3C
    have hzx : orderOf (z * x) = 3 := (orderOf_eq_of_isConj (S57.isConj_mul_swap z x)).trans hxz
    have hzxy : orderOf (z * x * y) = 3 := by
      have e : z * x * y = z * (x * (y * z)) * z⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right hzz]
        calc z * x * y = z * x * y * (z * z) := by rw [hzz, mul_one]
          _ = z * (x * (y * z)) * z := by group
      rw [e, orderOf_conj_eq, hxyz]
    have h3 : ∀ w : G, orderOf w = 3 → w ^ 3 = 1 := fun w hw => by
      have := pow_orderOf_eq_one w
      rwa [hw] at this
    have hyz2 : (y * z) ^ 2 = 1 := by
      rw [pow_two]
      exact sq_eq_one_of_isConj ha hz.2
    exact ne_one_of_isConj ha hz.1
      (coxeter_three_three_three_collapse hzz hxx hyy (h3 _ hzx) (h3 _ hxy) hyz2 (h3 _ hzxy)).1
  rcases hnot with hn | hn
  · exact (vreach_of_mem_gammaNbr_aux I hG hCN hF5 hx hzg hn).trans
      (VReach.of_mem_twoANbr ha hyA hz).symm
  · exact (vreach_of_mem_gammaNbr_aux I hG hCN hF5 hx hyzg hn).trans
      (VReach.of_mem_twoANbr ha hyA hyz).symm

theorem exists_twoB_cent
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hx : IsConj a x) :
    ∃ t ∈ Subgroup.centralizer ({x} : Set G), IsConj z₀ t := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  refine ⟨c * z * c⁻¹, ?_, h.isConj_z.trans (isConj_iff.mpr ⟨c, rfl⟩)⟩
  rw [← hc]
  have hza : z * a = a * z := mem_cent_iff.mp h.tableV.mem_z
  rw [mem_cent_iff]
  calc c * z * c⁻¹ * (c * a * c⁻¹) = c * (z * a) * c⁻¹ := by group
    _ = c * (a * z) * c⁻¹ := by rw [hza]
    _ = c * a * c⁻¹ * (c * z * c⁻¹) := by group

theorem vreach_all
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hCN : CommonNbrTwoB a z₀)
    (hES : EdgeSquares a) (hEC : EightCentOrders a z₀) (hE1 : EightOneOddOrder a z₀)
    (hF4 : FourAOddOrder a z₀) (hLO : LineOddOrder a) (hOD : OddTypeDvd a z₀)
    (hF5 : FiveATwoA a z₀) (hx : IsConj a x) (hy : IsConj a y) : VReach a x y := by
  have ha : orderOf a = 2 := hG.1.1
  have hz₀ : orderOf z₀ = 2 := hG.2.1
  obtain ⟨t, htx, htB⟩ := exists_twoB_cent I hG hx
  have ht2 : orderOf t = 2 := (orderOf_eq_of_isConj htB).symm.trans hz₀
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf ht2
  have hyy := sq_eq_one_of_isConj ha hy
  have hev : Even (orderOf (t * y)) := by
    rcases Nat.even_or_odd (orderOf (t * y)) with h | h
    · exact h
    · exact absurd (hy.trans (htB.trans (isConj_of_involutions_of_odd_orderOf_mul htt hyy h)).symm)
        hG.not_isConj
  obtain ⟨m, hm⟩ := hev
  have hm0 : 0 < m := by
    have := orderOf_pos (t * y)
    omega
  obtain ⟨hss, hs1, hst, hsy, -⟩ :=
    dihedral_data htt hyy (show orderOf (t * y) = 2 * m by omega) hm0
  have hs2 : orderOf ((t * y) ^ m) = 2 := orderOf_eq_two_of_mul_self hss hs1
  have htC : t ∈ Subgroup.centralizer ({(t * y) ^ m} : Set G) := mem_cent_iff.mpr hst.symm
  rcases s31_five I.sls I.tableV I.leech hG I.leechInv hs2 with hsA | hsB
  ·
    have hxs : (t * y) ^ m ∈ gammaNbr a z₀ x :=
      mem_gammaNbr_of_twoB I hG hx hsA ⟨t, Subgroup.mem_inf.mpr ⟨htx, htC⟩, htB⟩
    exact (vreach_of_mem_gammaNbr I hG hCN hES hEC hE1 hF4 hLO hOD hF5 hx hxs).trans
      (vreach_of_mem_cent I hG hy hsA (mem_cent_iff.mpr hsy)).symm
  ·
    obtain ⟨w, hwC, hwt, hwA⟩ := s31_four I.sls I.tableV I.leech hG I.leechInv hsB htC ht2
    have htw : t ∈ Subgroup.centralizer ({w} : Set G) := mem_cent_iff.mpr hwt.symm
    have hsw : (t * y) ^ m ∈ Subgroup.centralizer ({w} : Set G) := cent_symm.mp hwC
    have hsyC : (t * y) ^ m ∈ Subgroup.centralizer ({y} : Set G) := mem_cent_iff.mpr hsy
    have hxw : w ∈ gammaNbr a z₀ x :=
      mem_gammaNbr_of_twoB I hG hx hwA ⟨t, Subgroup.mem_inf.mpr ⟨htx, htw⟩, htB⟩
    have hyw : w ∈ gammaNbr a z₀ y :=
      mem_gammaNbr_of_twoB I hG hy hwA ⟨_, Subgroup.mem_inf.mpr ⟨hsyC, hsw⟩, hsB⟩
    exact (vreach_of_mem_gammaNbr I hG hCN hES hEC hE1 hF4 hLO hOD hF5 hx hxw).trans
      (vreach_of_mem_gammaNbr I hG hCN hES hEC hE1 hF4 hLO hOD hF5 hy hyw).symm

end Cover

end S37

section Headline

open S37

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem twoAGraph_connected
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hES : EdgeSquares a) (hEC : EightCentOrders a z₀)
    (hE1 : EightOneOddOrder a z₀) (hF4 : FourAOddOrder a z₀) (hLO : LineOddOrder a)
    (hOD : OddTypeDvd a z₀) (hF5 : FiveATwoA a z₀) : (twoAGraph a).Connected := by
  have : Nonempty (ConjVert a) := ⟨⟨a, IsConj.refl a⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  obtain ⟨_, _, h⟩ := vreach_all I hG hCN hES hEC hE1 hF4 hLO hOD hF5 u.2 v.2
  exact h

theorem gammaCover_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hES : EdgeSquares a) (hEC : EightCentOrders a z₀)
    (hE1 : EightOneOddOrder a z₀) (hF4 : FourAOddOrder a z₀) (hLO : LineOddOrder a)
    (hOD : OddTypeDvd a z₀) (hF5 : FiveATwoA a z₀) : GammaCover a z₀ := by
  intro x y hx hy
  have ha : orderOf a = 2 := hG.1.1
  have hr : (twoAGraph a).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
    (twoAGraph_connected I hG hCN hES hEC hE1 hF4 hLO hOD hF5).preconnected _ _
  have key : ∀ v : ConjVert a, Relation.ReflTransGen (twoAGraph a).Adj ⟨x, hx⟩ v →
      (v : G) ∈ gammaNbr a z₀ x := by
    intro v hv
    induction hv with
    | refl => exact self_mem_gammaNbr
    | @tail b c _ hbc ih =>
      exact (s372_one I hG hCN hES hEC hE1 hF4 hLO hOD hx ih
        ((S57.adj_iff_mem_twoANbr ha b c).mp hbc)).2
  exact key ⟨y, hy⟩ ((SimpleGraph.reachable_iff_reflTransGen _ _).mp hr)

theorem linesHaveInvolutions_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hES : EdgeSquares a) (hEC : EightCentOrders a z₀)
    (hE1 : EightOneOddOrder a z₀) (hF4 : FourAOddOrder a z₀) (hLO : LineOddOrder a)
    (hOD : OddTypeDvd a z₀) (hF5 : FiveATwoA a z₀) : LinesHaveInvolutions a :=
  fun x y _ hx hy hz =>
    (s372_one I hG hCN hES hEC hE1 hF4 hLO hOD hx
      (gammaCover_of I hG hCN hES hEC hE1 hF4 hLO hOD hF5 x y hx hy) hz).1

theorem s372_mem_oddNbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hCN : CommonNbrTwoB a z₀) (hES : EdgeSquares a) (hEC : EightCentOrders a z₀)
    (hE1 : EightOneOddOrder a z₀) (hF4 : FourAOddOrder a z₀) (hLO : LineOddOrder a)
    (hOD : OddTypeDvd a z₀) (hF5 : FiveATwoA a z₀) : OddPairsCommonTwoB a z₀ := by
  intro x y hx hy hyx hodd
  have ha : orderOf a = 2 := hG.1.1
  have hz₀ : orderOf z₀ = 2 := hG.2.1
  rcases gammaCover_of I hG hCN hES hEC hE1 hF4 hLO hOD hF5 x y hx hy with h | h
  · exact absurd h hyx
  · obtain ⟨K, hK⟩ := Set.mem_iUnion.mp h
    have ho := orderOf_mul_of_mem_typeSet ha hz₀ hK
    cases K with
    | threeA => exact hK.1
    | threeC => exact hK.1
    | fiveA => exact hK.1
    | twoA => rw [ho] at hodd; exact absurd hodd (by decide)
    | twoB => rw [ho] at hodd; exact absurd hodd (by decide)
    | fourA => rw [ho] at hodd; exact absurd hodd (by decide)
    | fourB => rw [ho] at hodd; exact absurd hodd (by decide)
    | sixA => rw [ho] at hodd; exact absurd hodd (by decide)

end Headline

end CFSG.Monster.GMS
