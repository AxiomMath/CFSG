module

public import CFSG.Timmesfeld.Exceptional.DeepWorldCBasic
public import CFSG.Timmesfeld.Exceptional.DeepAllNear
public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalStruct

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem commute_of_commute_mul_left {w a b : G} (hwb : Commute w b)
    (h : Commute (w * a) b) : Commute a b := by
  have := hwb.inv_left.mul_left h
  rwa [inv_mul_cancel_left] at this

namespace FiveLineSetting

variable (S : FiveLineSetting G D)
include S

theorem twoLocalSetting : Bridge.TwoLocalSetting G D :=
  ⟨S.hyp, S.sing, S.noLevi, S.noPlane⟩

theorem ncard_rootLines {d : G} (hd : d ∈ D) : (Bridge.rootLines D d).ncard = 5 := by
  have h := S.twoLocalSetting.ncard_collinearSet hd
  rw [S.ten d hd] at h
  omega

theorem sq_facts {p w s : G} (hp : p ∈ D) (hwD : w ∈ D) (hw2 : w ∉ nbhd D p 2)
    (hs : s ∈ collinearSet D w) (h4 : orderOf (s * p) = 4) :
    (s * p) ^ 2 ∈ collinearSet D p ∧ Commute s ((s * p) ^ 2) ∧
      (s * p) ^ 2 ∉ nbhd D w 1 ∧ orderOf ((s * p) ^ 2 * w) = 4 := by
  obtain ⟨hxD, hsx, hpx, -⟩ := sq_mem_of_orderOf_eq_four S.root hs.1 hp h4
  have hsp : ¬ Commute s p := not_commute_of_orderOf_eq_four (S.root.mul_self_eq_one hs.1)
    (S.root.mul_self_eq_one hp) h4
  have hxp : (s * p) ^ 2 ≠ p := fun e => hsp (e ▸ hsx)
  have hx : (s * p) ^ 2 ∈ collinearSet D p := (S.mem_collinearSet_iff hp).2 ⟨hxD, hpx, hxp⟩
  have hxw1 : (s * p) ^ 2 ∉ nbhd D w 1 := by
    intro h1
    have hp2 : p ∈ nbhd D w 2 := mem_nbhd_succ_of_commute hp h1 hpx
    exact hw2 (mem_nbhd_comm hwD hp2)
  refine ⟨hx, hsx, hxw1, ?_⟩
  have hs1 : s ∈ nbhd D w 1 := (mem_nbhd_one_iff hwD).2 ⟨hs.1, hs.2.1.symm⟩
  exact S.orderOf_eq_four_of_mem_two hwD (mem_nbhd_succ_of_commute hxD hs1 hsx.symm) hxw1

end FiveLineSetting

theorem FiveLineSetting.exists_far {G : Type} [Group G] {D : Set G} (S : FiveLineSetting G D)
    {p w : G} (hp : p ∈ D)
    (hw3 : w ∈ nbhd D p 3) (hw2 : w ∉ nbhd D p 2) :
    ∃ a ∈ collinearSet D w, a ∉ nbhd D p 3 := by
  by_contra hno
  push Not at hno
  have := S.finite
  have hD := S.root
  have hwD := nbhd_subset hp 3 hw3
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => S.conj g hx
  have T := S.twoLocalSetting
  have h5 := S.ncard_rootLines hwD
  obtain ⟨P, hPk, hP, hnc, -⟩ := T.exists_transversal hwD
  rw [h5] at hPk
  obtain ⟨e⟩ : Nonempty (Fin 5 ≃ P) := ⟨(P.equivFin.trans (finCongr hPk)).symm⟩
  have ht : ∀ i, ((e i : P) : G) ∈ collinearSet D w := fun i => by
    obtain ⟨htD, hwt, htw⟩ := hP _ (e i).2
    exact (S.mem_collinearSet_iff hwD).2 ⟨htD, hwt, htw⟩
  have htc : ∀ i j, i ≠ j → ¬ Commute ((e i : P) : G) (e j) := fun i j hij =>
    hnc _ (e i).2 _ (e j).2 fun h => hij (e.injective (Subtype.ext h))
  have hs : ∀ i, ∃ s, (s = (e i : G) ∨ s = w * (e i : G)) ∧ orderOf (s * p) = 4 := by
    intro i
    rcases special_of_mem_nbhd_three hD S.noLevi S.noPolar S.p1 hp hwD hw3 hw2 (ht i)
      (hno _ (ht i)) with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  choose s hst hs4 using hs
  have hsl : ∀ i, s i ∈ collinearSet D w := fun i => by
    rcases hst i with h | h <;> rw [h]
    · exact ht i
    · exact mul_mem_collinearSet hD hwD (ht i)
  have hsD : ∀ i, s i ∈ D := fun i => (hsl i).1
  have hws : ∀ i, Commute w (s i) := fun i => (hsl i).2.1
  have hsc : ∀ i j, i ≠ j → ¬ Commute (s i) (s j) := by
    intro i j hij hc
    have hwi : Commute w (e i : G) := (ht i).2.1
    have hwj : Commute w (e j : G) := (ht j).2.1
    refine htc i j hij ?_
    rcases hst i with hi | hi <;> rcases hst j with hj | hj <;> rw [hi, hj] at hc
    · exact hc
    · exact (commute_of_commute_mul_left hwi hc.symm).symm
    · exact commute_of_commute_mul_left hwj hc
    · have h1 := commute_of_commute_mul_left ((Commute.refl w).mul_right hwj) hc
      exact (commute_of_commute_mul_left hwi h1.symm).symm
  have hs2 : ∀ i, s i * s i = 1 := fun i => hD.mul_self_eq_one (hsD i)
  have hx := fun i => S.sq_facts hp hwD hw2 (hsl i) (hs4 i)
  have huq : ∀ j z, z ∈ D → Commute z w → Commute z ((s j * p) ^ 2) → z = s j := by
    intro j z hz hzw hzx
    obtain ⟨hxj, hsxj, hxj1, -⟩ := hx j
    exact (S.eq_sq_of_commute hwD hxj.1 hxj1 hz hzw hzx).trans
      (S.eq_sq_of_commute hwD hxj.1 hxj1 (hsD j) (hws j).symm hsxj).symm
  have r_wp : (w * p) ^ 3 = 1 := by
    rw [← orderOf_eq_three_of_mem_nbhd_three hD S.noLevi S.noPolar S.p1 hp hw3 hw2]
    exact pow_orderOf_eq_one _
  have r_sp4 : ∀ i, (s i * p) ^ 4 = 1 := fun i => by
    rw [← hs4 i]
    exact pow_orderOf_eq_one _
  have r_wsp : ∀ i, (w * s i * p) ^ 3 = 1 := by
    intro i
    have hwsl := mul_mem_collinearSet hD hwD (hsl i)
    have hsws : s i * (w * s i) = w := by
      rw [← mul_assoc, ← (hws i).eq, mul_assoc, hs2 i, mul_one]
    have h2 : w * s i ∉ nbhd D p 2 := by
      intro h2
      obtain ⟨-, hc | h4⟩ := (mem_nbhd_two_iff hD S.noLevi hp).1 h2
      · exact hw2 (mem_nbhd_succ_of_commute hwD ((mem_nbhd_one_iff hp).2 ⟨hwsl.1, hc⟩)
          ((Commute.refl w).mul_right (hws i)))
      · have hc := commute_of_special_special S.hclass hD S.sing S.commLambda S.noPolar
          S.noPlane (hsD i) hwsl.1 hp ((hws i).symm.mul_right (Commute.refl (s i)))
          (by rw [hsws]; exact hwD) (hs4 i) h4
        rw [hsws] at hc
        exact hw2 (nbhd_mono (by norm_num) ((mem_nbhd_one_iff hp).2 ⟨hwD, hc⟩))
    rw [← orderOf_eq_three_of_mem_nbhd_three hD S.noLevi S.noPolar S.p1 hp (hno _ hwsl) h2]
    exact pow_orderOf_eq_one _
  have r_pxw : ∀ i, (p * (s i * p) ^ 2 * w) ^ 3 = 1 := by
    intro i
    obtain ⟨hxl, hsx, -, hxw4⟩ := hx i
    have hpxl := mul_mem_collinearSet hD hp hxl
    have hxpx : (s i * p) ^ 2 * (p * (s i * p) ^ 2) = p := by
      rw [← mul_assoc, ← hxl.2.1.eq, mul_assoc, hD.mul_self_eq_one hxl.1, mul_one]
    have hx2 : (s i * p) ^ 2 ∈ nbhd D w 2 := mem_nbhd_succ_of_commute hxl.1
      ((mem_nbhd_one_iff hwD).2 ⟨hsD i, (hws i).symm⟩) hsx.symm
    have h3 : p * (s i * p) ^ 2 ∈ nbhd D w 3 :=
      mem_nbhd_succ_of_commute hpxl.1 hx2 (hxl.2.1.mul_left (Commute.refl _))
    have h2 : p * (s i * p) ^ 2 ∉ nbhd D w 2 := by
      intro h2
      obtain ⟨-, hc | h4⟩ := (mem_nbhd_two_iff hD S.noLevi hwD).1 h2
      · have : p ∈ nbhd D w 2 := mem_nbhd_succ_of_commute hp
          ((mem_nbhd_one_iff hwD).2 ⟨hpxl.1, hc⟩) ((Commute.refl p).mul_right hxl.2.1)
        exact hw2 (mem_nbhd_comm hwD this)
      · have hc := commute_of_special_special S.hclass hD S.sing S.commLambda S.noPolar
          S.noPlane hxl.1 hpxl.1 hwD (hxl.2.1.symm.mul_right (Commute.refl _))
          (by rw [hxpx]; exact hp) hxw4 h4
        rw [hxpx] at hc
        exact hw2 (mem_nbhd_comm hwD (nbhd_mono (by norm_num)
          ((mem_nbhd_one_iff hwD).2 ⟨hp, hc⟩)))
    rw [← orderOf_eq_three_of_mem_nbhd_three hD S.noLevi S.noPolar S.p1 hwD h3 h2]
    exact pow_orderOf_eq_one _
  have r_ss : ∀ i j, i < j → (s i * s j) ^ 2 = w := by
    intro i j hij
    rcases NoLevi.centralizer_cases hD hconj S.noLevi S.noPolar S.noPlane hwD (hsD i) (hsD j)
        (hws i) (hws j) (ne_of_mem_collinearSet hD hwD (hsl i))
        (ne_of_mem_collinearSet hD hwD (hsl j)) with h | h | ⟨-, h⟩
    · exact absurd (by rw [h]) (hsc i j hij.ne)
    · exact absurd (by rw [h]; exact (hws i).symm.mul_right (Commute.refl _)) (hsc i j hij.ne)
    · exact h
  have r_xx : ∀ i j, i < j → ((s i * p) ^ 2 * (s j * p) ^ 2) ^ 2 = p := by
    intro i j hij
    obtain ⟨hxi, hsxi, -, hxi4⟩ := hx i
    obtain ⟨hxj, -, -, hxj4⟩ := hx j
    rcases NoLevi.centralizer_cases hD hconj S.noLevi S.noPolar S.noPlane hp hxi.1 hxj.1
        hxi.2.1 hxj.2.1 (ne_of_mem_collinearSet hD hp hxi)
        (ne_of_mem_collinearSet hD hp hxj) with h | h | ⟨-, h⟩
    · exfalso
      have e := huq j (s i) (hsD i) (hws i).symm (by rw [h]; exact hsxi)
      exact hsc i j hij.ne (by rw [e])
    · exfalso
      have hpxl := mul_mem_collinearSet hD hp hxi
      have hxpx : (s i * p) ^ 2 * (p * (s i * p) ^ 2) = p := by
        rw [← mul_assoc, ← hxi.2.1.eq, mul_assoc, hD.mul_self_eq_one hxi.1, mul_one]
      have hc := commute_of_special_special S.hclass hD S.sing S.commLambda S.noPolar
        S.noPlane hxi.1 hpxl.1 hwD (hxi.2.1.symm.mul_right (Commute.refl _))
        (by rw [hxpx]; exact hp) hxi4 (by rw [← h]; exact hxj4)
      rw [hxpx] at hc
      exact hw2 (mem_nbhd_comm hwD (nbhd_mono (by norm_num)
        ((mem_nbhd_one_iff hwD).2 ⟨hp, hc⟩)))
    · exact h
  have r_sx : ∀ i j, i ≠ j → (s i * (s j * p) ^ 2) ^ 3 = 1 := by
    intro i j hij
    obtain ⟨hxj, hsxj, -, hxj4⟩ := hx j
    have h1 : s j ∈ nbhd D ((s j * p) ^ 2) 1 := (mem_nbhd_one_iff hxj.1).2 ⟨hsD j, hsxj⟩
    have h2' : w ∈ nbhd D ((s j * p) ^ 2) 2 := mem_nbhd_succ_of_commute hwD h1 (hws j)
    have h3 : s i ∈ nbhd D ((s j * p) ^ 2) 3 :=
      mem_nbhd_succ_of_commute (hsD i) h2' (hws i).symm
    have h2 : s i ∉ nbhd D ((s j * p) ^ 2) 2 := by
      intro h2
      obtain ⟨-, hc | h4⟩ := (mem_nbhd_two_iff hD S.noLevi hxj.1).1 h2
      · have e := huq j (s i) (hsD i) (hws i).symm hc
        exact hsc i j hij (by rw [e])
      · have hw4 : orderOf (w * (s j * p) ^ 2) = 4 := by rw [orderOf_mul_comm_eq]; exact hxj4
        have hwsl := mul_mem_collinearSet hD hwD (hsl i)
        have hc := commute_of_special_special S.hclass hD S.sing S.commLambda S.noPolar
          S.noPlane hwD (hsD i) hxj.1 (hws i) hwsl.1 hw4 h4
        have e := huq j (w * s i) hwsl.1 ((Commute.refl w).mul_left (hws i).symm) hc
        exact hsc i j hij (by rw [← e]; exact (hws i).symm.mul_right (Commute.refl _))
    rw [← orderOf_eq_three_of_mem_nbhd_three hD S.noLevi S.noPolar S.p1 hxj.1 h3 h2]
    exact pow_orderOf_eq_one _
  have hprod := T.mul_five_mem hwD h5 (x₁ := s 0) (x₂ := s 1) (x₃ := s 2) (x₄ := s 3)
    (x₅ := s 4) (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨hsD _, hws _, ne_of_mem_collinearSet hD hwD (hsl _)⟩) (by
      have e : [s 0, s 1, s 2, s 3, s 4] = List.ofFn s := by simp [List.ofFn_succ]
      rw [e, List.pairwise_ofFn]
      exact fun i j hij => hsc i j hij.ne)
  exact hD.ne_one hwD (allNearCollapse G w p s (hD.mul_self_eq_one hwD) (hD.mul_self_eq_one hp)
    r_wp hs2 hws r_sp4 r_wsp r_pxw r_ss r_xx r_sx hprod)

end CFSG.Timmesfeld.Moufang.Deep
