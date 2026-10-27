module

public import CFSG.Timmesfeld.Bridge.RootStructR2Thin
public import CFSG.Timmesfeld.Bridge.RootStructThmD

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def AllLinesTI (D : Set G) : Prop :=
  ∀ b ∈ D, ∀ b' ∈ D, Commute b b' → b * b' ∈ D → b' ∉ rootSet D b → LineTI D b b'

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem allLinesTI_of_lineTI (hconn : Moufang.ExcCollConnected D) {a d : G} (ha : a ∈ D)
    (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    (hL : LineTI D a d) : AllLinesTI D := fun _ hb _ hb' hbb' hbb'D hb'T =>
  lineTI_of_lineTI h hc hs hconn ha hd had hadD hdT hL hb hb' hbb' hbb'D hb'T

theorem noPolar_of_lineTI (hconn : Moufang.ExcCollConnected D) {a d : G} (ha : a ∈ D)
    (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
    (hL : LineTI D a d) : Moufang.NoPolar D := by
  intro x hx y hy hxy hne
  have := h.finite
  have hD := h.root
  have hyQ := mem_twoCore_of_commute_of_lineTI h hc hs hconn ha hd had hadD hdT hL hx hy hxy.symm
  rcases mem_rootSet_or_collinear_of_mem_twoCore h.isClass hD (oppositeDetermines_of_hyp h) hc
      hs (nCoreCommutatorInRoot_of_hyp h hc) hx hy hyQ with hT | ⟨-, hxyD⟩
  · refine (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx (Subgroup.mul_mem _
      (rootSet_subset_rootGroup D x (mem_rootSet_self hx)) (rootSet_subset_rootGroup D x hT))
      fun h1 => hne ?_).1
    exact ((eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq hx)).symm
  · exact hxyD

theorem mem_rootSet_of_special_of_special (hconn : Moufang.ExcCollConnected D)
    (hAll : AllLinesTI D) {a d : G} (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d)
    (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x b p p' : G} (hx : x ∈ D) (hb : b ∈ D)
    (hbL : b ∈ rootGroup D a ⊔ rootGroup D d) (hbx : ¬ Commute b x)
    (hoddbx : Odd (orderOf (b * x))) (hp : p ∈ D) (hpL : p ∈ rootGroup D a ⊔ rootGroup D d)
    (hp' : p' ∈ D) (hp'L : p' ∈ rootGroup D a ⊔ rootGroup D d) (h4 : orderOf (x * p) = 4)
    (h4' : orderOf (x * p') = 4) : p' ∈ rootSet D p := by
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  have hL := hAll a ha d hd had hadD hdT
  by_contra hT
  have hxp := not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hp)
    h4
  obtain ⟨hzD, hxz, hpz, -⟩ := sq_mem_of_orderOf_eq_four hD hx hp h4
  have h4p : orderOf (p * x) = 4 := by rwa [orderOf_mul_comm_eq]
  have hsq : (p * x) ^ 2 = (x * p) ^ 2 :=
    (mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hx) (hD.mul_self_eq_one hp) h4).symm
  have hpzD : p * (x * p) ^ 2 ∈ D := by
    rw [← hsq]
    exact mul_sq_mem_of_orderOf_eq_four hclass hD hp hx h4p
  have hzpD : (x * p) ^ 2 * p ∈ D := by rw [← hpz.eq]; exact hpzD
  have hxzD : x * (x * p) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four hclass hD hx hp h4
  have hpT : p ∉ rootSet D ((x * p) ^ 2) := fun h' => hxp ((h'.2 x hx).2 hxz.symm).symm
  have hLz := hAll _ hzD p hp hpz.symm hzpD hpT
  have hpp' := commute_of_mem_sup_rootGroup ha hd had hpL hp'L
  have hwz : ¬ Commute p' ((x * p) ^ 2) := by
    intro hp'z
    have hne : p * p' ≠ 1 := by
      intro h1
      apply hT
      rw [(eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq hp)]
      exact mem_rootSet_self hp
    have hpp'D := mem_of_mem_sup_rootGroup h hc hs ha hd had hadD hdT
      (Subgroup.mul_mem _ hpL hp'L) hne
    have hLeq := sup_rootGroup_eq_of_mem h hc hs ha hd had hadD hdT hpL hp'L (hD.ne_one hp)
      (hD.ne_one hp') hT
    have hzQ := mem_twoCore_of_commute_of_lineTI h hc hs hconn ha hd had hadD hdT hL hp' hzD
      hp'z.symm
    have hzL : (x * p) ^ 2 ∈ rootGroup D a ⊔ rootGroup D d := by
      rcases mem_rootSet_or_collinear_of_mem_twoCore hclass hD (oppositeDetermines_of_hyp h) hc
          hs (nCoreCommutatorInRoot_of_hyp h hc) hp' hzD hzQ with hzT | ⟨hp'z', hp'zD⟩
      · rw [← hLeq]
        exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D p' hzT)
      · rw [← hLeq]
        exact mem_sup_of_collinear_of_lineTI h hc hs hp hp' hpp' hpp'D hT
          (hAll p hp p' hp' hpp' hpp'D hT) hzD hpz.symm hzpD hp'z'.symm
          (by rw [← hp'z'.eq]; exact hp'zD)
    exact not_commute_of_collinear hD hb hzD hbx hoddbx hxz hxzD
      (commute_of_mem_sup_rootGroup ha hd had hbL hzL)
  have hopp := opposite_of_lineTI h hc hs hx hp hp' h4 hpp' hwz hLz
  rw [h4'] at hopp
  exact absurd hopp.2 (by decide)

theorem exists_mem_line_special_of_orderOf_eq_three {a d : G} (ha : a ∈ D) (hd : d ∈ D)
    (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a) {x a' d' : G} (hx : x ∈ D)
    (ha' : a' ∈ rootSet D a) (hd' : d' ∈ rootSet D d) (h3a : orderOf (x * a') = 3)
    (h3d : orderOf (x * d') = 3) :
    ∃ p ∈ D, p ∈ rootGroup D a ⊔ rootGroup D d ∧ orderOf (x * p) = 4 := by
  have hD := h.root
  have ha'd' : Commute a' d' := commute_of_mem_rootSet_of_commute hd ha' hd' had
  have hne : a' ≠ d' := fun e => by
    have e1 : rootSet D d' = rootSet D a := rootSet_eq_of_mem (e ▸ ha')
    have e2 : rootSet D d' = rootSet D d := rootSet_eq_of_mem hd'
    exact hdT (by rw [← e1, e2]; exact mem_rootSet_self hd)
  have hp3 : ∀ {y : G}, orderOf (x * y) = 3 → (y * x) ^ 3 = 1 := fun hy => by
    rw [← hy, orderOf_mul_comm_eq]; exact pow_orderOf_eq_one _
  refine ⟨a' * d', mul_mem_of_mem_rootGroup h hc hs (nCoreCommutatorInRoot_of_hyp h hc) ha hd had
    hadD hdT (rootSet_subset_rootGroup D a ha') (rootSet_subset_rootGroup D d hd')
    (Or.inl (hD.ne_one ha'.1)), Subgroup.mul_mem _
    (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a ha'))
    (Subgroup.mem_sup_right (rootSet_subset_rootGroup D d hd')), ?_⟩
  exact orderOf_mul_mul_eq_four_of_pow_three (hD.mul_self_eq_one ha'.1)
    (hD.mul_self_eq_one hd'.1) (hD.mul_self_eq_one hx) ha'd' hne (hp3 h3a) (hp3 h3d)

end CFSG.Timmesfeld.Bridge
