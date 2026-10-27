
module

public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocalBase

public import CFSG.Monster.B.TwoA.Base.GeomRes

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open scoped Pointwise

theorem Eam_inf_Xgrp :
    Eam ⊓ Xgrp = P4 := by
  apply le_antisymm
  · rintro x ⟨hE, hX⟩
    exact ⟨hX, Eam_le_centralizer hE⟩
  · intro x hx
    exact ⟨Pc_le_Eam 3 hx, hx.1⟩

@[expose] def a0 :
    Dfull := exists_mem_Ehat_not_mem_N1.choose

theorem a0_mem_Ehat :
    a0 ∈ Ehat := exists_mem_Ehat_not_mem_N1.choose_spec.1

theorem a0_not_mem_N1 :
    a0 ∉ N1 := exists_mem_Ehat_not_mem_N1.choose_spec.2

abbrev a0S :
    Shat := elS a0_mem_Ehat

@[expose] def toS
    (e : Eam) : Shat := ⟨e, Eam_le_Shat e.2⟩

theorem coe_toS
    (e : Eam) : ((toS e : Shat) : Dfull) = e := rfl

theorem toS_mul
    (e f : Eam) : toS (e * f) = toS e * toS f := rfl

theorem toS_one :
    toS 1 = 1 := rfl

theorem a0_not_mem_Eam :
    a0 ∉ Eam := not_mem_Eam_of a0_mem_Ehat a0_not_mem_N1

theorem cvOf_toS_mul
    (e : Eam) (g : Shat) : cvOf (toS e * g) = cvOf g := by
  rw [cvOf_eq_iff]
  have : ((g * (toS e * g)⁻¹ : Shat) : Dfull) = (e : Dfull)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toS]
    group
  rw [this]
  exact Eam.inv_mem e.2

theorem cvOf_toS
    (e : Eam) : cvOf (toS e) = cv0 := by
  have h := cvOf_toS_mul e 1
  rwa [mul_one] at h

theorem adj_cv0_iff
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) (g : Shat) :
    cgraph.Adj cv0 (cvOf g) ↔ ∃ e : Eam, cvOf g = cvOf (elS ha * toS e) := by
  rw [cv0, cgraph_adj_iff]
  simp only [inv_one, mul_one]
  constructor
  · rintro ⟨-, hs⟩
    obtain ⟨x, hx, y, hy, e⟩ := (mem_stepSet_iff ha hn).1 hs
    refine ⟨⟨y, hy⟩, ?_⟩
    have hg : g = toS ⟨x, hx⟩ * (elS ha * toS ⟨y, hy⟩) := Subtype.ext (by
      simp only [Subgroup.coe_mul, coe_toS, coe_elS]
      rw [e, mul_assoc])
    rw [hg, cvOf_toS_mul]
  · rintro ⟨e, he⟩
    have hx : ((elS ha * toS e * g⁻¹ : Shat) : Dfull) ∈ Eam := cvOf_eq_iff.1 he
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toS, coe_elS] at hx
    refine ⟨fun h => not_mem_Eam_of ha hn ?_,
      (mem_stepSet_iff ha hn).2 ⟨_, Eam.inv_mem hx, e, e.2, by group⟩⟩
    have h' : (g : Dfull) ∈ Eam := (cvOf_eq_cv0_iff g).1 h.symm
    have h2 := Eam.mul_mem (Eam.mul_mem hx h') (Eam.inv_mem e.2)
    rwa [show a * (e : Dfull) * (g : Dfull)⁻¹ * g * (e : Dfull)⁻¹ = a by group] at h2

theorem adj_cv0_elS
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) : cgraph.Adj cv0 (cvOf (elS ha)) :=
  (adj_cv0_iff ha hn _).2 ⟨1, by rw [toS_one, mul_one]⟩

theorem coe_nbr_quot
    {a : Dfull} (ha : a ∈ Ehat) (e f : Eam) :
    ((elS ha * toS f * (elS ha * toS e)⁻¹ : Shat) : Dfull) =
      a * ((f * e⁻¹ : Eam) : Dfull) * a⁻¹ := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_toS, coe_elS]
  group

theorem nbr_congr
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) {e f : Eam}
    (h : ((f * e⁻¹ : Eam) : Dfull) ∈ Pc 0) : cvOf (elS ha * toS e) = cvOf (elS ha * toS f) := by
  rw [cvOf_eq_iff, coe_nbr_quot]
  exact Pc_le_Eam 0 (conj_mem_Pc_zero ha hn h)

@[expose] def nbr
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) : P1Cos → CVert :=
  Quotient.lift (fun e : Eam => cvOf (elS ha * toS e)) fun _ _ h => nbr_congr ha hn (p1rel_iff.1 h)

theorem nbr_mk
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) (e : Eam) :
    nbr ha hn (Quotient.mk _ e) = cvOf (elS ha * toS e) := rfl

theorem nbr_injective
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    Function.Injective (nbr ha hn) := by
  intro u w h
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective w
  rw [nbr_mk, nbr_mk, cvOf_eq_iff, coe_nbr_quot] at h
  refine Quotient.sound (p1rel_iff.2 ?_)
  have hmem : ((f * e⁻¹ : Eam) : Dfull) ∈ Eam ⊓ Eam.map (MulAut.conj a⁻¹).toMonoidHom :=
    ⟨(f * e⁻¹).2, mem_conj_iff.2 h⟩
  rw [Eam_inf_conj ha hn] at hmem
  exact hmem

theorem nbr_adj
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) (u : P1Cos) :
    cgraph.Adj cv0 (nbr ha hn u) := by
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  rw [nbr_mk, adj_cv0_iff ha hn]
  exact ⟨e, rfl⟩

theorem exists_nbr_of_adj
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) {w : CVert}
    (h : cgraph.Adj cv0 w) : ∃ u, nbr ha hn u = w := by
  obtain ⟨g, rfl⟩ := cvOf_surjective w
  obtain ⟨e, he⟩ := (adj_cv0_iff ha hn g).1 h
  exact ⟨Quotient.mk _ e, he.symm⟩

@[expose] def nbrEquiv
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    P1Cos ≃ cgraph.neighborSet cv0 :=
  Equiv.ofBijective (fun u => ⟨nbr ha hn u, nbr_adj ha hn u⟩)
    ⟨fun _ _ h => nbr_injective ha hn (congrArg Subtype.val h), fun w => by
      obtain ⟨u, hu⟩ := exists_nbr_of_adj ha hn w.2
      exact ⟨u, Subtype.ext hu⟩⟩

theorem coe_nbrEquiv
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) (u : P1Cos) :
    (nbrEquiv ha hn u : CVert) = nbr ha hn u := rfl

theorem nbr_mk_mul
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) (e f : Eam) :
    nbr ha hn (Quotient.mk _ (e * f)) = cvMul (nbr ha hn (Quotient.mk _ e)) (toS f) := by
  rw [nbr_mk, nbr_mk, cvMul_cvOf, toS_mul, mul_assoc]

theorem natCard_neighborSet_cv0 :
    Nat.card (cgraph.neighborSet cv0) = ((Pc 0).subgroupOf Eam).index := by
  rw [← Nat.card_congr (nbrEquiv a0_mem_Ehat a0_not_mem_N1), Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]

@[expose] def cvIso
    (s : Shat) : cgraph ≃g cgraph where
  toFun v := cvMul v s
  invFun v := cvMul v s⁻¹
  left_inv v := by simp only [← cvMul_mul, mul_inv_cancel, cvMul_one]
  right_inv v := by simp only [← cvMul_mul, inv_mul_cancel, cvMul_one]
  map_rel_iff' := cgraph_adj_cvMul _ _ s

theorem reachable_cvMul
    {v w : CVert} (h : cgraph.Reachable v w) (s : Shat) :
    cgraph.Reachable (cvMul v s) (cvMul w s) :=
  h.map (cvIso s).toHom

theorem reachable_cv0
    (g : Shat) : cgraph.Reachable cv0 (cvOf g) := by
  have hcl := closure_Eam_eq a0_mem_Ehat a0_not_mem_N1
  have key : ∀ x : Dfull, x ∈ Subgroup.closure (insert a0 (Eam : Set Dfull)) →
      ∀ hS : x ∈ Shat, cgraph.Reachable cv0 (cvOf ⟨x, hS⟩) := by
    intro x hx
    induction hx using Subgroup.closure_induction_right with
    | one => exact fun _ => SimpleGraph.Reachable.refl _
    | mul_right x hx y hy ih =>
      intro hS
      have hxS : x ∈ Shat := hcl ▸ hx
      have hyS : y ∈ Shat := by
        rcases hy with rfl | hy
        · exact Ehat_le_Shat a0_mem_Ehat
        · exact Eam_le_Shat hy
      have h1 := reachable_cvMul (ih hxS) ⟨y, hyS⟩
      have e2 : cvMul (cvOf ⟨x, hxS⟩) ⟨y, hyS⟩ = cvOf ⟨x * y, hS⟩ := rfl
      rw [e2, cv0, cvMul_cvOf, one_mul] at h1
      refine SimpleGraph.Reachable.trans ?_ h1
      rcases hy with rfl | hy
      · exact (adj_cv0_elS a0_mem_Ehat a0_not_mem_N1).reachable
      · rw [show (⟨y, hyS⟩ : Shat) = toS ⟨y, hy⟩ from rfl, cvOf_toS]
    | mul_inv_cancel x hx y hy ih =>
      intro hS
      have hxS : x ∈ Shat := hcl ▸ hx
      have hyS : y ∈ Shat := by
        rcases hy with rfl | hy
        · exact Ehat_le_Shat a0_mem_Ehat
        · exact Eam_le_Shat hy
      have h1 := reachable_cvMul (ih hxS) (⟨y, hyS⟩ : Shat)⁻¹
      have e2 : cvMul (cvOf ⟨x, hxS⟩) (⟨y, hyS⟩ : Shat)⁻¹ = cvOf ⟨x * y⁻¹, hS⟩ := rfl
      rw [e2, cv0, cvMul_cvOf, one_mul] at h1
      refine SimpleGraph.Reachable.trans ?_ h1
      rcases hy with rfl | hy
      · have h3 := (cgraph_adj_cvMul cv0 (cvOf a0S) a0S⁻¹).2
          (adj_cv0_elS a0_mem_Ehat a0_not_mem_N1)
        rw [cv0, cvMul_cvOf, cvMul_cvOf, one_mul, mul_inv_cancel] at h3
        exact h3.symm.reachable
      · rw [show (⟨y, hyS⟩ : Shat)⁻¹ = toS ⟨y, hy⟩⁻¹ from rfl, cvOf_toS]
  exact key g (hcl.symm ▸ g.2) g.2

theorem cgraph_connected :
    cgraph.Connected := by
  have : Nonempty CVert := ⟨cv0⟩
  refine SimpleGraph.Connected.mk fun v w => ?_
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  obtain ⟨h, rfl⟩ := cvOf_surjective w
  exact (reachable_cv0 g).symm.trans (reachable_cv0 h)

theorem adj_cv0_of_adj
    {v w : CVert} {s : Shat} (hs : cvMul v s = cv0) (h : cgraph.Adj v w) :
    cgraph.Adj cv0 (cvMul w s) := by
  rw [← hs]
  exact (cgraph_adj_cvMul _ _ _).2 h

theorem cvMul_edge_transitive
    {v w v' w' : CVert} (h : cgraph.Adj v w) (h' : cgraph.Adj v' w') :
    ∃ s : Shat, cvMul v s = v' ∧ cvMul w s = w' := by
  obtain ⟨s₁, hs₁⟩ := cvMul_transitive v cv0
  obtain ⟨s₂, hs₂⟩ := cvMul_transitive v' cv0
  obtain ⟨u₁, hu₁⟩ := exists_nbr_of_adj a0_mem_Ehat a0_not_mem_N1 (adj_cv0_of_adj hs₁ h)
  obtain ⟨u₂, hu₂⟩ := exists_nbr_of_adj a0_mem_Ehat a0_not_mem_N1 (adj_cv0_of_adj hs₂ h')
  obtain ⟨e₁, rfl⟩ := Quotient.mk_surjective u₁
  obtain ⟨e₂, rfl⟩ := Quotient.mk_surjective u₂
  refine ⟨s₁ * toS (e₁⁻¹ * e₂) * s₂⁻¹, ?_, ?_⟩
  · rw [cvMul_mul, cvMul_mul, hs₁, cv0, cvMul_cvOf, one_mul, cvOf_toS, ← hs₂, cvMul_inv_cancel]
  · have e3 := nbr_mk_mul a0_mem_Ehat a0_not_mem_N1 e₁ (e₁⁻¹ * e₂)
    rw [mul_inv_cancel_left, hu₁, hu₂] at e3
    rw [cvMul_mul, cvMul_mul, ← e3, cvMul_inv_cancel]

theorem cvMul_faithful
    (s : Shat) (h : ∀ v, cvMul v s = v) : s = 1 := by
  have hK : s ∈ (Eam.subgroupOf Shat).normalCore := fun g => by
    have h1 := h (cvOf g)
    rw [cvMul_cvOf, cvOf_eq_iff] at h1
    rw [Subgroup.mem_subgroupOf]
    have e1 : ((g * (g * s)⁻¹ : Shat) : Dfull) = ((g * s * g⁻¹ : Shat) : Dfull)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1] at h1
    have h2 := Eam.inv_mem h1
    rwa [inv_inv] at h2
  rcases (Subgroup.normalCore_normal (Eam.subgroupOf Shat)).eq_bot_or_eq_top with hb | ht
  · rw [hb] at hK
    exact hK
  · exfalso
    have ha : a0S ∈ (Eam.subgroupOf Shat).normalCore := by
      rw [ht]
      exact Subgroup.mem_top a0S
    exact a0_not_mem_Eam (Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ ha))

theorem clabel_nbr
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) (e : Eam) :
    clabel (nbr ha hn (Quotient.mk _ e)) = cQ * ((e : Dfull)⁻¹ * xhat * e) := by
  rw [nbr_mk, clabel_cvOf]
  have h1 := conj_cQ_of_not_mem ha hn
  simp only [Subgroup.coe_mul, coe_toS, coe_elS]
  calc (a * e)⁻¹ * cQ * (a * e) = (e : Dfull)⁻¹ * (a⁻¹ * cQ * a) * e := by group
    _ = (e : Dfull)⁻¹ * (cQ * xhat) * e := by rw [h1]
    _ = cQ * ((e : Dfull)⁻¹ * xhat * e) := by
        rw [← mul_assoc, ← mul_assoc, conj_inv_cQ e.2]
        group

theorem clabel_nbr_injective
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    Function.Injective (fun u => clabel (nbr ha hn u)) := by
  intro u w h
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨f, rfl⟩ := Quotient.mk_surjective w
  simp only [clabel_nbr] at h
  have h' := mul_left_cancel h
  refine Quotient.sound (p1rel_iff.2 ?_)
  rw [← Eam_inf_centralizer_xhat]
  refine ⟨(f * e⁻¹).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc (f : Dfull) * (e : Dfull)⁻¹ * xhat
      = f * ((e : Dfull)⁻¹ * xhat * e) * (e : Dfull)⁻¹ := by group
    _ = f * ((f : Dfull)⁻¹ * xhat * f) * (e : Dfull)⁻¹ := by rw [h']
    _ = xhat * (f * (e : Dfull)⁻¹) := by group

theorem clabel_injOn_neighborSet
    (v : CVert) : Set.InjOn clabel (cgraph.neighborSet v) := by
  obtain ⟨s, hs⟩ := cvMul_transitive v cv0
  intro w₁ h₁ w₂ h₂ h
  obtain ⟨u₁, hu₁⟩ := exists_nbr_of_adj a0_mem_Ehat a0_not_mem_N1 (adj_cv0_of_adj hs h₁)
  obtain ⟨u₂, hu₂⟩ := exists_nbr_of_adj a0_mem_Ehat a0_not_mem_N1 (adj_cv0_of_adj hs h₂)
  have hl : clabel (nbr a0_mem_Ehat a0_not_mem_N1 u₁) =
      clabel (nbr a0_mem_Ehat a0_not_mem_N1 u₂) := by
    rw [hu₁, hu₂, clabel_cvMul, clabel_cvMul, h]
  have hu := clabel_nbr_injective a0_mem_Ehat a0_not_mem_N1 hl
  have e1 : cvMul w₁ s = cvMul w₂ s := by rw [← hu₁, ← hu₂, hu]
  have e2 := congrArg (fun z => cvMul z s⁻¹) e1
  simpa only [cvMul_inv_cancel] using e2

theorem clabel_adj
    {v w : CVert} (h : cgraph.Adj v w) :
    clabel v ≠ clabel w ∧ clabel v * clabel w = clabel w * clabel v ∧
      clabel v * clabel v = 1 ∧ clabel w * clabel w = 1 ∧
      ∃ s : Shat, clabel v * clabel w = (s : Dfull)⁻¹ * xhat * s := by
  obtain ⟨s, hs⟩ := cvMul_transitive v cv0
  obtain ⟨u, hu⟩ := exists_nbr_of_adj a0_mem_Ehat a0_not_mem_N1 (adj_cv0_of_adj hs h)
  obtain ⟨e, rfl⟩ := Quotient.mk_surjective u
  have hv : v = cvMul cv0 s⁻¹ := by rw [← hs, cvMul_inv_cancel]
  have hw : w = cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) s⁻¹ := by
    rw [hu, cvMul_inv_cancel]
  rw [hv, hw, clabel_cvMul, clabel_cvMul, clabel_nbr, clabel_cv0]
  obtain ⟨t, ht⟩ : ∃ t : Dfull, ((s⁻¹ : Shat) : Dfull) = t := ⟨_, rfl⟩
  rw [ht]
  set y := (e : Dfull)⁻¹ * xhat * e with hy
  have hyc : y * cQ = cQ * y := by
    have hc : (e : Dfull) * cQ = cQ * e :=
      Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer e.2)
    have hx : xhat * cQ = cQ * xhat := (xhat_comm_of_mem_Jhat (Ehat_le_Jhat cQ_mem_Ehat)).symm
    calc y * cQ = (e : Dfull)⁻¹ * xhat * (e * cQ) := by rw [hy]; group
      _ = (e : Dfull)⁻¹ * (xhat * cQ) * e := by rw [hc]; group
      _ = ((e : Dfull)⁻¹ * cQ) * xhat * e := by rw [hx]; group
      _ = cQ * y := by rw [conj_inv_cQ e.2, hy]; group
  have hy2 : y * y = 1 := by
    rw [hy, show (e : Dfull)⁻¹ * xhat * e * ((e : Dfull)⁻¹ * xhat * e) =
      (e : Dfull)⁻¹ * (xhat * xhat) * e by group, xhat_mul_self, mul_one, inv_mul_cancel]
  have hy1 : y ≠ 1 := by
    intro h1
    apply xhat_ne_one
    have h2 : (e : Dfull) * y * (e : Dfull)⁻¹ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    rw [hy] at h2
    rwa [show (e : Dfull) * ((e : Dfull)⁻¹ * xhat * e) * (e : Dfull)⁻¹ = xhat by group] at h2
  have hc2 := cQ_mul_self
  have hprod : (t⁻¹ * cQ * t) * (t⁻¹ * (cQ * y) * t) = t⁻¹ * y * t := by
    rw [show (t⁻¹ * cQ * t) * (t⁻¹ * (cQ * y) * t) = t⁻¹ * (cQ * cQ) * y * t by group, hc2,
      mul_one]
  have hprod' : (t⁻¹ * (cQ * y) * t) * (t⁻¹ * cQ * t) = t⁻¹ * y * t := by
    rw [show (t⁻¹ * (cQ * y) * t) * (t⁻¹ * cQ * t) = t⁻¹ * cQ * (y * cQ) * t by group, hyc,
      show t⁻¹ * cQ * (cQ * y) * t = t⁻¹ * (cQ * cQ) * y * t by group, hc2, mul_one]
  refine ⟨?_, hprod.trans hprod'.symm, ?_, ?_, ?_⟩
  · intro h1
    apply hy1
    have h2 : t * (t⁻¹ * cQ * t) * t⁻¹ = t * (t⁻¹ * (cQ * y) * t) * t⁻¹ := by rw [h1]
    rw [show t * (t⁻¹ * cQ * t) * t⁻¹ = cQ by group,
      show t * (t⁻¹ * (cQ * y) * t) * t⁻¹ = cQ * y by group] at h2
    have h3 : cQ * y = cQ * 1 := by rw [← h2, mul_one]
    exact mul_left_cancel h3
  · rw [show (t⁻¹ * cQ * t) * (t⁻¹ * cQ * t) = t⁻¹ * (cQ * cQ) * t by group, hc2, mul_one,
      inv_mul_cancel]
  · rw [show (t⁻¹ * (cQ * y) * t) * (t⁻¹ * (cQ * y) * t) = t⁻¹ * cQ * (y * cQ) * y * t by group,
      hyc, show t⁻¹ * cQ * (cQ * y) * y * t = t⁻¹ * (cQ * cQ) * (y * y) * t by group,
      hc2, hy2, mul_one, mul_one, inv_mul_cancel]
  · refine ⟨toS e * s⁻¹, ?_⟩
    rw [hprod, Subgroup.coe_mul, ht, coe_toS, hy]
    group

theorem natCard_fiber
    (v : CVert) : Nat.card (clabel ⁻¹' {clabel v}) = EinC.index := by
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  rw [← natCard_fiber_cQ]
  refine Nat.card_congr (Equiv.subtypeEquiv (cvIso s⁻¹).toEquiv fun w => ?_)
  show clabel w = clabel v ↔ clabel (cvMul w s⁻¹) = cQ
  rw [clabel_cvMul, ← hs, clabel_cvMul, clabel_cv0]
  constructor
  · intro h
    rw [h]
    simp only [Subgroup.coe_inv, inv_inv]
    group
  · intro h
    have h2 : (s : Dfull)⁻¹ * (((s⁻¹ : Shat) : Dfull)⁻¹ * clabel w * (s⁻¹ : Shat)) * s =
        (s : Dfull)⁻¹ * cQ * s := by rw [h]
    simp only [Subgroup.coe_inv, inv_inv] at h2
    rw [← h2]
    group

theorem ncard_cSigma :
    (cSigma 1).ncard = 120 := by
  have hinj : Set.InjOn clabel (cSigma 1) := by
    intro v hv w hw h
    obtain ⟨x₁, hx₁, rfl⟩ := mem_cSigma_one.1 hv
    obtain ⟨x₂, hx₂, rfl⟩ := mem_cSigma_one.1 hw
    rw [clabel_cvOf, clabel_cvOf] at h
    exact (cvOf_eq_iff_of_X hx₁ hx₂).2 h
  have himg : clabel '' cSigma 1 = cOrbit := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, hx, rfl⟩ := mem_cSigma_one.1 hv
      rw [clabel_cvOf]
      exact mem_cOrbit_conj hx
    · rintro ⟨x, hx, rfl⟩
      refine ⟨cvOf ⟨x⁻¹, Xgrp_le_Shat (Xgrp.inv_mem hx)⟩,
        mem_cSigma_one.2 ⟨_, Xgrp.inv_mem hx, rfl⟩, ?_⟩
      rw [clabel_cvOf]
      simp only [inv_inv]
  rw [← hinj.ncard_image, himg, cOrbit, ncard_orbit_cQ]

theorem cSigma_isClique
    {v w : CVert} (hv : v ∈ cSigma 1) (hw : w ∈ cSigma 1) (hne : v ≠ w) :
    cgraph.Adj v w := by
  obtain ⟨x₁, hx₁, rfl⟩ := mem_cSigma_one.1 hv
  obtain ⟨x₂, hx₂, rfl⟩ := mem_cSigma_one.1 hw
  have haX : a0 ∈ Xgrp := Ehat_le_Xgrp a0_mem_Ehat
  have hy₁ : cQ ∈ cOrbit := ⟨1, Xgrp.one_mem, by rw [one_mul, inv_one, mul_one]⟩
  have h34 : (x₁ : Dfull)⁻¹ * cQ * x₁ ≠ (x₂ : Dfull)⁻¹ * cQ * x₂ := fun h =>
    hne ((cvOf_eq_iff_of_X hx₁ hx₂).2 h)
  obtain ⟨z, hz, hz1, hz2⟩ := cOrbit_two_transitive hy₁ (mem_cOrbit_conj haX)
    (mem_cOrbit_conj hx₁) (mem_cOrbit_conj hx₂) (cQ_ne_conj a0_mem_Ehat a0_not_mem_N1) h34
  have hxX : z⁻¹ ∈ Xgrp := Xgrp.inv_mem hz
  have e1 : cvOf ⟨z⁻¹, Xgrp_le_Shat hxX⟩ = cvOf x₁ := by
    rw [cvOf_eq_iff_of_X hxX hx₁]
    show (z⁻¹)⁻¹ * cQ * z⁻¹ = _
    rw [inv_inv, hz1]
  have e2 : cvOf (a0S * ⟨z⁻¹, Xgrp_le_Shat hxX⟩) = cvOf x₂ := by
    rw [cvOf_eq_iff_of_X (Xgrp.mul_mem haX hxX) hx₂]
    show (a0 * z⁻¹)⁻¹ * cQ * (a0 * z⁻¹) = _
    rw [← hz2]
    group
  rw [← e1, ← e2, ← cvMul_cvOf, ← one_mul (⟨z⁻¹, _⟩ : Shat), ← cvMul_cvOf, one_mul]
  exact (cgraph_adj_cvMul _ _ _).2 (adj_cv0_elS a0_mem_Ehat a0_not_mem_N1)

theorem cSigma_diff_cv0
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    cSigma 1 \ {cv0} = {v | ∃ p : Eam, (p : Dfull) ∈ P4 ∧ v = cvOf (elS ha * toS p)} := by
  have haX : a ∈ Xgrp := Ehat_le_Xgrp ha
  have hy₁ : cQ ∈ cOrbit := ⟨1, Xgrp.one_mem, by rw [one_mul, inv_one, mul_one]⟩
  ext v
  constructor
  · rintro ⟨hv, hv0⟩
    obtain ⟨x₂, hx₂, rfl⟩ := mem_cSigma_one.1 hv
    have h34 : cQ ≠ (x₂ : Dfull)⁻¹ * cQ * x₂ := by
      intro h
      apply hv0
      rw [Set.mem_singleton_iff, cv0, cvOf_eq_iff_of_X hx₂ (Xgrp.one_mem), ← h]
      simp
    obtain ⟨z, hz, hz1, hz2⟩ := cOrbit_two_transitive hy₁ (mem_cOrbit_conj haX) hy₁
      (mem_cOrbit_conj hx₂) (cQ_ne_conj ha hn) h34
    have hzc : z⁻¹ * cQ = cQ * z⁻¹ := by
      calc z⁻¹ * cQ = z⁻¹ * (z * cQ * z⁻¹) := by rw [hz1]
        _ = cQ * z⁻¹ := by group
    have hzP : z⁻¹ ∈ P4 := ⟨Xgrp.inv_mem hz, Subgroup.mem_centralizer_singleton_iff.2 hzc⟩
    refine ⟨⟨z⁻¹, Pc_le_Eam 3 hzP⟩, hzP, ?_⟩
    rw [cvOf_eq_iff_of_X hx₂ (Xgrp.mul_mem haX hzP.1)]
    show _ = (a * z⁻¹)⁻¹ * cQ * (a * z⁻¹)
    rw [← hz2]
    group
  · rintro ⟨p, hp, rfl⟩
    refine ⟨mem_cSigma_one.2 ⟨elS ha * toS p, Xgrp.mul_mem haX hp.1, rfl⟩, ?_⟩
    rw [Set.mem_singleton_iff, cvOf_eq_cv0_iff]
    intro h
    apply not_mem_Eam_of ha hn
    have h2 := Eam.mul_mem h (Eam.inv_mem p.2)
    rw [Subgroup.coe_mul, coe_toS, mul_inv_cancel_right] at h2
    exact h2

end CFSG.Monster.B.TwoA.Amalgam
