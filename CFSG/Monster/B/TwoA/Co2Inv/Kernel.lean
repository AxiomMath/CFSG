
module

public import CFSG.Monster.B.TwoA.Co2Inv.KernelBase

public import CFSG.Monster.B.TwoA.Co2Inv.KerFix

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

theorem qElt_comm_iff
    {e l t e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16)
    (he' : e' < 2) (hl' : l' < 16) (ht' : t' < 16) :
    qElt e l t * qElt e' l' t' = qElt e' l' t' * qElt e l t ↔
      par4 (l' &&& t) = par4 (l &&& t') := by
  rw [qElt_mul he hl ht he' hl' ht', qElt_mul he' hl' ht' he hl ht]
  constructor
  · intro h
    obtain ⟨h1, -, -⟩ := qElt_inj (xor_lt_two (xor_lt_two he he') (par4_lt _))
      (xor_lt_sixteen hl hl') (xor_lt_sixteen ht ht') (xor_lt_two (xor_lt_two he' he) (par4_lt _))
      (xor_lt_sixteen hl' hl) (xor_lt_sixteen ht' ht) h
    rw [Nat.xor_comm e' e] at h1
    exact xor_left_cancel' h1
  · intro h
    rw [h, Nat.xor_comm e e', Nat.xor_comm l l', Nat.xor_comm t t']

theorem qElt_inv_mul_same
    {a b L T : ℕ} (ha : a < 2) (hb : b < 2) (hL : L < 16) (hT : T < 16) :
    (qElt a L T)⁻¹ * qElt b L T = qElt (a ^^^ b) 0 0 := by
  rw [qElt_inv ha hL hT, qElt_mul (xor_lt_two ha (par4_lt _)) hL hT hb hL hT, xor_four,
    Nat.xor_self, Nat.xor_self]

@[expose] def qQ
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) : Qgrp :=
  ⟨qElt e l t, mem_Qgrp_iff.2 ⟨e, he, l, hl, t, ht, rfl⟩⟩

theorem exists_qQ
    (x : Qgrp) : ∃ e, ∃ he : e < 2, ∃ l, ∃ hl : l < 16, ∃ t, ∃ ht : t < 16,
    x = qQ he hl ht := by
  obtain ⟨e, he, l, hl, t, ht, h⟩ := mem_Qgrp_iff.1 x.2
  exact ⟨e, he, l, hl, t, ht, Subtype.ext h⟩

theorem qQ_mul
    {e l t e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) (he' : e' < 2)
    (hl' : l' < 16) (ht' : t' < 16) :
    qQ he hl ht * qQ he' hl' ht' = qQ (xor_lt_two (xor_lt_two he he') (par4_lt (l' &&& t)))
      (xor_lt_sixteen hl hl') (xor_lt_sixteen ht ht') :=
  Subtype.ext (qElt_mul he hl ht he' hl' ht')

theorem qQ_inj
    {e l t e' l' t' : ℕ} {he : e < 2} {hl : l < 16} {ht : t < 16} {he' : e' < 2}
    {hl' : l' < 16} {ht' : t' < 16} (h : qQ he hl ht = qQ he' hl' ht') :
    e = e' ∧ l = l' ∧ t = t' :=
  qElt_inj he hl ht he' hl' ht' (congrArg Subtype.val h)

theorem qQ_zero
    {he : 0 < 2} {hl : 0 < 16} {ht : 0 < 16} : qQ he hl ht = 1 :=
  Subtype.ext qElt_zero

theorem qQ_comm_iff
    {e l t e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) (he' : e' < 2)
    (hl' : l' < 16) (ht' : t' < 16) :
    qQ he hl ht * qQ he' hl' ht' = qQ he' hl' ht' * qQ he hl ht ↔
      par4 (l' &&& t) = par4 (l &&& t') :=
  Subtype.ext_iff.trans (qElt_comm_iff he hl ht he' hl' ht')

@[expose] def rQ :
    Qgrp := qQ (e := 1) (l := 0) (t := 0) (by norm_num) (by norm_num) (by norm_num)

theorem coe_rQ :
    ((rQ : Qgrp) : OLq) = (rK : OLq) := qElt_one_zero_zero

theorem rQ_ne_one :
    rQ ≠ 1 := by
  intro h
  rw [← qQ_zero (he := by norm_num) (hl := by norm_num) (ht := by norm_num)] at h
  exact absurd (qQ_inj h).1 (by norm_num)

theorem rQ_mem_center :
    rQ ∈ Subgroup.center Qgrp := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ g
  refine (qQ_comm_iff he hl ht (by norm_num) (by norm_num) (by norm_num)).2 ?_
  rw [par4_zero_left t ht, par4_zero_right l hl]

theorem qQ_mem_center
    {e : ℕ} (he : e < 2) {hl : 0 < 16} {ht : 0 < 16} :
    qQ he hl ht ∈ Subgroup.center Qgrp := by
  rcases eq_zero_or_one he with rfl | rfl
  · rw [qQ_zero]
    exact Subgroup.one_mem _
  · exact rQ_mem_center

theorem mem_center_Qgrp_iff
    (x : Qgrp) : x ∈ Subgroup.center Qgrp ↔ x = 1 ∨ x = rQ := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h
    obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
    have ht0 : t = 0 := par4_sep_right t ht fun l' hl' => by
      have := (qQ_comm_iff (by norm_num : 0 < 2) hl' (by norm_num : 0 < 16) he hl ht).1 (h _)
      rw [par4_zero_right l hl] at this
      exact this.symm
    have hl0 : l = 0 := par4_sep_left l hl fun t' ht' => by
      have := (qQ_comm_iff (by norm_num : 0 < 2) (by norm_num : 0 < 16) ht' he hl ht).1 (h _)
      rw [par4_zero_left t ht] at this
      exact this
    subst ht0
    subst hl0
    rcases eq_zero_or_one he with rfl | rfl
    · exact Or.inl qQ_zero
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact rQ_mem_center

theorem center_Qgrp_eq_zpowers :
    Subgroup.center Qgrp = Subgroup.zpowers rQ := by
  refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 rQ_mem_center)
  rcases (mem_center_Qgrp_iff x).1 hx with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _

theorem natCard_center_Qgrp :
    Nat.card (Subgroup.center Qgrp) = 2 := by
  have h : ((Subgroup.center Qgrp : Subgroup Qgrp) : Set Qgrp) = {1, rQ} := by
    ext x
    rw [SetLike.mem_coe, mem_center_Qgrp_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_pair rQ_ne_one.symm]

theorem comm_mem_center
    (x y : Qgrp) : (x * y)⁻¹ * (y * x) ∈ Subgroup.center Qgrp := by
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  obtain ⟨e', he', l', hl', t', ht', rfl⟩ := exists_qQ y
  rw [qQ_mul, qQ_mul]
  have h : (qQ (xor_lt_two (xor_lt_two he he') (par4_lt (l' &&& t))) (xor_lt_sixteen hl hl')
      (xor_lt_sixteen ht ht'))⁻¹ * qQ (xor_lt_two (xor_lt_two he' he) (par4_lt (l &&& t')))
      (xor_lt_sixteen hl' hl) (xor_lt_sixteen ht' ht) =
      qQ (xor_lt_two (xor_lt_two (xor_lt_two he he') (par4_lt (l' &&& t)))
        (xor_lt_two (xor_lt_two he' he) (par4_lt (l &&& t')))) (by norm_num : 0 < 16)
        (by norm_num : 0 < 16) := by
    apply Subtype.ext
    change (qElt _ _ _)⁻¹ * qElt _ _ _ = qElt _ _ _
    rw [Nat.xor_comm l' l, Nat.xor_comm t' t]
    exact qElt_inv_mul_same (xor_lt_two (xor_lt_two he he') (par4_lt _))
      (xor_lt_two (xor_lt_two he' he) (par4_lt _)) (xor_lt_sixteen hl hl')
      (xor_lt_sixteen ht ht')
  rw [h]
  exact qQ_mem_center _

theorem sq_mem_center
    (x : Qgrp) : x ^ 2 ∈ Subgroup.center Qgrp := by
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  have h : qQ he hl ht ^ 2 = qQ (par4_lt (l &&& t)) (by norm_num : 0 < 16)
      (by norm_num : 0 < 16) :=
    Subtype.ext ((pow_two _).trans (qElt_sq he hl ht))
  rw [h]
  exact qQ_mem_center _

theorem isElementaryAbelian_quotient_center :
    IsElementaryAbelian 2 (Qgrp ⧸ Subgroup.center Qgrp) := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        exact comm_mem_center x y
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact sq_mem_center x

theorem qQ_one_not_mem_center :
    qQ (e := 0) (l := 1) (t := 0) (by norm_num) (by norm_num) (by norm_num) ∉
      Subgroup.center Qgrp := by
  rw [mem_center_Qgrp_iff]
  rintro (h | h)
  · rw [← qQ_zero (he := by norm_num) (hl := by norm_num) (ht := by norm_num)] at h
    exact absurd (qQ_inj h).2.1 (by norm_num)
  · exact absurd (qQ_inj h).2.1 (by norm_num)

theorem isExtraspecial_Qgrp :
    CFSG.IsExtraspecial 2 Qgrp :=
  ⟨natCard_center_Qgrp, isElementaryAbelian_quotient_center,
    ⟨⟨QuotientGroup.mk (qQ (e := 0) (l := 1) (t := 0) (by norm_num) (by norm_num)
      (by norm_num)), 1, fun h => qQ_one_not_mem_center ((QuotientGroup.eq_one_iff _).1 h)⟩⟩⟩

theorem isExtraspecialPGroup_Qgrp :
    IsExtraspecialPGroup 2 Qgrp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Qgrp := Nat.finite_of_card_ne_zero (by rw [natCard_Qgrp]; norm_num)
  exact isExtraspecialPGroup_iff_isExtraspecial.2 isExtraspecial_Qgrp

theorem exists_params
    (x : Qgrp) : ∃ p : ℕ × ℕ × ℕ, p.1 < 2 ∧ p.2.1 < 16 ∧ p.2.2 < 16 ∧
    (x : OLq) = qElt p.1 p.2.1 p.2.2 := by
  obtain ⟨e, he, l, hl, t, ht, h⟩ := mem_Qgrp_iff.1 x.2
  exact ⟨(e, l, t), he, hl, ht, h⟩

@[expose] def qPar
    (x : Qgrp) : ℕ × ℕ × ℕ := (exists_params x).choose

theorem qPar_qQ
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    qPar (qQ he hl ht) = (e, l, t) := by
  obtain ⟨h1, h2, h3, h4⟩ := (exists_params (qQ he hl ht)).choose_spec
  obtain ⟨a, b, c⟩ := qElt_inj h1 h2 h3 he hl ht h4.symm
  exact Prod.ext a (Prod.ext b c)

@[expose] def phiFun
    (x : Qgrp) : Multiplicative ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  Multiplicative.ofAdd (bvec 4 (qPar x).2.1, bvec 4 (qPar x).2.2)

theorem phiFun_qQ
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    phiFun (qQ he hl ht) = Multiplicative.ofAdd (bvec 4 l, bvec 4 t) := by
  rw [phiFun, qPar_qQ]

theorem phiFun_mul
    (x y : Qgrp) : phiFun (x * y) = phiFun x * phiFun y := by
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  obtain ⟨e', he', l', hl', t', ht', rfl⟩ := exists_qQ y
  rw [qQ_mul, phiFun_qQ, phiFun_qQ, phiFun_qQ, bvec_xor, bvec_xor, ← ofAdd_add, Prod.mk_add_mk]

@[expose] def phiQ :
    Qgrp →* Multiplicative ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  MonoidHom.mk' phiFun phiFun_mul

theorem phiQ_qQ
    {e l t : ℕ} (he : e < 2) (hl : l < 16) (ht : t < 16) :
    phiQ (qQ he hl ht) = Multiplicative.ofAdd (bvec 4 l, bvec 4 t) :=
  phiFun_qQ he hl ht

theorem ker_phiQ :
    phiQ.ker = Subgroup.center Qgrp := by
  ext x
  rw [MonoidHom.mem_ker, mem_center_Qgrp_iff]
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  rw [phiQ_qQ]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd, toAdd_one, Prod.mk_eq_zero] at h'
    have hl0 := bvec4_eq_zero l hl h'.1
    have ht0 := bvec4_eq_zero t ht h'.2
    subst hl0
    subst ht0
    rcases eq_zero_or_one he with rfl | rfl
    · exact Or.inl qQ_zero
    · exact Or.inr rfl
  · rintro (h | h)
    · rw [← qQ_zero (he := by norm_num) (hl := by norm_num) (ht := by norm_num)] at h
      obtain ⟨-, rfl, rfl⟩ := qQ_inj h
      simp only [bvec_zero, Prod.mk_zero_zero, ofAdd_zero]
    · obtain ⟨-, rfl, rfl⟩ := qQ_inj h
      simp only [bvec_zero, Prod.mk_zero_zero, ofAdd_zero]

theorem phiQ_surjective :
    Function.Surjective phiQ := by
  have h1 : Nat.card (Subgroup.center Qgrp) * Nat.card phiQ.range = 512 :=
    (congrArg (· * Nat.card phiQ.range) (congrArg (fun H : Subgroup Qgrp => Nat.card H)
      ker_phiQ.symm)).trans ((natCard_ker_mul_range phiQ).trans natCard_Qgrp)
  have h2 : Nat.card phiQ.range = 256 := by
    have h3 : 2 * Nat.card phiQ.range = 2 * 256 :=
      ((congrArg (· * Nat.card phiQ.range) natCard_center_Qgrp.symm).trans h1).trans
        (by norm_num)
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_card_eq _ (h2.trans natCard_vec.symm))

theorem qQ_eq_rQ_pow
    {c : ℕ} (hc : c < 2) {hl : 0 < 16} {ht : 0 < 16} :
    qQ hc hl ht = rQ ^ c := by
  rcases eq_zero_or_one hc with rfl | rfl
  · rw [pow_zero]
    exact qQ_zero
  · rw [pow_one]
    rfl

theorem sq_eq_rQ_pow
    (x : Qgrp) :
    x ^ 2 = rQ ^ ((Multiplicative.toAdd (phiQ x)).1 ⬝ᵥ (Multiplicative.toAdd (phiQ x)).2).val := by
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  have h : qQ he hl ht ^ 2 = qQ (par4_lt (l &&& t)) (by norm_num : 0 < 16)
      (by norm_num : 0 < 16) :=
    Subtype.ext ((pow_two _).trans (qElt_sq he hl ht))
  rw [h, qQ_eq_rQ_pow, phiQ_qQ, toAdd_ofAdd, bvec_dotProduct_par4 l hl t ht,
    ZMod.val_cast_of_lt (par4_lt _)]

theorem mem_AQ_iff
    (x : Qgrp) : x ∈ AQ ↔ ∃ e, ∃ he : e < 2, ∃ l, ∃ hl : l < 16,
    x = qQ he hl (by norm_num : 0 < 16) := by
  rw [AQ, Subgroup.mem_subgroupOf, mem_Agrp_iff]
  constructor
  · rintro ⟨e, he, l, hl, h⟩
    exact ⟨e, he, l, hl, Subtype.ext h⟩
  · rintro ⟨e, he, l, hl, rfl⟩
    exact ⟨e, he, l, hl, rfl⟩

theorem isElementaryAbelian_AQ :
    IsElementaryAbelian 2 AQ := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨e, he, l, hl, ha⟩ := (mem_AQ_iff a).1 a.2
    obtain ⟨e', he', l', hl', hb⟩ := (mem_AQ_iff b).1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb]
    refine (qQ_comm_iff he hl (by norm_num) he' hl' (by norm_num)).2 ?_
    rw [par4_zero_right l' hl', par4_zero_right l hl]
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    obtain ⟨e, he, l, hl, ha⟩ := (mem_AQ_iff a).1 a.2
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ha, OneMemClass.coe_one]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, pow_two]
    change qElt e l 0 * qElt e l 0 = 1
    rw [qElt_sq he hl (by norm_num), par4_zero_right l hl, qElt_zero]

theorem natCard_AQ :
    Nat.card AQ = 32 := by
  rw [AQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Agrp ≤ Qgrp from le_sup_left)).toEquiv,
    natCard_Agrp]

theorem AQ_maximal
    (B : Subgroup Qgrp) (hAB : AQ ≤ B) (hB : IsElementaryAbelian 2 B) : B = AQ := by
  refine le_antisymm (fun x hx => ?_) hAB
  obtain ⟨e, he, l, hl, t, ht, rfl⟩ := exists_qQ x
  have ht0 : t = 0 := par4_sep_right t ht fun l' hl' => by
    have hmem : qQ (by norm_num : 0 < 2) hl' (by norm_num : 0 < 16) ∈ B :=
      hAB ((mem_AQ_iff _).2 ⟨0, by norm_num, l', hl', rfl⟩)
    have hc := congrArg Subtype.val (hB.toIsMulCommutative.is_comm.comm ⟨_, hmem⟩ ⟨_, hx⟩)
    have := (qQ_comm_iff (by norm_num : 0 < 2) hl' (by norm_num : 0 < 16) he hl ht).1 hc
    rw [par4_zero_right l hl] at this
    exact this.symm
  subst ht0
  exact (mem_AQ_iff _).2 ⟨e, he, l, hl, rfl⟩

theorem isElementaryAbelian_Tperm :
    IsElementaryAbelian 2 Tperm := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨t, ht, ha⟩ := mem_Tperm_iff.1 a.2
    obtain ⟨t', ht', hb⟩ := mem_Tperm_iff.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb, transP_mul ht' ht, transP_mul ht ht',
      Nat.xor_comm]
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    obtain ⟨t, ht, ha⟩ := mem_Tperm_iff.1 a.2
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ha, pow_two, transP_mul ht ht, Nat.xor_self, transP_zero,
      OneMemClass.coe_one]

theorem qElt_conj_T
    {t e l : ℕ} (ht : t < 16) (he : e < 2) (hl : l < 16) :
    qElt 0 0 t * qElt e l 0 * (qElt 0 0 t)⁻¹ = qElt (e ^^^ par4 (l &&& t)) l 0 := by
  have h1 : qElt 0 0 t * qElt e l 0 = qElt (e ^^^ par4 (l &&& t)) l t := by
    rw [qElt_mul (by norm_num : (0 : ℕ) < 2) (by norm_num : (0 : ℕ) < 16) ht he hl
      (by norm_num : (0 : ℕ) < 16)]
    simp only [Nat.zero_xor, Nat.xor_zero]
  have h2 : (qElt 0 0 t)⁻¹ = qElt 0 0 t := by
    rw [qElt_inv (by norm_num : (0 : ℕ) < 2) (by norm_num : (0 : ℕ) < 16) ht,
      par4_zero_left t ht, Nat.xor_zero]
  have h3 : qElt (e ^^^ par4 (l &&& t)) l t * qElt 0 0 t = qElt (e ^^^ par4 (l &&& t)) l 0 := by
    rw [qElt_mul (xor_lt_two he (par4_lt _)) hl ht (by norm_num : (0 : ℕ) < 2)
      (by norm_num : (0 : ℕ) < 16) ht, par4_zero_left t ht]
    simp only [Nat.xor_zero, Nat.xor_self]
  rw [h1, h2, h3]

theorem Tgrp_normalizes_Agrp
    {x a : OLq} (hx : x ∈ Tgrp) (ha : a ∈ Agrp) :
    x * a * x⁻¹ ∈ Agrp := by
  obtain ⟨t, ht, rfl⟩ := mem_Tgrp_iff.1 hx
  obtain ⟨e, he, l, hl, rfl⟩ := mem_Agrp_iff.1 ha
  exact mem_Agrp_iff.2 ⟨_, xor_lt_two he (par4_lt _), l, hl, qElt_conj_T ht he hl⟩

theorem qElt_conj_eq
    {e l e' l' t' : ℕ} (he : e < 2) (hl : l < 16) (he' : e' < 2)
    (hl' : l' < 16) (ht' : t' < 16) :
    qElt e' l' t' * qElt e l 0 * (qElt e' l' t')⁻¹ =
      qElt (e' ^^^ e ^^^ par4 (l &&& t') ^^^ (e' ^^^ par4 (l' &&& t')) ^^^
        par4 (l' &&& t')) (l' ^^^ l ^^^ l') 0 := by
  rw [qElt_inv he' hl' ht', qElt_mul he' hl' ht' he hl (by norm_num : (0 : ℕ) < 16),
    Nat.xor_zero, qElt_mul (xor_lt_two (xor_lt_two he' he) (par4_lt _)) (xor_lt_sixteen hl' hl)
      ht' (xor_lt_two he' (par4_lt _)) hl' ht', Nat.xor_self]

theorem Agrp_inf_Tgrp :
    Agrp ⊓ Tgrp = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨e, he, l, hl, rfl⟩ := mem_Agrp_iff.1 hx.1
  obtain ⟨t, ht, h⟩ := mem_Tgrp_iff.1 hx.2
  obtain ⟨rfl, rfl, -⟩ := qElt_inj he hl (by norm_num) (by norm_num) (by norm_num) ht h
  exact qElt_zero

theorem Agrp_normal :
    (Agrp.subgroupOf Qgrp).Normal := by
  refine ⟨fun a ha g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  obtain ⟨e, he, l, hl, h⟩ := mem_Agrp_iff.1 ha
  obtain ⟨e', he', l', hl', t', ht', hg⟩ := mem_Qgrp_iff.1 g.2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h, hg,
    qElt_conj_eq he hl he' hl' ht']
  exact mem_Agrp_iff.2 ⟨_, xor_lt_two (xor_lt_two (xor_lt_two (xor_lt_two he' he) (par4_lt _))
    (xor_lt_two he' (par4_lt _))) (par4_lt _), _, xor_lt_sixteen (xor_lt_sixteen hl' hl) hl',
    rfl⟩

theorem exists_exact_sequence :
    ∃ π : Cr →* CFSG.Assembly.LowTwoRank.StatedSp 3 (ZMod 2), Function.Surjective π ∧
      ∀ k : Cr, π k = 1 ↔ ((k : Kstab v0) : OLq) ∈ Qgrp := by
  obtain ⟨e⟩ := nonempty_isometryGroup_bZ_equiv
  refine ⟨e.toMonoidHom.comp resZ, e.surjective.comp resZ_surjective_natCard_ker.1, fun k => ?_⟩
  change e (resZ k) = 1 ↔ _
  exact (MulEquiv.map_eq_one_iff e).trans (MonoidHom.mem_ker.symm.trans (mem_ker_resZ_iff k))

theorem native_Co2_central_involution_extraspecial_kernel :
    IsElementaryAbelian 2 Tperm ∧ Nat.card Tperm = 16 ∧
    (∀ x ∈ Tgrp, ∀ a ∈ Agrp, x * a * x⁻¹ ∈ Agrp) ∧
    Qgrp = Agrp ⊔ Tgrp ∧ Agrp ⊓ Tgrp = ⊥ ∧ (Agrp.subgroupOf Qgrp).Normal ∧
    Nat.card Agrp = 32 ∧ Nat.card Tgrp = 16 ∧
    (∀ x ∈ Qgrp, ∃ k : Cr, ((k : Kstab v0) : OLq) = x) ∧
    (∀ k : Cr, k ∈ resZ.ker ↔ ((k : Kstab v0) : OLq) ∈ Qgrp) ∧
    IsExtraspecialPGroup 2 Qgrp ∧ Nat.card Qgrp = 2 ^ 9 ∧
    ((rQ : Qgrp) : OLq) = (rK : OLq) ∧
    Subgroup.center Qgrp = Subgroup.zpowers rQ ∧ commutator Qgrp = Subgroup.zpowers rQ ∧
    Function.Surjective phiQ ∧ phiQ.ker = Subgroup.center Qgrp ∧
    (∀ x : Qgrp, x ^ 2 =
      rQ ^ ((Multiplicative.toAdd (phiQ x)).1 ⬝ᵥ (Multiplicative.toAdd (phiQ x)).2).val) ∧
    IsElementaryAbelian 2 AQ ∧ Nat.card AQ = 32 ∧
    (∀ B : Subgroup Qgrp, AQ ≤ B → IsElementaryAbelian 2 B → B = AQ) ∧
    ∃ π : Cr →* CFSG.Assembly.LowTwoRank.StatedSp 3 (ZMod 2), Function.Surjective π ∧
      ∀ k : Cr, π k = 1 ↔ ((k : Kstab v0) : OLq) ∈ Qgrp := by
  exact ⟨isElementaryAbelian_Tperm, natCard_Tperm, fun x hx a ha => Tgrp_normalizes_Agrp hx ha,
    rfl, Agrp_inf_Tgrp, Agrp_normal, natCard_Agrp, natCard_Tgrp,
    fun x hx => exists_Cr_of_mem_Qgrp hx, mem_ker_resZ_iff, isExtraspecialPGroup_Qgrp,
    natCard_Qgrp, coe_rQ, center_Qgrp_eq_zpowers,
    isExtraspecialPGroup_Qgrp.2.1.trans center_Qgrp_eq_zpowers, phiQ_surjective, ker_phiQ,
    sq_eq_rQ_pow, isElementaryAbelian_AQ, natCard_AQ, AQ_maximal, exists_exact_sequence⟩

end CFSG.Monster.B.TwoA.Co2Inv
