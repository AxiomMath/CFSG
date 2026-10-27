module

public import CFSG.Monster.B.CTIB.Rep4371Dims
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.SpinLattice
  CFSG.Monster.Spin CFSG.Monster.ScalarKernel CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371
open CFSG.Monster.B.Co2 (v0)

private theorem conj_eq_pow_val {G : Type*} [Group G] {a b z : G} {β : ZMod 2}
    (hβ : a * b = b * a ↔ β = 0) (hc : a⁻¹ * b * a * b⁻¹ = 1 ∨ a⁻¹ * b * a * b⁻¹ = z) :
    a⁻¹ * b * a = z ^ β.val * b := by
  have h2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h2 β with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, one_mul, mul_assoc, ← hβ.2 rfl, inv_mul_cancel_left]
  · rw [ZMod.val_one, pow_one]
    rcases hc with h | h
    · have e : a⁻¹ * b * a = b := mul_inv_eq_one.1 h
      have hab : a * b = b * a :=
        calc a * b = a * (a⁻¹ * b * a) := by rw [e]
          _ = b * a := by rw [mul_assoc, mul_inv_cancel_left]
      exact absurd (hβ.1 hab) one_ne_zero
    · exact mul_inv_eq_iff_eq_mul.1 h

private theorem phi0_conj_mul_inv (a b : Q) : phi0 (coordOf (a⁻¹ * b * a * b⁻¹)) = 0 := by
  rw [phi0_coordOf_mul, phi0_coordOf_mul, phi0_coordOf_mul, phi0_coordOf_inv, phi0_coordOf_inv]
  have h : ∀ x y : L2, x + y + x + y = 0 := fun x y => by
    rw [show x + y + x + y = (x + y) + (x + y) by abel, ZModModule.add_self]
  exact h _ _

theorem conj_eq_zQ_pow (a b : Q) :
    a⁻¹ * b * a = zQ ^ (bL (phi0 (coordOf a)) (phi0 (coordOf b))).val * b :=
  conj_eq_pow_val (commute_iff_bL a b) ((phi0_coordOf_eq_zero_iff _).1 (phi0_conj_mul_inv a b))

@[expose] noncomputable def sPart
    (t : Fin 2300) : Q := xRep octDataOK_true t

theorem isPartner_sPart
    (t : Fin 2300) : IsPartner isShortCoord_rStar (sPart t) :=
  isPartner_xRep octDataOK_true t

theorem sPart_mem_centralizer
    (t : Fin 2300) : sPart t ∈ Subgroup.centralizer {rStar} :=
  Subgroup.mem_centralizer_singleton_iff.2
    (mul_comm_of_partner isShortCoord_rStar (isPartner_sPart t)).symm

theorem coe_Rbasis_sPart (t : Fin 2300) :
    (Rbasis ⟨23 + t, by omega⟩ : SpaceB) = inX (Xlift (sPart t) - Xlift (rStar * sPart t)) := by
  rw [coe_Rbasis, show ((⟨23 + t, by omega⟩ : Fin 4371) : ℕ) = 23 + t from rfl,
    Rraw_xLab octDataOK_true (by omega) (by omega), sPart, xRep,
    rStar_mul_xLab octDataOK_true (k := 23 + t) (by omega) (by omega)]

@[expose] noncomputable def aWr
    (t : Fin 2300) : Wv (phi0 (coordOf rStar)) :=
  Submodule.Quotient.mk ⟨phi0 (coordOf (sPart t)), phi0_mem_vPerpL rfl (sPart_mem_centralizer t)⟩

@[expose] noncomputable def aW
    (t : Fin 2300) : Wv v0 := wvEquiv hv0 (aWr t)

theorem conjQ_rhoPair (q s : Q) : conjQ (rhoPair q) s = q⁻¹ * s * q :=
  Subtype.ext (by rw [coe_conjQ]; rfl)

theorem bL_rStar_mul {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) (s : Q) :
    bL (phi0 (coordOf q)) (phi0 (coordOf (rStar * s))) =
      bL (phi0 (coordOf q)) (phi0 (coordOf s)) := by
  rw [phi0_coordOf_mul, map_add, bL_comm (phi0 (coordOf q)) (phi0 (coordOf rStar)),
    (mem_centralizer_iff_bL rStar q).1 hq, zero_add]

theorem theta_rhoPair_xdiff {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) (s : Q) :
    theta (rhoPair q) (inX (Xlift s - Xlift (rStar * s))) =
      sgn (bL (phi0 (coordOf q)) (phi0 (coordOf s))) • inX (Xlift s - Xlift (rStar * s)) := by
  have k1 : Xlift (conjQ (rhoPair q) s) = sgn (bL (phi0 (coordOf q)) (phi0 (coordOf s))) •
      Xlift s := by
    rw [conjQ_rhoPair]
    exact (congrArg Xlift (conj_eq_zQ_pow q s)).trans (Xlift_zQ_pow_mul _ _)
  have k2 : Xlift (conjQ (rhoPair q) (rStar * s)) =
      sgn (bL (phi0 (coordOf q)) (phi0 (coordOf s))) • Xlift (rStar * s) := by
    rw [conjQ_rhoPair, ← bL_rStar_mul hq s]
    exact (congrArg Xlift (conj_eq_zQ_pow q (rStar * s))).trans (Xlift_zQ_pow_mul _ _)
  rw [theta_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show thetaA (mat (rhoPair q).1.2) (0 : symMat) =
      sgn (bL (phi0 (coordOf q)) (phi0 (coordOf s))) • (0 : symMat)
    rw [map_zero, smul_zero]
  · show thetaX (rhoPair q) (Xlift s - Xlift (rStar * s)) =
      sgn (bL (phi0 (coordOf q)) (phi0 (coordOf s))) • (Xlift s - Xlift (rStar * s))
    have h := congrArg₂ (· - ·) ((thetaX_Xlift (rhoPair q) s).trans k1)
      ((thetaX_Xlift (rhoPair q) (rStar * s)).trans k2)
    refine ((map_sub (thetaX (rhoPair q)) _ _).trans h).trans ?_
    exact (smul_sub _ _ _).symm
  · show thetaW _ _ (0 : SpaceW) =
      sgn (bL (phi0 (coordOf q)) (phi0 (coordOf s))) • (0 : SpaceW)
    rw [map_zero, smul_zero]

theorem psiW_iotaD_rho {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) (he : iotaD (kappa
    ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) ∈ Ehat) :
    psiW ⟨_, he⟩ =
      wvEquiv hv0 (Submodule.Quotient.mk ⟨phi0 (coordOf q), phi0_mem_vPerpL rfl hq⟩) := by
  have e : (⟨_, he⟩ : Ehat) = ehatEquiv ⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩,
      kappa_rho_mem_Ebar hq⟩ := Subtype.ext rfl
  rw [e, psiW_ehatEquiv, psiBar_kappa_rho hq, toAdd_ofAdd]

theorem bV_psiW_aW {q : Q} (hq : q ∈ Subgroup.centralizer {rStar})
    (he : iotaD (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩) ∈ Ehat) (t : Fin 2300) :
    bV (psiW ⟨_, he⟩) (aW t) = bL (phi0 (coordOf q)) (phi0 (coordOf (sPart t))) := by
  rw [psiW_iotaD_rho hq he, aW, aWr, polar_wvEquiv hv0 qL_phi0_coordOf_rStar qL_v0,
    polarBilin_qW_mk]

theorem rhoV_Ehat_R
    {e : Shat} (he : (e : Dfull) ∈ Ehat) (t : Fin 2300) :
    rhoV e (Rbasis ⟨23 + t, by omega⟩) =
      sgn (bV (psiW ⟨e, he⟩) (aW t)) • Rbasis ⟨23 + t, by omega⟩ := by
  obtain ⟨q, hq, hqe⟩ := exists_of_mem_Ehat he
  apply Subtype.ext
  rw [rhoV_Ehat_apply hq hqe, Submodule.coe_smul, coe_Rbasis_sPart, theta_rhoPair_xdiff hq]
  have e' : (⟨e, he⟩ : Ehat) = ⟨_, hqe ▸ he⟩ := Subtype.ext hqe.symm
  rw [e', bV_psiW_aW hq]

theorem rStar_mul_sPart (t : Fin 2300) :
    rStar * sPart t = labelElt (xLab octDataOK_true (23 + t) true) :=
  rStar_mul_xLab octDataOK_true (k := 23 + t) (by omega) (by omega)

theorem coordOf_eq_label {l l' : ShortLabel}
    (h : coordOf (labelElt l) = coordOf (labelElt l')) : l = l' :=
  labelIdx_injective (Subtype.ext h)

theorem aWr_injective : Function.Injective aWr := by
  intro t t' h
  rw [aWr, aWr, Submodule.Quotient.eq] at h
  have h' : phi0 (coordOf (sPart t)) - phi0 (coordOf (sPart t')) ∈
      vLineL (phi0 (coordOf rStar)) := h
  rw [mem_vLineL, sub_eq_zero] at h'
  rcases h' with h0 | hv
  · have hc := phi0_injective h0
    have hl := coordOf_eq_label hc
    exact Fin.ext (by have := (xLab_injective octDataOK_true (by omega) (by omega) (by omega)
      (by omega) hl).1; omega)
  · have e : phi0 (coordOf (sPart t')) = phi0 (coordOf (rStar * sPart t)) := by
      rw [phi0_coordOf_mul, ← hv, sub_eq_add_neg, ZModModule.neg_eq_self, add_comm,
        ← add_assoc, ZModModule.add_self, zero_add]
    have hc := phi0_injective e
    rw [rStar_mul_sPart] at hc
    have hl := coordOf_eq_label hc
    exact absurd (xLab_injective octDataOK_true (by omega) (by omega) (by omega) (by omega) hl).2
      (by decide)

theorem aW_injective : Function.Injective aW :=
  (wvEquiv hv0).injective.comp aWr_injective

@[expose] noncomputable def Rt
    (t : Fin 2300) : Vst := Rbasis ⟨23 + t, by omega⟩

theorem Rt_injective : Function.Injective fun t : Fin 2300 => (⟨23 + t, by omega⟩ : Fin 4371) :=
  fun t t' h => Fin.ext (by have := congrArg Fin.val h; simp only at this; omega)

theorem linearIndependent_Rt : LinearIndependent ℚ Rt :=
  Rbasis.linearIndependent.comp _ Rt_injective

theorem Rt_ne_zero
    (t : Fin 2300) : Rt t ≠ 0 := linearIndependent_Rt.ne_zero t

theorem Rt_mem_V2300 (t : Fin 2300) : Rt t ∈ V2300 := by
  rw [mem_V2300, Rt, coe_Rbasis_sPart]
  exact Submodule.subset_span ⟨sPart t, isPartner_sPart t, rfl⟩

theorem V2300_eq_span : V2300 = Submodule.span ℚ (Set.range Rt) := by
  apply le_antisymm
  · intro v hv
    have hv' : (v : SpaceB) ∈ Xdiff isShortCoord_rStar := hv
    rw [← (xdiff_Rraw octDataOK_true).2.1] at hv'
    have hmap : Submodule.span ℚ (Set.range fun t : Fin 2300 => Rraw (23 + t)) =
        (Submodule.span ℚ (Set.range Rt)).map Vst.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext x
      simp only [Set.mem_range, Function.comp_apply, Submodule.subtype_apply]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, by rw [Rt, coe_Rbasis]⟩
      · rintro ⟨t, rfl⟩
        exact ⟨t, by rw [Rt, coe_Rbasis]⟩
    rw [hmap] at hv'
    obtain ⟨w, hw, hwv⟩ := hv'
    rw [← Subtype.ext hwv]
    exact hw
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact Rt_mem_V2300 t

theorem sgn_zmod_injective : Function.Injective sgn := by
  intro a b h
  have h2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl
  · rfl
  · exact absurd h (by simp [sgn]; norm_num)
  · exact absurd h (by simp [sgn]; norm_num)
  · rfl

theorem eq_of_char {a a' : Wv v0}
    (h : ∀ e : Ehat, bV (psiW e) a = bV (psiW e) a') : a = a' := by
  have h0 : ∀ x : Wv v0, bV (a - a') x = 0 := by
    intro x
    obtain ⟨e, rfl⟩ := psiW_surjective x
    rw [bV_comm, map_sub, h e, sub_self]
  exact sub_eq_zero.1 (bV_nondegenerate.1 _ h0)

theorem Ehat_le_Shat' {e : Dfull} (he : e ∈ Ehat) : e ∈ Shat := Jhat_le_Shat (Ehat_le_Jhat he)

@[expose] def xIdx (t : Fin 2300) : Fin 4371 := ⟨23 + t, by omega⟩

theorem Rt_eq (t : Fin 2300) : Rt t = Rbasis (xIdx t) := rfl

theorem xIdx_injective : Function.Injective xIdx := Rt_injective

theorem repr_Rt (t : Fin 2300) (k : Fin 4371) :
    Rbasis.repr (Rt t) k = if xIdx t = k then 1 else 0 := by
  rw [Rt_eq, Module.Basis.repr_self, Finsupp.single_apply]

theorem repr_smul (c : ℚ) (x : Vst) (k : Fin 4371) :
    Rbasis.repr (c • x) k = c * Rbasis.repr x k := by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem repr_add (x y : Vst) (k : Fin 4371) :
    Rbasis.repr (x + y) k = Rbasis.repr x k + Rbasis.repr y k := by
  rw [map_add, Finsupp.add_apply]

theorem repr_zero' (k : Fin 4371) : Rbasis.repr (0 : Vst) k = 0 := by
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]

theorem repr_rhoV_Rt
    (e : Ehat) (t t' : Fin 2300) :
    Rbasis.repr (rhoV ⟨e, Ehat_le_Shat' e.2⟩ (Rt t')) (xIdx t) =
      sgn (bV (psiW e) (aW t)) * Rbasis.repr (Rt t') (xIdx t) := by
  rw [Rt, rhoV_Ehat_R e.2 t', ← Rt, repr_smul, repr_Rt]
  by_cases h : xIdx t' = xIdx t
  · rw [ite_eq_left h, xIdx_injective h]
  · rw [ite_eq_right h, mul_zero, mul_zero]

theorem repr_rhoV_Ehat
    {e : Ehat} {v : Vst} (hv : v ∈ V2300) (t : Fin 2300) :
    Rbasis.repr (rhoV ⟨e, Ehat_le_Shat' e.2⟩ v) (xIdx t) =
      sgn (bV (psiW e) (aW t)) * Rbasis.repr v (xIdx t) := by
  rw [V2300_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t', rfl⟩ := hx
    exact repr_rhoV_Rt e t t'
  | zero => rw [map_zero (rhoV _), repr_zero', mul_zero]
  | add x y _ _ hx hy =>
    rw [map_add (rhoV _) x y, repr_add, repr_add, hx, hy, mul_add]
  | smul c x _ hx =>
    rw [map_smul (rhoV _) c x, repr_smul, repr_smul, hx, mul_left_comm]

theorem repr_eq_zero_of_mem {v : Vst} (hv : v ∈ V2300) {k : Fin 4371}
    (hk : ∀ t, xIdx t ≠ k) : Rbasis.repr v k = 0 := by
  rw [V2300_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t', rfl⟩ := hx
    rw [repr_Rt, ite_eq_right (hk t')]
  | zero => exact repr_zero' k
  | add x y _ _ hx hy => rw [repr_add, hx, hy, add_zero]
  | smul c x _ hx => rw [repr_smul, hx, mul_zero]

theorem aW_eq_of_eigen
    {v : Vst} (hv : v ∈ V2300) {a : Wv v0}
    (he : ∀ e : Ehat, rhoV ⟨e, Ehat_le_Shat' e.2⟩ v = sgn (bV (psiW e) a) • v)
    {t : Fin 2300} (ht : Rbasis.repr v (xIdx t) ≠ 0) : aW t = a := by
  symm
  apply eq_of_char
  intro e
  have h : Rbasis.repr (rhoV ⟨e, Ehat_le_Shat' e.2⟩ v) (xIdx t) =
      Rbasis.repr (sgn (bV (psiW e) a) • v) (xIdx t) := by rw [he e]
  rw [repr_rhoV_Ehat hv, repr_smul] at h
  exact sgn_zmod_injective (mul_right_cancel₀ ht h).symm

theorem bV_wAct_left (k : Kstab v0) (x y : Wv v0) :
    bV (wAct v0 k x) y = bV x (wAct v0 k⁻¹ y) := by
  have := Unitary.bW_wAct k x (wAct v0 k⁻¹ y)
  rw [show wAct v0 k (wAct v0 k⁻¹ y) = y by
    have h2 := Co2.wAct_inv_apply k⁻¹ y
    rwa [inv_inv] at h2] at this
  exact this

theorem rhoV_conj_eigen
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) (t : Fin 2300) (e : Ehat) :
    rhoV ⟨e, Ehat_le_Shat' e.2⟩ (rhoV h (Rt t)) =
      sgn (bV (psiW e) (wAct v0 (jhatToKv0 ⟨h, hh⟩)⁻¹ (aW t))) • rhoV h (Rt t) := by
  have hconj : ((h⁻¹ * ⟨e, Ehat_le_Shat' e.2⟩ * h : Shat) : Dfull) ∈ Ehat := conj_mem_Ehat hh e.2
  have hrel : rhoV ⟨e, Ehat_le_Shat' e.2⟩ (rhoV h (Rt t)) =
      rhoV h (rhoV (h⁻¹ * ⟨e, Ehat_le_Shat' e.2⟩ * h) (Rt t)) := by
    have e1 : h * (h⁻¹ * ⟨e, Ehat_le_Shat' e.2⟩ * h) = ⟨e, Ehat_le_Shat' e.2⟩ * h := by group
    show (rhoV _ * rhoV h) (Rt t) = (rhoV h * rhoV _) (Rt t)
    rw [← map_mul, ← map_mul, e1]
  have h2 := rhoV_Ehat_R hconj t
  have hpsi : psiW ⟨_, hconj⟩ = wAct v0 (jhatToKv0 ⟨h, hh⟩) (psiW e) := psiW_conj hh e.2
  rw [hpsi, bV_wAct_left] at h2
  rw [hrel]
  exact (congrArg (rhoV h) h2).trans (map_smul _ _ _)

theorem rhoV_Jhat_Rt
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) (t : Fin 2300) :
    ∃ t', aW t' = wAct v0 (jhatToKv0 ⟨h, hh⟩)⁻¹ (aW t) ∧
      rhoV h (Rt t) ∈ Submodule.span ℚ {Rt t'} := by
  set w := rhoV h (Rt t) with hw
  have hmem : w ∈ V2300 := (Jhat_preserves hh).2.1 _ (Rt_mem_V2300 t)
  have heig := rhoV_conj_eigen hh t
  have hne : w ≠ 0 := fun h0 => Rt_ne_zero t ((rhoV h).injective (h0.trans (map_zero _).symm))
  obtain ⟨k, hk⟩ : ∃ k, Rbasis.repr w k ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Rbasis.repr.injective (Finsupp.ext fun k => by rw [hall k, map_zero,
      Finsupp.coe_zero, Pi.zero_apply]))
  obtain ⟨t', rfl⟩ : ∃ t', xIdx t' = k := by
    by_contra hall
    push Not at hall
    exact hk (repr_eq_zero_of_mem hmem hall)
  have ht' := aW_eq_of_eigen hmem heig hk
  refine ⟨t', ht', ?_⟩
  have hw' : w = Rbasis.repr w (xIdx t') • Rt t' := by
    apply Rbasis.repr.injective
    refine Finsupp.ext fun k => ?_
    rw [repr_smul, repr_Rt]
    by_cases hk' : xIdx t' = k
    · rw [ite_eq_left hk', mul_one, hk']
    · rw [ite_eq_right hk', mul_zero]
      by_cases hx : ∃ t'', xIdx t'' = k
      · obtain ⟨t'', rfl⟩ := hx
        by_contra hnz
        have := aW_eq_of_eigen hmem heig hnz
        exact hk' (congrArg xIdx (aW_injective (ht'.trans this.symm)))
      · push Not at hx
        exact repr_eq_zero_of_mem hmem hx
  rw [hw']
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem xLab_23 :
    xLab octDataOK_true 23 false = .inl (pairLab false 2) := by
  rw [xLab, ite_eq_left (by norm_num : (23 : ℕ) ≤ 66),
    ite_eq_left (by norm_num : (23 - 23) % 2 = 0)]

theorem aW_zero :
    aW 0 = Unitary.sigmaW := by
  rw [aW, aWr, wvEquiv_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  show phi0 (coordOf (labelElt (xLab octDataOK_true (23 + 0) false))) = Unitary.sigmaCls
  rw [phi0_labelElt, show 23 + 0 = 23 from rfl, xLab_23]
  show Code.classOf (Griess.vMinus (pairLab false 2).1.1 (pairLab false 2).1.2) =
    pairCls 0 2 0
  rw [pairCls, pairVec_zero, pairLab, dite_eq_left (by norm_num : 2 ≤ 2 ∧ 2 ≤ 23)]
  rfl

theorem exists_aW_wAct
    (k : Kstab v0) (t : Fin 2300) : ∃ t', aW t' = wAct v0 k (aW t) := by
  obtain ⟨h, hh⟩ := jhatToKv0_surjective k⁻¹
  obtain ⟨t', ht', -⟩ := rhoV_Jhat_Rt (h := ⟨h.1, Jhat_le_Shat h.2⟩) h.2 t
  refine ⟨t', ht'.trans ?_⟩
  rw [show (⟨((⟨h.1, Jhat_le_Shat h.2⟩ : Shat) : Dfull), h.2⟩ : Jhat) = h from rfl, hh, inv_inv]

theorem range_aW :
    Set.range aW = Unitary.OmegaW := by
  have hsub : Unitary.OmegaW ⊆ Set.range aW := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨t', ht'⟩ := exists_aW_wAct k 0
    exact ⟨t', by rw [ht', aW_zero]⟩
  have hfin : (Set.range aW).Finite := Set.finite_range aW
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm
  rw [Set.ncard_range_of_injective aW_injective, Unitary.ncard_OmegaW, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem aW_mem_OmegaW
    (t : Fin 2300) : aW t ∈ Unitary.OmegaW := by
  rw [← range_aW]
  exact ⟨t, rfl⟩

@[expose] noncomputable def omegaEquiv :
    Fin 2300 ≃ Unitary.OmegaPt :=
  Equiv.ofBijective (fun t => ⟨aW t, aW_mem_OmegaW t⟩)
    ⟨fun t t' h => aW_injective (congrArg Subtype.val h), fun a => by
      obtain ⟨t, ht⟩ : (a : Wv v0) ∈ Set.range aW := by rw [range_aW]; exact a.2
      exact ⟨t, Subtype.ext ht⟩⟩

theorem coe_omegaEquiv
    (t : Fin 2300) : (omegaEquiv t : Wv v0) = aW t := rfl

@[expose] noncomputable def lineB
    (a : Unitary.OmegaPt) : Submodule ℚ SpaceB :=
  Submodule.span ℚ {(Rt (omegaEquiv.symm a) : SpaceB)}

theorem aW_omegaEquiv_symm
    (a : Unitary.OmegaPt) : aW (omegaEquiv.symm a) = a := by
  rw [← coe_omegaEquiv, Equiv.apply_symm_apply]

theorem coe_Rt (t : Fin 2300) : (Rt t : SpaceB) = Rraw (23 + t) := by
  rw [Rt, coe_Rbasis]

theorem RrawX_ne_zero (t : Fin 2300) : Rraw (23 + t) ≠ 0 :=
  (xdiff_Rraw octDataOK_true).1.ne_zero t

theorem finrank_lineB
    (a : Unitary.OmegaPt) : Module.finrank ℚ (lineB a) = 1 := by
  rw [lineB, coe_Rt]
  exact finrank_span_singleton (RrawX_ne_zero _)

theorem iSupIndep_lineB :
    iSupIndep lineB := by
  have h :=
    ((xdiff_Rraw octDataOK_true).1.comp _ omegaEquiv.symm.injective).iSupIndep_span_singleton
  convert h using 2 with a
  rw [lineB, coe_Rt]
  rfl

theorem iSup_lineB :
    ⨆ a, lineB a = Xdiff isShortCoord_rStar := by
  rw [← (xdiff_Rraw octDataOK_true).2.1, Submodule.span_range_eq_iSup]
  have e : (fun a => lineB a) =
      fun a => Submodule.span ℚ {Rraw (23 + ((omegaEquiv.symm a : Fin 2300) : ℕ))} := by
    funext a
    rw [lineB, coe_Rt]
  rw [e]
  exact omegaEquiv.symm.iSup_comp
    (g := fun t : Fin 2300 => Submodule.span ℚ {Rraw (23 + (t : ℕ))})

theorem lineB_le_Xdiff
    (a : Unitary.OmegaPt) : lineB a ≤ Xdiff isShortCoord_rStar := by
  rw [← iSup_lineB]
  exact le_iSup lineB a

theorem mem_lineB_iff
    {a : Unitary.OmegaPt} {v : Vst} :
    (v : SpaceB) ∈ lineB a ↔ v ∈ Submodule.span ℚ {Rt (omegaEquiv.symm a)} := by
  rw [lineB, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext (by rw [Submodule.coe_smul, hc])⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩

theorem rhoV_lineB
    {e : Ehat} {a : Unitary.OmegaPt} {v : Vst} (hv : (v : SpaceB) ∈ lineB a) :
    rhoV ⟨e, Ehat_le_Shat' e.2⟩ v = sgn (bV (psiW e) a) • v := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (mem_lineB_iff.1 hv)
  rw [map_smul, Rt, rhoV_Ehat_R e.2, ← Rt, aW_omegaEquiv_symm, smul_comm]

theorem rhoV_mem_lineB
    {h : Shat} (hh : (h : Dfull) ∈ Jhat) {a : Unitary.OmegaPt} {v : Vst}
    (hv : (v : SpaceB) ∈ lineB a) : (rhoV h v : SpaceB) ∈ lineB (jhatToKv0 ⟨h, hh⟩ • a) := by
  obtain ⟨t', ht', hmem⟩ := rhoV_Jhat_Rt hh (omegaEquiv.symm a)
  have ht'' : omegaEquiv.symm (jhatToKv0 ⟨h, hh⟩ • a) = t' := by
    apply omegaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_omegaEquiv, ht', aW_omegaEquiv_symm, Unitary.coe_smul_OmegaPt]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (mem_lineB_iff.1 hv)
  rw [mem_lineB_iff, ht'', map_smul]
  exact Submodule.smul_mem _ _ hmem

theorem exists_char_ne
    {a a' : Unitary.OmegaPt} (h : a ≠ a') :
    ∃ e : Ehat, bV (psiW e) a ≠ bV (psiW e) a' := by
  by_contra hall
  push Not at hall
  exact h (Subtype.ext (eq_of_char hall))

@[expose] noncomputable def lineV
    (a : Unitary.OmegaPt) : Submodule ℚ Vst :=
  (lineB a).comap Vst.subtype

theorem mem_lineV
    {a : Unitary.OmegaPt} {v : Vst} : v ∈ lineV a ↔ (v : SpaceB) ∈ lineB a :=
  Iff.rfl

theorem lineB_le_Vst
    (a : Unitary.OmegaPt) : lineB a ≤ Vst :=
  (lineB_le_Xdiff a).trans Xdiff_le_Vst

theorem finrank_lineV
    (a : Unitary.OmegaPt) : Module.finrank ℚ (lineV a) = 1 :=
  (Submodule.comapSubtypeEquivOfLe (lineB_le_Vst a)).finrank_eq.trans (finrank_lineB a)

theorem iSupIndep_lineV :
    iSupIndep lineV := iSupIndep_comap_subtype Vst iSupIndep_lineB

theorem iSup_lineV :
    ⨆ a, lineV a = V2300 := by
  apply Submodule.map_injective_of_injective Vst.injective_subtype
  rw [Submodule.map_iSup]
  simp_rw [lineV, Submodule.map_comap_subtype, inf_eq_right.2 (lineB_le_Vst _)]
  rw [iSup_lineB, V2300, Submodule.map_comap_subtype, inf_eq_right.2 Xdiff_le_Vst]

end CFSG.Monster.B.CTIB
