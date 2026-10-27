module

public import CFSG.Monster.B.GSide.EdgeQCertLabel

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.Co2 (v0)

theorem zmod2_eq_one_of_ne_zero {t : ZMod 2} (h : t ≠ 0) : t = 1 := by
  rcases Fischer.zmod2_cases t with h1 | h1
  · exact absurd h1 h
  · exact h1

theorem exists_bV_one_zero
    {v₁ v₂ : Wv v0} (h1 : v₁ ≠ 0) (h12 : v₁ ≠ v₂) :
    ∃ z, bV v₁ z = 1 ∧ bV v₂ z = 0 := by
  obtain ⟨z₁, hz₁⟩ : ∃ z, bV v₁ z ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h1 (bV_nondegenerate.1 _ hall)
  obtain ⟨z, hz⟩ : ∃ z, bV v₁ z ≠ bV v₂ z := by
    by_contra hall
    push Not at hall
    apply h12
    refine sub_eq_zero.1 (bV_nondegenerate.1 _ fun y => ?_)
    rw [map_sub, LinearMap.sub_apply, hall y, sub_self]
  by_contra hno
  push Not at hno
  have hz₁' := zmod2_eq_one_of_ne_zero hz₁
  have h2z₁ := zmod2_eq_one_of_ne_zero (hno z₁ hz₁')
  rcases Fischer.zmod2_cases (bV v₁ z) with ha | ha <;>
    rcases Fischer.zmod2_cases (bV v₂ z) with hb | hb
  · exact hz (ha.trans hb.symm)
  · have e1 : bV v₁ (z + z₁) = 1 := by rw [map_add, ha, hz₁', zero_add]
    have e2 : bV v₂ (z + z₁) = 0 := by rw [map_add, hb, h2z₁]; rfl
    exact hno _ e1 e2
  · exact hno z ha hb
  · exact hz (ha.trans hb.symm)

theorem mem_N1_iff_bV
    (e : Ehat) : (e : Dfull) ∈ N1 ↔ bV Unitary.sigmaW (psiW e) = 0 := by
  have hx1 : xhat ≠ 1 := fun h => by
    have h2 := orderOf_xhat
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  constructor
  · intro h
    have hc := Ehat_comm e cE
    rw [psiW_cE] at hc
    change (e : Dfull) * cQ = cQ * e * xhat ^ (bV (psiW e) Unitary.sigmaW).val at hc
    have hcomm : (e : Dfull) * cQ = cQ * e := Subgroup.mem_centralizer_singleton_iff.1 h.2
    rw [hcomm] at hc
    have hp : xhat ^ (bV (psiW e) Unitary.sigmaW).val = 1 :=
      mul_left_cancel (a := cQ * (e : Dfull)) (by rw [mul_one]; exact hc.symm)
    rw [bV_comm]
    rcases Fischer.zmod2_cases (bV (psiW e) Unitary.sigmaW) with h0 | h0
    · exact h0
    · rw [h0, ZMod.val_one, pow_one] at hp
      exact absurd hp hx1
  · intro h
    refine mem_N1_of_comm e.2 ?_
    have hc := Ehat_comm e cE
    rw [psiW_cE, bV_comm, h] at hc
    change (e : Dfull) * cQ = cQ * e * xhat ^ (0 : ZMod 2).val at hc
    rw [ZMod.val_zero, pow_zero, mul_one] at hc
    exact hc

theorem conj_Ehat (e f : Ehat) :
    (f : Dfull)⁻¹ * e * f = e * xhat ^ (bV (psiW e) (psiW f)).val := by
  have hc := Ehat_comm e f
  have hx : (f : Dfull) * xhat ^ (bV (psiW e) (psiW f)).val =
      xhat ^ (bV (psiW e) (psiW f)).val * f :=
    ((Commute.symm (xhat_comm_of_mem_Jhat (Ehat_le_Jhat f.2))).pow_left _).symm
  calc (f : Dfull)⁻¹ * e * f = (f : Dfull)⁻¹ * (e * f) := by group
    _ = (f : Dfull)⁻¹ * (f * e * xhat ^ (bV (psiW e) (psiW f)).val) := by rw [hc]
    _ = e * xhat ^ (bV (psiW e) (psiW f)).val := by group

theorem exists_P1_conj
    {a b : Ehat} {p : Dfull} (hp : p ∈ P1)
    (hab : wAct v0 (jhatToKv0 ⟨p, P1_le_Jhat hp⟩) (psiW a) = psiW b) (hb0 : psiW b ≠ 0)
    (hbs : psiW b ≠ Unitary.sigmaW) : ∃ g ∈ P1, g⁻¹ * (a : Dfull) * g = b := by
  set f : Ehat := ⟨p⁻¹ * a * p, conj_mem_Ehat (P1_le_Jhat hp) a.2⟩ with hf
  have hpf : psiW f = psiW b := (psiW_conj (P1_le_Jhat hp) a.2).trans hab
  have h0 : psiW (b⁻¹ * f) = 0 := by rw [psiW_mul, psiW_inv, hpf, neg_add_cancel]
  rcases (psiW_eq_zero_iff _).1 h0 with h1 | h1
  · refine ⟨p, hp, ?_⟩
    have e : f = b := (inv_mul_eq_one.1 h1).symm
    exact congrArg Subtype.val e
  · have e : f = b * xhatE := inv_mul_eq_iff_eq_mul.1 h1
    obtain ⟨z, hz1, hz0⟩ := exists_bV_one_zero hb0 hbs
    obtain ⟨n, rfl⟩ := psiW_surjective z
    have hn : (n : Dfull) ∈ N1 := (mem_N1_iff_bV n).2 hz0
    refine ⟨p * n, P1.mul_mem hp (N1_le_P1 hn), ?_⟩
    have hc := conj_Ehat b n
    rw [hz1, ZMod.val_one, pow_one] at hc
    have hxn : (n : Dfull)⁻¹ * xhat * n = xhat := by
      rw [mul_assoc, ← xhat_comm_of_mem_Jhat (Ehat_le_Jhat n.2), ← mul_assoc,
        inv_mul_cancel, one_mul]
    have hfv : (f : Dfull) = b * xhat := congrArg Subtype.val e
    calc (p * n)⁻¹ * (a : Dfull) * (p * n) = (n : Dfull)⁻¹ * f * n := by
          rw [hf]; group
      _ = (n : Dfull)⁻¹ * b * n * ((n : Dfull)⁻¹ * xhat * n) := by rw [hfv]; group
      _ = b := by rw [hc, hxn, mul_assoc, xhat_mul_self, mul_one]

@[expose] def edgeL :
    Set cEdgeFix :=
  {a | cEdgeIncl a ∈ edgeQ ∧ (∃ v, (a : Shat) = clabelS v) ∧ a ≠ lamV0 ∧ a ≠ lamW0}

theorem lamV0_not_mem_edgeL :
    lamV0 ∉ edgeL := fun h => h.2.2.1 rfl

theorem lamW0_not_mem_edgeL :
    lamW0 ∉ edgeL := fun h => h.2.2.2 rfl

theorem edgeL_subset_edgeQ
    {a : cEdgeFix} (ha : a ∈ edgeL) : cEdgeIncl a ∈ edgeQ := ha.1

@[expose] def toEhat
    {a : cEdgeFix} (h : ((a : Shat) : Dfull) ∈ Ehat) : Ehat := ⟨_, h⟩

theorem mem_N1_of_cEdgeFix
    {a : cEdgeFix} (h : ((a : Shat) : Dfull) ∈ Ehat) :
    ((a : Shat) : Dfull) ∈ N1 :=
  ⟨h, (mem_cEdgeFix_iff.1 a.2).2⟩

theorem psiW_lamV0
    (h : ((lamV0 : Shat) : Dfull) ∈ Ehat) :
    psiW (toEhat h) = Unitary.sigmaW := by
  have e : toEhat h = cE := Subtype.ext coe_lamV0
  rw [e, psiW_cE]

theorem psiW_lamW0
    (h : ((lamW0 : Shat) : Dfull) ∈ Ehat) :
    psiW (toEhat h) = Unitary.sigmaW := by
  have e : toEhat h = cE * xhatE := Subtype.ext coe_lamW0
  rw [e, psiW_mul, psiW_cE, psiW_xhatE, add_zero]

theorem eq_lam_of_psiW
    {a : cEdgeFix} (h : ((a : Shat) : Dfull) ∈ Ehat)
    (hs : psiW (toEhat h) = Unitary.sigmaW) : a = lamV0 ∨ a = lamW0 := by
  have h0 : psiW (cE⁻¹ * toEhat h) = 0 := by rw [psiW_mul, psiW_inv, hs, psiW_cE, neg_add_cancel]
  rcases (psiW_eq_zero_iff _).1 h0 with h1 | h1
  · left
    have e : toEhat h = cE := (inv_mul_eq_one.1 h1).symm
    exact Subtype.ext (Subtype.ext ((congrArg Subtype.val e).trans coe_lamV0.symm))
  · right
    have e : toEhat h = cE * xhatE := inv_mul_eq_iff_eq_mul.1 h1
    exact Subtype.ext (Subtype.ext ((congrArg Subtype.val e).trans coe_lamW0.symm))

theorem mem_edgeL_iff
    (a : cEdgeFix) :
    a ∈ edgeL ↔ ∃ h : ((a : Shat) : Dfull) ∈ Ehat, psiW (toEhat h) ∈ Unitary.DeltaW := by
  constructor
  · rintro ⟨hQ, hlab, h0, h1⟩
    have h : ((a : Shat) : Dfull) ∈ Ehat := hQ
    refine ⟨h, ?_⟩
    obtain ⟨g, hg⟩ := (exists_clabelS_iff (a : Shat)).1 hlab
    have hΩ : psiW (toEhat h) ∈ Unitary.OmegaW := psiW_mem_OmegaW_of_label (t := toEhat h) hg
    have hperp : bV Unitary.sigmaW (psiW (toEhat h)) = 0 :=
      (mem_N1_iff_bV (toEhat h)).1 (mem_N1_of_cEdgeFix h)
    refine (mem_DeltaW_iff ⟨_, hΩ⟩).2 ⟨fun e => ?_, hperp⟩
    rcases eq_lam_of_psiW h (congrArg Subtype.val e).symm with e1 | e1
    · exact h0 e1
    · exact h1 e1
  · rintro ⟨h, hΔ⟩
    refine ⟨h, ?_, fun e => ?_, fun e => ?_⟩
    · obtain ⟨s, hs⟩ := exists_label_of_psiW_mem_OmegaW (Unitary.DeltaW_subset hΔ)
      exact (exists_clabelS_iff (a : Shat)).2 ⟨s, hs⟩
    · subst e
      exact Unitary.sigmaW_notMem_DeltaW (psiW_lamV0 h ▸ hΔ)
    · subst e
      exact Unitary.sigmaW_notMem_DeltaW (psiW_lamW0 h ▸ hΔ)

theorem ncard_preimage_of_surjective {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) (S : Set H) :
    (f ⁻¹' S).ncard = Nat.card f.ker * S.ncard := by
  have e : (f ⁻¹' S) ≃ f.ker × S :=
    { toFun := fun x => (⟨x * (Function.surjInv hf (f x))⁻¹, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, Function.surjInv_eq hf, mul_inv_cancel]⟩,
        ⟨f x, x.2⟩)
      invFun := fun y => ⟨y.1 * Function.surjInv hf y.2, by
          show f (y.1 * Function.surjInv hf y.2) ∈ S
          rw [map_mul, (MonoidHom.mem_ker).1 y.1.2, one_mul, Function.surjInv_eq hf]
          exact y.2.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show (x : G) * (Function.surjInv hf (f x))⁻¹ * Function.surjInv hf (f x) = x
        group
      right_inv := fun y => by
        have hy : f (y.1 * Function.surjInv hf y.2) = y.2 := by
          rw [map_mul, (MonoidHom.mem_ker).1 y.1.2, one_mul, Function.surjInv_eq hf]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext hy)
        show (y.1 : G) * Function.surjInv hf y.2 *
          (Function.surjInv hf (f (y.1 * Function.surjInv hf y.2)))⁻¹ = y.1
        rw [hy]
        group }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_prod, Nat.card_coe_set_eq]

theorem ncard_psiW_preimage_DeltaW :
    {e : Ehat | psiW e ∈ Unitary.DeltaW}.ncard = 1782 := by
  have h := ncard_preimage_of_surjective psiE psiE_surjective
    (Multiplicative.toAdd ⁻¹' Unitary.DeltaW)
  have e1 : (psiE ⁻¹' (Multiplicative.toAdd ⁻¹' Unitary.DeltaW)) =
      {e : Ehat | psiW e ∈ Unitary.DeltaW} := rfl
  have e2 : (Multiplicative.toAdd ⁻¹' Unitary.DeltaW).ncard = Unitary.DeltaW.ncard :=
    Set.ncard_preimage_of_injective_subset_range Multiplicative.toAdd.injective
      (fun x _ => ⟨Multiplicative.ofAdd x, rfl⟩)
  rw [← e1, h, natCard_ker_psiE, e2, Unitary.ncard_DeltaW]

theorem edgeL_bij :
    Set.BijOn (fun a : cEdgeFix => ((a : Shat) : Dfull)) edgeL
      ((fun e : Ehat => (e : Dfull)) '' {e : Ehat | psiW e ∈ Unitary.DeltaW}) := by
  refine ⟨fun a ha => ?_, fun a _ b _ hab => Subtype.ext (Subtype.ext hab), fun d hd => ?_⟩
  · obtain ⟨h, hΔ⟩ := (mem_edgeL_iff a).1 ha
    exact ⟨toEhat h, hΔ, rfl⟩
  · obtain ⟨e, he, rfl⟩ := hd
    have hN : (e : Dfull) ∈ N1 := by
      refine (mem_N1_iff_bV e).2 ?_
      obtain ⟨j, hj⟩ := he
      rw [← hj, map_add, bV_self, zero_add]
      exact LinearMap.mem_ker.1 (Unitary.n6vec_mem_sigmaPerp j)
    have hS : (e : Dfull) ∈ Shat := Ehat_le_Shat e.2
    have hA : (⟨e, hS⟩ : Shat) ∈ cEdgeFix := mem_cEdgeFix_iff.2 (N1_le_P1 hN)
    refine ⟨⟨⟨e, hS⟩, hA⟩, (mem_edgeL_iff _).2 ⟨e.2, he⟩, rfl⟩

theorem ncard_edgeL :
    edgeL.ncard = 1782 := by
  rw [edgeL_bij.ncard_eq, Set.ncard_image_of_injective _ Subtype.val_injective,
    ncard_psiW_preimage_DeltaW]

theorem psiW_ne_zero_of_DeltaW
    {e : Ehat} (h : psiW e ∈ Unitary.DeltaW) : psiW e ≠ 0 :=
  psiW_ne_zero_of_mem_OmegaW (Unitary.DeltaW_subset h)

theorem psiW_ne_sigma_of_DeltaW
    {e : Ehat} (h : psiW e ∈ Unitary.DeltaW) :
    psiW e ≠ Unitary.sigmaW := fun e' => Unitary.sigmaW_notMem_DeltaW (e' ▸ h)

theorem edgeL_conj
    {a b : cEdgeFix} (ha : a ∈ edgeL) (hb : b ∈ edgeL) :
    ∃ g : cEdgeFix, b = g * a * g⁻¹ := by
  obtain ⟨ha', haΔ⟩ := (mem_edgeL_iff a).1 ha
  obtain ⟨hb', hbΔ⟩ := (mem_edgeL_iff b).1 hb
  rw [← Unitary.usigOrbit_delta] at haΔ hbΔ
  obtain ⟨ua, hua, hua'⟩ := haΔ
  obtain ⟨ub, hub, hub'⟩ := hbΔ
  obtain ⟨p, hp⟩ := p1Proj_surjective ⟨ua⁻¹ * ub, Unitary.Usig.mul_mem (Unitary.Usig.inv_mem hua)
    hub⟩
  have hk : jhatToKv0 ⟨p, P1_le_Jhat p.2⟩ = ua⁻¹ * ub := by
    rw [← coe_p1Proj, hp]
  have hab : wAct v0 (jhatToKv0 ⟨p, P1_le_Jhat p.2⟩) (psiW (toEhat ha')) =
      psiW (toEhat hb') := by
    rw [hk, Co2.wAct_mul, Module.End.mul_apply, ← hua', Co2.wAct_inv_apply, hub']
  have hbΔ' : psiW (toEhat hb') ∈ Unitary.DeltaW := by
    rw [← hub', Unitary.usigOrbit_delta.symm]
    exact ⟨ub, hub, rfl⟩
  obtain ⟨g, hg, hgab⟩ := exists_P1_conj p.2 hab (psiW_ne_zero_of_DeltaW hbΔ')
    (psiW_ne_sigma_of_DeltaW hbΔ')
  have hgS : g ∈ Shat := Jhat_le_Shat (P1_le_Jhat hg)
  refine ⟨⟨⟨g, hgS⟩, mem_cEdgeFix_iff.2 hg⟩⁻¹, Subtype.ext (Subtype.ext ?_)⟩
  rw [inv_inv]
  show ((b : Shat) : Dfull) = g⁻¹ * ((a : Shat) : Dfull) * g
  exact hgab.symm

theorem conj_mem_edgeL
    {a : cEdgeFix} (ha : a ∈ edgeL) (g : cEdgeFix) : g * a * g⁻¹ ∈ edgeL := by
  obtain ⟨hQ, ⟨v, hv⟩, h0, h1⟩ := ha
  have hval : (((g * a * g⁻¹ : cEdgeFix) : Shat) : Dfull) =
      ((g : Shat) : Dfull) * ((a : Shat) : Dfull) * ((g : Shat) : Dfull)⁻¹ := rfl
  have hgJ : ((g : Shat) : Dfull) ∈ Jhat := P1_le_Jhat (mem_cEdgeFix_iff.1 g.2)
  refine ⟨?_, ⟨cvMul v (g : Shat)⁻¹, ?_⟩, fun e => h0 ?_, fun e => h1 ?_⟩
  · show (((g * a * g⁻¹ : cEdgeFix) : Shat) : Dfull) ∈ Ehat
    rw [hval]
    have h := conj_mem_Ehat (Jhat.inv_mem hgJ) (show ((a : Shat) : Dfull) ∈ Ehat from hQ)
    rwa [inv_inv] at h
  · rw [GSide.clabelS_cvMul, inv_inv, ← hv]
    apply Subtype.ext
    rw [hval]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  · have hc : g * lamV0 = lamV0 * g := ((Subgroup.mem_center_iff.1 lamV0_mem_center) g)
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = lamV0 := by rw [e, mul_assoc, ← hc]; group
  · have hc : g * lamW0 = lamW0 * g := ((Subgroup.mem_center_iff.1 lamW0_mem_center) g)
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = lamW0 := by rw [e, mul_assoc, ← hc]; group

theorem yhat_comm_cQ :
    yhat * cQ = cQ * yhat := by
  have hc := Ehat_comm yhatE cE
  rw [psiW_yhat, psiW_cE, bV_comm] at hc
  change yhat * cQ = cQ * yhat * xhat ^ (bV Unitary.sigmaW wFr).val at hc
  rw [show bV Unitary.sigmaW wFr = 0 from Unitary.bW_sigmaW_wFr, ZMod.val_zero, pow_zero,
    mul_one] at hc
  exact hc

theorem u0_mem_Ehat :
    cQ * yhat ∈ Ehat := Ehat.mul_mem cQ_mem_Ehat yhat_mem_Ehat

theorem u0_mem_N1 :
    cQ * yhat ∈ N1 :=
  mem_N1_of_comm u0_mem_Ehat (by
    calc cQ * yhat * cQ = cQ * (yhat * cQ) := by group
      _ = cQ * (cQ * yhat) := by rw [yhat_comm_cQ])

@[expose] def edgeU0 :
    cEdgeFix :=
  ⟨⟨cQ * yhat, Ehat_le_Shat u0_mem_Ehat⟩, mem_cEdgeFix_iff.2 (N1_le_P1 u0_mem_N1)⟩

theorem coe_edgeU0 :
    ((edgeU0 : Shat) : Dfull) = cQ * yhat := rfl

theorem psiW_edgeU0 :
    psiW (toEhat (a := edgeU0) u0_mem_Ehat) = Unitary.sigmaW + wFr := by
  have e : toEhat (a := edgeU0) u0_mem_Ehat = cE * yhatE := rfl
  rw [e, psiW_mul, psiW_cE, psiW_yhat]

theorem edgeU0_mem_edgeL :
    edgeU0 ∈ edgeL :=
  (mem_edgeL_iff _).2 ⟨u0_mem_Ehat, by rw [psiW_edgeU0]; exact Unitary.sigmaW_add_wFr_mem⟩

theorem tauhat_mem_Eam :
    tauhat ∈ Eam :=
  Pc_le_Eam 1 (show tauhat ∈ Par2.H2 from Subgroup.mem_inf.2 ⟨tauhat_mem_Ntwo,
    Subgroup.mem_centralizer_singleton_iff.2 (tauhat_mul_dhat 0 2)⟩)

@[expose] def tauE :
    Eam := ⟨(tauhat ^ 2)⁻¹, Eam.inv_mem (Eam.pow_mem tauhat_mem_Eam 2)⟩

theorem clabel_nbr_tauE :
    clabel (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ tauE)) = cQ * yhat := by
  rw [nbr_mk, clabel_cvOf, Subgroup.coe_mul, coe_elS, coe_toS]
  have hc : ((tauE : Eam) : Dfull) * cQ = cQ * (tauE : Dfull) :=
    Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer tauE.2)
  have hy : ((tauE : Eam) : Dfull)⁻¹ * xhat * (tauE : Dfull) = yhat := by
    have h := tauhat_sq_conj_xhat
    have htE : ((tauE : Eam) : Dfull) = (tauhat ^ 2)⁻¹ := rfl
    rw [htE, inv_inv]
    exact h
  have ha := conj_cQ_of_not_mem a0_mem_Ehat a0_not_mem_N1
  generalize ((tauE : Eam) : Dfull) = t at hc hy ⊢
  calc (Amalgam.a0 * t)⁻¹ * cQ * (Amalgam.a0 * t)
      = t⁻¹ * (Amalgam.a0⁻¹ * cQ * Amalgam.a0) * t := by group
    _ = (t⁻¹ * cQ * t) * (t⁻¹ * xhat * t) := by rw [ha]; group
    _ = cQ * yhat := by
        rw [hy, mul_assoc t⁻¹, ← hc]
        group

theorem edgeU0_mem_RA :
    cEdgeFixToH edgeU0 ∈ RA := by
  refine ⟨_, nbr_adj a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ tauE), Subtype.ext ?_⟩
  rw [coe_cEdgeFixToH, coe_edgeU0, coe_clabelS, clabel_nbr_tauE]

theorem edgeL_subset_RA
    {a : cEdgeFix} (ha : a ∈ edgeL) : cEdgeFixToH a ∈ RA := by
  obtain ⟨g, hg⟩ := edgeL_conj edgeU0_mem_edgeL ha
  obtain ⟨w, hw, hwl⟩ := edgeU0_mem_RA
  have hg0 : cvMul cv0 ((g : Shat))⁻¹ = cv0 :=
    mem_vStab.1 ((vStab cv0).inv_mem (Subgroup.mem_inf.1 g.2).1)
  refine ⟨cvMul w ((g : Shat))⁻¹, ?_, ?_⟩
  · have h := (cgraph_adj_cvMul cv0 w ((g : Shat))⁻¹).2 hw
    rwa [hg0] at h
  · rw [GSide.clabelS_cvMul, inv_inv, ← hwl]
    calc ((cEdgeFixToH a : vStab cv0) : Shat) = ((g * edgeU0 * g⁻¹ : cEdgeFix) : Shat) :=
          congrArg Subtype.val hg
      _ = (g : Shat) * ((cEdgeFixToH edgeU0 : vStab cv0) : Shat) * ((g : Shat))⁻¹ := rfl

theorem edgeL_eq_class :
    edgeL = {b | ∃ a : cEdgeFix, b = a * edgeU0 * a⁻¹} := by
  ext b
  constructor
  · intro hb
    exact edgeL_conj edgeU0_mem_edgeL hb
  · rintro ⟨a, rfl⟩
    exact conj_mem_edgeL edgeU0_mem_edgeL a

theorem mul_mem_edgeL
    {a : cEdgeFix} (ha : a ∈ edgeL) : a * (lamV0 * lamW0) ∈ edgeL := by
  obtain ⟨h, hΔ⟩ := (mem_edgeL_iff a).1 ha
  have hx : (((a * (lamV0 * lamW0) : cEdgeFix) : Shat) : Dfull) = ((a : Shat) : Dfull) * xhat := by
    show ((a : Shat) : Dfull) * (((lamV0 : Shat) : Dfull) * ((lamW0 : Shat) : Dfull)) = _
    rw [coe_lamV0, coe_lamW0, ← mul_assoc cQ, cQ_mul_self, one_mul]
  have h' : (((a * (lamV0 * lamW0) : cEdgeFix) : Shat) : Dfull) ∈ Ehat := by
    rw [hx]
    exact Ehat.mul_mem h xhat_mem_Ehat
  refine (mem_edgeL_iff _).2 ⟨h', ?_⟩
  have e : toEhat h' = toEhat h * xhatE := Subtype.ext hx
  rw [e, psiW_mul, psiW_xhatE, add_zero]
  exact hΔ

end CFSG.Monster.B.GSide
