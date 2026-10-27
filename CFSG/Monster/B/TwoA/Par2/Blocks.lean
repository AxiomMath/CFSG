
module

public import CFSG.Monster.B.TwoA.Par2.Pair
public import CFSG.Monster.B.TwoA.Triality.TwoCore
public import CFSG.Monster.B.TwoA.Sp8.QuadDataBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Par2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Sp8

attribute [local instance] restAction

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem psiW_of_mem_Vhat
    {v : Dfull} (hv : v ∈ Vhat) :
    psiW ⟨v, Vhat_le_Ehat hv⟩ = 0 ∨ psiW ⟨v, Vhat_le_Ehat hv⟩ = wFr := by
  rcases (mem_Vhat_iff v).1 hv with rfl | rfl | rfl | rfl
  · exact .inl psiW_one
  · exact .inl psiW_xhatE
  · right
    have e : (⟨xhat * yhat, Vhat_le_Ehat hv⟩ : Ehat) = xhatE * yhatE := rfl
    rw [e, psiW_mul, psiW_xhatE, psiW_yhat, zero_add]
  · exact .inr psiW_yhat

theorem mem_Vhat_of_psiW
    (e : Ehat) (h : psiW e = 0 ∨ psiW e = wFr) : (e : Dfull) ∈ Vhat := by
  rcases h with h | h
  · rcases (psiW_eq_zero_iff e).1 h with rfl | rfl
    · exact Vhat.one_mem
    · exact xhat_mem_Vhat
  · rcases fiber_cases (h.trans psiW_yhat.symm) with h1 | h1
    · rw [h1]; exact yhat_mem_Vhat
    · rw [h1]; exact Vhat.mul_mem yhat_mem_Vhat xhat_mem_Vhat

theorem qV_pW
    (j : Rest) (b : ZMod 2) : qV (pW j b) = 0 :=
  Griess.qL_classOf_minVecs (pairVec_mem (rest_ne_zero j) b)

theorem dhat0_mul_self
    (j : Rest) : dhat 0 j * dhat 0 j = 1 :=
  Ehat_mul_self (dhatE 0 j) (by rw [psiW_dhat0]; exact qV_pW j 0)

@[expose] def blk (j : Rest) : Set Dfull := {d | ∃ v ∈ Vhat, dhat 0 j * v = d}

theorem dhat_mem_blk (j : Rest) : dhat 0 j ∈ blk j := ⟨1, Vhat.one_mem, mul_one _⟩

theorem two_add_self
    (x : Wv v0) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem mem_blk_iff
    (j : Rest) (d : Dfull) :
    d ∈ blk j ↔ ∃ h : d ∈ Ehat, psiW ⟨d, h⟩ = pW j 0 ∨ psiW ⟨d, h⟩ = pW j 1 := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Ehat.mul_mem (dhat_mem_Ehat 0 j) (Vhat_le_Ehat hv), ?_⟩
    have e : (⟨dhat 0 j * v, Ehat.mul_mem (dhat_mem_Ehat 0 j) (Vhat_le_Ehat hv)⟩ : Ehat) =
        dhatE 0 j * ⟨v, Vhat_le_Ehat hv⟩ := rfl
    rw [e, psiW_mul, psiW_dhat0, pW_one]
    rcases psiW_of_mem_Vhat hv with h | h
    · exact .inl (by rw [h, add_zero])
    · exact .inr (by rw [h])
  · rintro ⟨h, hψ⟩
    refine ⟨dhat 0 j * d, mem_Vhat_of_psiW (dhatE 0 j * (⟨d, h⟩ : Ehat)) ?_, ?_⟩
    · rw [psiW_mul, psiW_dhat0]
      rcases hψ with h1 | h1
      · exact .inl (by rw [h1, two_add_self])
      · exact .inr (by rw [h1, pW_one, ← add_assoc, two_add_self, zero_add])
    · rw [← mul_assoc, dhat0_mul_self, one_mul]

theorem eq_of_mem_blk
    {j k : Rest} {d : Dfull} (hj : d ∈ blk j) (hk : d ∈ blk k) : j = k := by
  obtain ⟨h, hψ⟩ := (mem_blk_iff j d).1 hj
  obtain ⟨h', hψ'⟩ := (mem_blk_iff k d).1 hk
  have e : psiW ⟨d, h'⟩ = psiW ⟨d, h⟩ := rfl
  rw [e] at hψ'
  rcases hψ with h1 | h1 <;> rcases hψ' with h2 | h2 <;>
    exact ((pW_eq_iff j k _ _).1 (h1.symm.trans h2)).1

theorem dhat0_mul_inj
    {j k : Rest} {v v' : Dfull} (hv : v ∈ Vhat) (hv' : v' ∈ Vhat)
    (h : dhat 0 j * v = dhat 0 k * v') : j = k ∧ v = v' := by
  have hjk : j = k := eq_of_mem_blk ⟨v, hv, rfl⟩ ⟨v', hv', h.symm⟩
  subst hjk
  exact ⟨rfl, mul_left_cancel h⟩

theorem jhatToKv0_Ctwo
    {g : Dfull} (hg : g ∈ Ctwo) : ∃ a : C,
    ((jhatToKv0 ⟨g, Ctwo_le_Jhat hg⟩ : Kstab v0) : OLq) =
      QuotientGroup.mk (gO a * PO ((thetaC ⟨g, hg⟩ : AutPerm)⁻¹)) := by
  set x := MfrEquiv.symm (piC ⟨g, hg⟩) with hx
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (ΩIn Ceq) (Multiplicative.toAdd x.left)
  have hxe : x = ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), x.right⟩ :=
    SemidirectProduct.ext (by rw [ha]; rfl) rfl
  have hθ : thetaC ⟨g, hg⟩ = x.right := rfl
  refine ⟨Submodule.inclusion ceqHyp.le_C a, ?_⟩
  rw [coe_jhatToKv0, ← coe_piC ⟨g, hg⟩, ← MfrEquiv.apply_symm_apply (piC ⟨g, hg⟩), ← hx,
    coe_MfrEquiv, hxe, monoD_mk, hθ]

theorem wAct_Ctwo_pW
    {g : Dfull} (hg : g ∈ Ctwo) (j : Rest) (b : ZMod 2) :
    ∃ t : ZMod 2, wAct v0 (jhatToKv0 ⟨g, Ctwo_le_Jhat hg⟩) (pW j b) =
      pW ((thetaC ⟨g, hg⟩)⁻¹ • j) (b + t) := by
  obtain ⟨a, he⟩ := jhatToKv0_Ctwo hg
  have hk : (QuotientGroup.mk (gO a * PO ((thetaC ⟨g, hg⟩ : AutPerm)⁻¹)) : OLq) ∈ Kstab v0 :=
    he ▸ (jhatToKv0 ⟨g, Ctwo_le_Jhat hg⟩).2
  have e : jhatToKv0 ⟨g, Ctwo_le_Jhat hg⟩ = ⟨_, hk⟩ := Subtype.ext he
  refine ⟨(a : Fin 24 → ZMod 2) 0 + (a : Fin 24 → ZMod 2) j, ?_⟩
  rw [e, wAct_monomial_pW hk j b, add_assoc]
  rfl

theorem conj_blk_Ctwo
    {g : Dfull} (hg : g ∈ Ctwo) {j : Rest} {d : Dfull} (hd : d ∈ blk j) :
    g⁻¹ * d * g ∈ blk ((thetaC ⟨g, hg⟩)⁻¹ • j) := by
  obtain ⟨h, hψ⟩ := (mem_blk_iff j d).1 hd
  have hJ := Ctwo_le_Jhat hg
  refine (mem_blk_iff _ _).2 ⟨conj_mem_Ehat hJ h, ?_⟩
  rw [psiW_conj hJ h]
  have key : ∀ b : ZMod 2, psiW ⟨d, h⟩ = pW j b →
      wAct v0 (jhatToKv0 ⟨g, hJ⟩) (psiW ⟨d, h⟩) = pW ((thetaC ⟨g, hg⟩)⁻¹ • j) 0 ∨
      wAct v0 (jhatToKv0 ⟨g, hJ⟩) (psiW ⟨d, h⟩) = pW ((thetaC ⟨g, hg⟩)⁻¹ • j) 1 := by
    intro b hb
    obtain ⟨t, ht⟩ := wAct_Ctwo_pW hg j b
    rw [hb, ht]
    rcases zmod2_cases (b + t) with h0 | h0 <;> rw [h0]
    · exact .inl rfl
    · exact .inr rfl
  rcases hψ with h1 | h1
  · exact key 0 h1
  · exact key 1 h1

theorem conj_blk_Ctwo'
    {g : Dfull} (hg : g ∈ Ctwo) {j : Rest} {d : Dfull} (hd : d ∈ blk j) :
    g * d * g⁻¹ ∈ blk (thetaC ⟨g, hg⟩ • j) := by
  have h := conj_blk_Ctwo (Ctwo.inv_mem hg) hd
  have e : thetaC ⟨g⁻¹, Ctwo.inv_mem hg⟩ = (thetaC ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rwa [inv_inv, e, inv_inv] at h

@[expose] def blockP :
    Ntwo →* Ppair :=
  (MonoidHom.fst Ppair (Equiv.Perm (Fin 3))).comp (twoCoreEquiv.toMonoidHom.comp mkK)

theorem blockP_apply
    (n : Ntwo) : blockP n = (twoCoreEquiv (QuotientGroup.mk n)).1 := rfl

theorem blockP_inclCN
    (c : Ctwo) : blockP (inclCN c) = thetaC c := by
  rw [blockP, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    twoCoreEquiv_inclCN]
  rfl

theorem betaK_sym3K
    {b : KN} (hb : b ∈ Bsub) : betaK (sym3K b) = b := by
  have e : sym3K b = betaEquiv ⟨b, hb⟩ := rfl
  rw [e]
  change ((betaEquiv.symm (betaEquiv ⟨b, hb⟩) : Bsub) : KN) = b
  rw [MulEquiv.symm_apply_apply]

theorem twoCoreEquiv_psiK
    (x : Ppair × Equiv.Perm (Fin 3)) : twoCoreEquiv (psiK x) = x :=
  (MulEquiv.ofBijective psiK ⟨psiK_injective, psiK_surjective⟩).symm_apply_apply x

theorem twoCoreEquiv_of_mem_Bsub
    {b : KN} (hb : b ∈ Bsub) : twoCoreEquiv b = (1, sym3K b) := by
  have e : psiK (1, sym3K b) = b := by
    rw [psiK_apply, map_one, one_mul]
    exact betaK_sym3K hb
  calc twoCoreEquiv b = twoCoreEquiv (psiK (1, sym3K b)) := by rw [e]
    _ = (1, sym3K b) := twoCoreEquiv_psiK _

theorem blockP_hhatN :
    blockP hhatN = 1 :=
  congrArg Prod.fst (twoCoreEquiv_of_mem_Bsub (b := mkK hhatN)
    (Subgroup.subset_closure (Set.mem_insert _ _)))

theorem blockP_tauN :
    blockP tauN = 1 :=
  congrArg Prod.fst (twoCoreEquiv_of_mem_Bsub (b := mkK tauN)
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem blockP_of_mem_R2
    {n : Ntwo} (hn : (n : Dfull) ∈ R2) : blockP n = 1 := by
  have h : (QuotientGroup.mk n : KN) = 1 := (QuotientGroup.eq_one_iff n).2 hn
  rw [blockP_apply, h, map_one]
  rfl

theorem blockP_ghat
    (q : Ppair) : blockP (inclCN (ghatC q)) = q := by
  rw [blockP_inclCN, thetaC_ghatC]

theorem hhat_mul_dhat (i j : Fin 24) : hhat * dhat i j = dhat i j * hhat := by
  have h : (⟨hE0, hE0_mem_Cgen⟩ : Cgen) *
      ⟨rhoEquiv (rMinus i j), rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩ =
      ⟨rhoEquiv (rMinus i j), rhoEquiv_mem_Cgen (DQ_mem_centralizer _)⟩ *
      ⟨hE0, hE0_mem_Cgen⟩ := by
    apply Subtype.ext
    change hE0 * rhoEquiv (rMinus i j) = rhoEquiv (rMinus i j) * hE0
    rw [hE0, rMinus, ← rhoEquiv_mul, ← rhoEquiv_mul, DQ_comm]
  have := congrArg (fun x => iotaD (kappa x)) h
  simp only [map_mul] at this
  exact this

@[expose] def Bh : Subgroup Ntwo := Subgroup.closure {hhatN, tauN}

theorem Bh_le_ker_blockP :
    Bh ≤ blockP.ker := by
  rw [Bh, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact blockP_hhatN
  · exact blockP_tauN

theorem Bh_comm_dhat {b : Ntwo} (hb : b ∈ Bh) (i j : Fin 24) :
    (b : Dfull) * dhat i j = dhat i j * b := by
  have hle : Bh ≤ (Subgroup.centralizer {dhat i j}).comap Ntwo.subtype := by
    rw [Bh, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_comap.2 (Subgroup.mem_centralizer_singleton_iff.2
        (hhat_mul_dhat i j))
    · exact Subgroup.mem_comap.2 (Subgroup.mem_centralizer_singleton_iff.2
        (tauhat_mul_dhat i j))
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (hle hb))

theorem exists_Bh_sym3Hom (n : Ntwo) : ∃ b ∈ Bh, sym3Hom b = sym3Hom n := by
  have h : Bh.map sym3Hom = ⊤ := by
    rw [Bh, MonoidHom.map_closure, Set.image_pair, sym3Hom_hhatN, sym3Hom_tauN, Set.pair_comm,
      closure_three]
  have hσ : sym3Hom n ∈ Bh.map sym3Hom := h ▸ Subgroup.mem_top _
  obtain ⟨b, hb, he⟩ := hσ
  exact ⟨b, hb, he⟩

theorem conj_blk_Bh {b : Ntwo} (hb : b ∈ Bh) {j : Rest} {d : Dfull} (hd : d ∈ blk j) :
    (b : Dfull) * d * (b : Dfull)⁻¹ ∈ blk j := by
  obtain ⟨v, hv, rfl⟩ := hd
  refine ⟨(b : Dfull) * v * (b : Dfull)⁻¹, conj_mem_Vhat b.2 hv, ?_⟩
  rw [show (b : Dfull) * (dhat 0 j * v) * (b : Dfull)⁻¹ =
    ((b : Dfull) * dhat 0 j) * (v * (b : Dfull)⁻¹) by group, Bh_comm_dhat hb]
  group

theorem conj_blk_Ntwo
    (n : Ntwo) {j : Rest} {d : Dfull} (hd : d ∈ blk j) :
    (n : Dfull) * d * (n : Dfull)⁻¹ ∈ blk (blockP n • j) := by
  obtain ⟨b, hb, hbn⟩ := exists_Bh_sym3Hom n
  have hgC : ((n * b⁻¹ : Ntwo) : Dfull) ∈ Ctwo := by
    rw [mem_Ctwo_iff_sym3Hom, map_mul, map_inv, hbn, mul_inv_cancel]
  have hP : blockP n = thetaC ⟨_, hgC⟩ := by
    have e : n = inclCN ⟨_, hgC⟩ * b := by
      apply Subtype.ext
      change (n : Dfull) = (n : Dfull) * (b : Dfull)⁻¹ * b
      group
    calc blockP n = blockP (inclCN ⟨_, hgC⟩ * b) := congrArg blockP e
      _ = thetaC ⟨_, hgC⟩ := by rw [map_mul, blockP_inclCN, Bh_le_ker_blockP hb, mul_one]
  have h1 := conj_blk_Bh hb hd
  have h2 := conj_blk_Ctwo' hgC h1
  rw [hP]
  have e : (n : Dfull) * d * (n : Dfull)⁻¹ = ((n * b⁻¹ : Ntwo) : Dfull) *
      ((b : Dfull) * d * (b : Dfull)⁻¹) * ((n * b⁻¹ : Ntwo) : Dfull)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact h2

theorem image_conj_blk
    (n : Ntwo) (j : Rest) :
    (fun d => (n : Dfull) * d * (n : Dfull)⁻¹) '' blk j = blk (blockP n • j) := by
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact conj_blk_Ntwo n hd
  · intro hy
    refine ⟨(n : Dfull)⁻¹ * y * n, ?_, by group⟩
    have h := conj_blk_Ntwo n⁻¹ hy
    rw [map_inv, inv_smul_smul] at h
    simpa only [Subgroup.coe_inv, inv_inv] using h

theorem conj_blk_R2
    {r : Dfull} (hr : r ∈ R2) {j : Rest} {d : Dfull} (hd : d ∈ blk j) :
    r * d * r⁻¹ ∈ blk j := by
  have h := conj_blk_Ntwo ⟨r, R2_le_Ntwo hr⟩ hd
  rwa [blockP_of_mem_R2 (n := ⟨r, R2_le_Ntwo hr⟩) hr, one_smul] at h

@[expose] def rest2 : Rest := ⟨2, by decide, by decide⟩

theorem cQ_eq_dhat : cQ = dhat 0 rest2 := rfl

theorem cQ_mem_blk : cQ ∈ blk rest2 := dhat_mem_blk rest2

theorem psiW_cQ :
    psiW ⟨cQ, cQ_mem_Ehat⟩ = pW rest2 0 := psiW_dhat0 rest2

theorem mem_R2_of_Ehat
    {e : Dfull} (he : e ∈ Ehat) (hC : e ∈ Ctwo) : e ∈ R2 := by
  rw [mem_R2_iff hC, thetaC, MonoidHom.comp_apply]
  have h : piC ⟨e, hC⟩ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_piC, jhatToKv_eq_one_of_mem_Ehat he]
    rfl
  rw [h, map_one]

theorem pW_not_mem_span_wFr
    (j : Rest) (b : ZMod 2) : pW j b ∉ (ZMod 2) ∙ wFr := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  rcases zmod2_cases a with rfl | rfl
  · rw [zero_smul] at ha
    exact pW_ne_zero j b ha.symm
  · rw [one_smul] at ha
    exact pW_ne_wFr j b ha.symm

theorem exists_R2_xhat :
    ∃ r ∈ R2, r * cQ * r⁻¹ = cQ * xhat := by
  obtain ⟨e, he, hb⟩ := exists_Ehat_bV_eq_one (pW_not_mem_span_wFr rest2 0)
  have hw : bV wFr (psiW e) = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.1 he) wFr (Submodule.mem_span_singleton_self _)
  have hC : (e : Dfull) ∈ Ctwo := by
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have h := Ehat_comm ⟨v, Vhat_le_Ehat hv⟩ e
    have h0 : bV (psiW ⟨v, Vhat_le_Ehat hv⟩) (psiW e) = 0 := by
      rcases psiW_of_mem_Vhat hv with h1 | h1 <;> rw [h1]
      · exact LinearMap.map_zero₂ _ _
      · exact hw
    rw [h0, ZMod.val_zero, pow_zero, mul_one] at h
    exact h
  refine ⟨(e : Dfull)⁻¹, R2.inv_mem (mem_R2_of_Ehat e.2 hC), ?_⟩
  have h := conj_Ehat ⟨cQ, cQ_mem_Ehat⟩ e
  rw [psiW_cQ, hb, xhat_pow_val_one] at h
  rw [inv_inv]
  exact h

theorem B6_mem_Ceq : B 6 ∈ Ceq := mem_Ceq.2 ⟨B_mem_C 6, by decide⟩

theorem exists_R2_yhat :

    ∃ r ∈ R2, r * cQ * r⁻¹ = cQ * yhat ∨ r * cQ * r⁻¹ = cQ * yhat * xhat := by
  set m : Mfr := MfrEquiv ⟨Multiplicative.ofAdd (Submodule.Quotient.mk ⟨B 6, B6_mem_Ceq⟩), 1⟩
  obtain ⟨g, hg⟩ := piC_surjective m
  have hθ : thetaC g = 1 := by
    rw [thetaC, MonoidHom.comp_apply, hg, projP_MfrEquiv]
  have hR : (g : Dfull) ∈ R2 := (mem_R2_iff g.2).2 hθ
  have hk : (QuotientGroup.mk (gO ⟨B 6, B_mem_C 6⟩ * PO ((1 : Ppair) : AutPerm)⁻¹) : OLq) ∈
      Kstab v0 := (mk_mem_Kstab_iff_monomial _ _).2 ⟨Ppair.inv_mem Ppair.one_mem, B6_mem_Ceq⟩
  have he : jhatToKv0 ⟨g, Ctwo_le_Jhat g.2⟩ = ⟨_, hk⟩ := by
    apply Subtype.ext
    rw [coe_jhatToKv0, ← coe_piC, hg, coe_MfrEquiv, monoD_mk]
    rfl
  have hJ := Ctwo_le_Jhat g.2
  have hψ := psiW_conj hJ cQ_mem_Ehat
  have hψ' : psiW ⟨cQ, cQ_mem_Ehat⟩ = pW rest2 0 := psiW_cQ
  rw [hψ', show (⟨(g : Dfull), hJ⟩ : Jhat) = ⟨g, Ctwo_le_Jhat g.2⟩ from rfl, he,
    wAct_monomial_pW hk rest2 0] at hψ
  have hr : restImg ((mk_mem_Kstab_iff_monomial _ _).1 hk).1 rest2 = rest2 := rfl
  have hb : (0 : ZMod 2) + B 6 0 + B 6 2 = 1 := by decide
  rw [hr] at hψ
  change psiW _ = pW rest2 ((0 : ZMod 2) + B 6 0 + B 6 2) at hψ
  rw [hb, pW_one, ← psiW_cQ] at hψ
  have hc : (g : Dfull)⁻¹ * cQ * g ∈ blk rest2 := by
    have h := conj_blk_Ctwo g.2 cQ_mem_blk
    rwa [show (⟨(g : Dfull), g.2⟩ : Ctwo) = g from rfl, hθ, inv_one, one_smul] at h
  obtain ⟨v, hv, hve⟩ := hc
  have hvψ : psiW ⟨v, Vhat_le_Ehat hv⟩ = wFr := by
    have e1 : (⟨(g : Dfull)⁻¹ * cQ * g, conj_mem_Ehat hJ cQ_mem_Ehat⟩ : Ehat) =
        ⟨cQ, cQ_mem_Ehat⟩ * ⟨v, Vhat_le_Ehat hv⟩ := Subtype.ext hve.symm
    rw [e1, psiW_mul] at hψ
    have := congrArg (fun x => psiW ⟨cQ, cQ_mem_Ehat⟩ + x) hψ
    simp only [← add_assoc, two_add_self, zero_add] at this
    exact this
  refine ⟨(g : Dfull)⁻¹, R2.inv_mem hR, ?_⟩
  rw [inv_inv, ← hve, ← cQ_eq_dhat]
  rcases fiber_cases (hvψ.trans psiW_yhat.symm) with h1 | h1
  · left
    rw [show v = yhat from h1]
  · right
    rw [show v = yhat * xhat from h1, mul_assoc]

theorem blk_two_orbit
    {d : Dfull} (hd : d ∈ blk rest2) : ∃ r ∈ R2, r * cQ * r⁻¹ = d := by
  obtain ⟨r₁, hr₁, h₁⟩ := exists_R2_xhat
  obtain ⟨r₂, hr₂, h₂⟩ := exists_R2_yhat
  obtain ⟨v, hv, rfl⟩ := hd
  rw [← cQ_eq_dhat]
  have hx : r₂ * xhat * r₂⁻¹ = xhat := by
    rw [xhat_comm_of_mem_Jhat (Ctwo_le_Jhat (R2_le_Ctwo hr₂)), mul_inv_cancel_right]
  have h₁₂ : (r₂ * r₁) * cQ * (r₂ * r₁)⁻¹ = (r₂ * cQ * r₂⁻¹) * xhat := by
    calc (r₂ * r₁) * cQ * (r₂ * r₁)⁻¹ = r₂ * (r₁ * cQ * r₁⁻¹) * r₂⁻¹ := by group
      _ = (r₂ * cQ * r₂⁻¹) * (r₂ * xhat * r₂⁻¹) := by rw [h₁]; group
      _ = (r₂ * cQ * r₂⁻¹) * xhat := by rw [hx]
  have hxy : xhat * yhat = yhat * xhat := Vhat_comm xhat_mem_Vhat yhat_mem_Vhat
  have hxx := xhat_mul_self
  rcases (mem_Vhat_iff v).1 hv with rfl | rfl | rfl | rfl
  · exact ⟨1, R2.one_mem, by rw [one_mul, inv_one, mul_one]⟩
  · exact ⟨r₁, hr₁, by rw [h₁]⟩
  · rcases h₂ with h₂ | h₂
    · exact ⟨r₂ * r₁, R2.mul_mem hr₂ hr₁, by rw [h₁₂, h₂, hxy, mul_assoc]⟩
    · exact ⟨r₂, hr₂, by rw [h₂, hxy, mul_assoc]⟩
  · rcases h₂ with h₂ | h₂
    · exact ⟨r₂, hr₂, by rw [h₂]⟩
    · refine ⟨r₂ * r₁, R2.mul_mem hr₂ hr₁, ?_⟩
      rw [h₁₂, h₂, mul_assoc, mul_assoc, hxx, mul_one]

instance isPretransitive_rest' :
    MulAction.IsPretransitive Ppair Rest :=
  @MulAction.isPretransitive_of_is_two_pretransitive _ _ _ _ isMultiplyPretransitive_rest

theorem exists_Ntwo_blk
    (j : Rest) : ∃ n : Ntwo, blockP n • rest2 = j := by
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Ppair rest2 j
  exact ⟨inclCN (ghatC q), by rw [blockP_ghat, hq]⟩

theorem blk_R2_transitive
    (j : Rest) {x y : Dfull} (hx : x ∈ blk j) (hy : y ∈ blk j) :
    ∃ r ∈ R2, r * x * r⁻¹ = y := by
  obtain ⟨n, hn⟩ := exists_Ntwo_blk j
  rw [← hn, ← image_conj_blk] at hx hy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  obtain ⟨r₁, hr₁, rfl⟩ := blk_two_orbit hx₀
  obtain ⟨r₂, hr₂, rfl⟩ := blk_two_orbit hy₀
  refine ⟨(n : Dfull) * (r₂ * r₁⁻¹) * (n : Dfull)⁻¹,
    conj_mem_R2 n.2 (R2.mul_mem hr₂ (R2.inv_mem hr₁)), ?_⟩
  group

end CFSG.Monster.B.TwoA.Par2
