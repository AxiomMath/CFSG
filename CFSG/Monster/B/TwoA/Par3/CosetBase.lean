
module

public import CFSG.Monster.B.TwoA.Par2.Blocks
public import CFSG.Monster.B.TwoA.Base.RankThreeParBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Par3

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Par2
  CFSG.Monster.VisCert

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

abbrev sig :
    Wv v0 := pW rest2 0

theorem sig_eq_decW :
    sig = decW 6144 := by
  obtain ⟨hm, he⟩ := decW_eq_mk 6144
  rw [he, sig, pW]
  congr 1
  apply Subtype.ext
  change pairCls 0 2 0 = dec (Native.actD 22 Native.quotientBasis 6144)
  rw [show Native.actD 22 Native.quotientBasis 6144 = 20480 by decide]
  exact cls_pairN_eq (by decide) (pairN_eq 0 2 (by decide)) (by decide +kernel)

theorem sig_not_mem_Uplane :
    sig ∉ Uplane := by
  rw [mem_Uplane_iff, sig_eq_decW, wFr_eq_decW, sW, pairW23_eq_decW, ← decW_xor, ← decW_zero]
  rintro (h | h | h | h) <;>
    exact absurd (decW_injective (by norm_num) (by norm_num) h) (by decide)

theorem bV_sig_wFr :
    bV sig wFr = 0 := by
  rw [sig, pW, wFr, polarBilin_qW_mk, bL_comm]
  exact bL_twoΩCls_pairCls (by decide) 0

theorem hInt_pairVec_02_23 : hInt (pairVec 0 2 0) (pairVec 2 3 0) = -2 := by
  decide +kernel

theorem bV_sig_sW :
    bV sig sW = 0 := by
  rw [sig, pW, sW, pairW, polarBilin_qW_mk]
  change bL (pairCls 0 2 0) (pairCls 2 3 0) = 0
  rw [pairCls, pairCls, Griess.classOf_eq_cls (pairVec_mem (by decide) 0).1,
    Griess.classOf_eq_cls (pairVec_mem (by decide) 0).1, bL_apply]
  change QuadraticMap.polarBilin qL _ _ = 0
  rw [bL_cls, hInt_pairVec_02_23]
  rfl

theorem bV_sig_of_mem
    {u : Wv v0} (hu : u ∈ Uplane) : bV u sig = 0 := by
  rcases (mem_Uplane_iff u).1 hu with rfl | rfl | rfl | rfl
  · exact LinearMap.map_zero₂ _ _
  · rw [bV_comm, bV_sig_wFr]
  · rw [bV_comm, bV_sig_sW]
  · rw [map_add, LinearMap.add_apply, bV_comm, bV_sig_wFr, bV_comm, bV_sig_sW, add_zero]

@[expose] def U4 :
    Submodule (ZMod 2) (Wv v0) := Uplane ⊔ (ZMod 2) ∙ sig

theorem sig_mem_U4 :

    sig ∈ U4 := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem mem_U4_iff
    (x : Wv v0) : x ∈ U4 ↔ x ∈ Uplane ∨ x + sig ∈ Uplane := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rcases zmod2_cases a with rfl | rfl
    · left
      rw [zero_smul, add_zero]
      exact hy
    · right
      rw [one_smul, add_assoc, two_add_self, add_zero]
      exact hy
  · rintro (h | h)
    · exact Submodule.mem_sup_left h
    · have e : x = (x + sig) + sig := by rw [add_assoc, two_add_self, add_zero]
      rw [e]
      exact U4.add_mem (Submodule.mem_sup_left h) sig_mem_U4

theorem qV_U4 :
    ∀ x ∈ U4, qV x = 0 := by
  intro x hx
  rcases (mem_U4_iff x).1 hx with h | h
  · exact qV_Uplane x h
  · have e : x = (x + sig) + sig := by rw [add_assoc, two_add_self, add_zero]
    rw [e, qV_add, qV_Uplane _ h, qV_pW, bV_sig_of_mem h, add_zero, add_zero]

theorem Uplane_inf_span_sig :
    Uplane ⊓ (ZMod 2) ∙ sig = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hU, hs⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hs
  rcases zmod2_cases a with rfl | rfl
  · rw [zero_smul]
    exact Submodule.zero_mem _
  · rw [one_smul] at hU
    exact absurd hU sig_not_mem_Uplane

theorem finrank_U4 :
    Module.finrank (ZMod 2) U4 = 3 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq Uplane ((ZMod 2) ∙ sig)
  rw [Uplane_inf_span_sig, finrank_bot, add_zero, finrank_Uplane,
    finrank_span_singleton (pW_ne_zero rest2 0)] at h
  exact h

theorem natCard_U4 :
    Nat.card U4 = 8 := by
  rw [natCard_submodule, finrank_U4]
  rfl

@[expose] def E4 :
    Subgroup Dfull := EU U4

theorem E3_le_E4 :
    E3 ≤ E4 := by
  rw [E3_eq_EU]
  exact EU_mono le_sup_left

theorem cQ_mem_E4 :
    cQ ∈ E4 :=
  mem_EU_of (e := ⟨cQ, cQ_mem_Ehat⟩) (by rw [psiW_cQ]; exact sig_mem_U4)

theorem mem_E3_iff
    (d : Dfull) : d ∈ E3 ↔ ∃ h : d ∈ Ehat, psiW ⟨d, h⟩ ∈ Uplane := by
  rw [E3_eq_EU]
  exact mem_EU

theorem psiW_cQ_mul
    {d : Dfull} (h : d ∈ Ehat) :
    psiW ⟨cQ * d, Ehat.mul_mem cQ_mem_Ehat h⟩ = sig + psiW ⟨d, h⟩ := by
  have e : (⟨cQ * d, Ehat.mul_mem cQ_mem_Ehat h⟩ : Ehat) = ⟨cQ, cQ_mem_Ehat⟩ * ⟨d, h⟩ := rfl
  rw [e, psiW_mul, psiW_cQ]

theorem cQ_mul_self' :
    cQ * cQ = 1 := dhat0_mul_self rest2

theorem closure_eq_E4 :
    Subgroup.closure (insert cQ (E3 : Set Dfull)) = E4 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | h)
    · exact cQ_mem_E4
    · exact E3_le_E4 h
  · intro d hd
    obtain ⟨h, hψ⟩ := mem_EU.1 hd
    have hc : cQ ∈ Subgroup.closure (insert cQ (E3 : Set Dfull)) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hE : ∀ e ∈ E3, e ∈ Subgroup.closure (insert cQ (E3 : Set Dfull)) := fun e he =>
      Subgroup.subset_closure (Set.mem_insert_of_mem _ he)
    rcases (mem_U4_iff _).1 hψ with h1 | h1
    · exact hE d ((mem_E3_iff d).2 ⟨h, h1⟩)
    · have h2 : cQ * d ∈ E3 := (mem_E3_iff _).2 ⟨Ehat.mul_mem cQ_mem_Ehat h, by
        rw [psiW_cQ_mul, add_comm]; exact h1⟩
      have e : d = cQ * (cQ * d) := by rw [← mul_assoc, cQ_mul_self', one_mul]
      rw [e]
      exact Subgroup.mul_mem _ hc (hE _ h2)

instance isElementaryAbelian_E4 :
    CFSG.IsElementaryAbelian 2 E4 := isElementaryAbelian_EU qV_U4

theorem natCard_E4 :
    Nat.card E4 = 16 := by
  rw [E4, natCard_EU, natCard_U4]

@[expose] def cE3 : Set Dfull := {d | ∃ e ∈ E3, cQ * e = d}

theorem mem_cE3_iff
    (d : Dfull) : d ∈ cE3 ↔ ∃ h : d ∈ Ehat, psiW ⟨d, h⟩ + sig ∈ Uplane := by
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨h, hψ⟩ := (mem_E3_iff e).1 he
    refine ⟨Ehat.mul_mem cQ_mem_Ehat h, ?_⟩
    rw [psiW_cQ_mul, add_comm, ← add_assoc, two_add_self, zero_add]
    exact hψ
  · rintro ⟨h, hψ⟩
    refine ⟨cQ * d, (mem_E3_iff _).2 ⟨Ehat.mul_mem cQ_mem_Ehat h, ?_⟩, ?_⟩
    · rw [psiW_cQ_mul, add_comm]
      exact hψ
    · rw [← mul_assoc, cQ_mul_self', one_mul]

theorem cQ_mem_cE3 : cQ ∈ cE3 := ⟨1, E3.one_mem, mul_one _⟩

theorem cQ_not_mem_E3 :
    cQ ∉ E3 := by
  intro h
  obtain ⟨h', hψ⟩ := (mem_E3_iff cQ).1 h
  rw [show (⟨cQ, h'⟩ : Ehat) = ⟨cQ, cQ_mem_Ehat⟩ from rfl, psiW_cQ] at hψ
  exact sig_not_mem_Uplane hψ

theorem mem_cE3_of_mem_E4
    {d : Dfull} (hd : d ∈ E4) (hd' : d ∉ E3) : d ∈ cE3 := by
  obtain ⟨h, hψ⟩ := mem_EU.1 hd
  rcases (mem_U4_iff _).1 hψ with h1 | h1
  · exact absurd ((mem_E3_iff d).2 ⟨h, h1⟩) hd'
  · exact (mem_cE3_iff d).2 ⟨h, h1⟩

@[expose] def rest3 : Rest := ⟨3, by decide, by decide⟩

theorem pairVec_02_add_23 : pairVec 0 2 0 + pairVec 2 3 0 = pairVec 0 3 0 := by
  decide +kernel

theorem pW_rest3 :
    pW rest3 0 = sig + sW := by
  rw [sig, pW, pW, sW, pairW, ← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  change pairCls 0 3 0 = pairCls 0 2 0 + pairCls 2 3 0
  rw [pairCls, pairCls, pairCls, ← Griess.classOf_add_of_mem (pairVec_mem (by decide) 0).1
    (pairVec_mem (by decide) 0).1, pairVec_02_add_23]

@[expose] def Good
    (k : Kstab v0) : Prop := wAct v0 k sig + sig ∈ Uplane

theorem good_pW
    {j : Rest} (hj : (j : Fin 24) = 2 ∨ (j : Fin 24) = 3) (t : ZMod 2) :
    pW j t + sig ∈ Uplane := by
  have hw : ∀ t : ZMod 2, pW j t = pW j 0 + t • wFr := fun t => by
    rcases zmod2_cases t with rfl | rfl
    · rw [zero_smul, add_zero]
    · rw [one_smul, pW_one]
  rw [hw t]
  rcases hj with h | h
  · have e : j = rest2 := Subtype.ext h
    subst e
    rw [add_comm, ← add_assoc, two_add_self, zero_add]
    exact Uplane.smul_mem _ wFr_mem_Uplane
  · have e : j = rest3 := Subtype.ext h
    subst e
    rw [pW_rest3, show sig + sW + t • wFr + sig = (sig + sig) + (sW + t • wFr) by abel,
      two_add_self, zero_add]
    exact Uplane.add_mem sW_mem_Uplane (Uplane.smul_mem _ wFr_mem_Uplane)

theorem good_of_mem_NUw
    {k : Kstab v0} (hk : k ∈ NU ⊓ Mfr) : Good k := by
  obtain ⟨a, -, p, hp, hap⟩ := (mem_monoSub_iff ceqFtwoHyp).1 ((mem_NUw_iff k).1 hk)
  have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hap ▸ k.2
  have e : k = ⟨_, hk'⟩ := Subtype.ext hap
  rw [Good, e, wAct_monomial_pW hk' rest2 0]
  refine good_pW ?_ _
  rcases ((mem_Ftwo_iff p).1 hp).2 with ⟨h2, -⟩ | ⟨h2, -⟩
  · exact .inl h2
  · exact .inr h2

theorem good_mul
    {k k' : Kstab v0} (hk : Good k) (hk' : Good k') (hN : k' ∈ NU) :
    Good (k * k') := by
  have e : wAct v0 k sig = (wAct v0 k sig + sig) + sig := by
    rw [add_assoc, two_add_self, add_zero]
  rw [Good, wAct_mul, Module.End.mul_apply, e, map_add,
    show wAct v0 k' (wAct v0 k sig + sig) + wAct v0 k' sig + sig =
      wAct v0 k' (wAct v0 k sig + sig) + (wAct v0 k' sig + sig) by abel]
  exact Uplane.add_mem (hN _ hk) hk'

theorem wAct_ne_zero (k : Kstab v0) {x : Wv v0} (hx : x ≠ 0) : wAct v0 k x ≠ 0 := by
  intro h
  apply hx
  rw [← wAct_inv_apply k x, h, map_zero]

theorem mem_Mfr_of_fix
    {k : Kstab v0} (h : wAct v0 k wFr = wFr) : k ∈ Mfr := mem_wStab.2 h

theorem sgnK_mem_NUw :
    sgnK ∈ NU ⊓ Mfr := ⟨sgnK_mem_NU, sgnK_mem_Mfr⟩

theorem tauhat_mem_normalizer_E4 :
    tauhat ∈ Subgroup.normalizer (E4 : Set Dfull) := by
  rw [← closure_eq_E4]
  refine mem_normalizer_of_closure ?_
  rintro _ (rfl | h)
  · rw [cQ, tauhat_mul_dhat, mul_inv_cancel_right]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _
      (conj_mem_of_normalizer tauhat_mem_normalizer_E3 h))

theorem R3_le_C3 :
    R3 ≤ C3 := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem R3_le_K3 :
    R3 ≤ K3 := R3_le_C3.trans C3_le_K3

theorem mem_R3_of_Ehat
    {e : Dfull} (he : e ∈ Ehat) (hC : e ∈ C3) : e ∈ R3 := by
  refine ⟨⟨e, hC⟩, ?_, rfl⟩
  have h1 : c3Proj ⟨e, hC⟩ = 1 := by
    rw [← MonoidHom.mem_ker, ker_c3Proj, Subgroup.mem_subgroupOf]
    exact ⟨he, hC⟩
  change c3Proj ⟨e, hC⟩ ∈ CFSG.pCore 2 CU
  rw [h1]
  exact Subgroup.one_mem _

theorem exists_R3_xhat :
    ∃ r ∈ R3, r * cQ * r⁻¹ = cQ * xhat := by
  obtain ⟨e, he, hb⟩ := exists_Ehat_bV_eq_one sig_not_mem_Uplane
  have hC : (e : Dfull) ∈ C3 := by
    have h1 : (e : Dfull) ∈ EU (bV.orthogonal Uplane) := mem_EU_of he
    rw [← Ehat_inf_centralizer_EU] at h1
    rw [C3_eq]
    exact h1.2
  refine ⟨(e : Dfull)⁻¹, R3.inv_mem (mem_R3_of_Ehat e.2 hC), ?_⟩
  have h := conj_Ehat ⟨cQ, cQ_mem_Ehat⟩ e
  rw [psiW_cQ, hb, xhat_pow_val_one] at h
  rw [inv_inv]
  exact h

theorem conj_mem_R3
    {k : Dfull} (hk : k ∈ K3) {r : Dfull} (hr : r ∈ R3) : k * r * k⁻¹ ∈ R3 := by
  have h := (R3_subgroupOf_normal).conj_mem ⟨r, R3_le_K3 hr⟩ hr ⟨k, hk⟩
  exact h

end CFSG.Monster.B.TwoA.Par3
