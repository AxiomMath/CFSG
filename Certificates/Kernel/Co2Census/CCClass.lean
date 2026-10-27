module

public import Certificates.Kernel.Co2Census.CCSqrt
public import Certificates.Kernel.Co2Census.CCKO
public import CFSG.Sporadic.Co2Smith.CData
public import CFSG.Sporadic.Co2Smith.ClassCountFin
public import Certificates.Kernel.Co2Census.CCCount

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


theorem cR_eq (i : ℕ) : cR i = cE (Native.ccReps[i]!).1 (Native.ccReps[i]!).2 := rfl

theorem cc_rep (i : Fin 9) :
    cR i * cR i = 1 ∧ cR i ≠ 1 ∧ cR i ≠ zCz ∧ ceInv (cR i) = Native.ccCE[(i : ℕ)]! ∧
      invEInv (cR i) = Native.ccInvE[(i : ℕ)]! := by
  fin_cases i
  · exact rep_facts (er := 1) (nr := 0) (by norm_num) K0_rep
  · exact rep_facts (er := 0) (nr := 26805) (by norm_num) K1_rep
  · exact rep_facts (er := 32) (nr := 26805) (by norm_num) K2_rep
  · exact rep_facts (er := 0) (nr := 2331) (by norm_num) K3_rep
  · exact rep_facts (er := 2) (nr := 2331) (by norm_num) K4_rep
  · exact rep_facts (er := 80) (nr := 2331) (by norm_num) K5_rep
  · exact rep_facts (er := 0) (nr := 1082) (by norm_num) K6_rep
  · exact rep_facts (er := 13) (nr := 1082) (by norm_num) K7_rep
  · exact rep_facts (er := 0) (nr := 144) (by norm_num) K8_rep

theorem cc_sqrt (i : Fin 9) :
    sqrtCnt zCz (cR i) = Native.ccSqZ[(i : ℕ)]! ∧
      sqrtCnt (cR i) (cR i) = Native.ccSqR[(i : ℕ)]! := by
  fin_cases i
  · exact cc_sqrt0
  · exact cc_sqrt1
  · exact cc_sqrt2
  · exact cc_sqrt3
  · exact cc_sqrt4
  · exact cc_sqrt5
  · exact cc_sqrt6
  · exact cc_sqrt7
  · exact cc_sqrt8

theorem cc_cls_ge (i : Fin 9) : Native.ccCls[(i : ℕ)]! ≤ (conjSet (cR i)).ncard := by
  fin_cases i
  · exact cc_cls0
  · exact cc_cls1
  · exact cc_cls2
  · exact cc_cls3
  · exact cc_cls4
  · exact cc_cls5
  · exact cc_cls6
  · exact cc_cls7
  · exact cc_cls8

theorem cent_26805_le :
    centS0 (sElt 26805) ⊆ (gensSub (fun l => sElt (C26805Gt l)) 3 : Set K) := by
  have hmisc := C26805_misc
  simp only [centMisc, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at hmisc
  obtain ⟨h0, hg⟩ := hmisc
  have hsteps : MulSteps repK (rmStep C26805GRt) 3 fun l => sElt (C26805Gt l) := by
    intro l hl x M hx
    have e : rmStep C26805GRt l M = mulV M (SK (C26805Gt l)) := by
      rw [rmStep, (hg l hl).1]
    rw [e]
    exact repK_mul hx (repK_sElt _)
  have h1 : repK 1 (C26805Pt 0) := by
    rw [h0]
    exact repK_one
  rw [← cent_26805, mul_record (rep := repK) (fun _ _ _ h h' => repK_fun h h') hsteps C26805_tree
    C26805_clos (by norm_num) (fun i hi => Nat.eq_of_beq_eq_true (C26805_root i hi)) h1]

abbrev O1set : Set K := {x | ∃ i < 16, repK x (O1t i)}

theorem O1_conj {g : K} {G GI : ℕ} (hg : repK g G) (hgi : GI < 2 ^ 484) (hgg : mulV G GI = IDP)
    {l : ℕ} (hl : l < 515) (hG : o1G l = G) (hGI : o1GI l = GI) :
    ∀ y ∈ O1set, g * y * g⁻¹ ∈ O1set := by
  rintro y ⟨i, hi, hy⟩
  have h := O1_clos (16 * l + i) (by omega)
  have hl' : (16 * l + i) / 16 = l := by omega
  have hi' : (16 * l + i) % 16 = i := by omega
  simp only [letB_eq, hl', hi', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  refine ⟨_, h.1, ?_⟩
  rw [← h.2, hG, hGI]
  exact repK_mul (repK_mul hg hy) (repK_inv hg hgi hgg)

theorem cc_not_conj12 (h : Cz) : h * cR 1 * h⁻¹ ≠ cR 2 := by
  intro e
  obtain ⟨eh, heh, nh, -, rfl⟩ := exists_cE h
  have hO : ∀ y ∈ O1set, (cElt eh nh : K) * y * (cElt eh nh)⁻¹ ∈ O1set := by
    intro y hy
    have hq := QI_ok eh heh
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hq
    have hy' := O1_conj (g := qElt eh) (repK_qElt' heh) (QK_lt' hq.1) hq.2 (l := eh)
      (by omega) (by rw [o1G, if_pos heh]) (by rw [o1GI, if_pos heh]) y hy
    have hc : sElt nh ∈ centS0 (sElt 26805) := by
      refine ⟨sElt_mem_S0 nh, ?_⟩
      have h2 := congrArg piC e
      simp only [map_mul, map_inv, piC_cE, cR_eq] at h2
      change sElt nh * sElt 26805 * (sElt nh)⁻¹ = sElt 26805 at h2
      calc sElt nh * sElt 26805 = sElt nh * sElt 26805 * (sElt nh)⁻¹ * sElt nh := by group
        _ = sElt 26805 * sElt nh := by rw [h2]
    have hgen := cent_26805_le hc
    have hcl : ∀ l < 3, ∀ y ∈ O1set, sElt (C26805Gt l) * y * (sElt (C26805Gt l))⁻¹ ∈ O1set := by
      intro l hl
      have hm := C26805_misc
      simp only [centMisc, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at hm
      have hgi := C26805GI_ok
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, List.all_eq_true, List.mem_range]
        at hgi
      refine O1_conj (G := C26805GRt l) (by rw [(hm.2 l hl).1]; exact repK_sElt _) (hgi l hl).2
        (hgi l hl).1 (l := l + 512) (by omega) ?_ ?_
      · rw [o1G, if_neg (by omega), Nat.add_sub_cancel]
      · rw [o1GI, if_neg (by omega), Nat.add_sub_cancel]
    have h3 := conj_closure (S := O1set) (pts_finite (N := 16) (P := O1t)
      (fun _ _ _ h h' => repK_fun h h')) hcl _ hgen _ hy'
    rw [cElt]
    convert h3 using 1
    group
  have h1 : ((cR 1 : Cz) : K) ∈ O1set := by
    have hm := O1_misc
    simp only [Bool.and_eq_true, Nat.beq_eq] at hm
    rw [show cR 1 = cE 0 26805 from rfl]
    exact ⟨0, by norm_num, hm.1 ▸ repK_cE QK_eq (by norm_num) 26805⟩
  have h2 := hO _ h1
  rw [show (cElt eh nh : K) * ((cR 1 : Cz) : K) * (cElt eh nh)⁻¹ = ((cR 2 : Cz) : K) by
    rw [← e]; rfl] at h2
  obtain ⟨i, hi, hr⟩ := h2
  have hm := O1_misc
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    Nat.blt_eq] at hm
  rw [show cR 2 = cE 32 26805 from rfl] at hr
  exact Nat.ne_of_beq_eq_false (hm.2 i hi).2 (repK_unique hr (repK_cE QK_eq (by norm_num) 26805))

theorem cc_not_conj_cls {er nr er' nr' j j' : ℕ} (hj : j < 5) (hj' : j' < 5)
    (hr : s0Rep j = sElt nr) (hr' : s0Rep j' = sElt nr')
    (hs : s0Sizes.getD j 0 ≠ s0Sizes.getD j' 0) (h : Cz) :
    h * cE er nr * h⁻¹ ≠ cE er' nr' := by
  intro e
  have h2 := congrArg piC e
  simp only [map_mul, map_inv, piC_cE] at h2
  apply hs
  rw [← (s0_class hj).2, ← (s0_class hj').2, (s0_class hj).1, (s0_class hj').1, hr, hr']
  congr 1
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w * (piC h)⁻¹, S0.mul_mem hw (S0.inv_mem (piC_mem h)), ?_⟩
    rw [← h2]
    group
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w * piC h, S0.mul_mem hw (piC_mem h), ?_⟩
    rw [← h2]
    group

theorem table21 : ∀ i j : Fin 9, i ≠ j →
    Native.ccSqZ[(i : ℕ)]! ≠ Native.ccSqZ[(j : ℕ)]! ∨
      Native.ccSqR[(i : ℕ)]! ≠ Native.ccSqR[(j : ℕ)]! ∨
      Native.ccCE[(i : ℕ)]! ≠ Native.ccCE[(j : ℕ)]! ∨
      ((i : ℕ) = 1 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 2 ∧ (j : ℕ) = 1) ∨
      ((i : ℕ) ∈ [1, 2] ∧ (j : ℕ) = 7) ∨ ((i : ℕ) = 7 ∧ (j : ℕ) ∈ [1, 2]) := by
  decide

theorem cc_disj (i j : Fin 9) (hij : i ≠ j) (h : Cz) : h * cR i * h⁻¹ ≠ cR j := by
  intro e
  have ez : h * zCz * h⁻¹ = zCz := by rw [zCz_comm' h, mul_inv_cancel_right]
  rcases table21 i j hij with h1 | h1 | h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply h1
    rw [← (cc_sqrt i).1, ← (cc_sqrt j).1, ← e, ← sqrtCnt_conj h zCz (cR i), ez]
  · apply h1
    rw [← (cc_sqrt i).2, ← (cc_sqrt j).2, ← e, sqrtCnt_conj]
  · apply h1
    rw [← (cc_rep i).2.2.2.1, ← (cc_rep j).2.2.2.1, ← e, ceInv_conj]
  · rw [show i = 1 from Fin.ext h1, show j = 2 from Fin.ext h2] at e
    exact cc_not_conj12 h e
  · rw [show i = 2 from Fin.ext h1, show j = 1 from Fin.ext h2] at e
    have e' : h * cR 2 * h⁻¹ = cR 1 := e
    apply cc_not_conj12 h⁻¹
    rw [← e']
    group
  · have hj7 : j = 7 := Fin.ext h2
    rw [hj7] at e
    rcases (by simpa using h1 : (i : ℕ) = 1 ∨ (i : ℕ) = 2) with h3 | h3
    · rw [show i = 1 from Fin.ext h3] at e
      exact cc_not_conj_cls (j := 1) (j' := 3) (by norm_num) (by norm_num)
        (s0Rep_eq (by norm_num) rfl) (s0Rep_eq (by norm_num) rfl) (by decide) h e
    · rw [show i = 2 from Fin.ext h3] at e
      exact cc_not_conj_cls (j := 1) (j' := 3) (by norm_num) (by norm_num)
        (s0Rep_eq (by norm_num) rfl) (s0Rep_eq (by norm_num) rfl) (by decide) h e
  · have hi7 : i = 7 := Fin.ext h1
    rw [hi7] at e
    rcases (by simpa using h2 : (j : ℕ) = 1 ∨ (j : ℕ) = 2) with h3 | h3
    · rw [show j = 1 from Fin.ext h3] at e
      exact cc_not_conj_cls (j := 3) (j' := 1) (by norm_num) (by norm_num)
        (s0Rep_eq (by norm_num) rfl) (s0Rep_eq (by norm_num) rfl) (by decide) h e
    · rw [show j = 2 from Fin.ext h3] at e
      exact cc_not_conj_cls (j := 3) (j' := 1) (by norm_num) (by norm_num)
        (s0Rep_eq (by norm_num) rfl) (s0Rep_eq (by norm_num) rfl) (by decide) h e

theorem zCz_sq' : zCz * zCz = 1 :=
  Subtype.ext (by
    show z0 * z0 = 1
    have := pow_orderOf_eq_one z0
    rwa [orderOf_z0, sq] at this)

theorem zCz_ne_one' : zCz ≠ 1 := by
  intro e
  have := congrArg Subtype.val e
  exact absurd orderOf_z0 (by
    rw [show z0 = 1 from this, orderOf_one]
    norm_num)

theorem cc_classes :
    (∀ y : Cz, y * y = 1 → y = 1 ∨ y = zCz ∨ ∃ i : Fin 9, ∃ h : Cz, h * y * h⁻¹ = cR i) ∧
      ∀ i : Fin 9, (conjSet (cR i)).ncard = Native.ccCls[(i : ℕ)]! :=
  classes_of_card (fun i : Fin 9 => cR i) (fun i => Native.ccCls[(i : ℕ)]!)
    (cc_card_inv.trans (by decide)) zCz_sq' zCz_ne_one' zCz_comm'
    (fun i => ⟨(cc_rep i).1, (cc_rep i).2.1, (cc_rep i).2.2.1⟩) cc_cls_ge cc_disj

end CC

end CertificateChecks.KernelCo2Census

end
