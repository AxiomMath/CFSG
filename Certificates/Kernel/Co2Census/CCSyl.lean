module

public import Certificates.Kernel.Co2Census.CCX8
public import Certificates.Kernel.Co2Census.CCX7
public import Certificates.Kernel.Co2Census.CCKSy
public import Certificates.Kernel.Co2Census.CCSqrt

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


noncomputable abbrev TS : Subgroup K := gensSub (fun l => sElt (SyGt l)) 5

theorem Sy_misc' : SyPt 0 = IDP ∧ ∀ l < 5, SyGRt l = SK (SyGt l) := by
  have h := Sy_misc
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at h
  exact h

theorem mulSteps_Sy : MulSteps repK (rmStep SyGRt) 5 fun l => sElt (SyGt l) := by
  intro l hl x M hx
  have e : rmStep SyGRt l M = mulV M (SK (SyGt l)) := by
    rw [rmStep, Sy_misc'.2 l hl]
  rw [e]
  exact repK_mul hx (repK_sElt _)

theorem Sy_pts : {y | ∃ i < 512, repK y (SyPt i)} = (TS : Set K) :=
  mul_record (rep := repK) (fun _ _ _ h h' => repK_fun h h') mulSteps_Sy Sy_tree Sy_clos
    (by norm_num) (fun i hi => Nat.eq_of_beq_eq_true (Sy_root i hi))
    (by rw [Sy_misc'.1]; exact repK_one)

theorem Sy_ex : ∀ i < 512, ∃ s, repK s (SyPt i) := by
  intro i hi
  have tf := treeK_sound Sy_tree
  obtain ⟨-, -, hr⟩ := tf.1 i hi
  rw [Nat.eq_of_beq_eq_true (Sy_root i hi)] at hr
  obtain ⟨w, -, hw⟩ := reach_mul mulSteps_Sy hr (by rw [Sy_misc'.1]; exact repK_one)
  exact ⟨_, hw⟩

theorem TS_le : TS ≤ S0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨l, -, rfl⟩
  exact sElt_mem_S0 _

noncomputable def tE (j : ℕ) : K := if h : j < 512 then (Sy_ex j h).choose else 1

theorem tE_spec {j : ℕ} (hj : j < 512) : repK (tE j) (SyPt j) ∧ tE j ∈ TS := by
  simp only [tE, dif_pos hj]
  refine ⟨(Sy_ex j hj).choose_spec, ?_⟩
  have : (Sy_ex j hj).choose ∈ {y | ∃ i < 512, repK y (SyPt i)} := ⟨j, hj, (Sy_ex j hj).choose_spec⟩
  rw [Sy_pts] at this
  exact this

noncomputable def xSE (k j : ℕ) : Cz :=
  if h : j < 512 then ⟨tE j, S0_le_Cz (TS_le (tE_spec h).2)⟩ * qE (SL k j) else 1

noncomputable def xSGE (k l : ℕ) : Cz := cE (SGL k l) (SyGt l)

theorem cRk (k : ℕ) (hk : k < 3) : cR (k + 3) = cE (syE k) 2331 := by
  interval_cases k <;> rfl

theorem repK_rS {k : ℕ} (hk : k < 3) : repK ((cR (k + 3) : Cz) : K) (RS k) := by
  rw [cRk k hk]
  exact repK_cE QK_eq (by interval_cases k <;> decide) 2331

theorem S_lift' {k : ℕ} (hk : k < 3) (j : ℕ) (hj : j < 512) :
    SL k j < 512 ∧ commK (xS k j) (RS k) = true := by
  have h := S_lift k hk
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq] at h
  exact h j hj

theorem S_glift' {k : ℕ} (hk : k < 3) (l : ℕ) (hl : l < 5) :
    SGL k l < 512 ∧ commK (xSG k l) (RS k) = true := by
  have h := S_glift k hk
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq] at h
  exact h l hl

theorem repK_xS {k j : ℕ} (hk : k < 3) (hj : j < 512) : repK ((xSE k j : Cz) : K) (xS k j) := by
  simp only [xSE, dif_pos hj]
  exact repK_czmul (tE_spec hj).1 (repK_qE (S_lift' hk j hj).1)

theorem repK_xSG {k l : ℕ} (hk : k < 3) (hl : l < 5) :
    repK ((xSGE k l : Cz) : K) (xSG k l) := by
  have := repK_cE QK_eq (S_glift' hk l hl).1 (SyGt l)
  rwa [← Sy_misc'.2 l hl] at this

theorem piC_xS {k j : ℕ} (hj : j < 512) : piC (xSE k j) = tE j := by
  simp only [xSE, dif_pos hj]
  rw [map_mul, piC_qE, mul_one, piC_S0 (TS_le (tE_spec hj).2)]

noncomputable abbrev US' (k : ℕ) : Subgroup Cz := XC (k + 3) ⊓ TS.comap piC

theorem SD_mem {k : ℕ} (hk : k < 3) {t : ℕ} (ht : t < sDn k) :
    SD k t ∈ dlK QKt (RS k) := by
  have h := S_D k hk
  rw [beq_iff_eq] at h
  rw [h]
  exact List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩

theorem SD_lt {k : ℕ} (hk : k < 3) {t : ℕ} (ht : t < sDn k) : SD k t < 512 :=
  ((mem_dlK (repK_rS hk)).1 (SD_mem hk ht)).1

theorem qE_SD_mem {k : ℕ} (hk : k < 3) {t : ℕ} (ht : t < sDn k) :
    (qE (SD k t) : Cz) ∈ US' k := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
    ((mem_dlK (repK_rS hk)).1 (SD_mem hk ht)).2, ?_⟩
  show piC (qE (SD k t) : Cz) ∈ TS
  rw [piC_qE]
  exact TS.one_mem

theorem xS_mem {k j : ℕ} (hk : k < 3) (hj : j < 512) : xSE k j ∈ US' k := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
    (qE_comm (repK_xS hk hj) (repK_rS hk) (S_lift' hk j hj).2), ?_⟩
  show piC (xSE k j) ∈ TS
  rw [piC_xS hj]
  exact (tE_spec hj).2

theorem xSG_mem {k l : ℕ} (hk : k < 3) (hl : l < 5) : xSGE k l ∈ US' k := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
    (qE_comm (repK_xSG hk hl) (repK_rS hk) (S_glift' hk l hl).2), ?_⟩
  show piC (xSGE k l) ∈ TS
  rw [xSGE, piC_cE]
  exact gen_mem _ hl

noncomputable def uS (k c : ℕ) : Cz := xSE k (c / sDn k) * qE (SD k (c % sDn k))

theorem sDn_pos {k : ℕ} (hk : k < 3) : 0 < sDn k := by interval_cases k <;> decide

theorem mem_US {k : ℕ} (hk : k < 3) {u : Cz} (hu : u ∈ US' k) :
    ∃ j < 512, ∃ t < sDn k, u = xSE k j * qE (SD k t) := by
  obtain ⟨huX, huT⟩ := Subgroup.mem_inf.1 hu
  have hc : ∃ i < 512, repK (piC u) (SyPt i) := by
    have : piC u ∈ {y | ∃ i < 512, repK y (SyPt i)} := by rw [Sy_pts]; exact huT
    exact this
  have huX' := Subgroup.mem_centralizer_singleton_iff.1 huX
  rw [cRk k hk] at huX'
  obtain ⟨j, hj, e, he, rfl⟩ := mem_Xs (x := xSE k) (CP := SyPt)
    (by interval_cases k <;> decide)
    (fun j hj => ⟨by rw [piC_xS hj]; exact (tE_spec hj).1, by
      rw [← cRk k hk]
      exact qE_comm (repK_xS hk hj) (repK_rS hk) (S_lift' hk j hj).2⟩)
    huX' hc
  have h := S_D k hk
  rw [beq_iff_eq] at h
  rw [show mulV (SK 2331) (QKt (syE k)) = RS k from rfl, h] at he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he
  exact ⟨j, hj, t, List.mem_range.1 ht, rfl⟩

theorem SD_inj {k : ℕ} (hk : k < 3) {t t' : ℕ} (ht : t < sDn k) (ht' : t' < sDn k)
    (h : SD k t = SD k t') : t = t' := by
  have hnd : ((List.range (sDn k)).map (SD k)).Nodup := by
    have e := S_D k hk
    rw [beq_iff_eq] at e
    rw [← e]
    unfold dlK
    exact List.Nodup.filter _ List.nodup_range
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 ht) (List.mem_range.2 ht') h

theorem uS_inj {k : ℕ} (hk : k < 3) :
    ∀ c < 512 * sDn k, ∀ c' < 512 * sDn k, uS k c = uS k c' → c = c' := by
  intro c hc c' hc' h
  have hp := sDn_pos hk
  have hj : c / sDn k < 512 := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hc)
  have hj' : c' / sDn k < 512 := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hc')
  have hπ := congrArg piC h
  unfold uS at hπ
  rw [map_mul, map_mul, piC_qE, piC_qE, mul_one, mul_one, piC_xS hj, piC_xS hj'] at hπ
  have h1 := (tE_spec hj).1
  rw [hπ] at h1
  have hjj := (treeK_sound Sy_tree).2 _ hj _ hj' (repK_unique h1 (tE_spec hj').1)
  unfold uS at h
  rw [hjj] at h
  have hq := mul_left_cancel h
  have ht := Nat.mod_lt c hp
  have ht' := Nat.mod_lt c' hp
  have he := qE_injOn (SD_lt hk ht) (SD_lt hk ht') (Subtype.ext hq)
  have htt := SD_inj hk ht ht' he
  rw [← Nat.div_add_mod c (sDn k), ← Nat.div_add_mod c' (sDn k), hjj, htt]

theorem uS_enum {k : ℕ} (hk : k < 3) :
    (∀ c < 512 * sDn k, uS k c ∈ US' k) ∧ (∀ u ∈ US' k, ∃ c < 512 * sDn k, uS k c = u) := by
  have hp := sDn_pos hk
  refine ⟨fun c hc => ?_, fun u hu => ?_⟩
  · have hj : c / sDn k < 512 := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hc)
    exact (US' k).mul_mem (xS_mem hk hj) (qE_SD_mem hk (Nat.mod_lt c hp))
  · obtain ⟨j, hj, t, ht, rfl⟩ := mem_US hk hu
    refine ⟨sDn k * j + t, ?_, ?_⟩
    · calc sDn k * j + t < sDn k * j + sDn k := by omega
        _ = sDn k * (j + 1) := by ring
        _ ≤ sDn k * 512 := Nat.mul_le_mul_left _ (by omega)
        _ = 512 * sDn k := by ring
    · unfold uS
      rw [Nat.mul_add_div hp, Nat.div_eq_of_lt ht, add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]

theorem natCard_US {k : ℕ} (hk : k < 3) : Nat.card (US' k) = 512 * sDn k := by
  classical
  have := card_sub_enum (uS k) (uS_enum hk).1 (uS_enum hk).2 (uS_inj hk) (fun _ => True)
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)] at this
  rw [this]
  simp

theorem cc_syl : ∀ k < 3, ∃ U : Subgroup Cz, U ≤ XC (k + 3) ∧
    Nat.card U = Native.ccSylSize[k]! ∧ zCz ∈ U ∧ ∀ y ∈ U, (∀ u ∈ U, u * y = y * u) →
      y * y = 1 → y ≠ 1 → y ≠ zCz → invEInv y ≠ 32 := by
  intro k hk
  refine ⟨US' k, inf_le_left, by rw [natCard_US hk]; interval_cases k <;> rfl, ?_,
    fun y hy hcen hyy hy1 hyz => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (zCz_comm' _).symm, ?_⟩
    show piC zCz ∈ TS
    rw [piC_zCz]
    exact TS.one_mem
  obtain ⟨j, hj, t, ht, rfl⟩ := mem_US hk hy
  have hyR := repK_czmul (repK_xS hk hj) (repK_qE (SD_lt hk ht))
  have hjc : ∃ g < 4, SyZt g = j := by
    have h := Sy_cent j hj
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Nat.beq_eq, Bool.and_eq_true,
      Nat.blt_eq, Bool.not_eq_true'] at h
    rcases h with h | ⟨hw, hnc⟩
    · exact h
    · exfalso
      have e := congrArg piC (hcen _ (xSG_mem hk hw))
      simp only [map_mul, piC_qE, mul_one, piC_xS hj, xSGE, piC_cE] at e
      have hg := repK_sElt (SyGt (SyWt j))
      rw [← Sy_misc'.2 _ hw] at hg
      have h1 := repK_mul (tE_spec hj).1 hg
      have h2 := repK_mul hg (tE_spec hj).1
      rw [e] at h2
      unfold commK at hnc
      exact Nat.ne_of_beq_eq_false hnc (repK_unique h1 h2)
  obtain ⟨g, hg, rfl⟩ := hjc
  have hzlt := Sy_zlt
  simp only [List.all_eq_true, List.mem_range, Nat.blt_eq] at hzlt
  set c := g * sDn k + t
  have hc : c < 4 * sDn k := by
    calc g * sDn k + t < g * sDn k + sDn k := by omega
      _ = (g + 1) * sDn k := by ring
      _ ≤ 4 * sDn k := Nat.mul_le_mul_right _ (by omega)
  have hcand := List.all_eq_true.1 (S_cand k hk) c (List.mem_range.2 hc)
  have hp := sDn_pos hk
  have hcg : c / sDn k = g := by
    simp only [c]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ht, zero_add]
  have hct : c % sDn k = t := by
    simp only [c]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  unfold candOK at hcand
  simp only [letB_eq, hcg, hct] at hcand
  split_ifs at hcand with hk0 hk1
  · simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at hcand
    exact absurd (hcen _ (xSG_mem hk hcand.1)).symm
      (qE_ncomm hyR (repK_xSG hk hcand.1) hcand.2)
  · simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at hcand
    exact absurd (hcen _ (qE_SD_mem hk hcand.1)).symm
      (qE_ncomm hyR (repK_qE (SD_lt hk hcand.1)) hcand.2)
  · simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at hcand
    rw [invEInv_eqK hyR]
    rcases hcand with ((h | h) | h) | h
    · exact absurd ((cz_eq_iff (repK_czmul hyR hyR) repK_one').1 hyy) (Nat.ne_of_beq_eq_false h)
    · exact absurd ((cz_eq_iff hyR repK_one').2 h) hy1
    · exact absurd ((cz_eq_iff hyR repK_zCz).2 h) hyz
    · exact Nat.ne_of_beq_eq_false h

end CC

end CertificateChecks.KernelCo2Census

end
