module

public import CFSG.Sporadic.Co1Patterson.AmalgamInnerData
public import CFSG.Sporadic.Co1Patterson.AmalgamRigidCent
public import CFSG.Sporadic.Co1Patterson.TwistNativeRM
public import CFSG.Sporadic.Co1.Module.InvSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.InnerNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
  CFSG.Sporadic.Co1Patterson.TwistNative CFSG.Sporadic.Co1Patterson.Native CFSG.Monster.GMS
open CFSG.Blueprint (NativeSporadic.Co1)

local macro "CA" : term => `(centralizer ({aNC} : Set NativeSporadic.Co1))

theorem foldl_mul_six_CA (f : ℕ → CA) (j : ℕ) :
    [j, j, j, j, j, j].foldl (fun acc i => acc * f i) 1 = (f j * f j) ^ 3 := by
  simp only [List.foldl_cons, List.foldl_nil, one_mul, pow_succ, pow_zero, mul_assoc]


theorem innerOrbOK_parts : zRows = yRow 0 ∧ (ptSet orbQ).contains qRows = true := by
  have h := inner_orb_check
  simp only [innerOrbOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem innerBfsOK_parts : innerWords.length = 20160 ∧
    (innerWords.map fun u => wKey (wMat u)).Nodup ∧
    ∀ v ∈ wVecs, actWord [0, 0, 0, 0, 0, 0] v = v := by
  have h := inner_bfs_check
  simp only [innerBfsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, CFSG.Sporadic.Co1.Module.distinctKeys_nodup h.1.2, h.2⟩

theorem coe_repV_zero :
    ((repV 0 : Vt) : NativeSporadic.Co1) = ((yH 0 : CA) : NativeSporadic.Co1) := by
  have h1 : NRep zRows (repV 0 : NativeSporadic.Co1) := nrep_zRows
  have h2 : NRep (yRow 0) ((yH 0 : CA) : NativeSporadic.Co1) := (nrep_iff_mrep _ _).2 rep_w'
  rw [innerOrbOK_parts.1] at h1
  exact NRep.unique h1 h2

theorem card_K₀ : Nat.card K₀ = 330301440 := by
  have horb : MulAction.orbit CA (repV 0) = cOrb (repV 0) := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hstab : MulAction.stabilizer CA (repV 0) = K₀ := by
    ext k
    rw [MulAction.mem_stabilizer_iff, mem_K₀, Subgroup.smul_def, smul_eq_self_iff,
      mem_centralizer_singleton_iff, coe_repV_zero, ← Subtype.coe_inj, Subgroup.coe_mul,
      Subgroup.coe_mul]
  have h1 := MulAction.index_stabilizer CA (repV 0)
  have h2 := (MulAction.stabilizer CA (repV 0)).card_mul_index
  rw [horb, ncard_cOrb_z] at h1
  rw [h1, hstab, card_centralizer_aNC] at h2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h2.trans (by norm_num))

theorem card_R₀ : Nat.card R₀ = 2 ^ 14 := by
  rw [← card_Idx]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun q : Idx => (⟨hcH q.1.1 * aElt q.1.2, hcH_mul_aElt_mem q.2.1 q.2.2⟩ : R₀))
    ⟨fun q q' h => ?_, fun y => ?_⟩)).symm
  · have h' : hcH q.1.1 * aElt q.1.2 = hcH q'.1.1 * aElt q'.1.2 := Subtype.mk.inj h
    have := hcH_mul_aElt_inj q.2.1 q'.2.1 q.2.2 q'.2.2 h'
    exact Subtype.ext (Prod.ext this.1 this.2)
  · obtain ⟨c, hc, p, hp, hy⟩ := mem_R₀_iff.1 y.2
    exact ⟨⟨(c, p), hc, hp⟩, Subtype.ext hy.symm⟩

theorem genWords_lt (i : ℕ) : ∀ j ∈ genWords.getD i [], j < 2 := by
  by_cases hi : i < 2
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [genWords]; omega)]
    simp

theorem expandWord_lt (u : List ℕ) : ∀ j ∈ expandWord u, j < 2 := by
  intro j hj
  obtain ⟨i, -, hji⟩ := List.mem_flatMap.1 hj
  exact genWords_lt i j hji

theorem expandWord_cons (i : ℕ) (u : List ℕ) :
    expandWord (i :: u) = genWords.getD i [] ++ expandWord u := by
  simp [expandWord]

theorem actV_kW_bv {w : List ℕ} (hw : ∀ j ∈ w, j < 2) {v : ℕ} (hv : v ∈ wVecs) :
    actV (kW w) (bv v) = bv (actWord w v) := by
  induction w with
  | nil => rw [kW_nil, actV_one (bv_mem_W₀ hv)]; rfl
  | cons j w ih =>
    have hj := hw j List.mem_cons_self
    rw [kW_cons, actV_mul (kH_mem_K₀ hj), ih fun i hi => hw i (List.mem_cons_of_mem _ hi),
      actV_kH_bv hj]
    rfl

theorem actWord_lt {w : List ℕ} {v : ℕ} (hv : v < 256) : actWord w v < 256 := by
  cases w with
  | nil => exact hv
  | cons j w =>
    show actW (kCols.getD j []) (actWord w v) < 256
    exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

@[expose] noncomputable def eltW (u : List ℕ) : CA := kW (expandWord u)

theorem eltW_mem_K₀ (u : List ℕ) : eltW u ∈ K₀ := kW_mem_K₀ (expandWord_lt u)

theorem eltW_mem {D : Subgroup CA} (h₁ : kH 1 ∈ D) (h₂ : kH 0 * kH 0 ∈ D) (u : List ℕ) :
    eltW u ∈ D := by
  induction u with
  | nil => exact one_mem _
  | cons i u ih =>
    rw [eltW, expandWord_cons, kW_append]
    refine mul_mem ?_ ih
    by_cases hi : i < 2
    · interval_cases i
      · simpa [genWords, kW] using h₁
      · simpa [genWords, kW] using h₂
    · rw [List.getD_eq_default _ _ (by simp [genWords]; omega), kW_nil]
      exact one_mem _

theorem w0Basis_mem : ∀ b ∈ w0Basis, b ∈ wVecs := by decide

theorem wMat_eq_of_mul_mem {u u' : List ℕ} (h : (eltW u')⁻¹ * eltW u ∈ R₀) :
    wMat u = wMat u' := by
  refine List.map_congr_left fun b hb => ?_
  have hbW := w0Basis_mem b hb
  have hb256 : b < 256 := (mem_wVecs.1 hbW).1
  have e : eltW u = eltW u' * ((eltW u')⁻¹ * eltW u) := by group
  have h1 : actV (eltW u) (bv b) = actV (eltW u') (bv b) := by
    rw [e, actV_mul (eltW_mem_K₀ u'), h.2 _ (bv_mem_W₀ hbW)]
  rw [eltW, eltW, actV_kW_bv (expandWord_lt u) hbW, actV_kW_bv (expandWord_lt u') hbW] at h1
  exact bv_inj (actWord_lt hb256) (actWord_lt hb256) h1

theorem K₀_le_of_words (W : List (List ℕ)) (hlen : W.length = 20160)
    (hnd : (W.map fun u => wKey (wMat u)).Nodup) (D : Subgroup CA) (hDK : D ≤ K₀) (hRD : R₀ ≤ D)
    (h₁ : kH 1 ∈ D) (h₂ : kH 0 * kH 0 ∈ D) : K₀ ≤ D := by
  have hF : Function.Injective (fun q : Fin 20160 × R₀ =>
      (⟨eltW (W.getD q.1 []) * q.2, mul_mem (eltW_mem h₁ h₂ _) (hRD q.2.2)⟩ : D)) := by
    rintro ⟨i, r⟩ ⟨j, r'⟩ h
    have h' : eltW (W.getD i []) * r = eltW (W.getD j []) * r' := Subtype.mk.inj h
    have hmem : (eltW (W.getD j []))⁻¹ * eltW (W.getD i []) ∈ R₀ := by
      have e : (eltW (W.getD j []))⁻¹ * eltW (W.getD i []) = (r' : CA) * (r : CA)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
      rw [e]
      exact mul_mem r'.2 (inv_mem r.2)
    have hM := wMat_eq_of_mul_mem hmem
    have hi : (i : ℕ) < W.length := by rw [hlen]; exact i.2
    have hj : (j : ℕ) < W.length := by rw [hlen]; exact j.2
    have hkey : (W.map fun u => wKey (wMat u))[(i : ℕ)]'(by simpa using hi) =
        (W.map fun u => wKey (wMat u))[(j : ℕ)]'(by simpa using hj) := by
      rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ [] hi,
        ← List.getD_eq_getElem _ [] hj, hM]
    have hij : i = j := Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hkey)
    subst hij
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  have hcard : Nat.card K₀ ≤ Nat.card D := by
    rw [card_K₀]
    have h3 := Nat.card_le_card_of_injective _ hF
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 20160), Fintype.card_fin,
      card_R₀] at h3
    exact le_trans (by norm_num) h3
  exact (Subgroup.eq_of_le_of_card_ge hDK hcard).ge

theorem K₀_le_of_gens (D : Subgroup CA) (hDK : D ≤ K₀) (hRD : R₀ ≤ D) (h₁ : kH 1 ∈ D)
    (h₂ : kH 0 * kH 0 ∈ D) : K₀ ≤ D :=
  K₀_le_of_words innerWords innerBfsOK_parts.1 innerBfsOK_parts.2.1 D hDK hRD h₁ h₂

theorem pow_three_mem_R₀ : (kH 0 * kH 0) ^ 3 ∈ R₀ := by
  rw [← foldl_mul_six_CA kH 0, ← kW]
  refine ⟨kW_mem_K₀ (by decide), fun x hx => ?_⟩
  rw [← bv_enc x, actV_kW_bv (by decide) (enc_mem_wVecs hx),
    innerBfsOK_parts.2.2 _ (enc_mem_wVecs hx)]

end CFSG.Sporadic.Co1Patterson.InnerNative
