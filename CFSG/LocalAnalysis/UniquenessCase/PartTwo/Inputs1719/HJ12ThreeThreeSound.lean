module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12T1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJNormalizer
public import CFSG.Quasithin.Background.RonanE42Small
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
public import CFSG.CGT.Foote81L6.TStruct.ElemBound
public import Certificates.Certificate17283

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GF2Type.Smith1979.GammaU (vecOf)
open CFSG.GF2Type.Smith1979.GammaU.StepA (mulR idR)
open CFSG.GF2Type.Smith1979.GammaU.Viol (size_mulR)
open CFSG.GammaU.Native (appN)
open HJBridge (RowsOf grpOf rowsOf_mul rowsOf_one rowsOf_unique rowsOf_hjWord mem_grpOf_iff
  card_grpOf_eq card_fixV_zpowers mem_fixV_zpowers_iff)
open HJ12 (wordR hjTauc isInvol commR fixCodes)

theorem hjT1_enum_facts :
    CFSG.GF2Type.Smith1979.GammaU.SigmaP.gensOK
        (HJ12.hj_t0Words.map wordR ++ [hjTauc]) = true ∧
      CFSG.GF2Type.Smith1979.GammaU.Enum.closedCheck
        (HJ12.hj_t0Words.map wordR ++ [hjTauc])
        (CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
          (HJ12.hj_t0Words.map wordR ++ [hjTauc])) = true ∧
      Nat.card hjA1 = 16 ∧ Nat.card hjA2 = 16 := by
  classical
  have h1 : HJ12.hjT1Check = true := HJ12.hjT1Check_eq
  simp only [HJ12.hjT1Check, HJ12.gensL, Bool.and_eq_true, gensOKN_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_closedCheck,
    CFSG.GF2Type.Smith1979.GammaU.native_enumGrp,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_orbitOf] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg1, hga⟩, hc0⟩, hc1⟩, h128⟩, h256⟩, hca1⟩, hca2⟩, h16a⟩, h16b⟩,
    hall1⟩, hall2⟩, hcomm1⟩, hcomm2⟩, _⟩, he16⟩, _⟩ := h1
  have hga1 : CFSG.GF2Type.Smith1979.GammaU.SigmaP.gensOK
      (HJ12.hj_a1Words.map wordR) = true := gensOK_append_left hga
  have hga2 : CFSG.GF2Type.Smith1979.GammaU.SigmaP.gensOK
      (HJ12.hj_a2Words.map wordR) = true := gensOK_append_right hga
  refine ⟨hg1, hc1, ?_, ?_⟩
  · rw [hjA1, HJBridge.card_grpOf_eq hga1 hca1, beq_iff_eq.mp h16a]
  · rw [hjA2, HJBridge.card_grpOf_eq hga2 hca2, beq_iff_eq.mp h16b]

theorem hjT1_mem_iff (x : MulAut W12) :
    x ∈ hjT1 ↔
      ∃ r ∈ CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
        (HJ12.hj_t0Words.map wordR ++ [hjTauc]), RowsOf x r := by
  obtain ⟨hg, hc, -, -⟩ := hjT1_enum_facts
  exact HJBridge.mem_grpOf_iff hg hc x

theorem hjT1Invs_eq :
    HJ12.hjT1Invs () =
      (CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
        (HJ12.hj_t0Words.map wordR ++ [hjTauc])).filter isInvol := by
  simp only [HJ12.hjT1Invs, HJ12.hjT1Gens, CFSG.GF2Type.Smith1979.GammaU.native_enumGrp]

theorem hjT1Tab_eq :
    HJ12.hjT1Tab () =
      (HJ12.hjT1Invs ()).map (fun r => (r, (fixCodes r).length)) := rfl

theorem hjLookup_map {l : List (Array Nat)} {f : Array Nat → Nat} {r : Array Nat}
    (hr : r ∈ l) : HJ12.hjLookup (l.map fun r => (r, f r)) r = f r := by
  unfold HJ12.hjLookup
  rw [List.find?_map]
  simp only [Function.comp_def, Option.map_map]
  have hfind : l.find? (fun x => x == r) = some r := by
    have hsome : (l.find? (fun x => x == r)).isSome := by
      rw [List.find?_isSome]
      exact ⟨r, hr, by simp⟩
    cases h : l.find? (fun x => x == r) with
    | none => simp [h] at hsome
    | some x =>
      have hx : x = r := by
        have hpred := List.find?_some h
        simpa [beq_iff_eq] using hpred
      rw [hx]
  rw [hfind]
  rfl

theorem hjLookup_eq {r : Array Nat} (hr : r ∈ HJ12.hjT1Invs ()) :
    HJ12.hjLookup (HJ12.hjT1Tab ()) r = (fixCodes r).length := by
  rw [hjT1Tab_eq]
  exact hjLookup_map hr

theorem hjRows_invs {x : MulAut W12} {r : Array Nat}
    (hx : x ∈ hjT1) (hxr : RowsOf x r) (hsq : x ^ 2 = 1) (hne : x ≠ 1)
    (hrmem : r ∈ CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
      (HJ12.hj_t0Words.map wordR ++ [hjTauc])) :
    r ∈ HJ12.hjT1Invs () ∧ Nat.card (fixV (Subgroup.zpowers x)) = (fixCodes r).length := by
  classical
  obtain ⟨hg, hc, -, -⟩ := hjT1_enum_facts
  have hcan : r.size = 12 ∧ ∀ y ∈ r, y < 4096 := canon_of_mem_enumGrp hg hrmem
  have h1r : mulR r r = idR := by
    have h := HJBridge.rowsOf_mul hxr hxr
    rw [show x * x = 1 from by rw [← pow_two]; exact hsq] at h
    exact rows_eq_of_rowsOf h HJBridge.rowsOf_one
      ⟨by rw [size_mulR, hcan.1], mulR_lt hcan.2⟩ (by decide)
  have hrne : r ≠ idR := by
    intro h
    exact hne (HJBridge.rowsOf_unique (h ▸ hxr) HJBridge.rowsOf_one)
  have hinv : isInvol r = true := by
    simp only [HJ12.isInvol, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    exact ⟨hrne, h1r⟩
  refine ⟨?_, ?_⟩
  · rw [hjT1Invs_eq]
    exact List.mem_filter.2 ⟨hrmem, hinv⟩
  · exact card_fixV_zpowers hxr hcan.2

theorem hjZ_check_eq :
    HJ12.hjZCheck () = true ∧ HJ12.hjPureTripleCheck () = true ∧
      HJ12.hjE16A1Check () = true ∧ HJ12.hjE16A2Check () = true := by
  have h := Certificates.certificate17283
  simp only [HJ12.hjThreeThreeCheck, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem isInvol_spec {r : Array Nat} (h : isInvol r = true) :
    r ≠ idR ∧ mulR r r = idR := by
  simp only [HJ12.isInvol, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq] at h
  exact ⟨h.1, h.2⟩

theorem hjWord_sq_of_isInvol {w : List Nat} (hinv : isInvol (wordR w) = true) :
    (hjWord w) ^ 2 = 1 := by
  have h := HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord w) (HJBridge.rowsOf_hjWord w)
  rw [show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR (wordR w) (wordR w) =
      mulR (wordR w) (wordR w) from rfl, (isInvol_spec hinv).2] at h
  have h1 := HJBridge.rowsOf_unique h HJBridge.rowsOf_one
  simpa [pow_two] using h1

theorem hjWord_ne_one_of_isInvol {w : List Nat} (h : isInvol (wordR w) = true) :
    hjWord w ≠ 1 :=
  hjWord_ne_one (isInvol_spec h).1

theorem hjZ_isInvol : isInvol (wordR HJ12.hj_zWord) = true ∧
    (fixCodes (wordR HJ12.hj_zWord)).length = 256 := by
  have h := (hjZ_check_eq).1
  simp only [HJ12.hjZCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem hjZ_mem : hjWord HJ12.hj_zWord ∈ hjL0 := hjWord_mem _

theorem hjZ_orderOf : orderOf (hjWord HJ12.hj_zWord) = 2 :=
  orderOf_eq_prime (hjWord_sq_of_isInvol (hjZ_isInvol).1)
    (hjWord_ne_one_of_isInvol (hjZ_isInvol).1)

theorem hjZ_rank :
    rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers (hjWord HJ12.hj_zWord))) = 4 := by
  obtain ⟨-, h256⟩ := hjZ_isInvol
  have h256R : (HJBridge.fixCodesR (wordR HJ12.hj_zWord)).length = 256 := h256
  have hcard : Nat.card (fixV (Subgroup.zpowers (hjWord HJ12.hj_zWord))) = 256 := by
    have h := card_fixV_zpowers (x := hjWord HJ12.hj_zWord)
      (r := wordR HJ12.hj_zWord) (HJBridge.rowsOf_hjWord HJ12.hj_zWord)
      (HJBridge.wordR_canon _).2
    rw [h256R] at h
    exact h
  refine rk_commSub_eq_of_card_fixV (k := 4) (by norm_num) ?_
  have hpow : (2 : ℕ) ^ (12 - 4) = 256 := by norm_num
  rw [hpow]
  exact hcard

theorem hjWord_mem_grpOf_words {ws : List (List Nat)} {w : List Nat} (hw : w ∈ ws) :
    hjWord w ∈ grpOf (ws.map wordR) := by
  rw [HJBridge.grpOf_words]
  exact Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem hjWord_comm_of_commR {w₁ w₂ : List Nat}
    (h : HJ12.commR (wordR w₁) (wordR w₂) = true) :
    hjWord w₁ * hjWord w₂ = hjWord w₂ * hjWord w₁ := by
  have hrows : mulR (wordR w₁) (wordR w₂) = mulR (wordR w₂) (wordR w₁) := by
    rw [show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR (wordR w₁) (wordR w₂) =
        CFSG.GammaU.Native.mulR (wordR w₁) (wordR w₂) from rfl,
      show CFSG.GF2Type.Smith1979.GammaU.StepA.mulR (wordR w₂) (wordR w₁) =
        CFSG.GammaU.Native.mulR (wordR w₂) (wordR w₁) from rfl]
    simpa only [HJ12.commR, beq_iff_eq] using h
  refine HJBridge.rowsOf_unique (r := mulR (wordR w₁) (wordR w₂)) ?_ ?_
  · exact HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord w₁) (HJBridge.rowsOf_hjWord w₂)
  · rw [hrows]
    exact HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord w₂) (HJBridge.rowsOf_hjWord w₁)

theorem hjE16_not_mem_aSet_three {A₀ : Subgroup (MulAut W12)} {w₁ w₂ wg : List Nat} {c : ℕ}
    (hc : c < 4096) (hA₀card : Nat.card A₀ = 16)
    (hw₁ : hjWord w₁ ∈ A₀) (hw₂ : hjWord w₂ ∈ A₀) (hwg : hjWord wg ∈ A₀)
    (h₁inv : isInvol (wordR w₁) = true) (h₂inv : isInvol (wordR w₂) = true)
    (hrowsne : wordR w₁ ≠ wordR w₂)
    (hcomm : HJ12.commR (wordR w₁) (wordR w₂) = true)
    (hc₁ : appN (wordR w₁) c = c) (hc₂ : appN (wordR w₂) c = c)
    (hgc : appN (wordR wg) c ≠ c) :
    A₀ ∉ E3.aSet 3 hjT1 := by
  classical
  have : Finite (MulAut W12) :=
    Finite.of_injective (fun e : MulAut W12 => (e : W12 → W12))
      (fun a b h => MulEquiv.ext (congrFun h))
  intro hA
  let b₁ : MulAut W12 := hjWord w₁
  let b₂ : MulAut W12 := hjWord w₂
  let g : MulAut W12 := hjWord wg
  let B : Subgroup (MulAut W12) := Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂
  have hb₁sq : b₁ ^ 2 = 1 := hjWord_sq_of_isInvol h₁inv
  have hb₂sq : b₂ ^ 2 = 1 := hjWord_sq_of_isInvol h₂inv
  have hb₁ne : b₁ ≠ 1 := hjWord_ne_one_of_isInvol h₁inv
  have hb₂ne : b₂ ≠ 1 := hjWord_ne_one_of_isInvol h₂inv
  have hcomm' : b₁ * b₂ = b₂ * b₁ := hjWord_comm_of_commR hcomm
  have hbne : b₁ ≠ b₂ := by
    intro h
    have h1 : RowsOf b₁ (wordR w₁) := HJBridge.rowsOf_hjWord w₁
    have h2 : RowsOf b₁ (wordR w₂) := h ▸ HJBridge.rowsOf_hjWord w₂
    exact hrowsne (rows_eq_of_rowsOf h1 h2 (HJBridge.wordR_canon _) (HJBridge.wordR_canon _))
  have hBA : B ≤ A₀ :=
    sup_le (Subgroup.zpowers_le.mpr hw₁) (Subgroup.zpowers_le.mpr hw₂)
  have hBcard : Nat.card ↥B = 4 :=
    CFSG.CGT.Foote81L6.TStruct.card_zpowers_sup_zpowers (by simpa [pow_two] using hb₁sq)
      (by simpa [pow_two] using hb₂sq) hb₁ne hb₂ne hbne hcomm'
  have hBrel : B.relIndex A₀ = 4 := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := A₀)
    rw [inf_eq_left.2 hBA, hBcard, hA₀card] at h
    omega
  have hmq : E3.mQuot A₀ B = 2 := by
    unfold E3.mQuot
    rw [hBrel]
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, padicValNat.prime_pow]
  have hlt : E3.mQuot A₀ B < 3 := by rw [hmq]; norm_num
  have hfix := hA.2.2.2 B hBA hlt
  let v : W12 := Multiplicative.ofAdd (vecOf c)
  have hv₁ : v ∈ fixV (Subgroup.zpowers b₁) :=
    mem_fixV_of_mem_fixCodes (HJBridge.rowsOf_hjWord w₁) (by
      simp only [HJ12.fixCodes, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨hc, hc₁⟩)
  have hv₂ : v ∈ fixV (Subgroup.zpowers b₂) :=
    mem_fixV_of_mem_fixCodes (HJBridge.rowsOf_hjWord w₂) (by
      simp only [HJ12.fixCodes, List.mem_filter, List.mem_range, beq_iff_eq]
      exact ⟨hc, hc₂⟩)
  have hvB : v ∈ fixV B := by
    rw [show B = Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ from rfl,
      CFSG.Quasithin.FixVLat.fixV_sup_eq]
    exact ⟨hv₁, hv₂⟩
  have hvA : v ∉ fixV A₀ := by
    intro hv
    have hgv : g v = v := mem_fixV.mp hv g hwg
    have hrow := HJBridge.rowsOf_hjWord wg
    have h1 : g v = Multiplicative.ofAdd (CFSG.GF2Type.Smith1979.GammaU.linOfRows
      (wordR wg) (vecOf c)) := hrow (vecOf c)
    have h2 : vecOf c = CFSG.GF2Type.Smith1979.GammaU.linOfRows (wordR wg) (vecOf c) :=
      Multiplicative.ofAdd.injective (hgv.symm.trans h1)
    rw [← CFSG.GF2Type.Smith1979.GammaU.vecOf_appN] at h2
    exact hgc (CFSG.GF2Type.Smith1979.GammaU.vecOf_inj hc
      (CFSG.GF2Type.Smith1979.GammaU.StepA.appN_lt (HJBridge.wordR_canon wg).2 c) h2).symm
  exact hvA (hfix ▸ hvB)

theorem hjE16A1Check_spec :
    isInvol (wordR HJ12.hj_b1Word) = true ∧ isInvol (wordR HJ12.hj_b2Word) = true ∧
      wordR HJ12.hj_b1Word ≠ wordR HJ12.hj_b2Word ∧
      HJ12.commR (wordR HJ12.hj_b1Word) (wordR HJ12.hj_b2Word) = true ∧
      appN (wordR HJ12.hj_b1Word) 81 = 81 ∧ appN (wordR HJ12.hj_b2Word) 81 = 81 ∧
      appN (wordR HJ12.hj_g1Word) 81 ≠ 81 := by
  have h := (hjZ_check_eq).2.2.1
  simp only [HJ12.hjE16A1Check, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

theorem hjE16A2Check_spec :
    isInvol (wordR HJ12.hj_c1Word) = true ∧ isInvol (wordR HJ12.hj_c2Word) = true ∧
      wordR HJ12.hj_c1Word ≠ wordR HJ12.hj_c2Word ∧
      HJ12.commR (wordR HJ12.hj_c1Word) (wordR HJ12.hj_c2Word) = true ∧
      appN (wordR HJ12.hj_c1Word) 136 = 136 ∧ appN (wordR HJ12.hj_c2Word) 136 = 136 ∧
      appN (wordR HJ12.hj_h1Word) 136 ≠ 136 := by
  have h := (hjZ_check_eq).2.2.2
  simp only [HJ12.hjE16A2Check, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, ne_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

theorem hjA1_not_mem_aSet_three :
    hjA1 ∉ E3.aSet 3 hjT1 := by
  obtain ⟨-, -, hA1card, -⟩ := hjT1_enum_facts
  obtain ⟨h1inv, h2inv, hne, hcomm, hc1, hc2, hgc⟩ := hjE16A1Check_spec
  exact hjE16_not_mem_aSet_three (A₀ := hjA1) (w₁ := HJ12.hj_b1Word)
    (w₂ := HJ12.hj_b2Word) (wg := HJ12.hj_g1Word) (c := 81) (by norm_num) hA1card
    (hjWord_mem_grpOf_words (List.get_mem _ _))
    (hjWord_mem_grpOf_words (List.get_mem _ _))
    (hjWord_mem_grpOf_words (List.get_mem _ _)) h1inv h2inv hne hcomm hc1 hc2 hgc

theorem hjA2_not_mem_aSet_three :
    hjA2 ∉ E3.aSet 3 hjT1 := by
  obtain ⟨-, -, -, hA2card⟩ := hjT1_enum_facts
  obtain ⟨h1inv, h2inv, hne, hcomm, hc1, hc2, hgc⟩ := hjE16A2Check_spec
  exact hjE16_not_mem_aSet_three (A₀ := hjA2) (w₁ := HJ12.hj_c1Word)
    (w₂ := HJ12.hj_c2Word) (wg := HJ12.hj_h1Word) (c := 136) (by norm_num) hA2card
    (hjWord_mem_grpOf_words (List.get_mem _ _))
    (hjWord_mem_grpOf_words (List.get_mem _ _))
    (hjWord_mem_grpOf_words (List.get_mem _ _)) h1inv h2inv hne hcomm hc1 hc2 hgc

theorem hjPureTripleCheck_spec {x y z : Array Nat}
    (hx : x ∈ HJ12.hjT1Invs ()) (hy : y ∈ HJ12.hjT1Invs ()) (hz : z ∈ HJ12.hjT1Invs ())
    (hxy : (x == y) = false) (hxz : (x == z) = false) (hyz : (y == z) = false)
    (hcxy : HJ12.commR x y = true) (hcxz : HJ12.commR x z = true)
    (hcyz : HJ12.commR y z = true)
    (hind : ([idR, x, y, mulR x y].contains z) = false)
    (hlen : HJ12.hjLookup (HJ12.hjT1Tab ()) x = HJ12.hjLookup (HJ12.hjT1Tab ()) y)
    (hlen2 : HJ12.hjLookup (HJ12.hjT1Tab ()) y = HJ12.hjLookup (HJ12.hjT1Tab ()) z) :
    (∃ w ∈ HJ12.hjTripleRows x y z, HJ12.hjLookup (HJ12.hjT1Tab ()) w = 64) ∧
      ∃ w ∈ HJ12.hjTripleRows x y z, HJ12.hjLookup (HJ12.hjT1Tab ()) w = 256 := by
  have h := (hjZ_check_eq).2.1
  simp only [HJ12.hjPureTripleCheck, List.all_eq_true] at h
  have hok := h x hx y hy z hz
  have hind' : ([CFSG.GammaU.Native.idR, x, y,
      CFSG.GammaU.Native.mulR x y].contains z) = false := hind
  simp only [HJ12.hjTripleOK, HJ12.hjMixedSpan, Bool.and_eq_true, List.any_eq_true] at hok ⊢
  simp_all

theorem row_mem_enum_of_rows {u : MulAut W12} {w : Array Nat}
    (hu : u ∈ hjT1) (huw : RowsOf u w) (hcan : w.size = 12 ∧ ∀ a ∈ w, a < 4096) :
    w ∈ CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
      (HJ12.hj_t0Words.map wordR ++ [hjTauc]) := by
  classical
  obtain ⟨hg, -, -, -⟩ := hjT1_enum_facts
  obtain ⟨r, hr, hur⟩ := (hjT1_mem_iff u).1 hu
  have hwr : w = r := rows_eq_of_rowsOf huw hur hcan (canon_of_mem_enumGrp hg hr)
  rw [hwr]
  exact hr

theorem mQuot_zpowers_eq_two {A : Subgroup (MulAut W12)} (hcardA : Nat.card A = 8)
    {u : MulAut W12} (hu : u ∈ A) (hsq : u ^ 2 = 1) (hu1 : u ≠ 1) :
    E3.mQuot A (Subgroup.zpowers u) = 2 := by
  have hcardz : Nat.card ↥(Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hsq hu1]
  have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers u) (K := A)
  rw [inf_eq_left.2 (Subgroup.zpowers_le.mpr hu), hcardz, hcardA] at h
  have hrel : (Subgroup.zpowers u).relIndex A = 4 := by omega
  unfold E3.mQuot
  rw [hrel]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4, padicValNat.prime_pow]

theorem aSet_not_mixed {A : Subgroup (MulAut W12)} (hA : A ∈ E3.aSet 3 hjT1)
    (hcardA : Nat.card A = 8) {u v : MulAut W12} (hu : u ∈ A) (hv : v ∈ A)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hdiff : Nat.card (fixV (Subgroup.zpowers u)) ≠
      Nat.card (fixV (Subgroup.zpowers v))) : False := by
  have hu2 : u ^ 2 = 1 := hA.2.2.1.2 u hu
  have hv2 : v ^ 2 = 1 := hA.2.2.1.2 v hv
  have hmU : E3.mQuot A (Subgroup.zpowers u) = 2 := mQuot_zpowers_eq_two hcardA hu hu2 hu1
  have hmV : E3.mQuot A (Subgroup.zpowers v) = 2 := mQuot_zpowers_eq_two hcardA hv hv2 hv1
  have hfixU : fixV (Subgroup.zpowers u) = fixV A :=
    hA.2.2.2 (Subgroup.zpowers u) (Subgroup.zpowers_le.mpr hu) (by rw [hmU]; norm_num)
  have hfixV : fixV (Subgroup.zpowers v) = fixV A :=
    hA.2.2.2 (Subgroup.zpowers v) (Subgroup.zpowers_le.mpr hv) (by rw [hmV]; norm_num)
  exact hdiff (by rw [hfixU, hfixV])

theorem hjCommR_of_commute {x y : MulAut W12} {rx ry : Array Nat}
    (hxr : RowsOf x rx) (hyr : RowsOf y ry)
    (hxcan : rx.size = 12 ∧ ∀ a ∈ rx, a < 4096)
    (hycan : ry.size = 12 ∧ ∀ a ∈ ry, a < 4096)
    (hxy : x * y = y * x) : HJ12.commR rx ry = true := by
  have h1 : CFSG.GammaU.Native.mulR rx ry = CFSG.GammaU.Native.mulR ry rx := by
    refine rows_eq_of_rowsOf (rowsOf_mul hxr hyr) ?_
      ⟨(size_mulR rx ry).trans hycan.1, mulR_lt (g := rx) (h := ry) hxcan.2⟩
      ⟨(size_mulR ry rx).trans hxcan.1, mulR_lt (g := ry) (h := rx) hycan.2⟩
    rw [hxy]
    exact rowsOf_mul hyr hxr
  simpa only [HJ12.commR, beq_iff_eq] using h1

theorem exists_rows_triple
    {A : Subgroup (MulAut W12)} {x y z : MulAut W12} {rx ry rz : Array Nat}
    (hAle : A ≤ hjT1) (hxA : x ∈ A) (hyA : y ∈ A) (hzA : z ∈ A)
    (hxr : RowsOf x rx) (hyr : RowsOf y ry) (hzr : RowsOf z rz)
    (hxcan : rx.size = 12 ∧ ∀ a ∈ rx, a < 4096)
    (hycan : ry.size = 12 ∧ ∀ a ∈ ry, a < 4096)
    (hzcan : rz.size = 12 ∧ ∀ a ∈ rz, a < 4096)
    (hxsq : x ^ 2 = 1) (hysq : y ^ 2 = 1) (hzsq : z ^ 2 = 1)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hx1 : x ≠ 1) (hyNot : y ∉ Subgroup.zpowers x)
    (hzNot : z ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    ∀ w ∈ HJ12.hjTripleRows rx ry rz,
      ∃ u ∈ A, u ≠ 1 ∧ RowsOf u w ∧ w.size = 12 ∧ ∀ a ∈ w, a < 4096 := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hxsq)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hysq)
  have hy1 : y ≠ 1 := fun h => hyNot (h ▸ Subgroup.one_mem _)
  have hz1 : z ≠ 1 := fun h => hzNot (h ▸ Subgroup.one_mem _)
  have hxysq : (x * y) ^ 2 = 1 := by
    rw [pow_two]
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = x * x * (y * y) := by group
      _ = 1 := by rw [← pow_two, ← pow_two, hxsq, hysq, one_mul]
  have hxyinv : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hxysq)
  have hxy1 : x * y ≠ 1 := by
    intro h
    have hyx : y = x := by
      calc y = x⁻¹ * (x * y) := by group
        _ = x⁻¹ * 1 := by rw [h]
        _ = x⁻¹ := by rw [mul_one]
        _ = x := hxinv
    exact hyNot (hyx ▸ Subgroup.mem_zpowers x)
  have hzx1 : z * x ≠ 1 := by
    intro h
    have hzx : z = x := by
      calc z = x⁻¹ * (x * z) := by group
        _ = x⁻¹ * (z * x) := by rw [hxz]
        _ = x⁻¹ * 1 := by rw [h]
        _ = x⁻¹ := by rw [mul_one]
        _ = x := hxinv
    exact hzNot (Subgroup.mem_sup_left (hzx ▸ Subgroup.mem_zpowers x))
  have hzy1 : z * y ≠ 1 := by
    intro h
    have hzy : z = y := by
      calc z = y⁻¹ * (y * z) := by group
        _ = y⁻¹ * (z * y) := by rw [hyz]
        _ = y⁻¹ * 1 := by rw [h]
        _ = y⁻¹ := by rw [mul_one]
        _ = y := hyinv
    exact hzNot (Subgroup.mem_sup_right (hzy ▸ Subgroup.mem_zpowers y))
  have hxyz1 : x * y * z ≠ 1 := by
    intro h
    have hzxy : z = x * y := by
      calc z = (x * y)⁻¹ * (x * y * z) := by group
        _ = (x * y)⁻¹ * 1 := by rw [h]
        _ = (x * y)⁻¹ := by rw [mul_one]
        _ = x * y := hxyinv
    exact hzNot (hzxy ▸ (Subgroup.zpowers x ⊔ Subgroup.zpowers y).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
  have hxyA : x * y ∈ A := A.mul_mem hxA hyA
  have hzxA : z * x ∈ A := A.mul_mem hzA hxA
  have hzyA : z * y ∈ A := A.mul_mem hzA hyA
  have hxyzA : x * y * z ∈ A := A.mul_mem hxyA hzA
  intro w hw
  simp only [HJ12.hjTripleRows, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨x, hxA, hx1, hxr, hxcan⟩
  · exact ⟨y, hyA, hy1, hyr, hycan⟩
  · exact ⟨x * y, hxyA, hxy1, rowsOf_mul hxr hyr,
      (size_mulR rx ry).trans hycan.1, mulR_lt hxcan.2⟩
  · exact ⟨z, hzA, hz1, hzr, hzcan⟩
  · exact ⟨z * x, hzxA, hzx1, rowsOf_mul hzr hxr,
      (size_mulR rz rx).trans hxcan.1, mulR_lt hzcan.2⟩
  · exact ⟨z * y, hzyA, hzy1, rowsOf_mul hzr hyr,
      (size_mulR rz ry).trans hycan.1, mulR_lt hzcan.2⟩
  · exact ⟨x * y * z, hxyzA, hxyz1,
      rowsOf_mul (rowsOf_mul hxr hyr) hzr,
      (size_mulR (CFSG.GammaU.Native.mulR rx ry) rz).trans hzcan.1,
      mulR_lt (mulR_lt hxcan.2)⟩

theorem exists_rows_invs {x : MulAut W12} (hx : x ∈ hjT1)
    (hsq : x ^ 2 = 1) (hne : x ≠ 1) :
    ∃ r ∈ HJ12.hjT1Invs (), RowsOf x r ∧
      r ∈ CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
        (HJ12.hj_t0Words.map wordR ++ [hjTauc]) ∧
      r.size = 12 ∧ (∀ a ∈ r, a < 4096) ∧
      Nat.card (fixV (Subgroup.zpowers x)) = (fixCodes r).length := by
  classical
  obtain ⟨hg, -, -, -⟩ := hjT1_enum_facts
  obtain ⟨r, hrmem, hxr⟩ := (hjT1_mem_iff x).1 hx
  have hinv := hjRows_invs hx hxr hsq hne hrmem
  obtain ⟨hcan, hlt⟩ := canon_of_mem_enumGrp hg hrmem
  exact ⟨r, hinv.1, hxr, hrmem, hcan, hlt, hinv.2⟩

theorem not_mem_aSet_three_hjT1 :
    ∀ A : Subgroup (MulAut W12), A ∉ E3.aSet 3 hjT1 := by
  classical
  have : Finite (MulAut W12) :=
    Finite.of_injective (fun e : MulAut W12 => (e : W12 → W12))
      (fun a b h => MulEquiv.ext (congrFun h))
  intro A hA
  obtain ⟨-, -, -, -, -, -, -, -, hE16, -⟩ := hjT1_facts
  have hAel := hA.2.2.1
  have hAle : A ≤ hjT1 := hA.1
  have hA16 : Nat.card A ≤ 16 := (hE16 A hAle hAel).1
  have hA2p : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hAel
  have hm3 : 3 ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
  have hcardpow : Nat.card A = 2 ^ E3.mQuot A ⊥ := by
    rw [← E3.relIndex_eq_two_pow hA2p ⊥, Subgroup.relIndex_bot_left]
  have h8 : 8 ≤ Nat.card A := by
    rw [hcardpow]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hm3
  have hm34 : E3.mQuot A ⊥ = 3 ∨ E3.mQuot A ⊥ = 4 := by
    have hle4 : E3.mQuot A ⊥ ≤ 4 := by
      by_contra h
      have h5 : 5 ≤ E3.mQuot A ⊥ := by omega
      have h2 : 2 ^ 5 ≤ 2 ^ E3.mQuot A ⊥ := Nat.pow_le_pow_right (by norm_num : 0 < 2) h5
      rw [hcardpow] at hA16
      omega
    omega
  rcases hm34 with hm | hm
  ·
    have hcardA : Nat.card A = 8 := by rw [hcardpow, hm]; norm_num
    have hxExists : ∃ x ∈ A, x ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : A = ⊥ := eq_bot_iff.2 fun a ha => Subgroup.mem_bot.2 (h a ha)
      rw [hbot, Subgroup.card_bot] at hcardA
      omega
    obtain ⟨x, hxA, hx1⟩ := hxExists
    have hxT1 : x ∈ hjT1 := hAle hxA
    have hxsq : x ^ 2 = 1 := hAel.2 x hxA
    obtain ⟨rx, hrxinv, hrx, hrxenum, hrxcan, hrxlt, hrxlen⟩ := exists_rows_invs hxT1 hxsq hx1
    have hcardzx : Nat.card ↥(Subgroup.zpowers x) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxsq hx1]
    have hnotle1 : ¬ A ≤ Subgroup.zpowers x := by
      intro hle
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨y, hyA, hyNot⟩ := Set.not_subset.1 hnotle1
    have hy1 : y ≠ 1 := fun h => hyNot (h ▸ Subgroup.one_mem _)
    have hyT1 : y ∈ hjT1 := hAle hyA
    have hysq : y ^ 2 = 1 := hAel.2 y hyA
    have hxy : x * y = y * x := hAel.1 x hxA y hyA
    obtain ⟨ry, hryinv, hry, hryenum, hrycan, hrylt, hrylen⟩ := exists_rows_invs hyT1 hysq hy1
    let B2 : Subgroup (MulAut W12) := Subgroup.zpowers x ⊔ Subgroup.zpowers y
    have hxyne : x ≠ y := fun h => hyNot (h ▸ Subgroup.mem_zpowers x)
    have hB2card : Nat.card ↥B2 = 4 :=
      CFSG.CGT.Foote81L6.TStruct.card_zpowers_sup_zpowers (by simpa [pow_two] using hxsq)
        (by simpa [pow_two] using hysq) hx1 hy1 hxyne hxy
    have hnotle2 : ¬ A ≤ B2 := by
      intro hle
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨z, hzA, hzNot⟩ := Set.not_subset.1 hnotle2
    have hz1 : z ≠ 1 := fun h => hzNot (h ▸ Subgroup.one_mem _)
    have hzT1 : z ∈ hjT1 := hAle hzA
    have hzsq : z ^ 2 = 1 := hAel.2 z hzA
    have hxz : x * z = z * x := hAel.1 x hxA z hzA
    have hyz : y * z = z * y := hAel.1 y hyA z hzA
    obtain ⟨rz, hrzinv, hrz, hrzenum, hrzcan, hrzlt, hrzlen⟩ := exists_rows_invs hzT1 hzsq hz1
    have hrxry : rx ≠ ry := by
      intro h
      have hxy' : x = y := HJBridge.rowsOf_unique (h ▸ hrx) hry
      exact hyNot (hxy' ▸ Subgroup.mem_zpowers x)
    have hrxrz : rx ≠ rz := by
      intro h
      have hxz' : x = z := HJBridge.rowsOf_unique (h ▸ hrx) hrz
      exact hzNot (Subgroup.mem_sup_left (hxz' ▸ Subgroup.mem_zpowers x))
    have hryrz : ry ≠ rz := by
      intro h
      have hyz' : y = z := HJBridge.rowsOf_unique (h ▸ hry) hrz
      exact hzNot (Subgroup.mem_sup_right (hyz' ▸ Subgroup.mem_zpowers y))
    have hbxy : (rx == ry) = false := by simpa [beq_iff_eq] using hrxry
    have hbxz : (rx == rz) = false := by simpa [beq_iff_eq] using hrxrz
    have hbyz : (ry == rz) = false := by simpa [beq_iff_eq] using hryrz
    have hcommRxy : HJ12.commR rx ry = true :=
      hjCommR_of_commute hrx hry ⟨hrxcan, hrxlt⟩ ⟨hrycan, hrylt⟩ hxy
    have hcommRxz : HJ12.commR rx rz = true :=
      hjCommR_of_commute hrx hrz ⟨hrxcan, hrxlt⟩ ⟨hrzcan, hrzlt⟩ hxz
    have hcommRyz : HJ12.commR ry rz = true :=
      hjCommR_of_commute hry hrz ⟨hrycan, hrylt⟩ ⟨hrzcan, hrzlt⟩ hyz
    have hind : ([CFSG.GammaU.Native.idR, rx, ry,
        CFSG.GammaU.Native.mulR rx ry].contains rz) = false := by
      have hnotmem : rz ∉ [CFSG.GammaU.Native.idR, rx, ry,
          CFSG.GammaU.Native.mulR rx ry] := by
        intro hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h | h | h
        · have hz1' : z = 1 := by
            rw [h] at hrz
            exact HJBridge.rowsOf_unique hrz HJBridge.rowsOf_one
          exact hz1 hz1'
        · have hx' : z = x := by
            rw [h] at hrz
            exact HJBridge.rowsOf_unique hrz hrx
          exact hzNot (Subgroup.mem_sup_left (hx' ▸ Subgroup.mem_zpowers x))
        · have hy' : z = y := by
            rw [h] at hrz
            exact HJBridge.rowsOf_unique hrz hry
          exact hzNot (Subgroup.mem_sup_right (hy' ▸ Subgroup.mem_zpowers y))
        · have hxy' : z = x * y := by
            rw [h] at hrz
            exact HJBridge.rowsOf_unique hrz (rowsOf_mul hrx hry)
          exact hzNot (hxy' ▸ B2.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
      cases hc : ([CFSG.GammaU.Native.idR, rx, ry,
          CFSG.GammaU.Native.mulR rx ry].contains rz) with
      | false => rfl
      | true => exact absurd (List.contains_iff_mem.1 hc) hnotmem
    by_cases hxycard : Nat.card (fixV (Subgroup.zpowers x)) =
        Nat.card (fixV (Subgroup.zpowers y))
    · by_cases hyzcard : Nat.card (fixV (Subgroup.zpowers y)) =
          Nat.card (fixV (Subgroup.zpowers z))
      have hlenxy : HJ12.hjLookup (HJ12.hjT1Tab ()) rx =
          HJ12.hjLookup (HJ12.hjT1Tab ()) ry := by
        rw [hjLookup_eq hrxinv, hjLookup_eq hryinv, ← hrxlen, ← hrylen]
        exact hxycard
      have hlenyz : HJ12.hjLookup (HJ12.hjT1Tab ()) ry =
          HJ12.hjLookup (HJ12.hjT1Tab ()) rz := by
        rw [hjLookup_eq hryinv, hjLookup_eq hrzinv, ← hrylen, ← hrzlen]
        exact hyzcard
      have hindStep : ([idR, rx, ry, mulR rx ry].contains rz) = false := hind
      obtain ⟨⟨w64, hw64mem, hw64lookup⟩, ⟨w256, hw256mem, hw256lookup⟩⟩ :=
        hjPureTripleCheck_spec hrxinv hryinv hrzinv hbxy hbxz hbyz hcommRxy hcommRxz
          hcommRyz hindStep hlenxy hlenyz
      have hexTriple : ∀ w ∈ HJ12.hjTripleRows rx ry rz,
          ∃ u ∈ A, u ≠ 1 ∧ RowsOf u w ∧ w.size = 12 ∧ ∀ a ∈ w, a < 4096 :=
        exists_rows_triple hAle hxA hyA hzA hrx hry hrz ⟨hrxcan, hrxlt⟩
          ⟨hrycan, hrylt⟩ ⟨hrzcan, hrzlt⟩ hxsq hysq hzsq hxy hxz hyz hx1 hyNot hzNot
      obtain ⟨u, huA, hu1, huRows, hucan⟩ := hexTriple w64 hw64mem
      obtain ⟨v, hvA, hv1, hvRows, hvcan⟩ := hexTriple w256 hw256mem
      have huEnum : w64 ∈ CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
          (HJ12.hj_t0Words.map wordR ++ [hjTauc]) :=
        row_mem_enum_of_rows (hAle huA) huRows hucan
      have hvEnum : w256 ∈ CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
          (HJ12.hj_t0Words.map wordR ++ [hjTauc]) :=
        row_mem_enum_of_rows (hAle hvA) hvRows hvcan
      have huInv := hjRows_invs (hAle huA) huRows (hAel.2 u huA) hu1 huEnum
      have hvInv := hjRows_invs (hAle hvA) hvRows (hAel.2 v hvA) hv1 hvEnum
      have hcardU : Nat.card (fixV (Subgroup.zpowers u)) = 64 := by
        rw [huInv.2, ← hjLookup_eq huInv.1, hw64lookup]
      have hcardV : Nat.card (fixV (Subgroup.zpowers v)) = 256 := by
        rw [hvInv.2, ← hjLookup_eq hvInv.1, hw256lookup]
      exact aSet_not_mixed hA hcardA huA hvA hu1 hv1 (by rw [hcardU, hcardV]; norm_num)
      · exact aSet_not_mixed hA hcardA hyA hzA hy1 hz1 hyzcard
    · exact aSet_not_mixed hA hcardA hxA hyA hx1 hy1 hxycard
  ·
    have hcardA : Nat.card A = 16 := by rw [hcardpow, hm]; norm_num
    have hAeq := (hE16 A hAle hAel).2 hcardA
    rcases hAeq with rfl | rfl
    · exact hjA1_not_mem_aSet_three hA
    · exact hjA2_not_mem_aSet_three hA

theorem aParam_normalizer_hjL0_le_two :
    E3.aParam (Subgroup.normalizer (hjL0 : Set (MulAut W12))) ≤ 2 := by
  classical
  let N : Subgroup (MulAut W12) := Subgroup.normalizer (hjL0 : Set (MulAut W12))
  have : Finite (MulAut W12) :=
    Finite.of_injective (fun e : MulAut W12 => (e : W12 → W12))
      (fun a b h => MulEquiv.ext (congrFun h))
  obtain ⟨-, -, -, hT1N, -, hT1card, -, -, -, -⟩ := hjT1_facts
  have hT1p : IsPGroup 2 ↥hjT1 := IsPGroup.of_card (by rw [hT1card])
  have hNnorm : (hjL0.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer)).2 le_rfl
  have hNcard : Nat.card N ∣ 6 * Nat.card hjL0 :=
    card_dvd_six_mul_of_normal (Y := N) (Subgroup.le_normalizer) hNnorm
  have hLcard : Nat.card hjL0 = 604800 := by
    obtain ⟨e⟩ := hjL0_isSpor
    exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  rw [hLcard] at hNcard
  have hmul := Subgroup.relIndex_mul_card (H := hjT1) (K := N)
  rw [inf_eq_left.2 hT1N] at hmul
  rw [hT1card] at hmul
  have hdvd : hjT1.relIndex N * 2 ^ 8 ∣ 6 * 604800 := by
    rw [hmul]
    exact hNcard
  have hdvd' : hjT1.relIndex N ∣ 14175 := by
    have h6 : 6 * 604800 = 2 ^ 8 * 14175 := by norm_num
    rw [h6, mul_comm (hjT1.relIndex N) (2 ^ 8)] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 2 ^ 8)).1 hdvd
  have hodd : ¬ 2 ∣ hjT1.relIndex N := by
    intro h
    have h2 : 2 ∣ 14175 := h.trans hdvd'
    norm_num at h2
  have hSyl : CFSG.Quasithin.IsSylowIn 2 hjT1 N := ⟨hT1N, hT1p, hodd⟩
  refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty N 2 ?_
  intro A hA
  have hAel := hA.2.2.1
  have hAp : IsPGroup 2 ↥A := E3.isPGroup_of_isElemAbelian2 hAel
  obtain ⟨g, hgN, hconj⟩ :=
    exists_conj_le_of_quasithin_isSylowIn hSyl hA.1 hAp
  have hconjA : CFSG.Quasithin.conjAutSub g A ∈ E3.aSet 3 (CFSG.Quasithin.conjAutSub g N) :=
    aSet_conjAutSub hA
  have hNconj : CFSG.Quasithin.conjAutSub g N = N := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨n, hn, rfl⟩
      show MulAut.conj g n ∈ N
      rw [MulAut.conj_apply]
      exact N.mul_mem (N.mul_mem hgN hn) (N.inv_mem hgN)
    · have h : Nat.card ↥(N.map (MulAut.conj g).toMonoidHom) = Nat.card ↥N :=
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulEquiv.injective (MulAut.conj g))
      rw [CFSG.Quasithin.conjAutSub, h]
  have hmem : CFSG.Quasithin.conjAutSub g A ∈ E3.aSet 3 N := by
    rw [← hNconj]
    exact hconjA
  exact not_mem_aSet_three_hjT1 _ (mem_aSet_of_le hmem hconj)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
