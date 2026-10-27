module

public import Certificates.Kernel.Co1.Model
public import CFSG.Certificates.Kernel.Co1DceSound
public import CFSG.Certificates.Kernel.Co1.Data.D1S_0
public import CFSG.Certificates.Kernel.Co1.Data.C7_Sel
public import Certificates.Kernel.Co2.Join
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Co1.Checks.Bind
import CFSG.Certificates.Kernel.Co1.Checks.D1S_H_0
import CFSG.Certificates.Kernel.Co1.Checks.D1S_W_0
import CFSG.Certificates.Kernel.Co1.Checks.D1S_W_1
import CFSG.Certificates.Kernel.Co1.Checks.D1S_W_2
import CFSG.Certificates.Kernel.Co1.Checks.D1S_C_0
import CFSG.Certificates.Kernel.Co1.Checks.D1S_E_0
import CFSG.Certificates.Kernel.Co1.Checks.D1S_E_1
import CFSG.Certificates.Kernel.Co1.Checks.M1S_H_0

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.Bind CFSG.KC.DceS CFSG.KC.Loop CFSG.Certificates CFSG.Certificates.LCE
  CFSG.Certificates.Co1D CertificateChecks.KernelCo2

theorem dceFacts_append (blk LT HT PBT WT : ℕ → ℕ) (NL TL NB BB NH ND NO : ℕ) :
    ∀ l1 l2 x, runFacts blk LT HT PBT WT NL TL NB BB NH ND NO (List.append l1 l2) x =
      runFacts blk LT HT PBT WT NL TL NB BB NH ND NO l2 (runFacts blk LT HT PBT WT NL TL NB BB NH ND NO l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (runChunk blk LT HT PBT WT NL TL NB BB NH ND NO C x)
        (runFacts blk LT HT PBT WT NL TL NB BB NH ND NO (List.append l1 l2)) =
      runFacts blk LT HT PBT WT NL TL NB BB NH ND NO l2
        (strictN (runChunk blk LT HT PBT WT NL TL NB BB NH ND NO C x)
          (runFacts blk LT HT PBT WT NL TL NB BB NH ND NO l1))
    rw [strictN_eq, strictN_eq, dceFacts_append blk LT HT PBT WT NL TL NB BB NH ND NO l1 l2]

theorem dceCover_append (blk PBT OMT : ℕ → ℕ) (NB NO hi ALIVE nf : ℕ) :
    ∀ l1 l2 x, runCover blk PBT OMT NB NO hi ALIVE nf (List.append l1 l2) x =
      runCover blk PBT OMT NB NO hi ALIVE nf l2 (runCover blk PBT OMT NB NO hi ALIVE nf l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (covChunk blk PBT OMT NB NO hi ALIVE nf C x)
        (runCover blk PBT OMT NB NO hi ALIVE nf (List.append l1 l2)) =
      runCover blk PBT OMT NB NO hi ALIVE nf l2
        (strictN (covChunk blk PBT OMT NB NO hi ALIVE nf C x) (runCover blk PBT OMT NB NO hi ALIVE nf l1))
    rw [strictN_eq, strictN_eq, dceCover_append blk PBT OMT NB NO hi ALIVE nf l1 l2]

#kc_join_range D1Sfacts dceFacts_append CFSG.KD.D1S "sW" 0 45
#kc_join_range D1Scover dceCover_append CFSG.KD.D1S "sC" 0 3

set_option maxRecDepth 100000 in
theorem d1s_enum : Nat.beq (eCnt (enumRun CFSG.KD.D1S.NE (nGens CFSG.KD.D1S.LT CFSG.KD.D1S.NL CFSG.KD.D1S.TL)
    (nat_lit 3) CFSG.KD.D1S.nN (nat_lit 0) CFSG.KD.D1S.nN (nat_lit 1))) (Nat.succ CFSG.KD.D1S.nN) = true := by
  have j := enumRun_join CFSG.KD.D1S.sE0 CFSG.KD.D1S.sE1
  have j := enumRun_join j CFSG.KD.D1S.sE2
  have j := enumRun_join j CFSG.KD.D1S.sE3
  have j := enumRun_join j CFSG.KD.D1S.sE4
  have j := enumRun_join j CFSG.KD.D1S.sE5
  have j := enumRun_join j CFSG.KD.D1S.sE6
  have j := enumRun_join j CFSG.KD.D1S.sE7
  have j := enumRun_join j CFSG.KD.D1S.sE8
  have j := enumRun_join j CFSG.KD.D1S.sE9
  have j := enumRun_join j CFSG.KD.D1S.sE10
  have j := enumRun_join j CFSG.KD.D1S.sE11
  have j := enumRun_join j CFSG.KD.D1S.sE12
  have j := enumRun_join j CFSG.KD.D1S.sE13
  have j := enumRun_join j CFSG.KD.D1S.sE14
  have j := enumRun_join j CFSG.KD.D1S.sE15
  have j := enumRun_join j CFSG.KD.D1S.sE16
  have j := enumRun_join j CFSG.KD.D1S.sE17
  have j := enumRun_join j CFSG.KD.D1S.sE18
  have j := enumRun_last j CFSG.KD.D1S.sE19
  exact enumRun_len j (by quickRfl)

theorem dceOk_intro {blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE : ℕ → ℕ}
    {NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT
      hL hH hO hR hD P : ℕ} {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}
    (c1 : constOK OMT NB NO I0 BB BASEM NL TL ND ALIVE = true)
    (c2 : invSelfOK INV INV8 NL = true) (c3 : invRelOK RT NL NR IH = true)
    (c4 : allBelow NL hL (letOK LT TL) = true) (c5 : allBelow NH hH (hdrOK HT LT NL) = true)
    (c6 : allBelow NO hO (omOK PBT OMT GT HT NB NH (PBT I0)) = true)
    (c7 : wordsOK WT RT LT INV INV8 NL TL NR NW HS = true)
    (c8 : allBelow NR hR (relOK RT LT NL TL) = true) (c9 : wtDceOK WT NW P = true)
    (c10 : Nat.ble NL (Nat.mul (nat_lit 64) hL) = true) (c11 : Nat.ble NH (Nat.mul (nat_lit 64) hH) = true)
    (c12 : Nat.ble NO (Nat.mul (nat_lit 64) hO) = true) (c13 : Nat.ble NR (Nat.mul (nat_lit 64) hR) = true)
    (c14 : Nat.ble ND (Nat.mul (nat_lit 64) hD) = true) (c15 : Nat.ble ND (nat_lit 16384) = true)
    (c16 : Nat.blt NH (nat_lit 65536) = true) (c17 : Nat.blt nf (nat_lit 4294967296) = true)
    (c18 : Nat.blt nN (nat_lit 16777215) = true) (c19 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true)
    (c20 : Nat.beq (runFacts blk LT HT PBT WT NL TL NB BB NH ND NO Cs S0) S1 = true)
    (c21 : Nat.beq S1 (mkS nf ND) = true) (c22 : Nat.beq X0 (nat_lit 1) = true)
    (c23 : Nat.beq (runCover blk PBT OMT NB NO hO ALIVE nf CCs X0) X1 = true)
    (c24 : Nat.beq X1 (Nat.succ ND) = true) (c25 : Nat.beq ngN (Nat.sub NL (nat_lit 1)) = true)
    (c26 : Nat.beq (eCnt (enumRun NE (nGens LT NL TL) ngN nN (nat_lit 0) nN (nat_lit 1))) (Nat.succ nN) = true)
    (c27 : Nat.blt SUMIDX failV = true)
    (c28 : Nat.beq (indexSum blk SE STT nf nN ND hD ALIVE) SUMIDX = true)
    (c29 : Nat.ble ngT (nat_lit 7) = true) (c30 : tgOK PBT OMT NB I0 TGs ngT = true)
    (c31 : Nat.beq (eCnt (enumRun TTE TGs ngT nT (nat_lit 0) nT (nat_lit 1))) (Nat.succ nT) = true)
    (c32 : Nat.beq (Nat.mul nT NO) nN = true)
    (c33 : allBelow NO hO (CFSG.KC.Co1M.omClosOK LT PBT OMT OHT NL TL NB NO) = true) :
    dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH
      NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0 X1 = true := by
  unfold dceOk
  rw [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22,
    c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33]
  rfl

noncomputable abbrev dx : ℕ → PG := fun c => cg2 (mget CFSG.KD.Co1B.QMD c)

theorem nl_eq : CFSG.KD.D1S.NL = 4 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem tl_eq : CFSG.KD.D1S.TL = 3 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem iqd_spec : ∀ g < 127, mget CFSG.KD.Co1B.IQD g < 255 →
    mget CFSG.KD.Co1B.IQD g < 4 ∧ mget CFSG.KD.Co1B.QMD (mget CFSG.KD.Co1B.IQD g) = g ∧ g < 7 := by
  decide +kernel

theorem hrels : ∀ r < CFSG.KD.D1S.NR, rval dx (CFSG.KD.D1S.RT r) = 1 :=
  BindA.relsA_sound pg2 dx CFSG.KD.Co1B.bD CFSG.KD.Co1B.bS2 sb2_lt pg2_sq r2' r2_let
    (fun g hg hm => by
      obtain ⟨h1, h2, h3⟩ := iqd_spec g hg hm
      change 1 * mget CFSG.KD.Co1B.IQD g < 256 ∧ dx (1 * mget CFSG.KD.Co1B.IQD g) = pg2 g
      rw [Nat.one_mul]
      refine ⟨by omega, ?_⟩
      change cg2 (mget CFSG.KD.Co1B.QMD (mget CFSG.KD.Co1B.IQD g)) = (if g < 7 then cg2 g else 1)
      rw [h2]
      simp only [h3, ↓reduceIte])

theorem h2_eq : Subgroup.closure ((fun j => bval cg2 (CFSG.KC.LceS.wWord (CFSG.KD.C2.selST j))
    (CFSG.KC.LceS.wLen (CFSG.KD.C2.selST j))) '' {j | j < nat_lit 6}) =
      Subgroup.closure (dx '' {c | c < CFSG.KD.D1S.NL}) := by
  have hIQ : invMap CFSG.KD.Co1B.QMD CFSG.KD.D1S.NL ≠ 0 := by
    rw [← Nat.eq_of_beq_eq_true CFSG.KD.Co1B.bID]
    decide
  exact BindA.levelOK_sound cg2 CFSG.KD.Co1B.bLD (Nat.eq_of_beq_eq_true CFSG.KD.Co1B.bM2S) (by decide) hIQ
    CFSG.KD.Co1B.bS2 sb2_lt r2 (fun r hr => (r2_let r hr).2)

theorem lt_spec : ∀ c < 3, Nat.land (CFSG.KD.D1S.LT c) m64 = CFSG.KD.M1S.MPT c := by decide +kernel
theorem qm_spec : ∀ c < 3, mget CFSG.KD.Co1B.QM3 c = mget CFSG.KD.Co1B.QMD c := by decide +kernel

theorem hrho : ∀ w : List ℕ, (∀ c ∈ w, c < CFSG.KD.D1S.NL ∧ c ≠ CFSG.KD.D1S.TL) →
    wcode CFSG.KD.D1S.LT w = idP → (w.map dx).prod = 1 := by
  intro w hw hwc
  rw [nl_eq, tl_eq] at hw
  have hc : ∀ c ∈ w, c < 3 := fun c h => by
    have := hw c h
    omega
  have h1 : CFSG.Certificates.Co1M.wcodeL CFSG.KD.M1S.MPT CFSG.KD.M1S.MM3 (w.map (2 * ·)) =
      wcode CFSG.KD.D1S.LT w := by
    unfold CFSG.Certificates.Co1M.wcodeL wcode
    rw [List.foldl_map]
    apply List.foldl_ext
    intro acc c hcw
    have hc3 := hc c hcw
    unfold CFSG.Certificates.Co1M.lcode
    have e1 : 2 * c % 2 = 0 := by omega
    have e2 : 2 * c / 2 = c := by omega
    simp only [e1, e2, ↓reduceIte, mm3_spec c (by omega), lt_spec c hc3]
  have h2 : ((w.map (2 * ·)).map (letV cg3)).prod = (w.map dx).prod := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hcw
    have hc3 := hc c hcw
    change letV cg3 (2 * c) = cg2 (mget CFSG.KD.Co1B.QMD c)
    rw [letV_two]
    change cg2 (mget CFSG.KD.Co1B.QM3 c) = _
    rw [qm_spec c hc3]
  rw [← h2]
  refine model_faithful _ ?_ (h1.trans hwc)
  intro l hl
  obtain ⟨c, hcw, rfl⟩ := List.mem_map.mp hl
  have := hc c hcw
  omega

theorem rval_lit {G : Type*} [Group G] (y : ℕ → G) {e : ℕ} {L : List ℕ}
    (h : (List.range (rN e)).map (fun q => wLet (rW e) q) = L) : rval y e = (L.map y).prod := by
  unfold rval
  rw [← h, List.map_map]
  rfl

theorem comm_of_sq {G : Type*} [Group G] {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (h : s * t * (s * t) = 1) : s * t = t * s := by
  have e : s * t = (s * t)⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [e, mul_inv_rev, inv_eq_of_mul_eq_one_right hs, inv_eq_of_mul_eq_one_right ht]

theorem rel_prod (r : ℕ) (hr : r < 16) {L : List ℕ}
    (h : (List.range (rN (CFSG.KD.D1S.RT r))).map (fun q => wLet (rW (CFSG.KD.D1S.RT r)) q) = L) :
    (L.map dx).prod = 1 := by
  rw [← rval_lit dx h]
  exact hrels r (by rw [show CFSG.KD.D1S.NR = 16 from Nat.eq_of_beq_eq_true (by quickRfl)]; exact hr)

noncomputable abbrev TGs : ℕ := CFSG.KC.Co1M.tGens CFSG.KD.M1S.MPT CFSG.KD.C7.selST CFSG.KD.M1S.MM5 3

theorem hT : ∀ k < 3, ∃ w : List ℕ, (∀ c ∈ w, c < CFSG.KD.D1S.NL ∧ c ≠ CFSG.KD.D1S.TL) ∧
    wcode CFSG.KD.D1S.LT w = gk TGs k ∧
      (w.map dx).prod * dx CFSG.KD.D1S.TL = dx CFSG.KD.D1S.TL * (w.map dx).prod := by
  have ht : dx 3 * dx 3 = 1 := by
    have h := rel_prod 1 (by norm_num) (L := [3, 3]) (by decide +kernel)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h
  intro k hk
  rw [nl_eq, tl_eq]
  interval_cases k
  · refine ⟨[1], by decide, Nat.eq_of_beq_eq_true (by quickRfl), ?_⟩
    have hs : dx 1 * dx 1 = 1 := by
      have h := rel_prod 2 (by norm_num) (L := [1, 1]) (by decide +kernel)
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using h
    have h := rel_prod 14 (by norm_num) (L := [3, 1, 3, 1]) (by decide +kernel)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h ⊢
    exact (comm_of_sq ht hs (by simpa only [mul_assoc] using h)).symm
  · refine ⟨[0, 2, 0, 2], by decide, Nat.eq_of_beq_eq_true (by quickRfl), ?_⟩
    have hs := rel_prod 4 (by norm_num) (L := [0, 2, 0, 2, 0, 2, 0, 2]) (by decide +kernel)
    have h := rel_prod 12 (by norm_num) (L := [0, 2, 0, 2, 3, 0, 2, 0, 2, 3]) (by decide +kernel)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hs h ⊢
    exact comm_of_sq (by simpa only [mul_assoc] using hs) ht (by simpa only [mul_assoc] using h)
  · refine ⟨[1, 2, 1, 2, 1, 2], by decide, Nat.eq_of_beq_eq_true (by quickRfl), ?_⟩
    have hs := rel_prod 5 (by norm_num) (L := [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2]) (by decide +kernel)
    have h := rel_prod 13 (by norm_num) (L := [1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3]) (by decide +kernel)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hs h ⊢
    exact comm_of_sq (by simpa only [mul_assoc] using hs) ht (by simpa only [mul_assoc] using h)

theorem andB_split {a b : Bool} (h : CFSG.KC.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

set_option maxRecDepth 100000 in
theorem h2_card : Finite (Subgroup.closure (dx '' {c | c < CFSG.KD.D1S.NL})) ∧
    Nat.card (Subgroup.closure (dx '' {c | c < CFSG.KD.D1S.NL})) ≤ CFSG.KD.D1S.nN * CFSG.KD.D1S.SUMIDX := by
  obtain ⟨s1, s2⟩ := andB_split CFSG.KD.D1S.sS
  have hd := dceOk_intro (P := 64) (TGs := TGs) CFSG.KD.D1S.sH0 CFSG.KD.D1S.sH1 CFSG.KD.D1S.sH2
    CFSG.KD.D1S.sH3 CFSG.KD.D1S.sH4 CFSG.KD.D1S.sH5 CFSG.KD.D1S.sH6 CFSG.KD.D1S.sH7 (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) D1Sfacts (by quickRfl) (by quickRfl) D1Scover (by quickRfl)
    (by quickRfl) d1s_enum s1 s2 (by quickRfl) (by quickRfl) CFSG.KD.M1S.sM11 (by quickRfl)
    CFSG.KD.M1S.sM9
  exact dceOk_sound hd (Nat.pos_of_ne_zero (by decide)) dx hrels hrho hT

end CertificateChecks.KernelCo1

end
