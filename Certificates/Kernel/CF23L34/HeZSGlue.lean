module

public import Certificates.Kernel.CF23L34.HeZS
public import Certificates.Kernel.CF23L34.HeGSLGlue
public import Certificates.Kernel.SporSch.HeT.W2117
public import Certificates.Kernel.LocalComp.HeNormGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeZS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.ComponentClassification.GrSLit.HeGS Certificates.GrSLitHeZStar
open CertificateChecks.KernelLC.HeFix CertificateChecks.KernelLC.HeGS36
open CertificateChecks.KernelLC.HeGSL CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem beqN (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · simpa using Nat.ne_of_beq_eq_false h
  · simpa using Nat.eq_of_beq_eq_true h

theorem allBelow_iff' {m : Nat} {f : Nat → Bool} :
    CFSG.PSL3Four.Native.allBelow m f = true ↔ ∀ i < m, f i = true := by
  simp [CFSG.PSL3Four.Native.allBelow, List.all_eq_true]

theorem cmp32 {p q : Nat} (hp : canonK 32 6 (mask 6) (32 * 6) p = true)
    (hq : canonK 32 6 (mask 6) (32 * 6) q = true) :
    comp 32 (unpack 32 6 p) (unpack 32 6 q) = unpack 32 6 (pcomp 32 6 (mask 6) p q) :=
  compA_unpack hp hq

theorem comm_eq {t j : Nat} (ht : canonK 32 6 (mask 6) (32 * 6) t = true) (hj : j < 5) :
    heZCommMod (unpack 32 6 t) j = cmK t j := by
  have q := HeFix2329.cnQ5 hj
  have q0 := HeFix2329.cnQ5 (k := 0) (by decide)
  unfold heZCommMod cmK p32
  rw [HeFix2329.tTabs32_get hj, HeFix2329.tTabs32_get (k := 0) (by decide), cmp32 ht q, cmp32 q ht,
    cmp32 q0 (canonK_pcomp q ht),
    CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp ht q) (canonK_pcomp q ht),
    CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp ht q) (canonK_pcomp q0 (canonK_pcomp q ht))]

theorem syl_true : heZSylowOK = true := by
  have hi32 := ch22704_id32
  simp only [Bool.and_eq_true] at hi32
  have id32 : idTab 32 = unpack 32 6 (pidn 32 6) := (idK_sound hi32.1.1).symm
  unfold heZSylowOK
  rw [CertificateChecks.KernelLC.HeNorm.tabs_eq, Array.all_eq_true]
  intro i hi
  rw [Array.size_ofFn] at hi
  rw [Array.getElem_ofFn]
  have ht : canonK 32 6 (mask 6) (32 * 6) (HeT32.T i) = true :=
    (CFSG.KC.HeFixKSnd.pin_pts_PP HeFix2329.pinT i hi).1
  have h := allN_spec ch22704_syl i hi
  unfold sylK p32 at h
  have hcm : CFSG.PSL3Four.Native.allBelow 5 (heZCommMod (unpack 32 6 (HeT32.T i))) =
      allN 5 (cmK (HeT32.T i)) := by
    apply Bool.eq_iff_iff.2
    rw [allBelow_iff', CFSG.KS.Raw.Orb.allN_iff]
    exact forall_congr' fun j => imp_congr_right fun hj => by rw [comm_eq ht hj]
  rw [hcm, cmp32 ht ht, id32, CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp ht ht) hi32.1.2]
  exact h

theorem zw : ∀ x < 105, ∀ j ∈ heZWords.getD x [], j < 5 := by decide +kernel

theorem zu {x : Nat} (hx : x < 105) :
    heZU x = unpack 105 7 (ZU x) ∧ canonK 105 7 (mask 7) (105 * 7) (ZU x) = true := by
  unfold heZU ZU
  rw [lget2_eq]
  exact wordTabK_eq HeL.idTab_eq HeL.base.2.1 _ fun j hj =>
    ⟨HeL.dgens_get (zw x hx j hj), (HeL.dg_facts (zw x hx j hj)).2.1⟩

theorem trans_true : heZTransOK = true := by
  unfold heZTransOK
  rw [allBelow_iff']
  intro x hx
  rw [(zu hx).1, CFSG.KC.HeFixK.unpack_getElem! (by decide : 0 < 105), beqN]
  exact allN_spec ch22704_trans x hx

theorem fix_true : heZFixOK = true := by
  have h := ch22704_fix
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h79, h94⟩, hall⟩ := h
  have d2 : heDGens[2]! = unpack 105 7 (HDE.G 2) := HeL.dgens_get (by decide)
  obtain ⟨e79, c79⟩ := zu (x := 79) (by decide)
  obtain ⟨e94, c94⟩ := zu (x := 94) (by decide)
  have e63 := (zu (x := 63) (by decide)).1
  have e86 := (zu (x := 86) (by decide)).1
  unfold heZFixOK
  rw [d2, e79, e63, e94, e86]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [CFSG.KC.HeFixK.unpack_getElem! (by decide), beqN]
    exact h79
  · rw [CFSG.KC.HeFixK.unpack_getElem! (by decide), beqN]
    exact h94
  · rw [allBelow_iff']
    intro x hx
    have hx' := allN_spec hall x hx
    rw [CFSG.KC.HeFixK.unpack_getElem! hx, CFSG.KC.HeFixK.unpack_getElem! hx,
      CFSG.KC.HeFixK.unpack_getElem! hx, CFSG.KC.HeFixK.unpack_getElem! hx,
      CFSG.KC.HeFixK.unpack_getElem! (HeL.canon_lt c79 hx),
      CFSG.KC.HeFixK.unpack_getElem! (HeL.canon_lt c94 hx)]
    simp only [beqN]
    exact hx'

theorem check22704 :
    comp 8330 heZOuterTab heZOuterTab = idTab 8330 ∧ heZOuterTab ≠ idTab 8330 ∧
      heGSFix heZOuterTab = 346 ∧
      comp 8330 heZD1Tab heZD1Tab = idTab 8330 ∧ comp 8330 heZD2Tab heZD2Tab = idTab 8330 ∧
      heZD1Tab ≠ idTab 8330 ∧ heZD2Tab ≠ idTab 8330 ∧ heZD1Tab ≠ heZD2Tab ∧
      comp 8330 heZD1Tab heZD2Tab = comp 8330 heZD2Tab heZD1Tab ∧
      heZSylowOK = true ∧ heZTransOK = true ∧ heZFixOK = true ∧
      heGSFix heZUTab = 346 ∧ heGSFix heZT0UTab = 346 ∧
      comp 8330 heZT0UTab heZT0UTab = idTab 8330 ∧ heZT0UTab ≠ idTab 8330 := by
  have hc := ch22704_c
  have hd := ch22704_d
  have hu := ch22704_u
  simp only [Bool.and_eq_true] at hc hd
  simp only [sB, Bool.and_eq_true] at hu
  obtain ⟨⟨⟨cC, hOO⟩, hO1⟩, hOf⟩ := hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c0, c2⟩, h11⟩, h22⟩, h1⟩, h2⟩, h12⟩, hcm⟩ := hd
  obtain ⟨hu1, ⟨hu2, hu3⟩, hu4⟩ := hu
  have cO : cn O = true := cnpc cC cC
  have cD1 : cn D1 = true := cnpc c0 c0
  have cDY : cn DY = true := cnpc (cnpc cD1 c2) c2
  have cD2 : cn D2 = true := cnpc cDY (cnpc cDY cDY)
  have eO : heZOuterTab = unpack 8330 14 O := by
    unfold heZOuterTab O
    rw [(HeW17.C_word (j := 0) (by decide)).1, cmp cC cC]
  have eD1 : heZD1Tab = unpack 8330 14 D1 := by
    unfold heZD1Tab D1
    rw [(HeW17.D_word (j := 0) (by decide)).1, cmp c0 c0]
  have eDY : heZDYTab = unpack 8330 14 DY := by
    unfold heZDYTab DY
    rw [eD1, (HeW17.D_word (j := 2) (by decide)).1, cmp cD1 c2, cmp (cnpc cD1 c2) c2]
  have eD2 : heZD2Tab = unpack 8330 14 D2 := by
    unfold heZD2Tab D2
    rw [eDY, cmp cDY cDY, cmp cDY (cnpc cDY cDY)]
  have ku := kw (w := heGSComm2 heGSUComm) (by decide)
  have cT : cn (pc (HG.F 0) (K (heGSComm2 heGSUComm))) = true := cnpc cnG.1 ku.2
  have eT : heZT0UTab = unpack 8330 14 (pc (HG.F 0) (K (heGSComm2 heGSUComm))) := by
    unfold heZT0UTab heZUTab
    rw [ku.1, heGen_eq (k := 0) (by decide), cmp cnG.1 ku.2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, syl_true, trans_true, fix_true, ?_, ?_, ?_, ?_⟩
  · rw [eO, cmp cO cO, Nat.eq_of_beq_eq_true hOO, hidT]
  · rw [eO, hidT]
    exact ne_of cO hid hO1
  · rw [eO, fix_eq]
    exact Nat.eq_of_beq_eq_true hOf
  · rw [eD1, cmp cD1 cD1, Nat.eq_of_beq_eq_true h11, hidT]
  · rw [eD2, cmp cD2 cD2, Nat.eq_of_beq_eq_true h22, hidT]
  · rw [eD1, hidT]
    exact ne_of cD1 hid h1
  · rw [eD2, hidT]
    exact ne_of cD2 hid h2
  · rw [eD1, eD2]
    exact ne_of cD1 cD2 h12
  · rw [eD1, eD2, cmp cD1 cD2, cmp cD2 cD1, Nat.eq_of_beq_eq_true hcm]
  · unfold heZUTab
    rw [ku.1, fix_eq]
    exact Nat.eq_of_beq_eq_true hu1
  · rw [eT, fix_eq]
    exact Nat.eq_of_beq_eq_true hu2
  · rw [eT, cmp cT cT, Nat.eq_of_beq_eq_true hu3, hidT]
  · rw [eT, hidT]
    exact ne_of cT hid hu4

end CertificateChecks.KernelLC.HeZS

end
