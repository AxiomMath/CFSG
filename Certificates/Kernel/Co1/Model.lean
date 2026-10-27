module

public import Certificates.Kernel.Co1.Chain
public import CFSG.Certificates.Kernel.BindASound
public import CFSG.Certificates.Kernel.Co1ModelSound
public import CFSG.Certificates.Kernel.Co1.Data.C3_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C4_Sel
public import CFSG.Certificates.Kernel.Co1.Data.M1S_0
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Co1.FactsC34
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Co1.Checks.Bind
import CFSG.Certificates.Kernel.Co1.Checks.C3
import CFSG.Certificates.Kernel.Co1.Checks.C4
import CFSG.Certificates.Kernel.Co1.Checks.M1S_H_0
import CFSG.Certificates.Kernel.Co1.Checks.M1S_E_0
import CFSG.Certificates.Kernel.Co1.Checks.M1S_E_1
import CFSG.Certificates.Kernel.Co1.Checks.M1S_E_2
import CFSG.Certificates.Kernel.Co1.Checks.M1S_E_3

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Bind CFSG.KC.DceS CFSG.Certificates CFSG.Certificates.LCE
  CertificateChecks.KernelCo2

theorem enumRun_add (ET : ℕ → ℕ) (G ng n off : ℕ) :
    ∀ a b S, enumRun ET G ng n off (a + b) S = enumRun ET G ng n off b (enumRun ET G ng n off a S)
  | 0, b, S => by rw [Nat.zero_add]; rfl
  | a + 1, b, S => by
    rw [Nat.add_right_comm]
    change strictN (eStep ET G ng n off S) (enumRun ET G ng n off (a + b)) =
      enumRun ET G ng n off b (strictN (eStep ET G ng n off S) (enumRun ET G ng n off a))
    rw [strictN_eq, strictN_eq, enumRun_add ET G ng n off a b]

theorem enumRun_join {ET : ℕ → ℕ} {G ng n off a b S S' T : ℕ}
    (h1 : Nat.beq (enumRun ET G ng n off a S) S' = true) (h2 : Nat.beq (enumRun ET G ng n off b S') T = true) :
    Nat.beq (enumRun ET G ng n off (a + b) S) T = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [enumRun_add, h1, h2]

theorem enumRun_last {ET : ℕ → ℕ} {G ng n off a b S S' T : ℕ}
    (h1 : Nat.beq (enumRun ET G ng n off a S) S' = true)
    (h2 : Nat.beq (eCnt (enumRun ET G ng n off b S')) T = true) :
    Nat.beq (eCnt (enumRun ET G ng n off (a + b) S)) T = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [enumRun_add, h1, h2]

theorem enumRun_len {ET : ℕ → ℕ} {G ng n off M M' S T : ℕ}
    (h : Nat.beq (eCnt (enumRun ET G ng n off M S)) T = true) (hM : Nat.beq M M' = true) :
    Nat.beq (eCnt (enumRun ET G ng n off M' S)) T = true := by
  rw [← Nat.eq_of_beq_eq_true hM]
  exact h

noncomputable abbrev cg3 : ℕ → PG := fun k => cg2 (mget CFSG.KD.Co1B.QM3 k)

theorem iq3_spec : ∀ g < 127, mget CFSG.KD.Co1B.IQ3 g < 255 →
    mget CFSG.KD.Co1B.IQ3 g < 4 ∧ mget CFSG.KD.Co1B.QM3 (mget CFSG.KD.Co1B.IQ3 g) = g ∧ g < 7 := by
  decide +kernel

theorem sb2_lt : ∀ s < 2, Nat.shiftRight (Nat.land (Nat.shiftRight CFSG.KD.Co1B.SB2 (24 * s)) 16777215) 8 < 33 := by
  decide +kernel

theorem r2_let : ∀ r < 33, wLen (CFSG.KD.C2.selRT r) < 256 ∧
    ∀ q < wLen (CFSG.KD.C2.selRT r), wLet (wWord (CFSG.KD.C2.selRT r)) q < 254 :=
  relsLet_spec (by quickRfl)

theorem r3 : ∀ r < 18, bval cg3 (wWord (CFSG.KD.C3.selRT r)) (wLen (CFSG.KD.C3.selRT r)) = 1 :=
  BindA.relsA_sound pg2 (letV cg3) CFSG.KD.Co1B.b3 CFSG.KD.Co1B.bS2 sb2_lt pg2_sq r2' r2_let
    (fun g hg hm => by
      obtain ⟨h1, h2, h3⟩ := iq3_spec g hg hm
      change 2 * mget CFSG.KD.Co1B.IQ3 g < 256 ∧ letV cg3 (2 * mget CFSG.KD.Co1B.IQ3 g) = pg2 g
      refine ⟨by omega, ?_⟩
      rw [letV_two]
      change cg2 (mget CFSG.KD.Co1B.QM3 (mget CFSG.KD.Co1B.IQ3 g)) = (if g < 7 then cg2 g else 1)
      rw [h2]
      simp only [h3, ↓reduceIte])

theorem t34_bound (H : Type) [Group H] (y : ℕ → H)
    (hy : ∀ r < 18, bval y (wWord (CFSG.KD.C3.selRT r)) (wLen (CFSG.KD.C3.selRT r)) = 1) :
    Finite (Subgroup.closure (y '' {g | g < 4})) ∧
      Nat.card (Subgroup.closure (y '' {g | g < 4})) ≤ CFSG.KD.M1S.nG4 := by
  have t3 : Tab y CFSG.KD.C3.selST (nat_lit 3) (nat_lit 8) (nat_lit 4480) :=
    lceOk_sound (lceOk_intro CFSG.KD.C3.sH1 CFSG.KD.C3.sH0 CFSG.KD.Co1B.bHC3 CFSG.KD.C3.sH2
      CFSG.KD.C3.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
      C3facts (by quickRfl) (by quickRfl) C3cover (by quickRfl)) y hy
  let cg4 : ℕ → H := fun j => bval y (wWord (CFSG.KD.C3.selST j)) (wLen (CFSG.KD.C3.selST j))
  have r4 : ∀ r < 8, bval cg4 (wWord (CFSG.KD.C4.selRT r)) (wLen (CFSG.KD.C4.selRT r)) = 1 :=
    BindS.relsSub_sound y cg4 CFSG.KD.Co1B.b4 (stmap_hM y CFSG.KD.Co1B.bM34 (by decide) (by decide))
      hy (fun r hr => (relsLet_spec (by quickRfl) r hr).2)
  have t4 : Tab cg4 CFSG.KD.C4.selST (nat_lit 0) (nat_lit 6) (nat_lit 72) :=
    lceOk_sound (lceOk_intro CFSG.KD.C4.sH1 CFSG.KD.C4.sH0 CFSG.KD.Co1B.bHC4 CFSG.KD.C4.sH2
      CFSG.KD.C4.sH3 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
      C4facts (by quickRfl) (by quickRfl) C4cover (by quickRfl)) cg4 r4
  unfold Tab at t3 t4
  rw [img_eq _ (nat_lit 3) (nat_lit 6) (fun x => by change x < 3 ↔ 2 * x < 6; omega)] at t3
  have e0 : (fun j => bval cg4 (wWord (CFSG.KD.C4.selST j)) (wLen (CFSG.KD.C4.selST j))) ''
      {j | j < nat_lit 0} = ∅ :=
    Set.image_eq_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun j hj => Nat.not_lt_zero j hj)
  rw [e0, Subgroup.closure_empty, Subgroup.relIndex_bot_left] at t4
  have c := card_le_step' t3 t4
  have e : {g : ℕ | 2 * g < nat_lit 8} = {g | g < 4} := by
    ext g
    change 2 * g < 8 ↔ g < 4
    omega
  rw [e] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (Nat.le_of_ble_eq_true (by quickRfl))⟩

set_option maxRecDepth 100000 in
theorem g4_enum : Nat.beq (eCnt (enumRun CFSG.KD.M1S.G4E (packGens CFSG.KD.M1S.MPT (nat_lit 4)) (nat_lit 4)
    CFSG.KD.M1S.nG4 (nat_lit 0) CFSG.KD.M1S.nG4 (nat_lit 1))) (Nat.succ CFSG.KD.M1S.nG4) = true := by
  have j := enumRun_join CFSG.KD.M1S.sG0 CFSG.KD.M1S.sG1
  have j := enumRun_join j CFSG.KD.M1S.sG2
  have j := enumRun_join j CFSG.KD.M1S.sG3
  have j := enumRun_join j CFSG.KD.M1S.sG4
  have j := enumRun_join j CFSG.KD.M1S.sG5
  have j := enumRun_join j CFSG.KD.M1S.sG6
  have j := enumRun_join j CFSG.KD.M1S.sG7
  have j := enumRun_join j CFSG.KD.M1S.sG8
  have j := enumRun_join j CFSG.KD.M1S.sG9
  have j := enumRun_join j CFSG.KD.M1S.sG10
  have j := enumRun_join j CFSG.KD.M1S.sG11
  have j := enumRun_join j CFSG.KD.M1S.sG12
  have j := enumRun_join j CFSG.KD.M1S.sG13
  have j := enumRun_join j CFSG.KD.M1S.sG14
  have j := enumRun_join j CFSG.KD.M1S.sG15
  have j := enumRun_join j CFSG.KD.M1S.sG16
  have j := enumRun_join j CFSG.KD.M1S.sG17
  have j := enumRun_join j CFSG.KD.M1S.sG18
  have j := enumRun_join j CFSG.KD.M1S.sG19
  have j := enumRun_join j CFSG.KD.M1S.sG20
  have j := enumRun_join j CFSG.KD.M1S.sG21
  have j := enumRun_join j CFSG.KD.M1S.sG22
  have j := enumRun_join j CFSG.KD.M1S.sG23
  have j := enumRun_join j CFSG.KD.M1S.sG24
  have j := enumRun_join j CFSG.KD.M1S.sG25
  have j := enumRun_join j CFSG.KD.M1S.sG26
  have j := enumRun_join j CFSG.KD.M1S.sG27
  have j := enumRun_join j CFSG.KD.M1S.sG28
  have j := enumRun_join j CFSG.KD.M1S.sG29
  have j := enumRun_join j CFSG.KD.M1S.sG30
  have j := enumRun_join j CFSG.KD.M1S.sG31
  have j := enumRun_join j CFSG.KD.M1S.sG32
  have j := enumRun_join j CFSG.KD.M1S.sG33
  have j := enumRun_join j CFSG.KD.M1S.sG34
  have j := enumRun_join j CFSG.KD.M1S.sG35
  have j := enumRun_join j CFSG.KD.M1S.sG36
  have j := enumRun_join j CFSG.KD.M1S.sG37
  have j := enumRun_join j CFSG.KD.M1S.sG38
  have j := enumRun_join j CFSG.KD.M1S.sG39
  have j := enumRun_join j CFSG.KD.M1S.sG40
  have j := enumRun_join j CFSG.KD.M1S.sG41
  have j := enumRun_join j CFSG.KD.M1S.sG42
  have j := enumRun_join j CFSG.KD.M1S.sG43
  have j := enumRun_join j CFSG.KD.M1S.sG44
  have j := enumRun_join j CFSG.KD.M1S.sG45
  have j := enumRun_join j CFSG.KD.M1S.sG46
  have j := enumRun_join j CFSG.KD.M1S.sG47
  have j := enumRun_join j CFSG.KD.M1S.sG48
  have j := enumRun_join j CFSG.KD.M1S.sG49
  have j := enumRun_join j CFSG.KD.M1S.sG50
  have j := enumRun_join j CFSG.KD.M1S.sG51
  have j := enumRun_join j CFSG.KD.M1S.sG52
  have j := enumRun_join j CFSG.KD.M1S.sG53
  have j := enumRun_join j CFSG.KD.M1S.sG54
  have j := enumRun_join j CFSG.KD.M1S.sG55
  have j := enumRun_join j CFSG.KD.M1S.sG56
  have j := enumRun_join j CFSG.KD.M1S.sG57
  have j := enumRun_join j CFSG.KD.M1S.sG58
  have j := enumRun_join j CFSG.KD.M1S.sG59
  have j := enumRun_join j CFSG.KD.M1S.sG60
  have j := enumRun_join j CFSG.KD.M1S.sG61
  have j := enumRun_join j CFSG.KD.M1S.sG62
  have j := enumRun_join j CFSG.KD.M1S.sG63
  have j := enumRun_join j CFSG.KD.M1S.sG64
  have j := enumRun_join j CFSG.KD.M1S.sG65
  have j := enumRun_join j CFSG.KD.M1S.sG66
  have j := enumRun_join j CFSG.KD.M1S.sG67
  have j := enumRun_join j CFSG.KD.M1S.sG68
  have j := enumRun_join j CFSG.KD.M1S.sG69
  have j := enumRun_join j CFSG.KD.M1S.sG70
  have j := enumRun_join j CFSG.KD.M1S.sG71
  have j := enumRun_join j CFSG.KD.M1S.sG72
  have j := enumRun_join j CFSG.KD.M1S.sG73
  have j := enumRun_join j CFSG.KD.M1S.sG74
  have j := enumRun_join j CFSG.KD.M1S.sG75
  have j := enumRun_join j CFSG.KD.M1S.sG76
  have j := enumRun_join j CFSG.KD.M1S.sG77
  have j := enumRun_last j CFSG.KD.M1S.sG78
  exact enumRun_len j (by quickRfl)

theorem mm3_spec : ∀ g < 4, mget CFSG.KD.M1S.MM3 g = g := by decide +kernel

theorem model_faithful (w : List ℕ) (hw : ∀ l ∈ w, l < 2 * 4)
    (hwc : CFSG.Certificates.Co1M.wcodeL CFSG.KD.M1S.MPT CFSG.KD.M1S.MM3 w = idP) :
    (w.map (letV cg3)).prod = 1 :=
  CFSG.Certificates.Co1M.faithful_sound (MM := CFSG.KD.M1S.MM3) (ng := nat_lit 4) (ne := nat_lit 4)
    (by norm_num)
    (fun g hg => by
      change g < 4 at hg
      rw [mm3_spec g hg]
      exact ⟨by omega, by interval_cases g <;> quickRfl⟩)
    (fun r hr q hq => by
      have h : ∀ r < 18, ∀ q < wLen (CFSG.KD.C3.selRT r), wLet (wWord (CFSG.KD.C3.selRT r)) q < 2 * 4 :=
        relsBelow_spec (by quickRfl)
      exact h r hr q hq)
    CFSG.KD.M1S.sM6
    (fun k hk => ⟨k, hk, by
      change k < 4 at hk
      rw [mm3_spec k hk]
      interval_cases k <;> exact Nat.eq_of_beq_eq_true (by quickRfl)⟩)
    (fun g hg => ⟨g, hg, by
      change g < 4 at hg
      rw [mm3_spec g hg]
      interval_cases g <;> exact Nat.eq_of_beq_eq_true (by quickRfl)⟩)
    g4_enum t34_bound cg3 r3 w hw hwc

end CertificateChecks.KernelCo1

end
