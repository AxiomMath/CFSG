module

public import Certificates.Kernel.Co1SevenK.Glue
public import Certificates.Kernel.Co1SevenK.BndChk
public import Certificates.Kernel.Co1SevenK.BndLvlB
public import Certificates.Kernel.Co1SevenK.CenB
public import Certificates.Kernel.Co1B.C17330
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1B CFSG.KC.Co1F2
  CFSG.KC.Co1BSpin CFSG.KC.Co1BBoundP CFSG.KC.Co1BBound
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block CFSG.Open
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S Timmesfeld.Co1Seven
open CertificateChecks.KernelCo1B.Bound17591 (XB)

local notation "U" => unpack 24 24


theorem chunksB : ∀ n < 9 * 6,
    lvlChunkP 7 XB BD.TB BD.CFB BD.NPB CertificateChecks.KernelCo1B.CV.F BD.CNB n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 27 with h | h
  · interval_cases n
    exacts [ch13698bB0, ch13698bB1, ch13698bB2, ch13698bB3, ch13698bB4, ch13698bB5, ch13698bB6,
      ch13698bB7, ch13698bB8, ch13698bB9, ch13698bB10, ch13698bB11, ch13698bB12, ch13698bB13,
      ch13698bB14, ch13698bB15, ch13698bB16, ch13698bB17, ch13698bB18, ch13698bB19, ch13698bB20,
      ch13698bB21, ch13698bB22, ch13698bB23, ch13698bB24, ch13698bB25, ch13698bB26]
  · interval_cases n
    exacts [ch13698bB27, ch13698bB28, ch13698bB29, ch13698bB30, ch13698bB31, ch13698bB32,
      ch13698bB33, ch13698bB34, ch13698bB35, ch13698bB36, ch13698bB37, ch13698bB38, ch13698bB39,
      ch13698bB40, ch13698bB41, ch13698bB42, ch13698bB43, ch13698bB44, ch13698bB45, ch13698bB46,
      ch13698bB47, ch13698bB48, ch13698bB49, ch13698bB50, ch13698bB51, ch13698bB52, ch13698bB53]

theorem boundB : boundOK (colsOf (powList (unpackR 24 TK) 7)) 7 BD.baseB BD.condsB BD.cntsB
    BD.spanB BD.combB = true := by
  have hT := kBTB
  rw [Bool.and_eq_true, Nat.beq_eq] at hT
  have hN := kNB
  simp only [Bool.and_eq_true, Nat.beq_eq] at hN
  obtain ⟨⟨⟨⟨⟨hb, hc⟩, hn⟩, -⟩, -⟩, hall⟩ := hN
  rw [cs_of hT.1 (CFSG.KC.Co1BSpin.allN_true' hT.2)]
  refine CertificateChecks.KernelCo1B.Bound17330.boundOK_of_sel (m := 6) hT.1 hb hc hn
    (of_decide_eq_true kCFB) (fun i hi => ?_) chunksB kSpanB
  have h' := CFSG.KC.Co1BSpin.allN_true' hall i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem rep_TK' : MRep (U TK) ((tE : ↥GA) : GL24) := rep_dag iT_lt

theorem card_le_B : Nat.card (Subgroup.centralizer ({tE} : Set ↥GA)) ≤ 1176 := by
  have rk : MRep (unpackR 24 TK) ((tE : ↥GA) : GL24) := by
    rw [unpackR_eq_unpack]
    exact rep_TK'
  have h := card_inf_GA_le_of_powBound rk 7 boundB
  have hp := kNB
  simp only [Bool.and_eq_true, Nat.beq_eq] at hp
  rw [hp.1.2] at h
  rw [card_centralizer_GA_eq_inf]
  exact h

theorem gensB : Inst7.gens instB = [70, 71] := by unfold instB; rfl

theorem rep_GB : ∀ l < 2, MRep (U (GB l)) ((gE ((Inst7.gens instB).getD l 0) : ↥GA) : GL24) := by
  intro l hl
  simp only [GB, gensB]
  interval_cases l <;> exact rep_dag (by decide)

theorem comm_GB : ∀ l < 2,
    gE ((Inst7.gens instB).getD l 0) * tE = tE * gE ((Inst7.gens instB).getD l 0) := by
  have h := kGB
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h
  have hx : Inst7.xi instB = iT := by unfold instB; rfl
  have hb : MRep (U TB) ((tE : ↥GA) : GL24) := by
    unfold TB
    rw [hx]
    exact rep_TK'
  exact comm_of_K h.2 rep_GB hb

theorem comm_70 : gE 70 * tE = tE * gE 70 := by
  have h := comm_GB 0 (by norm_num)
  rwa [gensB] at h

theorem nB : CB.N = 1176 := by
  have h := kTB
  rw [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1

theorem cenB : Nat.card (Subgroup.centralizer ({tE} : Set ↥GA)) = 1176 ∧
    ∃ f : ℕ → ↥GA, (∀ i < 1176, MRep (U (CB.P i)) (f i : GL24) ∧
      f i ∈ Subgroup.centralizer ({tE} : Set ↥GA)) ∧
      ∀ c ∈ Subgroup.centralizer ({tE} : Set ↥GA), ∃ i < 1176, c = f i := by
  have h := kTB
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h
  rw [← nB]
  exact cen_tree h.2 rep_GB comm_GB (by rw [nB]; exact card_le_B)

theorem factsB : Nat.card (Subgroup.centralizer ({tE} : Set ↥GA)) = 1176 ∧
    gE 70 ∈ Subgroup.centralizer ({tE} : Set ↥GA) ∧
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({tE} : Set ↥GA)) = ⊥ := by
  obtain ⟨hcard, f, hf, hall⟩ := cenB
  have hF : closK CB.P 1176 FB.R FB.C FB.W = true := by
    rw [← nB]
    exact kFB
  exact ⟨hcard, (mem_Cen (g := tE)).2 comm_70, bot_tree hf hall hcard qs_B hF⟩

end CertificateChecks.KernelCo1SevenK

end
