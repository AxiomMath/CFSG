module

public import Certificates.Kernel.Co1SevenK.Glue
public import Certificates.Kernel.Co1SevenK.BndChk
public import Certificates.Kernel.Co1SevenK.BndLvlA
public import Certificates.Kernel.Co1SevenK.CenA
public import Certificates.Kernel.Co1SevenK.CenAF
public import Certificates.Kernel.Co1SevenK.CenAZ
public import Certificates.Kernel.Co1B.C17330
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1BSpin
  CFSG.KC.Co1BBoundP CFSG.KC.Co1BBound
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block CFSG.Open
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S Timmesfeld.Co1Seven
open CertificateChecks.KernelCo1B.Bound17591 (XB)

local notation "U" => unpack 24 24


theorem chunksA : ∀ n < 9 * 4,
    lvlChunkP 7 XB BD.TA BD.CFA BD.NPA CertificateChecks.KernelCo1B.CV.F BD.CNA n = true := by
  intro n hn
  interval_cases n
  exacts [ch13697bA0, ch13697bA1, ch13697bA2, ch13697bA3, ch13697bA4, ch13697bA5, ch13697bA6,
    ch13697bA7, ch13697bA8, ch13697bA9, ch13697bA10, ch13697bA11, ch13697bA12, ch13697bA13,
    ch13697bA14, ch13697bA15, ch13697bA16, ch13697bA17, ch13697bA18, ch13697bA19, ch13697bA20,
    ch13697bA21, ch13697bA22, ch13697bA23, ch13697bA24, ch13697bA25, ch13697bA26, ch13697bA27,
    ch13697bA28, ch13697bA29, ch13697bA30, ch13697bA31, ch13697bA32, ch13697bA33, ch13697bA34,
    ch13697bA35]

theorem boundA : boundOK (colsOf (powList (unpackR 24 SK) 7)) 7 BD.baseA BD.condsA BD.cntsA
    BD.spanA BD.combA = true := by
  have hT := kBTA
  rw [Bool.and_eq_true, Nat.beq_eq] at hT
  have hN := kNA
  simp only [Bool.and_eq_true, Nat.beq_eq] at hN
  obtain ⟨⟨⟨⟨⟨hb, hc⟩, hn⟩, -⟩, -⟩, hall⟩ := hN
  rw [cs_of hT.1 (CFSG.KC.Co1BSpin.allN_true' hT.2)]
  refine CertificateChecks.KernelCo1B.Bound17330.boundOK_of_sel (m := 4) hT.1 hb hc hn
    (of_decide_eq_true kCFA) (fun i hi => ?_) chunksA kSpanA
  have h' := CFSG.KC.Co1BSpin.allN_true' hall i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem rep_SK : MRep (U SK) ((sE : ↥GA) : GL24) := rep_dag iS_lt

theorem rep_TK : MRep (U TK) ((tE : ↥GA) : GL24) := rep_dag iT_lt

theorem card_le_A : Nat.card (Subgroup.centralizer ({sE} : Set ↥GA)) ≤ 17640 := by
  have rk : MRep (unpackR 24 SK) ((sE : ↥GA) : GL24) := by
    rw [unpackR_eq_unpack]
    exact rep_SK
  have h := card_inf_GA_le_of_powBound rk 7 boundA
  have hp := kNA
  simp only [Bool.and_eq_true, Nat.beq_eq] at hp
  rw [hp.1.2] at h
  rw [card_centralizer_GA_eq_inf]
  exact h

theorem gensA : Inst7.gens instA = [68, 69] := by unfold instA; rfl

theorem rep_GA' : ∀ l < 2, MRep (U (GA' l)) ((gE ((Inst7.gens instA).getD l 0) : ↥GA) : GL24) := by
  intro l hl
  simp only [GA', gensA]
  interval_cases l <;> exact rep_dag (by decide)

theorem comm_GA' : ∀ l < 2, gE ((Inst7.gens instA).getD l 0) * sE = sE * gE ((Inst7.gens instA).getD l 0) := by
  have h := kGA
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h
  have hx : Inst7.xi instA = iS := by unfold instA; rfl
  have hb : MRep (U BA) ((sE : ↥GA) : GL24) := by
    unfold BA
    rw [hx]
    exact rep_SK
  exact comm_of_K h.2 rep_GA' hb

theorem comm_68 : gE 68 * sE = sE * gE 68 := by
  have h := comm_GA' 0 (by norm_num)
  rwa [gensA] at h

theorem comm_69 : gE 69 * sE = sE * gE 69 := by
  have h := comm_GA' 1 (by norm_num)
  rwa [gensA] at h

theorem nA : CA.N = 17640 := by
  have h := kTA
  rw [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1

theorem cenA : Nat.card (Subgroup.centralizer ({sE} : Set ↥GA)) = 17640 ∧
    ∃ f : ℕ → ↥GA, (∀ i < 17640, MRep (U (CA.P i)) (f i : GL24) ∧
      f i ∈ Subgroup.centralizer ({sE} : Set ↥GA)) ∧
      ∀ c ∈ Subgroup.centralizer ({sE} : Set ↥GA), ∃ i < 17640, c = f i := by
  have h := kTA
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h
  rw [← nA]
  exact cen_tree h.2 rep_GA' comm_GA' (by rw [nA]; exact card_le_A)

theorem qs_17640 (q : ℕ) (hq : q.Prime) (hd : q ∣ 17640) (h7 : q ≠ 7) : q ∈ qsList :=
  qs_A q hq hd h7

theorem factsA : Nat.card (Subgroup.centralizer ({sE} : Set ↥GA)) = 17640 ∧
    gE 68 ∈ Subgroup.centralizer ({sE} : Set ↥GA) ∧
    gE 69 ∈ Subgroup.centralizer ({sE} : Set ↥GA) ∧
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({sE} : Set ↥GA)) = ⊥ ∧
    ∀ c ∈ Subgroup.centralizer ({sE} : Set ↥GA), c * tE = tE * c → c ^ 7 = 1 := by
  obtain ⟨hcard, f, hf, hall⟩ := cenA
  have hF : closK CA.P 17640 FA.R FA.C FA.W = true := by
    rw [← nA]
    exact kFA
  have hZ : centK CA.P 17640 (D.M iT) = true := by
    rw [← nA]
    exact kZA
  exact ⟨hcard, (mem_Cen (g := sE)).2 comm_68, (mem_Cen (g := sE)).2 comm_69,
    bot_tree hf hall hcard qs_17640 hF, cent_tree hf hall rep_TK hZ⟩

end CertificateChecks.KernelCo1SevenK

end
