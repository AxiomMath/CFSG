module

public import Certificates.Kernel.Co3Pair.Checks
public import CFSG.Certificates.Kernel.B3S3KSound
public import Certificates.Data.Co3PairSize
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.SporSch.PairJ3FaithSound
import CFSG.Certificates.Kernel.RouteP.TextSplit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Pair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K
open CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump CFSG.Sporadic.Schreier.Co3
open CFSG.RankThree.Native

theorem keys_eq : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.keys =
    co3ChainBaseArr.toList := by decide +kernel

theorem hkeys : ∀ p ∈ co3ChainBaseArr.toList, p < 276 := by decide +kernel

theorem utf8ByteSize_ascii : ∀ {l : List Char}, (∀ c ∈ l, c.toNat < 128) →
    (String.ofList l).utf8ByteSize = l.length
  | [], _ => by simp
  | c :: l, hl => by
    have e : String.ofList (c :: l) = String.singleton c ++ String.ofList l := by
      rw [String.singleton_eq_ofList, ← String.ofList_append]
      rfl
    rw [e, String.utf8ByteSize_append, String.utf8ByteSize_singleton,
      utf8ByteSize_ascii (fun d hd => hl d (List.mem_cons_of_mem _ hd)),
      CFSG.KS.RouteP.utf8Size_ascii (hl c List.mem_cons_self), List.length_cons, Nat.add_comm]

theorem size_eq : pumpText.toUTF8.size = 4973 := by
  have ha : PT.chars.all (fun c => decide (c.toNat < 128)) = true := by decide +kernel
  rw [PT.eq, String.toUTF8_eq_toByteArray, String.size_toByteArray,
    utf8ByteSize_ascii (fun c hc => of_decide_eq_true (List.all_eq_true.1 ha c hc))]
  decide +kernel

theorem perm_eq {k : Nat} (hk : k < 6) : pumpPerm k = unpack 276 9 (PTN.L k) := by
  have h := CFSG.KS.Text.hexBind_sound PTN.all k hk
  rw [Nat.zero_add, PTN.chars, String.ofList_append, CFSG.KS.SporSch.PF2.toUTF8_append,
    ← PT.eq] at h
  rw [← h]
  unfold pumpPerm CFSG.Sporadic.Schreier.Co3.Native.hexLine
  apply Array.ext (by simp)
  intro i h1 _
  have hi : i < 276 := by simpa using h1
  simp only [Array.getElem_ofFn]
  rw [CFSG.KS.SporSch.PF2.hexAt_append_left _ _ _ _ (by rw [size_eq]; omega)]

theorem pP {k : Nat} (hk : k < 6) : permB 276 9 (PTN.L k) = true := Orb.allN_iff.1 kPerm k hk

theorem and3 {a b c : Bool} (h : (a && b && c) = true) : a = true ∧ b = true ∧ c = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem eA : Nat.beq EA.ng 2 = true ∧ Nat.beq EA.N 1215 = true ∧
    allN 2 (fun k => Nat.beq (EA.G k) (PTN.L (2 + k))) = true := and3 kEA

theorem eB : Nat.beq EB.ng 2 = true ∧ Nat.beq EB.N 14580 = true ∧
    allN 2 (fun k => Nat.beq (EB.G k) (PTN.L (4 + k))) = true := and3 kEB

theorem bindA : BindA 276 9 (pairGensA ()) EA.ng EA.G := by
  rw [Nat.eq_of_beq_eq_true eA.1]
  refine ⟨by simp [pairGensA], fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eA.2.2 j hj)]
  unfold pairGensA
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact perm_eq (by omega)

theorem bindB : BindA 276 9 (pairGensB ()) EB.ng EB.G := by
  rw [Nat.eq_of_beq_eq_true eB.1]
  refine ⟨by simp [pairGensB], fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eB.2.2 j hj)]
  unfold pairGensB
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact perm_eq (by omega)

theorem pAG : ∀ k < EA.ng, permB 276 9 (EA.G k) = true := by
  intro k hk
  rw [Nat.eq_of_beq_eq_true eA.1] at hk
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eA.2.2 k hk)]
  exact pP (by omega)

theorem pBG : ∀ k < EB.ng, permB 276 9 (EB.G k) = true := by
  intro k hk
  rw [Nat.eq_of_beq_eq_true eB.1] at hk
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eB.2.2 k hk)]
  exact pP (by omega)

theorem pairASize_eq : pairASize () = 1215 := by
  unfold pairASize
  rw [keys_eq, (enum_of bindA pAG EA.ok hkeys kEAkeys
    (by rw [Nat.eq_of_beq_eq_true eA.2.1]; norm_num)).2.1, Nat.eq_of_beq_eq_true eA.2.1]

theorem pairBSize_eq : pairBSize () = 14580 := by
  unfold pairBSize
  rw [keys_eq, (enum_of bindB pBG EB.ok hkeys kEBkeys
    (by rw [Nat.eq_of_beq_eq_true eB.2.1]; norm_num)).2.1, Nat.eq_of_beq_eq_true eB.2.1]

end CertificateChecks.KernelCo3Pair
