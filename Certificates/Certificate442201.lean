module

public import Certificates.Kernel.HN1408.Bridge442201
import Certificates.Kernel.HN1408.EnumH

public section

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5 CFSG.KD.HN1408

namespace CertificateChecks.Batch442201

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5 CFSG.KD.HN1408

theorem smallPerms_getElem {k : Nat} (hk : k < 6) :
    HNUnitaryBridge.smallPerms[k]! = (HNUnitaryBridge.smallPermLists[k]!).toArray := by
  have hs : k < HNUnitaryBridge.smallPermLists.size := by
    simp only [HNUnitaryBridge.smallPermLists, List.size_toArray, List.length_cons,
      List.length_nil]
    omega
  rw [getElem!_pos HNUnitaryBridge.smallPerms k (by simpa [HNUnitaryBridge.smallPerms] using hs),
    getElem!_pos _ k hs]
  simp [HNUnitaryBridge.smallPerms]

theorem bridgeWordOK_of {w : List Nat} {s : List Nat} (hw : lettersOK w = true)
    (hp : ∀ l ∈ List.range 50, bridgePts[l]! < 1408) (h : brW (WK w) s = true) :
    bridgeWordOK w s.toArray = true := by
  obtain ⟨e, c⟩ := tabW_eq hw
  unfold brW at h
  unfold bridgeWordOK
  simp only [e, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Nat.beq_eq,
    List.getElem!_toArray] at h ⊢
  refine ⟨?_, fun l hl => ?_⟩
  · rw [ap_eq c (by norm_num)]
    exact h.1
  · rw [ap_eq c (hp l hl)]
    exact h.2 l hl

theorem bridge_0 : bridgeOK = true := by
  have hw : (List.range 6).all (fun k => lettersOK bridgeWords[k]!) = true := by decide +kernel
  have hp : (List.range 50).all (fun l => decide (bridgePts[l]! < 1408)) = true := by
    decide +kernel
  have h1 : bridgeWords.all wordOK = true := by decide +kernel
  have h2 : (decide (bridgeWords.length = 6) && decide (bridgePts.length = 50) &&
      decide bridgePts.Nodup && bridgePts.all (fun p => decide (p < 1408))) = true := by
    decide +kernel
  have h3 : (List.range 6).all (fun k =>
      bridgeWordOK bridgeWords[k]! HNUnitaryBridge.smallPerms[k]!) = true := by
    rw [List.all_eq_true]
    intro k hk
    rw [smallPerms_getElem (List.mem_range.1 hk)]
    exact bridgeWordOK_of (List.all_eq_true.1 hw k hk)
      (fun l hl => of_decide_eq_true (List.all_eq_true.1 hp l hl))
      (List.all_eq_true.1 brK_true k hk)
  unfold bridgeOK
  simp only [Bool.and_eq_true] at h2
  rw [gensOK_true, h1, h3, h2.1.1.1, h2.1.1.2, h2.1.2, h2.2]
  rfl

end CertificateChecks.Batch442201

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HNRecog.Simple2S5 in
theorem certificate442201 : bridgeOK = true :=
  CertificateChecks.Batch442201.bridge_0

end Certificates
