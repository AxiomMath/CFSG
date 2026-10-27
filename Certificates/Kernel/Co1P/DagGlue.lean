module

public import Certificates.Kernel.Co1P.Dag
public import Certificates.Kernel.Co1B.Twist
public import CFSG.Certificates.Kernel.Co1PSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KD.Co1B CFSG.KD.Co1P CFSG.KC.Co1P CertificateChecks.KernelCo1B
  CertificateChecks.KernelCo1Cover CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native

theorem BRS_len : BRS59.length = 35 := rfl

theorem GDS_len : GDS.length = 190 := rfl

theorem GDIS_len : GDIS.length = 190 := rfl

theorem bray_dag : CFSG.Sporadic.Co1Block.Native.brayRows CFSG.Sporadic.Co1Block.iotaARows
    CFSG.Sporadic.Co1Block.twoAD1 = (BRS59.map (unpackR 24), BRIS59.map (unpackR 24), true) := by
  rw [CFSG.Sporadic.Co1Block.Native.brayRows, aR_eq, bR_eq, iotaA_eq]
  exact dag_sound bray_chk

theorem brayG_eq : brayG = BK.map (unpackR 24) := by
  rw [brayG, CFSG.Sporadic.Co1Block.Native.brayElts, bray_dag, BK, List.map_map]
  apply List.map_congr_left
  intro j _
  rw [Function.comp_apply, ← KernelCo1B.one_eq]
  exact getD_map_u oneK BRS59 (j - 1)

theorem gBase_eq : gBase = gBaseK.map (unpackR 24) := by
  have hq : CFSG.Sporadic.Co1Block.twoAQRows = IQK.map (unpackR 24) := twoAQ_eq
  rw [gBase, aR_eq, bR_eq, iotaA_eq, hq, brayG_eq, gBaseK, List.map_append, List.map_append]
  rfl

theorem gWords_eq : gWords = GWL := by
  rw [gWords, gwords_text]
  exact parseWords_wordsC (by decide)

theorem gDag_eq : gDag = (GDS.map (unpackR 24), GDIS.map (unpackR 24), true) := by
  rw [gDag, gBase_eq, gWords_eq]
  exact dag_sound gdag_chk

theorem gEl_eq (j : Nat) : gEl j = unpackR 24 (getL oneK GDS (j - 1)) := by
  rw [gEl, gDag_eq, ← KernelCo1B.one_eq]
  exact getD_map_u oneK GDS (j - 1)

theorem gElInv_eq (j : Nat) : gElInv j = unpackR 24 (getL oneK GDIS (j - 1)) := by
  have h := dag_snd gBase gWords
  rw [← gDag, gDag_eq] at h
  rw [gElInv, gEl_eq, ← getD_map_u, ← getD_map_u, KernelCo1B.one_eq]
  by_cases hk : j - 1 < 190
  · have h1 : ((GDS.map (unpackR 24)).map inv).getD (j - 1) one =
        inv ((GDS.map (unpackR 24)).getD (j - 1) one) := by
      rw [List.getD_eq_getElem _ _ (by simpa [GDS_len] using hk),
        List.getD_eq_getElem _ _ (by simpa [GDS_len] using hk), List.getElem_map]
    rw [← h1]
    exact congrArg (fun l => l.getD (j - 1) one) h.symm
  · rw [List.getD_eq_default _ _ (by simpa [GDS_len] using hk),
      List.getD_eq_default _ _ (by simpa [GDIS_len] using hk), inv_one']

theorem iotaA_K : CFSG.Sporadic.Co1Block.iotaARows = unpackR 24 AL := iotaA_eq

theorem repX_eq (i : Nat) : repX i = unpackR 24 (repXK i) := gEl_eq _

theorem repXi_eq (i : Nat) : repXi i = unpackR 24 (repXiK i) := gElInv_eq _

theorem repRows_eq (i : Nat) : repRows i = unpackR 24 (repK i) := by
  rw [repRows, conjA, repX_eq, repXi_eq, iotaA_eq, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
  rfl

theorem BK_len : BK.length = 8 := rfl

theorem brayArr_get {l : Nat} (hl : l < 8) : brayArr[l]! = unpackR 24 (getL 0 BK l) := by
  rw [brayArr, brayG_eq, getElem!_pos _ l (by simpa [BK_len] using hl), List.getElem_toArray,
    List.getElem_map, CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [BK_len]; exact hl)]
  rfl

theorem brayArr_size : brayArr.size = 8 := by simp [brayArr, brayG_eq, BK_len]

theorem inv_BK {l : Nat} (hl : l < 8) : inv (unpackR 24 (getL 0 BK l)) = unpackR 24 (getL 0 BIK l) := by
  obtain ⟨-, hinv⟩ := invsK_sound _ _ (andB_true (andB_true bray_chk).2).1
  have h0 : getL 0 BK l = getL oneK BRS59 (CFSG.Sporadic.Co1Block.twoABray.getD l 0 - 1) := by
    interval_cases l <;> rfl
  have h1 : getL 0 BIK l = getL oneK BRIS59 (CFSG.Sporadic.Co1Block.twoABray.getD l 0 - 1) := by
    interval_cases l <;> rfl
  have hj : CFSG.Sporadic.Co1Block.twoABray.getD l 0 - 1 < 35 := by interval_cases l <;> decide
  rw [h0, h1]
  apply inv_sound'
  have := hinv _ (by rw [BRS_len]; exact hj) (by rw [show BRIS59.length = 35 from rfl]; exact hj)
  rwa [CFSG.KC.Co1B.getL_eq, CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem, List.getElem?_eq_getElem]

theorem brayInvArr_get {l : Nat} (hl : l < 8) : brayInvArr[l]! = unpackR 24 (getL 0 BIK l) := by
  have hs : l < brayArr.size := by rw [brayArr_size]; exact hl
  rw [brayInvArr, getElem!_pos _ l (by simpa using hs), Array.getElem_map, ← getElem!_pos _ l hs,
    brayArr_get hl, inv_BK hl]

end CertificateChecks.KernelCo1P

end
