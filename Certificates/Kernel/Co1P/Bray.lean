module

public import Certificates.Kernel.Co1P.DagGlue

public section

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1Patterson.Native

theorem treeT_eq (ms : List Nat) : treeT ms = treeArr (recsT ms) := by
  rw [treeT, treeOfMasks_eq]
  rfl

theorem brayTree_parts {ms : List Nat} (h : brayTreeOK ms = true) :
    (CFSG.KC.TreeK.treePts (hsAct BK) 8 oneK (recsT ms)).2 = true ∧
      (CFSG.KC.TreeK.treePts (hisAct BIK) 8 oneK (recsT ms)).2 = true :=
  CFSG.KC.TreeK.andB_true h

theorem bray_hs {ms : List Nat} (h : brayTreeOK ms = true) (R : Nat) {j : Nat}
    (hj : j < (recsT ms).length + 1) :
    (mkOrbT brayArr brayInvArr (unpackR 24 R) (treeT ms)).hs[j]! = unpackR 24 (hsW ms j) := by
  rw [treeT_eq]
  exact mkOrbT_hs (Gi := brayInvArr) (fun l hl => brayArr_get hl) (brayTree_parts h).1 hj

theorem bray_his {ms : List Nat} (h : brayTreeOK ms = true) (R : Nat) {j : Nat}
    (hj : j < (recsT ms).length + 1) :
    (mkOrbT brayArr brayInvArr (unpackR 24 R) (treeT ms)).his[j]! = unpackR 24 (hisW ms j) := by
  rw [treeT_eq]
  exact mkOrbT_his (G := brayArr) (fun l hl => brayInvArr_get hl) (brayTree_parts h).2 hj

theorem bray_pts {ms : List Nat} (h : brayTreeOK ms = true) (R : Nat) {j : Nat}
    (hj : j < (recsT ms).length + 1) :
    (mkOrbT brayArr brayInvArr (unpackR 24 R) (treeT ms)).c.pts[j]! =
      unpackR 24 (mulWK (mulWK (hsW ms j) R) (hisW ms j)) := by
  rw [treeT_eq]
  exact mkOrbT_pts (fun l hl => brayArr_get hl) (fun l hl => brayInvArr_get hl)
    (brayTree_parts h).1 (brayTree_parts h).2 hj

theorem orbQ_eq : orbQ = mkOrbT brayArr brayInvArr (unpackR 24 (repK 0)) (treeT orbQMasks) := by
  rw [orbQ, repRows_eq]

theorem orbE_eq : orbE = mkOrbT brayArr brayInvArr (unpackR 24 (repK 1)) (treeT orbEMasks) := by
  rw [orbE, repRows_eq]

end CertificateChecks.KernelCo1P

end
