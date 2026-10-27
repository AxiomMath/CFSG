module

public import CFSG.Monster.B.Fischer.InducedChecks
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.Fischer.InducedChecks
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.Fischer.InducedOrbitChecksInputs
public import Certificates.Certificate3035
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.TwoA.Census

theorem indAB_eq : ∀ g < 2, indAB g = indM22Gen g := by
  intro g hg
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · simp only [indAB, ↓reduceIte, indA]
  · simp only [indAB, one_ne_zero, ↓reduceIte, indB]

theorem wCert_ok : ∀ s ∈ [0, 1, 3, 7],
    natCertOK linW 2 (fun u => decide (u < 1024)) s (wCert s) = true :=
  Certificates.certificate3035.1

theorem wCert_size :
    (wCert 0).pts.size = 1 ∧ (wCert 1).pts.size = 22 ∧
    (wCert 3).pts.size = 231 ∧ (wCert 7).pts.size = 770 :=
  Certificates.certificate3035.2.1

theorem wCert_sorted :
    ((wCert 0).pts.toList ++ (wCert 1).pts.toList ++ (wCert 3).pts.toList ++
    (wCert 7).pts.toList).mergeSort (fun a b => decide (a ≤ b)) = List.range 1024 :=
  Certificates.certificate3035.2.2.1

theorem wCert_cover : ∀ u < 1024, u ∈ (wCert 0).pts.toList ∨ u ∈
    (wCert 1).pts.toList ∨
    u ∈ (wCert 3).pts.toList ∨ u ∈ (wCert 7).pts.toList := by
  intro u hu
  have h : u ∈ (wCert 0).pts.toList ++ (wCert 1).pts.toList ++ (wCert 3).pts.toList ++
      (wCert 7).pts.toList := by
    rw [← (List.mergeSort_perm _ (fun a b => decide (a ≤ b))).mem_iff, wCert_sorted]
    exact List.mem_range.2 hu
  simp only [List.mem_append] at h
  tauto

theorem zCert_ok : ∀ s ∈ [0, 24, 1],
    natCertOK zAct 2 (fun n => decide (n < 2464)) s (zCert s) = true :=
  Certificates.certificate3035.2.2.2.1

theorem zCert_size :
    (zCert 0).pts.size = 462 ∧ (zCert 24).pts.size = 770 ∧
    (zCert 1).pts.size = 1232 :=
  Certificates.certificate3035.2.2.2.2.1

theorem zCert_sorted :
    ((zCert 0).pts.toList ++ (zCert 24).pts.toList ++
    (zCert 1).pts.toList).mergeSort (fun a b => decide (a ≤ b)) = List.range 2464 :=
  Certificates.certificate3035.2.2.2.2.2.1

theorem zCert_cover : ∀ n < 2464, n ∈ (zCert 0).pts.toList ∨ n ∈
    (zCert 24).pts.toList ∨
    n ∈ (zCert 1).pts.toList := by
  intro n hn
  have h : n ∈ (zCert 0).pts.toList ++ (zCert 24).pts.toList ++ (zCert 1).pts.toList := by
    rw [← (List.mergeSort_perm _ (fun a b => decide (a ≤ b))).mem_iff, zCert_sorted]
    exact List.mem_range.2 hn
  simp only [List.mem_append] at h
  tauto

theorem zAct_range : ∀ g < 2, ∀ n < 2464,
    1046 ≤ (indAB g)[1046 + n]! ∧ (indAB g)[1046 + n]! < 3510 :=
  Certificates.certificate3035.2.2.2.2.2.2.1

theorem sArrs_get : ∀ k < 4, sArrs[k]! = wordArr (sWord k) := by
  intro k hk
  rw [sArrs, getElem!_pos _ _ (by simp [hk])]
  simp

theorem s2Arrs_get : ∀ k < 3, s2Arrs[k]! = wordArr (s2Word k) := by
  intro k hk
  rw [s2Arrs, getElem!_pos _ _ (by simp [hk])]
  simp

theorem sWord_letters : ∀ k < 4, ∀ z ∈ sWord k, z = 1 ∨ z = 2 := by decide +kernel

theorem s2Word_letters : ∀ k < 3, ∀ z ∈ s2Word k, z = 1 ∨ z = 2 := by decide +kernel

theorem sFix : ∀ k < 4, (sArrs[k]!)[22 + 7]! = 22 + 7 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.1

theorem sFix_W : ∀ u ∈ (wCert 7).pts.toList,
    (∀ k < 4, (sArrs[k]!)[22 + u]! = 22 + u) → u = 7 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.1

theorem sFix_Z : ∀ n ∈ (zCert 24).pts.toList,
    (∀ k < 4, (sArrs[k]!)[1046 + n]! = 1046 + n) → n = 24 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.1

theorem s2Fix : ∀ k < 3, (s2Arrs[k]!)[1046 + 1]! = 1046 + 1 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.1

theorem s2Fix_Z : ∀ n ∈ (zCert 1).pts.toList,
    (∀ k < 3, (s2Arrs[k]!)[1046 + n]! = 1046 + n) → n = 1 ∨ n = 277 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.1

theorem sArrs_size : ∀ k < 4, (sArrs[k]!).size = 3510 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem s2Arrs_size : ∀ k < 3, (s2Arrs[k]!).size = 3510 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem indSigma_spec :
    ∀ p ∈ indSigma, p.1 ∈ (wCert 7).pts.toList ∧ sigmaFun p.1 = p.2 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem indTau_spec :
    ∀ p ∈ indTau, p.1 ∈ (zCert 1).pts.toList ∧ tauFun p.1 = p.2 :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sigma_check : sigmaFun 7 = 24 ∧ (∀ u ∈ (wCert 7).pts.toList,
    sigmaFun u ∈ (zCert 24).pts.toList ∧ ∀ g < 2, sigmaFun (linW g u) = zAct g (sigmaFun u)) ∧
    ∀ u ∈ (wCert 7).pts.toList, ∀ u' ∈ (wCert 7).pts.toList,
      sigmaFun u = sigmaFun u' → u = u' :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tau_check : tauFun 1 = 277 ∧ ∀ n ∈ (zCert 1).pts.toList,
    tauFun n ∈ (zCert 1).pts.toList ∧ tauFun (tauFun n) = n ∧ tauFun n ≠ n ∧
      ∀ g < 2, tauFun (zAct g n) = zAct g (tauFun n) :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem indSigma_graph :
    ∀ u ∈ (wCert 7).pts.toList, (u, sigmaFun u) ∈ indSigma :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem indTau_graph :
    ∀ n ∈ (zCert 1).pts.toList, (n, tauFun n) ∈ indTau :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hexMask_lt : ∀ i < 76,
    hexMask ((hexCat (hCat i)).map jEmb) < hexMask ((hexCat (hCat (i + 1))).map jEmb) :=
  Certificates.certificate3035.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Monster.B.Fischer
