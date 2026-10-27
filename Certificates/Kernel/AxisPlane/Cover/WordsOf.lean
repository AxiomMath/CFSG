module

public import CFSG.Monster.AxisCount.CertData
public import Certificates.Kernel.AxisPlane.Letters
public import Batteries.Data.List.Basic

public section

namespace CertificateChecks.KernelAP.Cover

open CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Cert CFSG.Monster.AxisCount.Native
  CertificateChecks.KernelAP

theorem wordM_getD {ws : List (List Gen)} {mss : List (List (Array Nat))}
    (h : List.Forall₂ WordM ws mss) : ∀ r < ws.length, WordM (ws.getD r []) (mss.getD r []) := by
  induction h with
  | nil =>
    intro r hr
    exact absurd hr (Nat.not_lt_zero r)
  | cons hab _ ih =>
    intro r hr
    cases r with
    | zero => simpa using hab
    | succ r => simpa using ih r (by simpa using hr)

theorem words_of {i : Fin 12} {d : OrbitData} (hd : orbits[i.val]! = d) {rA rB : List Nat}
    {msA msB : List (Array Nat)} {msH : List (List (Array Nat))}
    (hA : WordM d.UA msA) (hB : WordM d.UB msB) (hH : List.Forall₂ WordM d.h.toList msH)
    (hk : (rowsOf msA == rA.toArray && rowsOf msB == rB.toArray &&
      (List.range (nW i)).all fun r => foldRows (msH.getD r []) (lamW i r) == 63) = true) :
    (Cover.wordRows (UA i) == rA.toArray && Cover.wordRows (UB i) == rB.toArray &&
      ((UA i).all Gen.isVis && (UB i).all Gen.isVis && (List.range (nW i)).all fun r =>
        (hW i r).all Gen.isVis && Cover.l2Word (hW i r) (lamW i r) == 63)) = true := by
  have eA : UA i = d.UA := by rw [UA, hd]
  have eB : UB i = d.UB := by rw [UB, hd]
  have eN : nW i = d.h.toList.length := by rw [nW, hd, Array.length_toList]
  have eH : ∀ r < nW i, hW i r = d.h.toList.getD r [] := by
    intro r hr
    rw [eN, Array.length_toList] at hr
    rw [hW, hd, getElem!_pos d.h r hr]
    simp [List.getD_eq_getElem?_getD, hr]
  rw [Bool.and_eq_true, Bool.and_eq_true] at hk
  obtain ⟨⟨hkA, hkB⟩, hkH⟩ := hk
  rw [eA, eB, wordRows_eq hA.1, wordRows_eq hB.1, hA.2, hB.2, hkA, hkB]
  simp only [Bool.true_and]
  rw [List.all_eq_true] at hkH ⊢
  intro r hr
  have hr' := List.mem_range.1 hr
  have hw := wordM_getD hH r (eN ▸ hr')
  rw [eH r hr', hw.2, l2Word_eq hw.1, Bool.true_and]
  exact hkH r hr

end CertificateChecks.KernelAP.Cover

end
