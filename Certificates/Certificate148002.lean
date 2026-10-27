module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148DGenDefs
import Certificates.Kernel.Misc.ON.Base
import Certificates.Kernel.Misc.ON.E27A
import Certificates.Kernel.Misc.ON.E27B

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON CFSG.RankThree.Native.ONTriple CFSG.RankThree.PartTwo.Sec14.Ronan148D

theorem mrep_e27C {j : ℕ} (hj : j < 2) {i : ℕ} (hi : i < 9) :
    MRep (e27C j i) ((e27InitG j).getD i 1) ∧ MRep (e27IC j i) ((e27InitG j).getD i 1)⁻¹ := by
  rw [e27InitG_getD j hi]
  unfold e27C e27IC
  rw [CFSG.KC.Misc.F7.nIf_eq, CFSG.KC.Misc.F7.nIf_eq]
  by_cases h8 : i < 8
  · have hb : Nat.blt i 8 = true := by simp [Nat.blt_eq, h8]
    simp only [hb, if_true, h8]
    have hn := regOKK _ (e27NReg_lt hj h8)
    have hk := regOKK _ (e27KReg_lt i)
    refine ⟨?_, ?_⟩
    · have := mrep_mmul hn.2 (mrep_mmul hk.1 hn.1)
      rwa [← mul_assoc] at this
    · have := mrep_mmul hn.2 (mrep_mmul hk.2 hn.1)
      rwa [← mul_assoc, show (eM (e27NReg j i))⁻¹ * (eM (e27KReg i))⁻¹ * eM (e27NReg j i) =
        ((eM (e27NReg j i))⁻¹ * eM (e27KReg i) * eM (e27NReg j i))⁻¹ by group] at this
  · have hb : Nat.blt i 8 = false := by
      cases h : Nat.blt i 8
      · rfl
      · exact absurd (Nat.blt_eq.mp h) h8
    simp only [hb, h8, Bool.false_eq_true, if_false]
    exact regOKK 7 (by norm_num)

theorem forceL_eq (l : List ℕ) (k : List ℕ → Bool) : forceL l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    change strictB x (fun y => forceL l fun ys => k (y :: ys)) = k (x :: l)
    rw [strictB_eq, ih]

theorem nthN_map_range9 (f : ℕ → ℕ) {i : ℕ} (hi : i < 9) :
    nthN ((List.range 9).map f) i = f i := by
  rw [nthN_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem e27Word_lt : ∀ j < 2, ∀ k < 7, ∀ l ∈ e27Word j k, l.1 < 9 := by decide +kernel

theorem wordG_e27_of {j : ℕ} (hj : j < 2) (hc : e27ChkM j = true) (k : Fin 7) :
    wordG (e27InitG j) (e27Word j k) = gM k.castSucc := by
  have h := hc
  rw [e27ChkM, forceL_eq, forceL_eq, CFSG.KC.Misc.F7.allN_iff] at h
  have hw := mrep_wordC (F := nthN ((List.range 9).map (e27C j)))
    (FI := nthN ((List.range 9).map (e27IC j))) (R := e27InitG j) (e27Word j k) fun l hl => by
      have hl9 := e27Word_lt j hj k k.isLt l hl
      rw [nthN_map_range9 _ hl9, nthN_map_range9 _ hl9]
      exact mrep_e27C hj hl9
  exact mrep_eq hw (chkGensM_spec gensB k.castSucc).1.1 (h k k.isLt)

open CFSG.RankThree.PartTwo.Sec14.Ronan148D CFSG.RankThree.Native.ONTriple in
theorem certificate148002 : ∀ j < 2, ∀ k : Fin 7, wordG (e27InitG j) (e27Word j k) = gM k.castSucc := by
  intro j hj
  interval_cases j
  · exact wordG_e27_of (by norm_num) e27Chk0
  · exact wordG_e27_of (by norm_num) e27Chk1

end Certificates
