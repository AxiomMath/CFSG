module

public import Certificates.Data.E6ThreeTwD4T2Stab
import Certificates.Kernel.E6TwD4T2.Checks
import Certificates.Kernel.E6TwD4T2.Glue

public section

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.KD.E6TwD4T2
  CertificateChecks.KernelE6TwD4T2 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg

namespace Certificates

theorem certificate214103 : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twD4T2StabCheck () = true := by
  have hs := stabK_sound ch214101_planes ch214101_r3 len_check ch214103_stab
  have hlt := elems_lt_check
  have hn := negs_check
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at hlt hn
  unfold twD4T2StabCheck
  simp only [List.all_eq_true, List.mem_range]
  intro k hk e he
  have hm : decodeT Tag.E6.rank e.1 ∈ elems := by
    rw [← elems_eq]
    exact List.mem_map_of_mem (f := fun e : ℕ × ℕ × ℕ => decodeT Tag.E6.rank e.1) he
  obtain ⟨i, hil, hei⟩ := List.getElem_of_mem hm
  rw [← hei]
  rcases hs i hil with hid | hs
  · rw [getElem!_pos elems i hil] at hid
    have hr : List.range Tag.E6.rank = [0, 1, 2, 3, 4, 5] := by decide
    rw [hid, hr]
    simp
  have ht : ∀ j < 6, elems[i].getD j 0 < 72 := hlt _ (List.getElem_mem hil)
  rw [getElem!_pos elems i hil] at hs
  cases hf : twD4T2Fixes (vec3OfIndex (τ := .E6) k) elems[i]
  · simp
  · obtain ⟨p, hp, h0⟩ := hs k hk ((fixes_iff k ht).1 hf)
    have hnp := hn i hil p hp
    obtain ⟨⟨⟨hp72, hpsig⟩, hpos⟩, hneg⟩ := hnp
    have hpos' : twD4T2PosOK (vec3OfIndex (τ := .E6) k) (twD4T2Sig ()) elems[i] = false := by
      rw [sig_eq]
      unfold twD4T2PosOK
      rw [List.all_eq_false]
      refine ⟨p, hpsig, ?_⟩
      have hc : triPairing (vec3OfIndex (τ := .E6) k) (e6Certificate.root p) = 0 := by
        rw [pair_root k hp72, h0, Nat.cast_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some] at hneg
      simp [hc, hpos, not_lt.2 hneg]
    simp [hpos']

end Certificates
