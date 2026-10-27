module

public import CFSG.LargeExtraspecial.AS35WQP45W2Data
import Certificates.Certificate2012
import Certificates.Kernel.QP45W.Glue
import Certificates.Kernel.QP45W.W2Checks
import CFSG.Certificates.Kernel.PermCent.CVSound
import Mathlib.Tactic.Group
public import Certificates.Data.Kernel.PermCent.CV

set_option maxRecDepth 100000

namespace Certificates.Kernel.QP45W

open Subgroup CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups.NativeChecks CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.KC.QP45W CFSG.Certificates.Kernel.PkCV CFSG.KC.ONanSmall
  CFSG.LargeExtraspecial.AS35W Certificates.Kernel.ONanSmall

theorem w2_rep {r : CV 45} (hr : r ∈ P43P.reps) :
    ∃ a ∈ centC (elemsC QP45) r, ∃ b ∈ centC (elemsC QP45) r,
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ ¬ (a * b) ^ 3 = 1 := by
  have hc : centC (elemsC QP45) r ∈ P43P.cents := by
    rw [← P43P.cent_ok]
    exact List.mem_map_of_mem hr
  have h := List.all_eq_true.1 ch21297_w2 _ hc
  unfold w2C at h
  obtain ⟨a, ha, h⟩ := List.any_eq_true.1 h
  obtain ⟨b, hb, h⟩ := List.any_eq_true.1 h
  rw [List.mem_filter, powOneC_eq, decide_eq_true_iff] at ha hb
  rw [powOneC_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact ⟨a, ha.1, b, hb.1, ha.2, hb.2, h⟩

theorem conj_cent {g s : Equiv.Perm (Fin 45)} {r c : CV 45} (hg : g ∈ QP45.originalSubgroup)
    (hgr : g * s * g⁻¹ = ev r) (hc : c ∈ centC (elemsC QP45) r) :
    g⁻¹ * ev c * g ∈ QP45.originalSubgroup ∧ g⁻¹ * ev c * g * s = s * (g⁻¹ * ev c * g) := by
  unfold centC at hc
  rw [List.mem_filter, eq22C_eq, decide_eq_true_iff] at hc
  have hcP : ev c ∈ QP45.originalSubgroup := (mem_elemsT QP45 QP45_ok _).1
    (by rw [elemsT_eq_elemsC]; exact List.mem_map_of_mem hc.1)
  refine ⟨mul_mem (mul_mem (inv_mem hg) hcP) hg, ?_⟩
  have hs : s = g⁻¹ * ev r * g := by rw [← hgr]; group
  have hcr : ev c * ev r = ev r * ev c := by rw [← ev_mul, ← ev_mul, hc.2]
  rw [hs]
  calc g⁻¹ * ev c * g * (g⁻¹ * ev r * g) = g⁻¹ * (ev c * ev r) * g := by group
    _ = g⁻¹ * (ev r * ev c) * g := by rw [hcr]
    _ = g⁻¹ * ev r * g * (g⁻¹ * ev c * g) := by group

theorem cube_conj (g : Equiv.Perm (Fin 45)) (c : CV 45) :
    g⁻¹ * ev c * g * (g⁻¹ * ev c * g * (g⁻¹ * ev c * g)) = g⁻¹ * ev (c ^ 3) * g := by
  rw [← ev_pow', pow_succ, pow_succ, pow_one]
  group

theorem cube1_iff (Y : Equiv.Perm (Fin 45)) : cube1A45 (toA Y) = true ↔ Y * (Y * Y) = 1 := by
  unfold cube1A45
  exact eqA_iff (rep_compA (rep_toA Y) (rep_compA (rep_toA Y) (rep_toA Y))) rep_idA

theorem qp45W2Check_true : qp45W2Check () = true := by
  unfold qp45W2Check qp45W2CheckL
  dsimp only
  rewrite [enumA_eq]
  refine List.all_eq_true.2 fun sA hsA => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hsA
  have hsP := (mem_elemsT QP45 QP45_ok s).1 hs
  have hrs := rep_toA s
  rw [Bool.or_eq_true]
  by_cases hinv : s * s = 1 ∧ s ≠ 1
  · right
    obtain ⟨g, hg, r, hr, hgr⟩ := cover hsP hinv.1 hinv.2
    obtain ⟨a, ha, b, hb, ha3, hb3, hab⟩ := w2_rep hr
    obtain ⟨haP, hac⟩ := conj_cent hg hgr ha
    obtain ⟨hbP, hbc⟩ := conj_cent hg hgr hb
    have memC : ∀ c : CV 45, g⁻¹ * ev c * g ∈ QP45.originalSubgroup →
        g⁻¹ * ev c * g * s = s * (g⁻¹ * ev c * g) → c ^ 3 = 1 →
        toA (g⁻¹ * ev c * g) ∈ ((((elemsT QP45).map toA).filter cube1A45).filter fun y =>
          eqA 45 (compA 45 y (toA s)) (compA 45 (toA s) y)) := by
      intro c hcP hcc hc3
      refine List.mem_filter.2 ⟨List.mem_filter.2 ⟨List.mem_map_of_mem
        ((mem_elemsT QP45 QP45_ok _).2 hcP), ?_⟩, ?_⟩
      · rw [cube1_iff, cube_conj, hc3, ev_one]
        group
      · exact (eqA_iff (rep_compA (rep_toA _) hrs) (rep_compA hrs (rep_toA _))).2 hcc
    refine List.any_eq_true.2 ⟨_, memC a haP hac ha3, List.any_eq_true.2 ⟨_, memC b hbP hbc hb3, ?_⟩⟩
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro h
    have hp := rep_compA (rep_toA (g⁻¹ * ev a * g)) (rep_toA (g⁻¹ * ev b * g))
    unfold cube1A45 at h
    rw [eqA_iff (rep_compA hp (rep_compA hp hp)) rep_idA] at h
    have e : g⁻¹ * ev a * g * (g⁻¹ * ev b * g) = g⁻¹ * ev (a * b) * g := by
      rw [ev_mul]
      group
    rw [e, cube_conj] at h
    apply hab
    apply ev_injective
    rw [ev_one]
    calc ev ((a * b) ^ 3) = g * (g⁻¹ * ev ((a * b) ^ 3) * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · left
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro h
    apply hinv
    unfold invA45 at h
    rw [Bool.and_eq_true, eqA_iff (rep_compA hrs hrs) rep_idA, Bool.not_eq_true',
      Bool.eq_false_iff, Ne, eqA_iff hrs rep_idA] at h
    exact h

end Certificates.Kernel.QP45W

public section

namespace Certificates

theorem certificate21297 : CFSG.LargeExtraspecial.AS35W.qp45W2Check () = true :=
  Kernel.QP45W.qp45W2Check_true

end Certificates
