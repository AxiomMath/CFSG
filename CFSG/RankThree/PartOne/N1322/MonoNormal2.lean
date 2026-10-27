module

public import CFSG.RankThree.PartOne.N1322.MonoNormal
public import CFSG.RankThree.PartOne.N1322.MonoFrame

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open Equiv

variable {K : Type*} [Field K]

theorem aU_pm {r : Kˣ} (hr : r = 1 ∨ r = -1) (i j : Fin 3) :
    ∀ m, aU i j r m = 1 ∨ aU i j r m = -1 := by
  intro m
  unfold aU
  split_ifs
  · exact hr
  · exact pm_inv hr
  · exact Or.inl rfl

theorem D_subset_wb3 (h2 : (2 : K) ≠ 0) {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X)
    (hc2 : ∃ μ : K, μ ≠ 0 ∧ d.c = μ • Pi.single 2 1)
    (a01 : aref 0 1 1 ∈ d.Lm) (a12 : aref 1 2 1 ∈ d.X)
    (hL01 : ∀ s : Kˣ, aref 0 1 s ∈ d.Lm → s = 1 ∨ s = -1) :
    ∀ g ∈ d.D, g ∈ wb3 K := by
  obtain ⟨μ, hμ, hc⟩ := hc2
  have hp01 : permMono (swap 0 1) ∈ d.X := by
    have : (permMono (swap 0 1) : GL (Fin 3) K) = aref 0 1 1 := by
      show mono (swap 0 1) (fun _ => 1) = mono (swap 0 1) (aU 0 1 1)
      rw [aU_one]
    rw [this]; exact h.Lle a01
  have hp12 : permMono (swap 1 2) ∈ d.X := by
    have : (permMono (swap 1 2) : GL (Fin 3) K) = aref 1 2 1 := by
      show mono (swap 1 2) (fun _ => 1) = mono (swap 1 2) (aU 1 2 1)
      rw [aU_one]
    rw [this]; exact a12
  have hperm := permMono_mem hp01 hp12
  have hdiagstab : ∀ dd : Fin 3 → Kˣ, ∃ μ' : K,
      ((mono 1 dd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c = μ' • d.c := by
    intro dd
    refine ⟨(dd 2 : K), ?_⟩
    rw [hc, Matrix.mulVec_smul, mono_mulVec_single, Perm.one_apply, single_eq_smul, smul_comm]
  have hN01 : ∀ dd : Fin 3 → Kˣ, (mono 1 dd : GL (Fin 3) K) ∈ d.X →
      (dd 1 * (dd 0)⁻¹ = 1 ∨ dd 1 * (dd 0)⁻¹ = -1) := by
    intro dd hdd
    have h3 := h.N _ hdd (hdiagstab dd) _ a01
    rw [diag_conj_aref (by decide : (0 : Fin 3) ≠ 1)] at h3
    have h4 := hL01 _ h3
    simpa using h4
  have hXD : ∀ g ∈ d.D, g ∈ d.X := fun g hg => by
    rw [h.gen]; exact Subgroup.subset_closure hg
  have h02 : ∀ r : Kˣ, aref 0 2 r ∈ d.D → r = 1 ∨ r = -1 := by
    intro r hr
    have hrX := hXD _ hr
    have hp02 : aref 0 2 (1 : Kˣ) ∈ d.X := by
      have : aref 0 2 (1 : Kˣ) = permMono (swap 0 2) := by
        show mono (swap 0 2) (aU 0 2 1) = mono (swap 0 2) (fun _ => 1)
        rw [aU_one]
      rw [this]; exact hperm _
    have hdd : (mono 1 (aU 0 2 (r⁻¹ * 1)) : GL (Fin 3) K) ∈ d.X := by
      rw [← aref_mul_aref (by decide : (0 : Fin 3) ≠ 2) r 1]
      exact d.X.mul_mem hrX hp02
    have h3 := hN01 _ hdd
    have e1 : aU 0 2 (r⁻¹ * 1) 1 = 1 := aU_other (by decide) (by decide) _
    have e0 : aU 0 2 (r⁻¹ * 1) 0 = r⁻¹ * 1 := aU_left _
    rw [e1, e0] at h3
    simpa using h3
  have h12 : ∀ r : Kˣ, aref 1 2 r ∈ d.D → r = 1 ∨ r = -1 := by
    intro r hr
    have hrX := hXD _ hr
    have hdd : (mono 1 (aU 1 2 (r⁻¹ * 1)) : GL (Fin 3) K) ∈ d.X := by
      rw [← aref_mul_aref (by decide : (1 : Fin 3) ≠ 2) r 1]
      exact d.X.mul_mem hrX a12
    have h3 := hN01 _ hdd
    have e1 : aU 1 2 (r⁻¹ * 1) 1 = r⁻¹ * 1 := aU_left _
    have e0 : aU 1 2 (r⁻¹ * 1) 0 = 1 := aU_other (by decide) (by decide) _
    rw [e1, e0] at h3
    have h4 : r⁻¹ = 1 ∨ r⁻¹ = -1 := by simpa using h3
    simpa using pm_inv h4
  have h01 : ∀ r : Kˣ, aref 0 1 r ∈ d.D → r = 1 ∨ r = -1 := by
    intro r hr
    have hw := hperm (swap 1 2)
    have h3 := h.Dconj _ hw _ hr
    have e : (permMono (swap 1 2) : GL (Fin 3) K) * aref 0 1 r * (permMono (swap 1 2))⁻¹ =
        aref 0 2 r := by
      show (mono (swap 1 2) (fun _ => 1) : GL (Fin 3) K) * mono (swap 0 1) (aU 0 1 r) *
        (mono (swap 1 2) (fun _ => 1))⁻¹ = mono (swap 0 2) (aU 0 2 r)
      rw [mono_conj_perm]
      refine mono_ext (by decide) (fun j => ?_)
      fin_cases j
      · simp [aU, swap_apply_def]
      · simp [aU]
      · simp [aU]
    rw [e] at h3
    exact h02 r h3
  intro g hg
  obtain ⟨σ, a, rfl⟩ := hm.isMono g (hXD g hg)
  rcases isRefl_mono_cases' h2 (h.refl _ hg) with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩
  · refine mem_wb3_iff.mpr ⟨1, a, rfl, fun j => ?_⟩
    rcases ha with rfl | rfl | rfl <;> (unfold epsU; split_ifs <;> simp)
  · have hr := h01 (a 0) (by rw [aref, ← ha]; exact hg)
    exact mem_wb3_iff.mpr ⟨swap 0 1, a, rfl, by rw [ha]; exact aU_pm hr 0 1⟩
  · have hr := h02 (a 0) (by rw [aref, ← ha]; exact hg)
    exact mem_wb3_iff.mpr ⟨swap 0 2, a, rfl, by rw [ha]; exact aU_pm hr 0 2⟩
  · have hr := h12 (a 1) (by rw [aref, ← ha]; exact hg)
    exact mem_wb3_iff.mpr ⟨swap 1 2, a, rfl, by rw [ha]; exact aU_pm hr 1 2⟩

end CFSG.RankThree.PartOne.N1322
