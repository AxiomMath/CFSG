module

public import CFSG.RankThree.PartOne.N1322.MonoNormal3
public import CFSG.RankThree.PartOne.N1322.MonoFrameB

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open Equiv

variable {K : Type*} [Field K]

theorem perm_swap_conj : ∀ σ : Perm (Fin 3), σ 0 = 2 →
    σ * swap 0 1 * σ⁻¹ = swap 1 2 ∨ σ⁻¹ * swap 0 1 * σ = swap 1 2 := by decide

theorem exists_aref12 {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X) {r : Kˣ}
    (hr : aref 0 1 r ∈ d.D) : ∃ μ : Kˣ, aref 1 2 μ ∈ d.D := by
  obtain ⟨x, hxX, σ, a, hx, hσ⟩ := hm.trans 0 2
  have hxX' : x⁻¹ ∈ d.X := d.X.inv_mem hxX
  have key : ∀ g ∈ d.D, HasPerm g (swap 1 2) → ∃ μ : Kˣ, aref 1 2 μ ∈ d.D := by
    intro g hg hp
    obtain ⟨b, hb⟩ := hp
    have hrefl := h.refl g hg
    rw [hb] at hrefl hg
    have hbU := isRefl_swap (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
      (by decide) hrefl
    exact ⟨b 1, by rw [aref, ← hbU]; exact hg⟩
  rcases perm_swap_conj σ hσ with hc | hc
  · refine key (x * aref 0 1 r * x⁻¹) (h.Dconj x hxX _ hr) ?_
    have h3 := ((hasPerm_mono σ a).mul (hasPerm_mono (swap 0 1) (aU 0 1 r))).mul
      (hasPerm_mono σ a).inv
    rw [hc] at h3
    rw [hx]
    exact h3
  · refine key (x⁻¹ * aref 0 1 r * x⁻¹⁻¹) (h.Dconj x⁻¹ hxX' _ hr) ?_
    have h3 := ((hasPerm_mono σ a).inv.mul (hasPerm_mono (swap 0 1) (aU 0 1 r))).mul
      (hasPerm_mono σ a).inv.inv
    simp only [inv_inv] at h3
    rw [hc] at h3
    simp only [hx, inv_inv]
    exact h3

theorem cj_diag_eps (dd : Fin 3 → Kˣ) (i : Fin 3) :
    (mono 1 dd : GL (Fin 3) K) * eps i * (mono 1 dd)⁻¹ = eps i := by
  rw [eps, mono_conj_diag]
  refine mono_ext (by simp) (fun j => ?_)
  simp only [Perm.one_apply]
  rw [mul_comm (dd j), mul_inv_cancel_right]

theorem mono_main2 (h2 : (2 : K) ≠ 0) {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X)
    (hc2 : ∃ μ : K, μ ≠ 0 ∧ d.c = μ • Pi.single 2 1)
    (hL2 : ∀ l ∈ d.Lm, ∃ σ a, l = mono σ a ∧ σ 2 = 2 ∧ a 2 = 1) :
    d.n = 4 ∧ Nonempty (d.X ≃* Multiplicative (ZMod 2) × Perm (Fin 4)) := by
  have fb := frame_dichotomy h2 h hm hc2 hL2
  obtain ⟨hn4, ⟨e0D, e0L⟩, ⟨e1D, e1L⟩, r, hrD, hrL, -⟩ := fb
  refine ⟨hn4, ?_⟩
  obtain ⟨x, hxX, σ, a, hx, hσ⟩ := hm.trans 0 2
  have e2D : eps 2 ∈ d.D := by
    have := h.Dconj x hxX _ e0D
    rw [hx, eps_conj, hσ] at this
    exact this
  obtain ⟨μ₀, hμ₀⟩ := exists_aref12 h hm hrD
  obtain ⟨dd, hdd0, hdd1, hdd2⟩ : ∃ dd : Fin 3 → Kˣ, dd 0 = 1 ∧ dd 1 = r⁻¹ ∧ dd 2 = (μ₀ * r)⁻¹ :=
    ⟨fun j => if j = 0 then 1 else if j = 1 then r⁻¹ else (μ₀ * r)⁻¹, by simp, by simp, by simp⟩
  set P : GL (Fin 3) K := mono 1 dd with hP
  have hP' := h.conj P
  have hm' : MonoStd (d.conj P).X := hm.conj 1 dd
  obtain ⟨μ, hμ, hc⟩ := hc2
  have hc2' : ∃ μ' : K, μ' ≠ 0 ∧ (d.conj P).c = μ' • Pi.single 2 1 := by
    refine ⟨μ * (dd 2 : K), mul_ne_zero hμ (dd 2).ne_zero, ?_⟩
    show ((mono 1 dd : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c = _
    rw [hc, Matrix.mulVec_smul, mono_mulVec_single, Perm.one_apply, single_eq_smul, smul_smul]
  have hL2' : ∀ l ∈ (d.conj P).Lm, ∃ σ a, l = mono σ a ∧ σ 2 = 2 ∧ a 2 = 1 := by
    intro l' hl'
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
    obtain ⟨σ, a, rfl, hσ, ha⟩ := hL2 l hl
    refine ⟨σ, fun j => dd (σ j) * a j * (dd j)⁻¹, ?_, hσ, ?_⟩
    · exact mono_conj_diag dd σ a
    · show dd (σ 2) * a 2 * (dd 2)⁻¹ = 1
      rw [hσ, ha, mul_one, mul_inv_cancel]
  have fb' := frame_dichotomy h2 hP' hm' hc2' hL2'
  obtain ⟨-, -, -, r', -, hr'L, hr'⟩ := fb'
  have e0' : eps 0 ∈ (d.conj P).D := ⟨eps 0, e0D, cj_diag_eps dd 0⟩
  have e1' : eps 1 ∈ (d.conj P).D := ⟨eps 1, e1D, cj_diag_eps dd 1⟩
  have e2' : eps 2 ∈ (d.conj P).D := ⟨eps 2, e2D, cj_diag_eps dd 2⟩
  have a01' : aref 0 1 1 ∈ (d.conj P).Lm := by
    refine Subgroup.mem_map.mpr ⟨aref 0 1 r, hrL, ?_⟩
    show (mono 1 dd : GL (Fin 3) K) * aref 0 1 r * (mono 1 dd)⁻¹ = _
    rw [diag_conj_aref (by decide : (0 : Fin 3) ≠ 1), hdd0, hdd1]
    congr 1
    group
  have a12' : aref 1 2 1 ∈ (d.conj P).X := by
    refine Subgroup.mem_map.mpr ⟨aref 1 2 μ₀, ?_, ?_⟩
    · rw [h.gen]; exact Subgroup.subset_closure hμ₀
    · show (mono 1 dd : GL (Fin 3) K) * aref 1 2 μ₀ * (mono 1 dd)⁻¹ = _
      rw [diag_conj_aref (by decide : (1 : Fin 3) ≠ 2), hdd1, hdd2]
      congr 1
      group
  have hL01' : ∀ s : Kˣ, aref 0 1 s ∈ (d.conj P).Lm → s = 1 ∨ s = -1 := by
    intro s hs
    have h1 := hr' 1 a01'
    have hr1 : r' = 1 ∨ r' = -1 := by
      rcases h1 with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr (neg_eq_iff_eq_neg.mp h1.symm)
    rcases hr' s hs with h3 | h3
    · rw [h3]; exact hr1
    · rw [h3]
      rcases hr1 with h4 | h4
      · right; rw [h4]
      · left; rw [h4, neg_neg]
  obtain ⟨e⟩ := mono_normal h2 hP' hm' hc2' e0' e1' e2' a01' a12' hL01'
  exact ⟨((cj P).subgroupMap d.X).trans e⟩

theorem mono_main (h2 : (2 : K) ≠ 0) {d : CoreData K} (h : MonoHyp d) (hm : MonoStd d.X) :
    d.n = 4 ∧ Nonempty (d.X ≃* Multiplicative (ZMod 2) × Perm (Fin 4)) := by
  obtain ⟨P, hP, hmP, hc2, hL2⟩ := exists_relabel h hm
  obtain ⟨hn, e⟩ := mono_main2 h2 hP hmP hc2 hL2
  obtain ⟨e⟩ := e
  exact ⟨hn, ⟨((cj P).subgroupMap d.X).trans e⟩⟩

end CFSG.RankThree.PartOne.N1322
