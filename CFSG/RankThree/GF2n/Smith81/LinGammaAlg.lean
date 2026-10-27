module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import CFSG.RankThree.GF2n.DihedralCompl

public section

namespace CFSG.RankThree.GF2n.Smith81.LinGamma

open Module

section Lin

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem B_symm (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0) (halt : ∀ e, B e e = 0)
    (a b : E) : B a b = B b a := by
  have h := halt (a + b)
  simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
  linear_combination h - B b a * hK2

theorem nondeg_of (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0) (halt : ∀ e, B e e = 0)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) : B.Nondegenerate :=
  ⟨hnd, fun e he => hnd e fun f => by rw [B_symm B hK2 halt]; exact he f⟩

theorem two_mul_finrank_le_of_iso (B : LinearMap.BilinForm K E) (hK2 : (2 : K) = 0)
    (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (W : Submodule K E)
    (hW : ∀ u ∈ W, ∀ v ∈ W, B u v = 0) : 2 * finrank K W ≤ finrank K E := by
  have hle : W ≤ B.orthogonal W := fun v hv =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => hW u hu v hv
  have h1 := LinearMap.BilinForm.finrank_orthogonal (nondeg_of B hK2 halt hnd) W
  have h2 := Submodule.finrank_mono hle
  have h3 := Submodule.finrank_le W
  omega

theorem range_eq_sup_map (N : E →ₗ[K] E) (W₁ W₂ : Submodule K E) (hW : IsCompl W₁ W₂) :
    LinearMap.range N = W₁.map N ⊔ W₂.map N := by
  rw [← Submodule.map_top, ← hW.sup_eq_top, Submodule.map_sup]

theorem finrank_range_of_isCompl (N : E →ₗ[K] E) (W₁ W₂ : Submodule K E) (hW : IsCompl W₁ W₂)
    (h₁ : ∀ w ∈ W₁, N w ∈ W₁) (h₂ : ∀ w ∈ W₂, N w ∈ W₂) {m : ℕ}
    (hm₁ : finrank K (W₁.map N) = m) (hm₂ : finrank K (W₂.map N) = m) :
    finrank K (LinearMap.range N) = 2 * m := by
  have hle₁ : W₁.map N ≤ W₁ := by
    rintro _ ⟨w, hw, rfl⟩
    exact h₁ w hw
  have hle₂ : W₂.map N ≤ W₂ := by
    rintro _ ⟨w, hw, rfl⟩
    exact h₂ w hw
  have hdisj : W₁.map N ⊓ W₂.map N = ⊥ := by
    refine le_bot_iff.mp ?_
    calc W₁.map N ⊓ W₂.map N ≤ W₁ ⊓ W₂ := inf_le_inf hle₁ hle₂
      _ = ⊥ := hW.inf_eq_bot
  have h := Submodule.finrank_sup_add_finrank_inf_eq (W₁.map N) (W₂.map N)
  rw [hdisj, finrank_bot, ← range_eq_sup_map N W₁ W₂ hW, hm₁, hm₂] at h
  omega

theorem finrank_ker_of_isCompl (N : E →ₗ[K] E) (W₁ W₂ : Submodule K E) (hW : IsCompl W₁ W₂)
    (h₁ : ∀ w ∈ W₁, N w ∈ W₁) (h₂ : ∀ w ∈ W₂, N w ∈ W₂) {m : ℕ}
    (hm₁ : finrank K (W₁.map N) = m) (hm₂ : finrank K (W₂.map N) = m) :
    finrank K (LinearMap.ker N) + 2 * m = finrank K E := by
  have h := LinearMap.finrank_range_add_finrank_ker N
  rw [finrank_range_of_isCompl N W₁ W₂ hW h₁ h₂ hm₁ hm₂] at h
  omega

theorem lagrangian_split (B : LinearMap.BilinForm K E) (Qf : E → K) (hK2 : (2 : K) = 0)
    (halt : ∀ e, B e e = 0) (hnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (hQadd : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f)
    (T : E ≃ₗ[K] E) (hTT : ∀ e, T (T e) = e) (hTB : ∀ e f, B (T e) (T f) = B e f)
    {m : ℕ} (hE : finrank K E = 4 * m + 2) (W₁ W₂ : Submodule K E) (hW : IsCompl W₁ W₂)
    (hW₁T : ∀ w ∈ W₁, T w ∈ W₁) (hW₂T : ∀ w ∈ W₂, T w ∈ W₂)
    (hW₁Q : ∀ w ∈ W₁, Qf w = 0) (hW₂Q : ∀ w ∈ W₂, Qf w = 0)
    (hN₁ : finrank K (W₁.map ((T : E →ₗ[K] E) - LinearMap.id)) = m)
    (hN₂ : finrank K (W₂.map ((T : E →ₗ[K] E) - LinearMap.id)) = m)
    (W : Submodule K E) (hWC : W ≤ LinearMap.ker ((T : E →ₗ[K] E) - LinearMap.id))
    (hWQ : ∀ w ∈ W, Qf w = 0) (hWd : finrank K W = 2 * m + 1) :
    finrank K ↥(W ⊓ W₁) = m + 1 ∨ finrank K ↥(W ⊓ W₂) = m + 1 := by
  set N : E →ₗ[K] E := (T : E →ₗ[K] E) - LinearMap.id with hNdef
  have h2 : ∀ e : E, e + e = 0 := fun e => by rw [← two_smul K e, hK2, zero_smul]
  have hneg : ∀ e : E, -e = e := fun e => neg_eq_of_add_eq_zero_right (h2 e)
  have hN : ∀ f, N f = T f + f := fun f => by simp [hNdef, sub_eq_add_neg, hneg]
  have hNN : ∀ u, N (N u) = 0 := fun u => by
    rw [hN, hN, map_add, hTT, show u + T u + (T u + u) = (u + u) + (T u + T u) by abel, h2, h2,
      add_zero]
  have hadj : ∀ a f, B a (N f) = B (N a) f := fun a f => by
    have : B a (T f) = B (T a) f := by rw [← hTB a (T f), hTT]
    simp only [hN, map_add, LinearMap.add_apply, this]
  have hsymm := B_symm B hK2 halt
  have hN₁' : ∀ w ∈ W₁, N w ∈ W₁ := fun w hw => by
    rw [hN]
    exact W₁.add_mem (hW₁T w hw) hw
  have hN₂' : ∀ w ∈ W₂, N w ∈ W₂ := fun w hw => by
    rw [hN]
    exact W₂.add_mem (hW₂T w hw) hw
  have hiso_of : ∀ S : Submodule K E, (∀ w ∈ S, Qf w = 0) → ∀ u ∈ S, ∀ v ∈ S, B u v = 0 :=
    fun S hS u hu v hv => by
      have := hQadd u v
      rw [hS u hu, hS v hv, hS _ (S.add_mem hu hv)] at this
      linear_combination -this
  have hd₁ := two_mul_finrank_le_of_iso B hK2 halt hnd W₁ (hiso_of W₁ hW₁Q)
  have hd₂ := two_mul_finrank_le_of_iso B hK2 halt hnd W₂ (hiso_of W₂ hW₂Q)
  have hdsum := Submodule.finrank_add_eq_of_isCompl hW
  have hW₁d : finrank K W₁ = 2 * m + 1 := by omega
  have hW₂d : finrank K W₂ = 2 * m + 1 := by omega
  have hR : finrank K (LinearMap.range N) = 2 * m :=
    finrank_range_of_isCompl N W₁ W₂ hW hN₁' hN₂' hN₁ hN₂
  have hWiso := hiso_of W hWQ
  have hdW := two_mul_finrank_le_of_iso B hK2 halt hnd W hWiso
  have hWperp : B.orthogonal W = W := by
    have hle : W ≤ B.orthogonal W := fun v hv =>
      (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun u hu => hWiso u hu v hv
    have h1 := LinearMap.BilinForm.finrank_orthogonal (nondeg_of B hK2 halt hnd) W
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hRW : LinearMap.range N ≤ W := by
    rw [← hWperp]
    rintro _ ⟨e, rfl⟩
    refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun w hw => ?_
    show B w (N e) = 0
    rw [hadj, LinearMap.mem_ker.mp (hWC hw), map_zero, LinearMap.zero_apply]
  obtain ⟨w₀, hw₀W, hw₀R⟩ : ∃ w₀ ∈ W, w₀ ∉ LinearMap.range N := by
    by_contra hcon
    push Not at hcon
    have := Submodule.finrank_mono (show W ≤ LinearMap.range N from hcon)
    omega
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀R (h ▸ Submodule.zero_mem _)
  have hWeq : LinearMap.range N ⊔ K ∙ w₀ = W := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hRW
      (Submodule.span_singleton_le_iff_mem _ _ |>.mpr hw₀W)) ?_
    have hdisj : Disjoint (LinearMap.range N) (K ∙ w₀) :=
      (Submodule.disjoint_span_singleton' hw₀0).mpr hw₀R
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range N) (K ∙ w₀)
    rw [disjoint_iff.mp hdisj, finrank_bot, finrank_span_singleton hw₀0] at h
    omega
  have hw₀mem : w₀ ∈ W₁ ⊔ W₂ := by
    rw [hW.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw₀mem
  have hNw₀ : N w₀ = 0 := LinearMap.mem_ker.mp (hWC hw₀W)
  have hNab : N a + N b = 0 := by rw [← map_add, hab, hNw₀]
  have hNa : N a = 0 := by
    have hmem : N a ∈ W₁ ⊓ W₂ :=
      ⟨hN₁' a ha, by rw [eq_neg_of_add_eq_zero_left hNab]; exact W₂.neg_mem (hN₂' b hb)⟩
    rw [hW.inf_eq_bot] at hmem
    exact (Submodule.mem_bot K).mp hmem
  have hBab : B a b = 0 := by
    have := hQadd a b
    rw [hab, hW₁Q a ha, hW₂Q b hb, hWQ w₀ hw₀W] at this
    linear_combination -this
  have haW : a ∈ W := by
    rw [← hWperp]
    refine (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun w hw => ?_
    show B w a = 0
    rw [← hWeq] at hw
    obtain ⟨r, hr, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨e, rfl⟩ := hr
    have h1 : B (N e) a = 0 := by rw [← hadj e a, hNa, map_zero]
    have h2' : B w₀ a = 0 := by
      rw [← hab, map_add, LinearMap.add_apply, halt a, zero_add, hsymm b a, hBab]
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, h1, h2', smul_zero,
      add_zero]
  have hbW : b ∈ W := by
    have : b = w₀ - a := by rw [← hab]; abel
    rw [this]
    exact W.sub_mem hw₀W haW
  have hsplit : W ≤ (W ⊓ W₁) ⊔ (W ⊓ W₂) := by
    intro w hw
    rw [← hWeq] at hw
    obtain ⟨r, hr, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨e, rfl⟩ := hr
    have he : e ∈ W₁ ⊔ W₂ := by
      rw [hW.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Submodule.mem_sup.mp he
    refine Submodule.mem_sup.mpr ⟨N e₁ + s • a, ⟨W.add_mem (hRW ⟨e₁, rfl⟩) (W.smul_mem s haW),
      W₁.add_mem (hN₁' e₁ he₁) (W₁.smul_mem s ha)⟩, N e₂ + s • b,
      ⟨W.add_mem (hRW ⟨e₂, rfl⟩) (W.smul_mem s hbW),
        W₂.add_mem (hN₂' e₂ he₂) (W₂.smul_mem s hb)⟩, ?_⟩
    rw [map_add, add_add_add_comm, ← smul_add, hab]
  have hD : finrank K ↥(W ⊓ W₁) + finrank K ↥(W ⊓ W₂) = 2 * m + 1 := by
    have hWeq' : (W ⊓ W₁) ⊔ (W ⊓ W₂) = W := le_antisymm (sup_le inf_le_left inf_le_left) hsplit
    have h := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ W₁) (W ⊓ W₂)
    have hdisj : (W ⊓ W₁) ⊓ (W ⊓ W₂) = ⊥ := by
      refine le_bot_iff.mp ?_
      calc (W ⊓ W₁) ⊓ (W ⊓ W₂) ≤ W₁ ⊓ W₂ := inf_le_inf inf_le_right inf_le_right
        _ = ⊥ := hW.inf_eq_bot
    rw [hdisj, finrank_bot, hWeq', hWd] at h
    omega
  have hb₁ : finrank K ↥(W ⊓ W₁) ≤ m + 1 := by
    have h := CFSG.RankThree.GF2n.finrank_map_add_finrank_inf_ker N W₁
    have hle : W ⊓ W₁ ≤ W₁ ⊓ LinearMap.ker N := fun w hw => ⟨hw.2, hWC hw.1⟩
    have := Submodule.finrank_mono hle
    omega
  have hb₂ : finrank K ↥(W ⊓ W₂) ≤ m + 1 := by
    have h := CFSG.RankThree.GF2n.finrank_map_add_finrank_inf_ker N W₂
    have hle : W ⊓ W₂ ≤ W₂ ⊓ LinearMap.ker N := fun w hw => ⟨hw.2, hWC hw.1⟩
    have := Submodule.finrank_mono hle
    omega
  omega

end Lin

end CFSG.RankThree.GF2n.Smith81.LinGamma
