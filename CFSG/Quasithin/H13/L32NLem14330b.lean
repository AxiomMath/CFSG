module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

namespace L14330

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem mem_span_singleton_zmod2 {α x : W} : x ∈ (ZMod 2) ∙ α ↔ x = 0 ∨ x = α := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    fin_cases c
    · left
      exact zero_smul _ α
    · right
      exact one_smul _ α
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem B_symm (B : LinearMap.BilinForm (ZMod 2) W) (hB : ∀ v, B v v = 0) (u v : W) :
    B u v = B v u := by
  have h := hB (u + v)
  have e : B (u + v) (u + v) = B u u + B u v + (B v u + B v v) := by
    simp only [map_add, LinearMap.add_apply]
    abel
  rw [e, hB u, hB v, zero_add, add_zero] at h
  have h2 : B u v = -B v u := eq_neg_of_add_eq_zero_left h
  rw [h2]
  have : ∀ y : ZMod 2, -y = y := by decide
  exact this _

theorem delta_eq (B : LinearMap.BilinForm (ZMod 2) W) (hB : ∀ v, B v v = 0)
    {α β ua ub : W} (hα₁ : B ua α = 1) (hβ₁ : B ub β = 1) (hα₂ : B ub α = 0) (hβ₂ : B ua β = 0)
    {δ : W →ₗ[ZMod 2] W}
    (h1 : ∀ u, B u α = 0 → δ u ∈ (ZMod 2) ∙ α) (h2 : ∀ u, B u β = 0 → δ u ∈ (ZMod 2) ∙ β)
    (h3 : ∀ u v, B (δ u) v = B u (δ v)) :
    ∃ ε : ZMod 2, ∀ u, δ u = ε • (B u α • β + B u β • α) := by
  have hα0 : α ≠ 0 := fun h => by rw [h, map_zero] at hα₁; exact absurd hα₁ (by decide)
  have hβ0 : β ≠ 0 := fun h => by rw [h, map_zero] at hβ₁; exact absurd hβ₁ (by decide)
  have hαβ : α ≠ β := fun h => by rw [h, hβ₂] at hα₁; exact absurd hα₁ (by decide)
  obtain ⟨ε₁, hε₁⟩ := Submodule.mem_span_singleton.mp (h2 ua hβ₂)
  obtain ⟨ε₂, hε₂⟩ := Submodule.mem_span_singleton.mp (h1 ub hα₂)
  have h3' := h3 ua ub
  rw [← hε₁, ← hε₂, LinearMap.map_smul₂, smul_eq_mul, map_smul, smul_eq_mul,
    B_symm B hB β ub, hβ₁, hα₁, mul_one, mul_one] at h3'
  refine ⟨ε₁, fun u => ?_⟩
  set n := u + B u α • ua + B u β • ub with hn
  have h2a : ∀ y : ZMod 2, y + y = 0 := by decide
  have hnα : B n α = 0 := by
    have e : B n α = B u α + B u α * B ua α + B u β * B ub α := by
      simp only [hn, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e, hα₁, hα₂, mul_one, mul_zero, add_zero, h2a]
  have hnβ : B n β = 0 := by
    have e : B n β = B u β + B u α * B ua β + B u β * B ub β := by
      simp only [hn, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e, hβ₁, hβ₂, mul_one, mul_zero, add_zero, add_comm, h2a]
  have hδn : δ n = 0 := by
    rcases mem_span_singleton_zmod2.mp (h1 n hnα) with h | h
    · exact h
    · rcases mem_span_singleton_zmod2.mp (h2 n hnβ) with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hαβ
  have hu : u = n + B u α • ua + B u β • ub := by
    rw [hn, add_assoc u, add_assoc, add_assoc, ZModModule.add_self, add_zero]
  rw [hu, map_add, map_add, hδn, zero_add, map_smul, map_smul, ← hε₁, ← hε₂, ← h3']
  have hcα : B (n + B u α • ua + B u β • ub) α = B u α := by rw [← hu]
  have hcβ : B (n + B u α • ua + B u β • ub) β = B u β := by rw [← hu]
  rw [hcα, hcβ, smul_smul, smul_smul, smul_add, smul_smul, smul_smul, mul_comm (B u α),
    mul_comm (B u β), add_comm]

theorem delta_mem_span (B : LinearMap.BilinForm (ZMod 2) W)
    {α β ua ub : W} (hα₁ : B ua α = 1) (hα₂ : B ub α = 0) (hβ₂ : B ua β = 0)
    {δ : W →ₗ[ZMod 2] W}
    (h1 : ∀ u, B u α = 0 → δ u ∈ (ZMod 2) ∙ α) (h2 : ∀ u, B u β = 0 → δ u ∈ (ZMod 2) ∙ β)
    (u : W) : ∃ c d : ZMod 2, δ u = c • α + d • β := by
  set n := u + B u α • ua + B u β • ub with hn
  have h2a : ∀ y : ZMod 2, y + y = 0 := by decide
  have hnα : B n α = 0 := by
    have e : B n α = B u α + B u α * B ua α + B u β * B ub α := by
      simp only [hn, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e, hα₁, hα₂, mul_one, mul_zero, add_zero, h2a]
  have hu : u = n + B u α • ua + B u β • ub := by
    rw [hn, add_assoc u, add_assoc, add_assoc, ZModModule.add_self, add_zero]
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp (h1 n hnα)
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp (h2 ua hβ₂)
  obtain ⟨c₃, hc₃⟩ := Submodule.mem_span_singleton.mp (h1 ub hα₂)
  refine ⟨c₁ + B u β * c₃, B u α * c₂, ?_⟩
  rw [hu, map_add, map_add, map_smul, map_smul, ← hc₁, ← hc₂, ← hc₃]
  have hcα : B (n + B u α • ua + B u β • ub) α = B u α := by rw [← hu]
  have hcβ : B (n + B u α • ua + B u β • ub) β = B u β := by rw [← hu]
  rw [hcα, hcβ, add_smul, mul_smul, mul_smul]
  abel

theorem delta_eq_of_inv (B : LinearMap.BilinForm (ZMod 2) W) (hB : ∀ v, B v v = 0)
    {α β ua ub : W} (hα₁ : B ua α = 1) (hβ₁ : B ub β = 1) (hα₂ : B ub α = 0) (hβ₂ : B ua β = 0)
    (hαβ : B α β = 0) {δ : W →ₗ[ZMod 2] W}
    (h1 : ∀ u, B u α = 0 → δ u ∈ (ZMod 2) ∙ α) (h2 : ∀ u, B u β = 0 → δ u ∈ (ZMod 2) ∙ β)
    (hinv : ∀ u v, B (u + δ u) (v + δ v) = B u v) :
    ∃ ε : ZMod 2, ∀ u, δ u = ε • (B u α • β + B u β • α) := by
  have hBαβ : ∀ c d c' d' : ZMod 2, B (c • α + d • β) (c' • α + d' • β) = 0 := by
    intro c d c' d'
    have hβα : B β α = 0 := by rw [B_symm B hB]; exact hαβ
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hB α, hB β, hαβ,
      hβα, smul_eq_mul, mul_zero, add_zero]
  refine delta_eq B hB hα₁ hβ₁ hα₂ hβ₂ h1 h2 fun u v => ?_
  obtain ⟨c, d, hcd⟩ := delta_mem_span B hα₁ hα₂ hβ₂ h1 h2 u
  obtain ⟨c', d', hcd'⟩ := delta_mem_span B hα₁ hα₂ hβ₂ h1 h2 v
  have h := hinv u v
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hcd, hcd', hBαβ, add_zero,
    ← hcd, ← hcd'] at h
  have h' : B (δ u) v + B u (δ v) = 0 := by
    rw [add_assoc] at h
    exact add_eq_left.mp h
  have hneg : ∀ y y' : ZMod 2, y + y' = 0 → y = y' := by decide
  exact hneg _ _ h'

theorem exists_dual_one (B : LinearMap.BilinForm (ZMod 2) W) {α β u₁ u₃ : W}
    (hu₁ : B u₁ α = 1) (hu₃ : B u₃ α + B u₃ β = 1) : ∃ w, B w α = 1 ∧ B w β = 0 := by
  have hcases : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  have hB2 : ∀ u v w : W, B (u + v) w = B u w + B v w := fun u v w => by
    rw [map_add, LinearMap.add_apply]
  rcases hcases (B u₁ β) with h1 | h1
  · exact ⟨u₁, hu₁, h1⟩
  · rcases hcases (B u₃ α) with h3 | h3
    · have h3' : B u₃ β = 1 := by rw [h3, zero_add] at hu₃; exact hu₃
      refine ⟨u₁ + u₃, by rw [hB2, hu₁, h3]; decide, by rw [hB2, h1, h3']; decide⟩
    · have h3' : B u₃ β = 0 := by
        rw [h3] at hu₃
        have : ∀ y : ZMod 2, 1 + y = 1 → y = 0 := by decide
        exact this _ hu₃
      exact ⟨u₃, h3, h3'⟩

theorem exists_dual (B : LinearMap.BilinForm (ZMod 2) W)
    (hnd : ∀ v, (∀ w, B w v = 0) → v = 0) {α β : W} (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α ≠ β) :
    ∃ ua ub : W, B ua α = 1 ∧ B ub β = 1 ∧ B ub α = 0 ∧ B ua β = 0 := by
  have hex : ∀ v : W, v ≠ 0 → ∃ w, B w v = 1 := by
    intro v hv
    by_contra hcon
    push Not at hcon
    apply hv
    refine hnd v fun w => ?_
    have h2 : ∀ y : ZMod 2, y ≠ 1 → y = 0 := by decide
    exact h2 _ (hcon w)
  have hαβ0 : α + β ≠ 0 := fun h => hαβ (by
    have h1 : α = -β := eq_neg_of_add_eq_zero_left h
    rw [h1]
    exact neg_eq_of_add_eq_zero_left (ZModModule.add_self β))
  obtain ⟨u₁, hu₁⟩ := hex α hα
  obtain ⟨u₂, hu₂⟩ := hex β hβ
  obtain ⟨u₃, hu₃⟩ := hex (α + β) hαβ0
  rw [map_add] at hu₃
  obtain ⟨ua, hua, hua'⟩ := exists_dual_one B hu₁ hu₃
  obtain ⟨ub, hub, hub'⟩ := exists_dual_one (α := β) (β := α) B hu₂ (by rw [add_comm]; exact hu₃)
  exact ⟨ua, ub, hua, hub, hub', hua'⟩

end L14330

end CFSG.Quasithin.H13
