module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
import CFSG.LocalAnalysis.StandardType.GGF4A3StdCore
import CFSG.LocalAnalysis.StandardType.GGF4RankFour
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Model

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

private theorem a3_classify {a0 a1 a2 : W} (h0 : R.IsRefl a0) (h1 : R.IsRefl a1)
    (h2 : R.IsRefl a2) (o01 : orderOf (a0 * a1) = 3) (o12 : orderOf (a1 * a2) = 3)
    (o02 : orderOf (a0 * a2) = 2) :
    ∃ g : W, (g * a0 * g⁻¹ = R.s 0 ∧ g * a1 * g⁻¹ = R.s 1 ∧ g * a2 * g⁻¹ = R.rL) ∨
      (g * a0 * g⁻¹ = R.s 3 ∧ g * a1 * g⁻¹ = R.s 2 ∧ g * a2 * g⁻¹ = R.rS) := by
  obtain ⟨g1, T, hT, e1⟩ := R.stage1_conj h1
  have o01' : orderOf (g1 * a0 * g1⁻¹ * R.s T) = 3 := by
    rw [← e1, show g1 * a0 * g1⁻¹ * (g1 * a1 * g1⁻¹) = g1 * (a0 * a1) * g1⁻¹ by group,
      orderOf_conj_eq, o01]
  have o12' : orderOf (R.s T * (g1 * a2 * g1⁻¹)) = 3 := by
    rw [← e1, show g1 * a1 * g1⁻¹ * (g1 * a2 * g1⁻¹) = g1 * (a1 * a2) * g1⁻¹ by group,
      orderOf_conj_eq, o12]
  have o02' : orderOf (g1 * a0 * g1⁻¹ * (g1 * a2 * g1⁻¹)) = 2 := by
    rw [show g1 * a0 * g1⁻¹ * (g1 * a2 * g1⁻¹) = g1 * (a0 * a2) * g1⁻¹ by group,
      orderOf_conj_eq, o02]
  rcases hT with rfl | rfl
  · obtain ⟨x0, hx0, ρ0⟩ := R.refl_rep (h0.conj g1)
    obtain ⟨x2, hx2, ρ2⟩ := R.refl_rep (h2.conj g1)
    have hrel : relAb (Rm x0) (Sm 1) (Rm x2) = true := by
      rw [relAb_iff]
      exact ⟨R.ord3b_of ρ0 (R.hs 1) o01', R.ord3b_of (R.hs 1) ρ2 o12',
        R.ord2b_of ρ0 ρ2 o02'⟩
    obtain ⟨k, -, c0, c2, c1⟩ := a3_stage2L x0 hx0 x2 hx2 hrel
    refine ⟨R.wd (a3W2L k) * g1, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rw [show R.wd (a3W2L k) * g1 * a0 * (R.wd (a3W2L k) * g1)⁻¹ =
        R.wd (a3W2L k) * (g1 * a0 * g1⁻¹) * (R.wd (a3W2L k))⁻¹ by group]
      exact R.conj_wd_eq ρ0 (R.hs 0) c0
    · rw [show R.wd (a3W2L k) * g1 * a1 * (R.wd (a3W2L k) * g1)⁻¹ =
        R.wd (a3W2L k) * (g1 * a1 * g1⁻¹) * (R.wd (a3W2L k))⁻¹ by group, e1]
      exact R.conj_wd_eq (R.hs 1) (R.hs 1) c1
    · rw [show R.wd (a3W2L k) * g1 * a2 * (R.wd (a3W2L k) * g1)⁻¹ =
        R.wd (a3W2L k) * (g1 * a2 * g1⁻¹) * (R.wd (a3W2L k))⁻¹ by group]
      exact R.conj_wd_eq ρ2 R.rho_rL c2
  · obtain ⟨x0, hx0, ρ0⟩ := R.refl_rep (h0.conj g1)
    obtain ⟨x2, hx2, ρ2⟩ := R.refl_rep (h2.conj g1)
    have hrel : relAb (Rm x0) (Sm 2) (Rm x2) = true := by
      rw [relAb_iff]
      exact ⟨R.ord3b_of ρ0 (R.hs 2) o01', R.ord3b_of (R.hs 2) ρ2 o12',
        R.ord2b_of ρ0 ρ2 o02'⟩
    obtain ⟨k, -, c0, c2, c1⟩ := a3_stage2S x0 hx0 x2 hx2 hrel
    refine ⟨R.wd (a3W2S k) * g1, Or.inr ⟨?_, ?_, ?_⟩⟩
    · rw [show R.wd (a3W2S k) * g1 * a0 * (R.wd (a3W2S k) * g1)⁻¹ =
        R.wd (a3W2S k) * (g1 * a0 * g1⁻¹) * (R.wd (a3W2S k))⁻¹ by group]
      exact R.conj_wd_eq ρ0 (R.hs 3) c0
    · rw [show R.wd (a3W2S k) * g1 * a1 * (R.wd (a3W2S k) * g1)⁻¹ =
        R.wd (a3W2S k) * (g1 * a1 * g1⁻¹) * (R.wd (a3W2S k))⁻¹ by group, e1]
      exact R.conj_wd_eq (R.hs 2) (R.hs 2) c1
    · rw [show R.wd (a3W2S k) * g1 * a2 * (R.wd (a3W2S k) * g1)⁻¹ =
        R.wd (a3W2S k) * (g1 * a2 * g1⁻¹) * (R.wd (a3W2S k))⁻¹ by group]
      exact R.conj_wd_eq ρ2 R.rho_rS c2

private theorem a3_transport {a0 a1 a2 b0 b1 b2 : W} (g : W) (e0 : g * a0 * g⁻¹ = b0)
    (e1 : g * a1 * g⁻¹ = b1) (e2 : g * a2 * g⁻¹ = b2) {H₀ : Fin 3 → Subgroup W}
    (hne : ∀ j, H₀ j ≠ ⊤) (hb : ∀ j, b0 ∈ H₀ j ∧ b1 ∈ H₀ j ∧ b2 ∈ H₀ j)
    (hcov : ∀ t, R.IsRefl t → ∃ j, t ∈ H₀ j)
    (hpair : ∀ t t', R.IsRefl t → R.IsRefl t' → orderOf (t * t') = 3 →
      (∀ j, t ∈ H₀ j ∧ t' ∈ H₀ j) ∨ Subgroup.closure ({b0, b1, b2, t, t'} : Set W) = ⊤) :
    ∃ H : Fin 3 → Subgroup W, (∀ j, H j ≠ ⊤) ∧
      (∀ j, a0 ∈ H j ∧ a1 ∈ H j ∧ a2 ∈ H j) ∧
      (∀ t, R.IsRefl t → ∃ j, t ∈ H j) ∧
      ∀ t t', R.IsRefl t → R.IsRefl t' → orderOf (t * t') = 3 →
        (∀ j, t ∈ H j ∧ t' ∈ H j) ∨
          Subgroup.closure ({a0, a1, a2, t, t'} : Set W) = ⊤ := by
  refine ⟨fun j => conjSub g (H₀ j), ?_, ?_, ?_, ?_⟩
  · intro j htop
    change conjSub g (H₀ j) = ⊤ at htop
    apply hne j
    rw [eq_top_iff]
    intro x _
    have h1 : g⁻¹ * x * g ∈ conjSub g (H₀ j) := by rw [htop]; exact Subgroup.mem_top _
    rw [mem_conjSub] at h1
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [h2] at h1
  · intro j
    exact ⟨mem_conjSub.2 (by rw [e0]; exact (hb j).1),
      mem_conjSub.2 (by rw [e1]; exact (hb j).2.1),
      mem_conjSub.2 (by rw [e2]; exact (hb j).2.2)⟩
  · intro t ht
    obtain ⟨j, hj⟩ := hcov (g * t * g⁻¹) (ht.conj g)
    exact ⟨j, mem_conjSub.2 hj⟩
  · intro t t' ht ht' hord
    have hord' : orderOf ((g * t * g⁻¹) * (g * t' * g⁻¹)) = 3 := by
      rw [show (g * t * g⁻¹) * (g * t' * g⁻¹) = g * (t * t') * g⁻¹ by group,
        orderOf_conj_eq, hord]
    rcases hpair (g * t * g⁻¹) (g * t' * g⁻¹) (ht.conj g) (ht'.conj g) hord' with h | h
    · exact Or.inl fun j => ⟨mem_conjSub.2 (h j).1, mem_conjSub.2 (h j).2⟩
    · right
      rw [eq_top_iff]
      intro w _
      have hw : g * w * g⁻¹ ∈ Subgroup.closure
          ({b0, b1, b2, g * t * g⁻¹, g * t' * g⁻¹} : Set W) := by
        rw [h]; exact Subgroup.mem_top _
      have hle : Subgroup.closure ({b0, b1, b2, g * t * g⁻¹, g * t' * g⁻¹} : Set W) ≤
          conjSub g⁻¹ (Subgroup.closure ({a0, a1, a2, t, t'} : Set W)) := by
        rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rw [SetLike.mem_coe, mem_conjSub]
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · rw [← e0, show g⁻¹ * (g * a0 * g⁻¹) * (g⁻¹)⁻¹ = a0 by group]
          exact Subgroup.subset_closure (by simp)
        · rw [← e1, show g⁻¹ * (g * a1 * g⁻¹) * (g⁻¹)⁻¹ = a1 by group]
          exact Subgroup.subset_closure (by simp)
        · rw [← e2, show g⁻¹ * (g * a2 * g⁻¹) * (g⁻¹)⁻¹ = a2 by group]
          exact Subgroup.subset_closure (by simp)
        · rw [show g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t by group]
          exact Subgroup.subset_closure (by simp)
        · rw [show g⁻¹ * (g * t' * g⁻¹) * (g⁻¹)⁻¹ = t' by group]
          exact Subgroup.subset_closure (by simp)
      have hw' := hle hw
      rw [mem_conjSub, show g⁻¹ * (g * w * g⁻¹) * (g⁻¹)⁻¹ = w by group] at hw'
      exact hw'

theorem a3_core {a : Fin 3 → W} (ha : ∀ i, R.IsRefl (a i)) (o01 : orderOf (a 0 * a 1) = 3)
    (o12 : orderOf (a 1 * a 2) = 3) (o02 : orderOf (a 0 * a 2) = 2) :
    ∃ H : Fin 3 → Subgroup W, (∀ j, H j ≠ ⊤) ∧ (∀ i j, a i ∈ H j) ∧
      (∀ t, R.IsRefl t → ∃ j, t ∈ H j) ∧
      ∀ t t', R.IsRefl t → R.IsRefl t' → orderOf (t * t') = 3 →
        (∀ j, t ∈ H j ∧ t' ∈ H j) ∨ Subgroup.closure ({a 0, a 1, a 2, t, t'} : Set W) = ⊤ := by
  have hi3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  obtain ⟨g, hg | hg⟩ := R.a3_classify (ha 0) (ha 1) (ha 2) o01 o12 o02
  · obtain ⟨H₀, hne, hb, hcov, hpair⟩ := R.std_A3L
    obtain ⟨H, hne', hmem, hcov', hpair'⟩ :=
      R.a3_transport g hg.1 hg.2.1 hg.2.2 hne hb hcov hpair
    refine ⟨H, hne', ?_, hcov', hpair'⟩
    intro i j
    rcases hi3 i with rfl | rfl | rfl
    · exact (hmem j).1
    · exact (hmem j).2.1
    · exact (hmem j).2.2
  · obtain ⟨H₀, hne, hb, hcov, hpair⟩ := R.std_A3S
    obtain ⟨H, hne', hmem, hcov', hpair'⟩ :=
      R.a3_transport g hg.1 hg.2.1 hg.2.2 hne hb hcov hpair
    refine ⟨H, hne', ?_, hcov', hpair'⟩
    intro i j
    rcases hi3 i with rfl | rfl | rfl
    · exact (hmem j).1
    · exact (hmem j).2.1
    · exact (hmem j).2.2

end F4Rep

end CFSG.StandardType.F4Model

end
