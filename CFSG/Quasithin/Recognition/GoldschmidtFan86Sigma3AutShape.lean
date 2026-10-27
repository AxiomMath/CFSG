module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Dih

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open DihedralGroup
open scoped commutatorElement

variable {R : Type*} [Group R]

theorem comm_prod (g h : DihedralGroup 4 × R) : ⁅g, h⁆ = (⁅g.1, h.1⁆, ⁅g.2, h.2⁆) :=
  Prod.ext (by simp [commutatorElement_def]) (by simp [commutatorElement_def])

theorem a0_ne_one : (a0 : DihedralGroup 4) ≠ 1 := by decide

theorem shape (g c : DihedralGroup 4 × R) (hc : c ≠ 1)
    (hcg : ∀ h, ⁅g, h⁆ = 1 ∨ ⁅g, h⁆ = c) (hex : ∃ h, ⁅g, h⁆ = c) :
    ((g.1 = r 0 ∨ g.1 = r 2) ∧ c.1 = 1) ∨
    (¬ (g.1 = r 0 ∨ g.1 = r 2) ∧ (∀ s : R, g.2 * s = s * g.2) ∧ c = (a0, 1)) := by
  by_cases hz : g.1 = r 0 ∨ g.1 = r 2
  · left
    refine ⟨hz, ?_⟩
    obtain ⟨h, rfl⟩ := hex
    rw [comm_prod]
    show ⁅g.1, h.1⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (central_iff g.1).2 hz h.1
  · right
    obtain ⟨y, hy⟩ := exists_comm g.1 hz
    have h1 : ⁅g, ((y : DihedralGroup 4), (1 : R))⁆ = (a0, 1) := by
      rw [comm_prod]
      exact Prod.ext hy (by simp)
    have hne : ((a0 : DihedralGroup 4), (1 : R)) ≠ 1 := fun h => a0_ne_one (congrArg Prod.fst h)
    have hceq : c = (a0, 1) := by
      rcases hcg (y, 1) with h | h
      · exact absurd (h1.symm.trans h) hne
      · exact h1.symm.trans h |>.symm
    refine ⟨hz, ?_, hceq⟩
    intro s
    by_contra hs
    have hs' : ⁅g.2, s⁆ ≠ 1 := fun h => hs ((commutatorElement_eq_one_iff_mul_comm).1 h)
    have h2 : ⁅g, ((1 : DihedralGroup 4), s)⁆ = (1, ⁅g.2, s⁆) := by
      rw [comm_prod]
      exact Prod.ext (by simp) rfl
    rcases hcg (1, s) with h | h
    · exact hs' (congrArg Prod.snd (h2.symm.trans h))
    · have := (h2.symm.trans h).trans hceq
      exact a0_ne_one (congrArg Prod.fst this).symm

theorem setup (φ : MulAut (DihedralGroup 4 × R)) (d₀ : DihedralGroup 4)
    (hd₀ : ¬ (d₀ = r 0 ∨ d₀ = r 2)) :
    (∀ h, ⁅φ (d₀, 1), h⁆ = 1 ∨ ⁅φ (d₀, 1), h⁆ = φ (a0, 1)) ∧
      (∃ h, ⁅φ (d₀, 1), h⁆ = φ (a0, 1)) ∧ φ (a0, 1) ≠ 1 := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have e : ⁅φ (d₀, 1), h⁆ = φ ⁅((d₀ : DihedralGroup 4), (1 : R)), φ.symm h⁆ := by
      rw [map_commutatorElement]; simp
    rw [e, comm_prod]
    rcases comm_mem d₀ (φ.symm h).1 with h' | h'
    · left; simp [h']
    · right; simp [h']
  · obtain ⟨y, hy⟩ := exists_comm d₀ hd₀
    refine ⟨φ (y, 1), ?_⟩
    rw [← map_commutatorElement, comm_prod]
    simp [hy]
  · intro h
    have := φ.injective (h.trans (map_one φ).symm)
    exact a0_ne_one (congrArg Prod.fst this)

theorem image_shape (φ : MulAut (DihedralGroup 4 × R)) (d₀ : DihedralGroup 4)
    (hd₀ : ¬ (d₀ = r 0 ∨ d₀ = r 2)) :
    (((φ (d₀, 1)).1 = r 0 ∨ (φ (d₀, 1)).1 = r 2) ∧ (φ (a0, 1)).1 = 1) ∨
    (¬ ((φ (d₀, 1)).1 = r 0 ∨ (φ (d₀, 1)).1 = r 2) ∧
      (∀ s : R, (φ (d₀, 1)).2 * s = s * (φ (d₀, 1)).2) ∧ φ (a0, 1) = (a0, 1)) := by
  obtain ⟨h1, h2, h3⟩ := setup φ d₀ hd₀
  exact shape _ _ h3 h1 h2

end CFSG.Quasithin.Fan86.Sigma3
