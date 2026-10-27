module

public import CFSG.RankThree.GF2n.Basic

public section

namespace CFSG.RankThree.GF2n.Tim79a.TwoGame

section Part1

open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

structure TIData (V Q P M : Subgroup G) (a v₀ b : G) : Prop where
  a_mem : a ∈ V
  v_mem : v₀ ∈ V
  V_enum : ∀ z ∈ V, z = 1 ∨ z = a ∨ z = v₀ ∨ z = a * v₀
  a_ne : a ≠ 1
  a_sq : a * a = 1
  v_sq : v₀ * v₀ = 1
  av_comm : a * v₀ = v₀ * a
  ti : IsTI V
  M_norm : ∀ g, g ∈ M ↔ g ∈ Subgroup.normalizer (V : Set G)
  M_cent : ∀ g, g ∈ M ↔ g * a = a * g
  cent_v : ∀ g, g * v₀ = v₀ * g → g ∈ M
  b_mem : b ∈ M
  b_swap : b * v₀ * b⁻¹ = a * v₀
  Q_le : Q ≤ M
  Q_norm : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q
  P_le : P ≤ Q
  P_cent : ∀ p ∈ P, ∀ z ∈ V, p * z = z * p
  P_norm : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P
  QP : ∀ q ∈ Q, ∀ p ∈ P, ⁅q, p⁆ ∈ V
  QV : ∀ q ∈ Q, (∀ z ∈ V, q * z = z * q) → q ∈ P

structure LocalFacts (V M : Subgroup G) (a v₀ : G) : Prop where
  enum : ∀ y t : G, t ∈ conjSubgroup y V →
    t = 1 ∨ t = y * a * y⁻¹ ∨ t = y * v₀ * y⁻¹ ∨ t = y * (a * v₀) * y⁻¹
  cent_le : ∀ y g : G, (g * (y * v₀ * y⁻¹) = (y * v₀ * y⁻¹) * g ∨
      g * (y * (a * v₀) * y⁻¹) = (y * (a * v₀) * y⁻¹) * g) →
    g * (y * a * y⁻¹) = (y * a * y⁻¹) * g
  normalizes : ∀ y g : G, g * (y * a * y⁻¹) = (y * a * y⁻¹) * g →
    g ∈ Subgroup.normalizer ((conjSubgroup y V : Subgroup G) : Set G)
  inf_eq_bot : ∀ y y' : G, conjSubgroup y V ≠ conjSubgroup y' V →
    conjSubgroup y V ⊓ conjSubgroup y' V = ⊥
  conj_eq : ∀ y : G, y * a * y⁻¹ ∉ V → conjSubgroup y V ≠ V

end Part1

section Part2

open CFSG.CGT.Timmesfeld75
open CFSG.RankThree.GF2n

variable {G : Type} [Group G]

theorem conj_comm_iff_TwoGame (y g x : G) :
    g * (y * x * y⁻¹) = (y * x * y⁻¹) * g ↔ (y⁻¹ * g * y) * x = x * (y⁻¹ * g * y) := by
  obtain ⟨c, rfl⟩ : ∃ c, g = y * c * y⁻¹ := ⟨y⁻¹ * g * y, by group⟩
  have e1 : y⁻¹ * (y * c * y⁻¹) * y = c := by group
  have e2 : y * c * y⁻¹ * (y * x * y⁻¹) = y * (c * x) * y⁻¹ := by group
  have e3 : y * x * y⁻¹ * (y * c * y⁻¹) = y * (x * c) * y⁻¹ := by group
  rw [e1, e2, e3]
  constructor
  · intro hh
    exact mul_left_cancel (mul_right_cancel hh)
  · intro hh
    rw [hh]

theorem TIData.localFacts [Finite G] {V Q P M : Subgroup G} {a v₀ b : G}
    (h : TIData V Q P M a v₀ b) : LocalFacts V M a v₀ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y t ht
    have hz : y⁻¹ * t * y ∈ V := mem_conjSubgroup.mp ht
    have e : t = y * (y⁻¹ * t * y) * y⁻¹ := by group
    rcases h.V_enum _ hz with h1 | h1 | h1 | h1
    · rw [h1] at e
      left
      simpa using e
    · rw [h1] at e
      exact Or.inr (Or.inl e)
    · rw [h1] at e
      exact Or.inr (Or.inr (Or.inl e))
    · rw [h1] at e
      exact Or.inr (Or.inr (Or.inr e))
  · intro y g hyp
    have hcM : y⁻¹ * g * y ∈ M := by
      rcases hyp with hv | hav
      · exact h.cent_v (y⁻¹ * g * y) ((conj_comm_iff_TwoGame y g v₀).mp hv)
      · have hc : (y⁻¹ * g * y) * (a * v₀) = (a * v₀) * (y⁻¹ * g * y) :=
          (conj_comm_iff_TwoGame y g (a * v₀)).mp hav
        have hc' : (b⁻¹ * (y⁻¹ * g * y) * b) * v₀ = v₀ * (b⁻¹ * (y⁻¹ * g * y) * b) :=
          (conj_comm_iff_TwoGame b (y⁻¹ * g * y) v₀).mp (by rw [h.b_swap]; exact hc)
        have hc'M : b⁻¹ * (y⁻¹ * g * y) * b ∈ M := h.cent_v _ hc'
        have e : y⁻¹ * g * y = b * (b⁻¹ * (y⁻¹ * g * y) * b) * b⁻¹ := by group
        rw [e]
        exact M.mul_mem (M.mul_mem h.b_mem hc'M) (M.inv_mem h.b_mem)
    exact (conj_comm_iff_TwoGame y g a).mpr ((h.M_cent (y⁻¹ * g * y)).mp hcM)
  · intro y g hg
    have hc : (y⁻¹ * g * y) * a = a * (y⁻¹ * g * y) :=
      (conj_comm_iff_TwoGame y g a).mp hg
    have hcN : conjSubgroup (y⁻¹ * g * y) V = V :=
      conjSubgroup_eq_self_iff.mpr ((h.M_norm (y⁻¹ * g * y)).mp ((h.M_cent _).mpr hc))
    apply conjSubgroup_eq_self_iff.mp
    have e : g * y = y * (y⁻¹ * g * y) := by group
    rw [← conjSubgroup_mul, e, conjSubgroup_mul, hcN]
  · intro y y' hne
    have hTI : IsTI (conjSubgroup y V) := isTI_conjSubgroup h.ti y
    have e : conjSubgroup y' V = conjSubgroup (y' * y⁻¹) (conjSubgroup y V) := by
      rw [← conjSubgroup_mul]
      congr 1
      group
    have hne' : conjSubgroup (y' * y⁻¹) (conjSubgroup y V) ≠ conjSubgroup y V := by
      rw [← e]
      exact hne.symm
    rw [e]
    exact inf_conjSubgroup_eq_bot_of_isTI hTI hne'
  · intro y hy heq
    apply hy
    have hmem : y * a * y⁻¹ ∈ conjSubgroup y V := by
      rw [mem_conjSubgroup]
      have e : y⁻¹ * (y * a * y⁻¹) * y = a := by group
      rw [e]
      exact h.a_mem
    rw [heq] at hmem
    exact hmem

end Part2

end CFSG.RankThree.GF2n.Tim79a.TwoGame
