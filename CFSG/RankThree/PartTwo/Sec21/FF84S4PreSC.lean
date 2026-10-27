module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreD0

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem conj_bb₁sq_mem (h : FF84Sec4 b L B K b₁ b₂) {n : G} (hD : n ∈ Cen (b * b₁))
    (hN : n ∈ Nor B) : n * (b * b₁ ^ 2) * n⁻¹ ∈ Subgroup.zpowers (b * b₁ ^ 2) := by
  obtain ⟨ε, -, -, hbb⟩ := D_action h hD hN
  have e : n * (b * b₁ ^ 2) * n⁻¹ = (n * b * n⁻¹) * (n * b₁ * n⁻¹) ^ 2 := by simp only [pow_two]; group
  rcases hbb with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e, e1, e2]; exact Subgroup.mem_zpowers _
  · rw [e, e1, e2]
    have hc : Commute b b₁ := comm_of_mem h (mem_b h) (mem_b₁ h)
    have h3 := pow3_of_mem h (mem_b₁ h)
    have : b₁ * b ^ 2 = (b * b₁ ^ 2) ^ 2 := by
      rw [(hc.pow_right 2).mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3,
        one_mul, pow_one, ← hc.pow_left 2 |>.eq]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2

theorem sc_P₁ (h : FF84Sec4 b L B K b₁ b₂) {a g : G} (ha : a ∈ Subgroup.zpowers (b * b₁ ^ 2))
    (hg : g ∈ Cen (b * b₁)) (hgB : g⁻¹ * a * g ∈ B) :
    g⁻¹ * a * g ∈ Subgroup.zpowers (b * b₁ ^ 2) := by
  have haB : a ∈ B := (Subgroup.zpowers_le.2 (bb₁sq_mem h)) ha
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => (comm_of_mem h hx hy).eq
  obtain ⟨n, hnD, hnN, hn⟩ := burnside_sub (S41_B_sylow h) hBc haB hgB (inv_mem hg)
    (by rw [inv_inv])
  rw [← hn]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ (conj_bb₁sq_mem h hnD hnN) k

theorem sc_P₂ (h : FF84Sec4 b L B K b₁ b₂) {a g : G} (ha : a ∈ Subgroup.zpowers b₂)
    (hg : g ∈ Cen (b * b₁)) (hgB : g⁻¹ * a * g ∈ B) :
    g⁻¹ * a * g ∈ Subgroup.zpowers b₂ := by
  have haB : a ∈ B := (Subgroup.zpowers_le.2 (mem_b₂ h)) ha
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => (comm_of_mem h hx hy).eq
  obtain ⟨n, hnD, hnN, hn⟩ := burnside_sub (S41_B_sylow h) hBc haB hgB (inv_mem hg)
    (by rw [inv_inv])
  rw [← hn]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rw [← conj_zpow]
  obtain ⟨ε, -, hε, -⟩ := D_action h hnD hnN
  rw [hε]
  exact Subgroup.zpow_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) ε) k

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
