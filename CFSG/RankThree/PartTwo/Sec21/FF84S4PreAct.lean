module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreCoord

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem coord_of_mem_B (h : FF84Sec4 b L B K b₁ b₂) {x : G} (hx : x ∈ B) :
    ∃ a c d : ℤ, x = b ^ a * b₁ ^ c * b₂ ^ d := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a c d : ℤ, x = b ^ a * b₁ ^ c * b₂ ^ d}
      mul_mem' := by
        rintro x y ⟨a, c, d, rfl⟩ ⟨a', c', d', rfl⟩
        exact ⟨a + a', c + c', d + d', mul_coord h a c d a' c' d'⟩
      one_mem' := ⟨0, 0, 0, by simp⟩
      inv_mem' := by
        rintro x ⟨a, c, d, rfl⟩
        refine ⟨-a, -c, -d, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [mul_coord h]
        simp }
  have : B ≤ S := B_le_of_mem' h ⟨1, 0, 0, by simp⟩ ⟨0, 1, 0, by simp⟩ ⟨0, 0, 1, by simp⟩
  exact this hx

theorem D_action (h : FF84Sec4 b L B K b₁ b₂) {n : G} (hD : n ∈ Cen (b * b₁))
    (hN : n ∈ Nor B) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ n * b₂ * n⁻¹ = b₂ ^ ε ∧
      ((n * b * n⁻¹ = b ∧ n * b₁ * n⁻¹ = b₁) ∨ (n * b * n⁻¹ = b₁ ∧ n * b₁ * n⁻¹ = b)) := by
  have hS : ∀ u ∈ ({b, b₁, b₂} : Set G),
      n * u * n⁻¹ ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G) := fun u hu =>
    h.mono.2.2.1 n hN u hu
  have hxy : (n * b * n⁻¹) * (n * b₁ * n⁻¹) = b * b₁ := by
    have hc : n * (b * b₁) = (b * b₁) * n := Subgroup.mem_centralizer_singleton_iff.1 hD
    calc (n * b * n⁻¹) * (n * b₁ * n⁻¹) = n * (b * b₁) * n⁻¹ := by group
      _ = (b * b₁) * n * n⁻¹ := by rw [hc]
      _ = b * b₁ := by group
  have hinj : ∀ u v : G, n * u * n⁻¹ = n * v * n⁻¹ → u = v := fun u v hw =>
    mul_left_cancel (mul_right_cancel hw)
  have hz := hS b₂ (by simp)
  have hmain := xy_cases h (hS b (by simp)) (hS b₁ (by simp)) hxy
  have hinvconj : ∀ u : G, n * u⁻¹ * n⁻¹ = (n * u * n⁻¹)⁻¹ := fun u => by group
  refine ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hmain with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases hz with hz | hz | hz | hz | hz | hz
    · exfalso
      have := hinj b₂ b (by rw [hz, e1])
      exact b₂_notin_zpowers_b h (this ▸ Subgroup.mem_zpowers b)
    · exfalso
      have := hinj b₂ b⁻¹ (by rw [hz, hinvconj, e1])
      exact b₂_notin_zpowers_b h (this ▸ inv_mem (Subgroup.mem_zpowers b))
    · exfalso
      have := hinj b₂ b₁ (by rw [hz, e2])
      exact b₂_notin_zpowers_b₁ h (this ▸ Subgroup.mem_zpowers b₁)
    · exfalso
      have := hinj b₂ b₁⁻¹ (by rw [hz, hinvconj, e2])
      exact b₂_notin_zpowers_b₁ h (this ▸ inv_mem (Subgroup.mem_zpowers b₁))
    · exact ⟨1, Or.inl rfl, by rw [hz]; simp, Or.inl ⟨e1, e2⟩⟩
    · exact ⟨-1, Or.inr rfl, by rw [hz]; simp, Or.inl ⟨e1, e2⟩⟩
  · rcases hz with hz | hz | hz | hz | hz | hz
    · exfalso
      have := hinj b₂ b₁ (by rw [hz, e2])
      exact b₂_notin_zpowers_b₁ h (this ▸ Subgroup.mem_zpowers b₁)
    · exfalso
      have := hinj b₂ b₁⁻¹ (by rw [hz, hinvconj, e2])
      exact b₂_notin_zpowers_b₁ h (this ▸ inv_mem (Subgroup.mem_zpowers b₁))
    · exfalso
      have := hinj b₂ b (by rw [hz, e1])
      exact b₂_notin_zpowers_b h (this ▸ Subgroup.mem_zpowers b)
    · exfalso
      have := hinj b₂ b⁻¹ (by rw [hz, hinvconj, e1])
      exact b₂_notin_zpowers_b h (this ▸ inv_mem (Subgroup.mem_zpowers b))
    · exact ⟨1, Or.inl rfl, by rw [hz]; simp, Or.inr ⟨e1, e2⟩⟩
    · exact ⟨-1, Or.inr rfl, by rw [hz]; simp, Or.inr ⟨e1, e2⟩⟩

theorem focal_core (h : FF84Sec4 b L B K b₁ b₂) {n : G} (hD : n ∈ Cen (b * b₁))
    (hN : n ∈ Nor B) {x : G} (hx : x ∈ B) :
    x⁻¹ * (n * x * n⁻¹) ∈ Subgroup.closure ({b * b₁⁻¹, b₂} : Set G) := by
  obtain ⟨a, c, d, rfl⟩ := coord_of_mem_B h hx
  obtain ⟨ε, hε, hb₂, hbb⟩ := D_action h hD hN
  have hconj : n * (b ^ a * b₁ ^ c * b₂ ^ d) * n⁻¹ =
      (n * b * n⁻¹) ^ a * (n * b₁ * n⁻¹) ^ c * (n * b₂ * n⁻¹) ^ d := by
    have e : ∀ X Y Z : G, n * (X * Y * Z) * n⁻¹ = (n * X * n⁻¹) * (n * Y * n⁻¹) * (n * Z * n⁻¹) :=
      fun X Y Z => by group
    rw [e]
    simp only [conj_zpow]
  have hx' : (b ^ a * b₁ ^ c * b₂ ^ d)⁻¹ = b ^ (-a) * b₁ ^ (-c) * b₂ ^ (-d) := by
    apply inv_eq_of_mul_eq_one_right
    rw [mul_coord h]
    simp
  have hmem2 : ∀ k : ℤ, b₂ ^ k ∈ Subgroup.closure ({b * b₁⁻¹, b₂} : Set G) := fun k =>
    Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k
  rw [hconj, hx']
  rcases hbb with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2, hb₂, ← zpow_mul, mul_coord h, show -a + a = 0 by ring, show -c + c = 0 by ring]
    simp only [zpow_zero, one_mul]
    exact hmem2 _
  · have hcomm1 : Commute b b₁ := comm_of_mem h (mem_b h) (mem_b₁ h)
    have hc' : b₁ ^ a * b ^ c = b ^ c * b₁ ^ a := (hcomm1.symm.zpow_zpow a c).eq
    rw [e1, e2, hb₂, ← zpow_mul, hc', mul_coord h]
    have hp : b ^ (-a + c) * b₁ ^ (-c + a) = (b * b₁⁻¹) ^ (c - a) := by
      have hcc : Commute b b₁⁻¹ := hcomm1.inv_right
      rw [hcc.mul_zpow, inv_zpow']
      congr 2 <;> ring
    rw [hp]
    exact mul_mem (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _) (hmem2 _)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
