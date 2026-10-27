module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.I51

section Transport

variable {H K : Type*} [Group H] [Group K]

theorem transport_core (φ : H →* K) (hφ : Function.Surjective φ) {P : Subgroup H}
    {A : Subgroup K} (hPA : P.map φ = A)
    (hcore : ∀ n : K, (∀ g : K, g⁻¹ * n * g ∈ A) → n = 1) :
    ∀ n : H, (∀ g : H, g⁻¹ * n * g ∈ P) → n ∈ φ.ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  apply hcore
  intro g
  obtain ⟨g', rfl⟩ := hφ g
  rw [← hPA]
  exact ⟨g'⁻¹ * n * g', hn g', by simp⟩

theorem transport_noNormal (φ : H →* K) {P M : Subgroup H} {A : Subgroup K}
    (hPA : P.map φ = A) (hcenter : ∀ n ∈ A, (∀ a ∈ A, a * n = n * a) → n = 1)
    (hMP : M ≤ P) (hnorm : ∀ a ∈ P, ∀ m ∈ M, a * m * a⁻¹ ∈ M)
    (hord : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ ∈ φ.ker ∨ m₂ ∈ φ.ker ∨ m₁ * m₂⁻¹ ∈ φ.ker) :
    M ≤ φ.ker := by
  intro m hm
  by_contra hmk
  have hφm : φ m ∈ A := hPA ▸ ⟨m, hMP hm, rfl⟩
  have hc : φ m = 1 := by
    apply hcenter _ hφm
    intro a ha
    rw [← hPA] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    rcases hord _ (hnorm a' ha' m hm) m hm with h | h | h
    · exfalso
      apply hmk
      rw [MonoidHom.mem_ker] at h ⊢
      have : φ (a' * m * a'⁻¹) = φ a' * φ m * (φ a')⁻¹ := by simp
      rw [this] at h
      have h' : φ m = (φ a')⁻¹ * (φ a' * φ m * (φ a')⁻¹) * φ a' := by group
      rw [h', h]; group
    · exact absurd h hmk
    · rw [MonoidHom.mem_ker] at h
      have h1 : φ (a' * m * a'⁻¹ * m⁻¹) = φ a' * φ m * (φ a')⁻¹ * (φ m)⁻¹ := by simp
      rw [h1] at h
      have h2 : φ a' * φ m * (φ a')⁻¹ = φ m := by
        have := mul_eq_one_iff_eq_inv.1 h
        simpa using this
      exact (mul_inv_eq_iff_eq_mul.1 h2)
  exact hmk (by rw [MonoidHom.mem_ker]; exact hc)

theorem transport_prod3 (φ : H →* K) {P R P' : Subgroup H}
    {A B A' : Subgroup K} (hPA : P.map φ = A) (hRB : R.map φ = B) (hP'A' : P'.map φ = A')
    (hker : φ.ker ≤ P') (h : ∀ g : K, ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ A', g = a * b * c) :
    ∀ g : H, ∃ a ∈ P, ∃ b ∈ R, ∃ c ∈ P', g = a * b * c := by
  intro g
  obtain ⟨a', ha', b', hb', c', hc', hg⟩ := h (φ g)
  rw [← hPA] at ha'
  rw [← hRB] at hb'
  rw [← hP'A'] at hc'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨b, hb, rfl⟩ := hb'
  obtain ⟨c, hc, rfl⟩ := hc'
  have hk : (a * b * c)⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hg]
    group
  refine ⟨a, ha, b, hb, c * ((a * b * c)⁻¹ * g), P'.mul_mem hc (hker hk), ?_⟩
  group

theorem transport_prod2 (φ : H →* K) {P R : Subgroup H} {A B : Subgroup K}
    (hPA : P.map φ = A) (hRB : R.map φ = B) (hker : φ.ker ≤ R)
    (h : ∀ g : K, ∃ a ∈ A, ∃ b ∈ B, g = a * b) :
    ∀ g : H, ∃ a ∈ P, ∃ b ∈ R, g = a * b := by
  intro g
  obtain ⟨a', ha', b', hb', hg⟩ := h (φ g)
  rw [← hPA] at ha'
  rw [← hRB] at hb'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨b, hb, rfl⟩ := hb'
  have hk : (a * b)⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hg]
    group
  refine ⟨a, ha, b * ((a * b)⁻¹ * g), R.mul_mem hb (hker hk), ?_⟩
  group

theorem transport_index (φ : H →* K) (hφ : Function.Surjective φ) {P : Subgroup H}
    {A : Subgroup K} (hPA : P.map φ = A) (hker : φ.ker ≤ P) : P.index = A.index := by
  have : P = A.comap φ := by
    rw [← hPA, Subgroup.comap_map_eq, sup_eq_left.2 hker]
  rw [this, Subgroup.index_comap_of_surjective A hφ]

end Transport

section Index

variable {H : Type*} [Group H] [Finite H]

theorem hord_of_relIndex_le_two {Q M : Subgroup H} (h : Q.relIndex M ≤ 2) :
    ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ ∈ Q ∨ m₂ ∈ Q ∨ m₁ * m₂⁻¹ ∈ Q := by
  intro m₁ hm₁ m₂ hm₂
  by_cases h1 : m₁ ∈ Q
  · exact Or.inl h1
  by_cases h2 : m₂ ∈ Q
  · exact Or.inr (Or.inl h2)
  right; right
  have hne : Q.relIndex M ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2' : Q.relIndex M = 2 := by
    have h1' : Q.relIndex M ≠ 1 := fun h1' => h1 (Subgroup.relIndex_eq_one.1 h1' hm₁)
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2'
  have e1 := ha ⟨m₁, hm₁⟩
  have e2 := ha ⟨m₂, hm₂⟩
  have n1 : (⟨m₁, hm₁⟩ : ↥M) ∉ Q.subgroupOf M := h1
  have n2 : (⟨m₂, hm₂⟩ : ↥M) ∉ Q.subgroupOf M := h2
  have i1 : (⟨m₁, hm₁⟩ * a : ↥M) ∈ Q.subgroupOf M := by
    rcases e1 with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h n1
  have i2 : (⟨m₂, hm₂⟩ * a : ↥M) ∈ Q.subgroupOf M := by
    rcases e2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h n2
  have := Q.mul_mem i1 (Q.inv_mem i2)
  simpa [mul_assoc] using this

omit [Finite H] in
theorem relIndex_le_two_of_hord {Q M : Subgroup H}
    (h : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ ∈ Q ∨ m₂ ∈ Q ∨ m₁ * m₂⁻¹ ∈ Q) : Q.relIndex M ≤ 2 := by
  by_cases hM : M ≤ Q
  · rw [Subgroup.relIndex_eq_one.2 hM]; norm_num
  obtain ⟨a, haM, haQ⟩ := IsConcreteLE.not_le_iff_exists.1 hM
  have h2 : Q.relIndex M = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haM⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hbQ : (b : H) ∈ Q
    · right
      exact ⟨hbQ, fun hba => haQ (by simpa using Q.mul_mem (Q.inv_mem hbQ) hba)⟩
    · left
      refine ⟨?_, hbQ⟩
      rcases h b.1 b.2 a⁻¹ (M.inv_mem haM) with h1 | h1 | h1
      · exact absurd h1 hbQ
      · exact absurd (by simpa using Q.inv_mem h1) haQ
      · simpa using h1
  omega

end Index

end CFSG.Quasithin.H13.I51
