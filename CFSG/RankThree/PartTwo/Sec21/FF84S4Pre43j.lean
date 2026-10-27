module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43a

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem two_group_cenS (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hinv : ∀ t ∈ T, ∀ β ∈ B, β * t * β⁻¹ ∈ T)
    (hD : ∀ t ∈ T, t * (b * b₁) = (b * b₁) * t) (hb₂ : ∀ t ∈ T, t * b₂ = b₂ * t) :
    T ≤ CenS B := by
  have hT2' : ∀ x ∈ T, ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hcommT : ∀ t ∈ T, ∀ β ∈ B, t * β * t⁻¹ * β⁻¹ ∈ T := by
    intro t ht β hβ
    have h1 : β * t⁻¹ * β⁻¹ ∈ T := hinv t⁻¹ (inv_mem ht) β hβ
    have := mul_mem ht h1
    rwa [show t * (β * t⁻¹ * β⁻¹) = t * β * t⁻¹ * β⁻¹ by group] at this
  obtain ⟨-, -, -, -, -, n, hnN, hnb, hnb₁, hnb₂⟩ := h.mono
  intro t ht
  have hnb' : n⁻¹ * b₁ * n = b := by rw [← hnb]; group
  have hnb₁' : n⁻¹ * b₂ * n = b₁ := by rw [← hnb₁]; group
  have hnb₂' : n⁻¹ * b * n = b₂ := by rw [← hnb₂]; group
  have htD : t * (b * b₁) = (b * b₁) * t := hD t ht
  have hteb : n * t * n⁻¹ ∈ Cen b := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h1 := hb₂ t ht
    calc n * t * n⁻¹ * b = n * (t * (n⁻¹ * b * n)) * n⁻¹ := by group
      _ = n * (t * b₂) * n⁻¹ := by rw [hnb₂']
      _ = n * (b₂ * t) * n⁻¹ := by rw [h1]
      _ = b * (n * t * n⁻¹) := by
        calc n * (b₂ * t) * n⁻¹ = (n * b₂ * n⁻¹) * (n * t * n⁻¹) := by group
          _ = _ := by rw [hnb₂]
  have he12 : n * t * n⁻¹ * (b₁ * b₂) = (b₁ * b₂) * (n * t * n⁻¹) := by
    have e1 : n⁻¹ * (b₁ * b₂) * n = b * b₁ := by
      calc n⁻¹ * (b₁ * b₂) * n = (n⁻¹ * b₁ * n) * (n⁻¹ * b₂ * n) := by group
        _ = b * b₁ := by rw [hnb', hnb₁']
    calc n * t * n⁻¹ * (b₁ * b₂) = n * (t * (n⁻¹ * (b₁ * b₂) * n)) * n⁻¹ := by group
      _ = n * (t * (b * b₁)) * n⁻¹ := by rw [e1]
      _ = n * ((b * b₁) * t) * n⁻¹ := by rw [htD]
      _ = (b₁ * b₂) * (n * t * n⁻¹) := by
        calc n * ((b * b₁) * t) * n⁻¹ = (n * (b * b₁) * n⁻¹) * (n * t * n⁻¹) := by group
          _ = (n * b * n⁻¹) * (n * b₁ * n⁻¹) * (n * t * n⁻¹) := by group
          _ = _ := by rw [hnb, hnb₁]
  obtain ⟨k, hk⟩ := hT2' t ht
  have hcon : ∀ x : G, ∀ m : ℕ, (n * x * n⁻¹) ^ m = n * x ^ m * n⁻¹ := fun x m => conj_pow
  obtain ⟨k₁, hk₁⟩ := hT2' _ (hcommT t ht b (mem_b h))
  obtain ⟨k₂, hk₂⟩ := hT2' _ (hcommT t ht b₁ (mem_b₁ h))
  have hc1 : (n * t * n⁻¹ * b₁ * (n * t * n⁻¹)⁻¹ * b₁⁻¹) ^ 2 ^ k₁ = 1 := by
    have e : n * t * n⁻¹ * b₁ * (n * t * n⁻¹)⁻¹ * b₁⁻¹ = n * (t * b * t⁻¹ * b⁻¹) * n⁻¹ := by
      rw [← hnb]; group
    rw [e, hcon, hk₁]; group
  have hc2 : (n * t * n⁻¹ * b₂ * (n * t * n⁻¹)⁻¹ * b₂⁻¹) ^ 2 ^ k₂ = 1 := by
    have e : n * t * n⁻¹ * b₂ * (n * t * n⁻¹)⁻¹ * b₂⁻¹ = n * (t * b₁ * t⁻¹ * b₁⁻¹) * n⁻¹ := by
      rw [← hnb₁]; group
    rw [e, hcon, hk₂]; group
  have hek : (n * t * n⁻¹) ^ 2 ^ k = 1 := by rw [hcon, hk]; group
  have hmem := cenS_of_two_elements hA h hteb he12 hek hc1 hc2
  have hn' : n⁻¹ ∈ Nor B := inv_mem hnN
  rw [Subgroup.mem_centralizer_iff]
  intro β hβ
  have hβ' : n * β * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hnN β).1 hβ
  have e := Subgroup.mem_centralizer_iff.1 hmem _ hβ'
  calc β * t = n⁻¹ * ((n * β * n⁻¹) * (n * t * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * t * n⁻¹) * (n * β * n⁻¹)) * n := by rw [e]
    _ = t * β := by group

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
