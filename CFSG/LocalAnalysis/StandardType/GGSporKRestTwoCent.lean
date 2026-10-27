module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestOrderE

public section

namespace CFSG.StandardType.SporadicShape

theorem isPGroup_zpowers_of_pow {K : Type} [Group K] {p : ℕ} {u : K} (h : u ^ p = 1) :
    IsPGroup p (Subgroup.zpowers u) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem sporKRest_generating_of_twoCent {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {u₁ u₂ h : K} (h1 : u₁ ^ p = 1) (h2 : u₂ ^ p = 1) (hc : u₁ * u₂ = u₂ * u₁)
    (hh : u₁ * h = h * u₂)
    (hgen : Subgroup.closure ((Subgroup.centralizer {u₁} : Set K) ∪ Subgroup.centralizer {u₂}) = ⊤)
    {x : K} (hx : IsConj u₁ x) : SporKRestGenerating p x := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : Subgroup.zpowers u₁ ≤ Subgroup.normalizer (Subgroup.zpowers u₂ : Set K) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [((Commute.zpow_right (show Commute u₁ u₂ from hc) n).eq), mul_inv_cancel_right]
      exact hg
    · intro hg
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
      have e : g = u₁⁻¹ * (u₁ * g * u₁⁻¹) * u₁ := by group
      rw [e, ← hn, ((Commute.zpow_right (show Commute u₁ u₂ from hc) n).inv_left.eq),
        inv_mul_cancel_right]
      exact Subgroup.zpow_mem_zpowers u₂ n
  have hP := (isPGroup_zpowers_of_pow h1).to_sup_of_normal_right' (isPGroup_zpowers_of_pow h2) hn
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hu₁ : u₁ ∈ (S : Subgroup K) := hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers u₁))
  have hu₂ : u₂ ∈ (S : Subgroup K) := hS (Subgroup.mem_sup_right (Subgroup.mem_zpowers u₂))
  refine ggSporKRest_generating_of_closure hp S hx
    ((Subgroup.centralizer {u₁} : Set K) ∪ Subgroup.centralizer {u₂}) ?_ ?_
  · rintro z (hz | hz)
    · exact ⟨1, u₁, hu₁, by group, hz⟩
    · refine ⟨h, u₂, hu₂, ?_, hz⟩
      rw [mul_assoc, hh, ← mul_assoc, inv_mul_cancel, one_mul]
  · rw [eq_top_iff, ← hgen]
    exact Subgroup.closure_mono Set.subset_union_right

theorem sporKRest_cover_of_twoCent {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hval : (Nat.card K).factorization p = 2) {u₁ u₂ h : K} (hne : u₁ ≠ 1) (h1 : u₁ ^ p = 1)
    (h2 : u₂ ^ p = 1) (hc : u₁ * u₂ = u₂ * u₁) (hh : u₁ * h = h * u₂)
    (hgen : Subgroup.closure ((Subgroup.centralizer {u₁} : Set K) ∪ Subgroup.centralizer {u₂}) = ⊤) :
    SporKRestCover p K :=
  sporKRest_cover_of_orderE hp hval u₁ hne (isPGroup_zpowers_of_pow h1)
    fun _ hx => sporKRest_generating_of_twoCent hp h1 h2 hc hh hgen hx

end CFSG.StandardType.SporadicShape

end
