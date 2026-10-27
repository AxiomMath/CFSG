module

public import CFSG.RankThree.PartOne.KLR.FrobTrick
public import CFSG.RankThree.PartOne.KLR.CoreGroup

public section

namespace CFSG.RankThree.PartOne.TCF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KLR
open scoped Pointwise

variable {τ : Tag} {L : Type} [Field L]

theorem mem_rootSpan_of_pow_two_pow_mem (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2) {h : ModGL τ L}
    (hh : h ∈ torusGroup τ L) {S : Set (Fin τ.rank → ℤ)} :
    ∀ k : ℕ, h ^ (2 ^ k) ∈ rootSpan τ L S → h ∈ rootSpan τ L S := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hk
    refine ih (mem_rootSpan_of_mul_self_mem σ hσ (pow_mem hh _) ?_)
    rw [← sq, ← pow_mul, ← pow_succ]
    exact hk

theorem mem_rootSpan_of_pow_two_pow_eq_one (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {g : ModGL τ L}
    (hg : g ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootSpan τ L S : Set (ModGL τ L)))
    {k : ℕ} (hgk : g ^ (2 ^ k) = 1) : g ∈ rootSpan τ L S := by
  obtain ⟨h, hh, u, hu, rfl⟩ := hg
  have hnorm := torusGroup_le_normalizer_rootSpan (τ := τ) (L := L) hS
  have key : ∀ n : ℕ, ∃ v ∈ rootSpan τ L S, (h * u) ^ n = h ^ n * v := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨v, hv, hvn⟩ := ih
      have hconj : h⁻¹ * v * h ∈ rootSpan τ L S := by
        have := (Subgroup.mem_normalizer_iff.1 (hnorm (inv_mem hh)) v).1 hv
        simpa using this
      refine ⟨h⁻¹ * v * h * u, mul_mem hconj hu, ?_⟩
      rw [pow_succ, hvn, pow_succ]
      group
  obtain ⟨v, hv, hvk⟩ := key (2 ^ k)
  rw [hgk] at hvk
  have hhk : h ^ (2 ^ k) ∈ rootSpan τ L S := by
    have : h ^ (2 ^ k) = v⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hvk.symm
    rw [this]
    exact inv_mem hv
  exact mul_mem (mem_rootSpan_of_pow_two_pow_mem σ hσ hh k hhk) hu

theorem commutator_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α)
    {g₁ g₂ : ModGL τ L}
    (hg₁ : g₁ ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootSpan τ L S : Set (ModGL τ L)))
    (hg₂ : g₂ ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootSpan τ L S : Set (ModGL τ L))) :
    g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ rootSpan τ L S := by
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := hg₁
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := hg₂
  have hnorm := torusGroup_le_normalizer_rootSpan (τ := τ) (L := L) hS
  have hconj : ∀ h ∈ torusGroup τ L, ∀ u ∈ rootSpan τ L S, h * u * h⁻¹ ∈ rootSpan τ L S :=
    fun h hh u hu => (Subgroup.mem_normalizer_iff.1 (hnorm hh) u).1 hu
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh₁
  have hcomm : h₁ * h₂ = h₂ * h₁ := by
    rw [hc]
    exact rootDiagUnit_mul_comm_of_mem_torusGroup c hh₂
  have hhh : h₁ * h₂ * h₁⁻¹ = h₂ := by rw [hcomm]; group
  have hq₁ : h₁ * u₁ * h₁⁻¹ ∈ rootSpan τ L S := hconj h₁ hh₁ u₁ hu₁
  have hq₂ : h₂ * u₂ * h₂⁻¹ ∈ rootSpan τ L S := hconj h₂ hh₂ u₂ hu₂
  have e : h₁ * u₁ * (h₂ * u₂) * (h₁ * u₁)⁻¹ * (h₂ * u₂)⁻¹ =
      (h₁ * u₁ * h₁⁻¹) * (h₁ * (h₂ * u₂ * h₂⁻¹) * h₁⁻¹) * (h₁ * h₂ * h₁⁻¹) *
        (h₁ * u₁ * h₁⁻¹)⁻¹ * h₂⁻¹ * (h₂ * u₂ * h₂⁻¹)⁻¹ := by
    group
  rw [e, hhh]
  have e' : (h₁ * u₁ * h₁⁻¹) * (h₁ * (h₂ * u₂ * h₂⁻¹) * h₁⁻¹) * h₂ * (h₁ * u₁ * h₁⁻¹)⁻¹ *
      h₂⁻¹ * (h₂ * u₂ * h₂⁻¹)⁻¹ =
      (h₁ * u₁ * h₁⁻¹) * (h₁ * (h₂ * u₂ * h₂⁻¹) * h₁⁻¹) *
        (h₂ * (h₁ * u₁ * h₁⁻¹)⁻¹ * h₂⁻¹) * (h₂ * u₂ * h₂⁻¹)⁻¹ := by
    group
  rw [e']
  exact mul_mem (mul_mem (mul_mem hq₁ (hconj h₁ hh₁ _ hq₂))
    (hconj h₂ hh₂ _ (inv_mem hq₁))) (inv_mem hq₂)

end CFSG.RankThree.PartOne.TCF
