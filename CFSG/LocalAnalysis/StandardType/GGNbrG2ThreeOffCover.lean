module

public import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.CentralExt.AdjointClosed
open scoped commutatorElement

theorem ggNbrG2Off_cover_injective
    {K : Type} [Field K] [Finite K] (hK : 5 ≤ Nat.card K)
    {L : Type} [Group L] (ψ : L →* adjointGroup Tag.G2 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) : Function.Injective ψ := by
  obtain ⟨s, hs⟩ := g2_exists_section_of_central hK hψ hker
  have decomp : ∀ l : L, ∃ c ∈ Subgroup.center L, ∃ a ∈ s.range, l = c * a := fun l =>
    ⟨l * (s (ψ l))⁻¹, hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]),
      s (ψ l), ⟨ψ l, rfl⟩, by group⟩
  have hcomm : ∀ l₁ l₂ : L, ⁅l₁, l₂⁆ ∈ s.range := by
    intro l₁ l₂
    obtain ⟨c, hc, a, ha, rfl⟩ := decomp l₁
    obtain ⟨d, hd, b, hb, rfl⟩ := decomp l₂
    rw [CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hc hd,
      commutatorElement_def]
    exact s.range.mul_mem (s.range.mul_mem (s.range.mul_mem ha hb) (s.range.inv_mem ha))
      (s.range.inv_mem hb)
  have hrange : s.range = ⊤ := by
    rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
    intro l₁ _ l₂ _
    exact hcomm l₁ l₂
  intro l₁ l₂ h
  obtain ⟨g₁, rfl⟩ : l₁ ∈ s.range := hrange ▸ Subgroup.mem_top l₁
  obtain ⟨g₂, rfl⟩ : l₂ ∈ s.range := hrange ▸ Subgroup.mem_top l₂
  rw [hs, hs] at h
  rw [h]

end CFSG.StandardType

end
