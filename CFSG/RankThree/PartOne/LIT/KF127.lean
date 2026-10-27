module

public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.PartOne.LIT.KF127SL
public import CFSG.RankThree.PartOne.LIT.KF127SSFinal
public import CFSG.RankThree.PartOne.LIT.KF127Sp
public import CFSG.RankThree.Classical.TransvectionGeneration

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.Classical (IsTransvectionWith
  prime_three_space_irreducible_transvection_generation)
open CFSG.RankThree.PartOne.LIT

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def McLaughlinFour : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V], Module.finrank (ZMod p) V = 4 →
    ∀ H : Subgroup (V ≃ₗ[ZMod p] V),
    (∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S) →
    (∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ LinearMap.det (g : V →ₗ[ZMod p] V) = 1) ∨
    (∃ B : LinearMap.BilinForm (ZMod p) V, B.IsAlt ∧ B.Nondegenerate ∧
      ∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ ∀ x y, B (g x) (g y) = B x y)

theorem kf127_of_mclaughlinFour (hM : McLaughlinFour) : KF127 := by
  intro p _ hp V _ _ _ hdim Γ hirr _ ⟨t, htΓ, htl⟩ v hv _ Λ hΛΓ hnorm hfix hOΛ hΛinv
  have hp3 : 3 ≤ p := by omega
  obtain ⟨x, f, htd⟩ := exists_isTransvectionWith_of_lin t htl.1 htl.2
  have hq : ∃ t, t ∈ trSet Γ := ⟨t, htΓ, x, f, htd⟩
  have hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      trGroup Γ = Subgroup.closure S :=
    ⟨trSet Γ, fun s hs => hs.2, rfl⟩
  have hSL : ∀ h ∈ trGroup Γ, LinearMap.det (h : V →ₗ[ZMod p] V) = 1 :=
    fun h hh => trGroup_det Γ hh
  have hm4 : Module.finrank (ZMod p) V ≤ 4 := by rcases hdim with h | h <;> omega
  have hslcase : (∀ g : V ≃ₗ[ZMod p] V, g ∈ trGroup Γ ↔
      LinearMap.det (g : V →ₗ[ZMod p] V) = 1) → ∀ a ∈ Λ, ∀ b ∈ Λ, a * b = b * a := fun h =>
    sl_final hp3 Γ Λ hΛΓ v hv hnorm hfix hOΛ
      (fun g hg => trGroup_le Γ ((h g).mpr hg))
  rcases trGroup_dichotomy hirr hq hm4 with hTirr | ⟨hd4, V₁, V₂, hc, hd₁, hd₂, h₁, h₂⟩
  · rcases hdim with hd3 | hd4
    · exact hslcase (prime_three_space_irreducible_transvection_generation hd3 (trGroup Γ) hSL
        hTirr hgen)
    · rcases hM p hp V hd4 (trGroup Γ) hTirr hgen with hsl | ⟨B, hB, hBnd, hT⟩
      · exact hslcase hsl
      · exact sp_final hp B hB hBnd (trGroup Γ) Γ Λ (trGroup_le Γ)
          (fun g hg y hy => trGroup_conj hg hy) hT hΛΓ v hv hnorm hfix hOΛ
  · exact ss_final hp hd4 hΛΓ hirr hq hc hd₁ hd₂ h₁ h₂ v hv hnorm hfix hOΛ hΛinv

end CFSG.RankThree.PartOne
