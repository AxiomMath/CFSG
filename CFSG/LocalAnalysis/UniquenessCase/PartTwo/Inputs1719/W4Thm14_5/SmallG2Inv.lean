module

public import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOffender
import CFSG.Quasithin.Background.SmithB42G2FOff
import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.Quasithin.Background.SmithB42G2FRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Setup.X7b
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin.B42G2F
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_involution_dispRank_le_two_mul
    {K : Type} [Field K] [Fintype K] [CharP K 2] {f : ℕ} (hK : Fintype.card K = 2 ^ f)
    (hf : 2 ≤ f) {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π)
    (hntM : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (a : M ≃ₗ[ZMod 2] M) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hnorm : ∀ x, ∃ y, a * π x * a⁻¹ = π y) :
    ∃ z : ↥(cayleyGroup K), z * z = 1 ∧ z ≠ 1 ∧ dispRank (π z) ≤ 2 * dispRank a := by
  classical
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hKn : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨ψ, -, hsurj, hker⟩ :=
    CFSG.Quasithin.B42G2Id.exists_adjointGroup_hom_cayleyGroup hKn hf
  have hZC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinjψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hZC]
  let πC := π.comp ψ
  have hπC : Function.Injective πC := hπ.comp hinjψ
  have hirrC : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, πC g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr U fun g u hu => by
      obtain ⟨g', rfl⟩ := hsurj g
      exact hU g' u hu
  let A : Subgroup (M ≃ₗ[ZMod 2] M) := Subgroup.zpowers a
  have ha : a ∈ A := Subgroup.mem_zpowers a
  have ha2' : a ^ 2 = 1 := by rwa [pow_two]
  have horder : orderOf a = 2 := orderOf_eq_prime ha2' ha1
  have hA : ∀ b ∈ A, b = 1 ∨ b = a := fun b hb =>
    (Subgroup.mem_zpowers_iff_of_orderOf_eq_two horder).mp hb
  have hsqA : ∀ b ∈ A, b * b = 1 := by
    intro b hb
    rcases hA b hb with rfl | rfl
    · simp
    · exact ha2
  have hnormA : ∀ b ∈ A, ∀ x, ∃ y, b * πC x * b⁻¹ = πC y := by
    intro b hb x
    rcases hA b hb with rfl | rfl
    · exact ⟨x, by simp⟩
    · obtain ⟨y, hy⟩ := hnorm (ψ x)
      obtain ⟨y', rfl⟩ := hsurj y
      exact ⟨y', hy⟩
  set α := normAut πC hπC A hnormA ⟨a, ha⟩ with hαdef
  by_cases hαinner : α ∈ inner (adjointGroup .G2 K)
  · obtain ⟨g, hg⟩ :=
      mem_range_of_normAut_mem_inner hπC hnormA hZC hntM hirrC hsqA ⟨a, ha⟩ hαinner
    have hga : πC g = a := hg
    have hgg : g * g = 1 := by
      apply hπC
      rw [map_mul, hga, ha2, map_one]
    have hz2 : ψ g * ψ g = 1 := by
      rw [← map_mul, hgg, map_one]
    have hz1 : ψ g ≠ 1 := by
      intro h
      apply ha1
      have h1 : π (ψ g) = 1 := by rw [h, map_one]
      rwa [show π (ψ g) = a from hga] at h1
    refine ⟨ψ g, hz2, hz1, ?_⟩
    rw [show π (ψ g) = a from hga]
    omega
  · have hαα : α ^ 2 = 1 := by
      rw [hαdef, ← map_pow]
      have h2 : (⟨a, ha⟩ : A) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, _root_.sq]
        exact ha2)
      rw [h2, map_one]
    have hα1 : α ≠ 1 := fun h => hαinner (h ▸ Subgroup.one_mem _)
    have hord : orderOf α = 2 := orderOf_eq_prime hαα hα1
    obtain ⟨-, Θ, -, -, hΘker, hΘinv⟩ :=
      even_G2_exact_automorphism_normal_form hf K hKn
    have hΘker' : Θ.ker = inner (adjointGroup .G2 K) := hΘker
    have hΘα : Θ α ≠ 1 := fun h => hαinner (by
      rw [← hΘker']
      exact MonoidHom.mem_ker.mpr h)
    obtain ⟨c₀, hc₀⟩ : ∃ c, Θ α c ≠ c := by
      by_contra h
      push Not at h
      exact hΘα (RingEquiv.ext h)
    have hδ : ∀ c, Θ α c = c ^ 2 ^ (f / 2) := by
      rcases hΘinv α hαα with h | ⟨-, h, -⟩
      · exact absurd h hΘα
      · exact h
    rcases even_G2_involution_inner_or_canonical_field hf K hKn α hord with h | ⟨-, hcan⟩
    · exact absurd h hαinner
    obtain ⟨β, ψ', hβ, hψ', -⟩ := hcan (Θ α).toRingHom hδ
    obtain ⟨g, hgg, hg1⟩ :=
      exists_involution_of_entrywise α β ψ' (Θ α).toRingHom hβ hψ' hc₀
    have h2 : πC (α g * g⁻¹) = a * (πC g * a⁻¹ * (πC g)⁻¹) := by
      rw [map_mul, map_inv, hαdef, π_normAut]
      group
    have hdisp : dispRank (π (ψ (α g * g⁻¹))) ≤ 2 * dispRank a := by
      rw [show π (ψ (α g * g⁻¹)) = πC (α g * g⁻¹) from rfl, h2]
      have h3 := dispRank_mul_le a (πC g * a⁻¹ * (πC g)⁻¹)
      rw [dispRank_conj, dispRank_inv_of_mul_self ha2] at h3
      omega
    refine ⟨ψ (α g * g⁻¹), ?_, ?_, ?_⟩
    · rw [← map_mul, hgg, map_one]
    · exact fun h => hg1 (hinjψ (h.trans (map_one ψ).symm))
    · exact hdisp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
