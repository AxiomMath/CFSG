module

public import CFSG.RankThree.PartTwo.Sec21.Star22
public import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item221ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly (IsElemAbelian)
open URoots (V3)
open Matrix

variable {G : Type} [Group G]

theorem diagRefl_not_fix_bodyDiag : ∀ v : V3, IsBodyDiag v →
    ((d0 : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ v ≠ v ∧ ((d1 : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ v ≠ v ∧
      ((d2 : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ v ≠ v := by
  decide +kernel

theorem p01_ne_m01 : (p01 : GL (Fin 3) (ZMod 3)) ≠ m01 := by decide +kernel

theorem card_inf_centralizer_eq_three [Finite G] (h66 : Sec6.Item6_6) {A : Subgroup G}
    (hst : PartTwoStanding G) (hAS : A ∈ partTwoS G) {Z : Subgroup G} (hZ : Z ∈ lStar A) :
    Nat.card (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) = 3 := by
  have hAe : IsElemAbelian 3 A := hAS.1.1
  obtain ⟨a, haA, ha1, hZa⟩ := mem_thetaComponentFamily_iff.mp hZ.1
  have hZC := Sec6.le_centralizer_of_mem_thetaComponentsAt hZa
  have haC : a ∈ A ⊓ Subgroup.centralizer (Z : Set G) := by
    refine ⟨haA, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hZC hl)
  have hle : A ⊓ Subgroup.centralizer (Z : Set G) ≤ A ⊓ Sec4.thetaQuotCentralizer Z := by
    rintro x ⟨hxA, hxC⟩
    refine ⟨hxA, Sec6.mem_thetaQuotCentralizer_iff.mpr
      ⟨Subgroup.centralizer_le_normalizer _ hxC, fun l hl => ?_⟩⟩
    rw [← Subgroup.mem_centralizer_iff.mp hxC l hl, mul_inv_cancel_right, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hcyc := h66 G hst A hAS Z hZ
  have hcyc' : IsCyclic (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) :=
    Subgroup.isCyclic_of_le hle
  have hexp : Monoid.exponent (A ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hAe.2 x x.2.1)
  rw [IsCyclic.exponent_eq_card] at hexp
  rcases (Nat.dvd_prime Nat.prime_three).mp hexp with h1 | h3
  · exfalso
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    have : a ∈ (⊥ : Subgroup G) := hbot ▸ haC
    exact ha1 ((Subgroup.mem_bot).mp this)
  · exact h3

theorem exists_ne_of_image_eq_swapRefl {A : Subgroup G}
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (hD : coordGL f '' dStar A = swapRefl)
    (φ : MulAut A) : ∃ ψ ∈ dStar A, ψ ≠ φ := by
  have hp : p01 ∈ coordGL f '' dStar A := by
    rw [hD]
    simp [swapRefl]
  have hm : m01 ∈ coordGL f '' dStar A := by
    rw [hD]
    simp [swapRefl]
  obtain ⟨ψ₁, hψ₁, h₁⟩ := hp
  obtain ⟨ψ₂, hψ₂, h₂⟩ := hm
  by_cases h : ψ₁ = φ
  · refine ⟨ψ₂, hψ₂, fun h' => p01_ne_m01 ?_⟩
    rw [← h₁, ← h₂, h, h']
  · exact ⟨ψ₁, hψ₁, h⟩

end CFSG.RankThree.PartTwo.Sec21.Item221ResProof
