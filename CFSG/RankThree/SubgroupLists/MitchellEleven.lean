module

public import CFSG.RankThree.SubgroupLists.MitchellFourFrame
public import CFSG.RankThree.SubgroupLists.MitchellFourIso
public import CFSG.RankThree.SubgroupLists.MitchellFourSquares

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem sq_mul_sq_of_sq_eq_half {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p)) (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod p)) = 1 ∨ (z : GL V₄ (ZMod p)) = -1)
    (hneg : (-1 : GL V₄ (ZMod p)) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {d₁ e₁ d₂ e₂ : GL V₄ (ZMod p)} (hd₁G : d₁ ∈ G) (he₁G : e₁ ∈ G) (hd₂G : d₂ ∈ G)
    (he₂G : e₂ ∈ G) (hd₁ : IsNCInv d₁) (he₁ : IsNCInv e₁) (hd₂ : IsNCInv d₂) (he₂ : IsNCInv e₂)
    (hβ₁ : cliffB (d₁ : Matrix V₄ V₄ (ZMod p)) (e₁ : Matrix V₄ V₄ (ZMod p)) ^ 2 = 2⁻¹)
    (hβ₂ : cliffB (d₂ : Matrix V₄ V₄ (ZMod p)) (e₂ : Matrix V₄ V₄ (ZMod p)) ^ 2 = 2⁻¹) :
    (d₁ * e₁) ^ 2 * (d₂ * e₂) ^ 2 = (d₂ * e₂) ^ 2 * (d₁ * e₁) ^ 2 ∨
      (d₁ * e₁) ^ 2 * (d₂ * e₂) ^ 2 = -((d₂ * e₂) ^ 2 * (d₁ * e₁) ^ 2) := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_charP hp2
  obtain ⟨v, hvM, hv0, hxv, hyv⟩ := exists_commute_of_isNCInv_four h2 hd₁ he₁ hd₂ he₂
  have hx4 := pow_four_eq_neg_one_of_sq_eq_half h2 hd₁ he₁ hβ₁
  have hy4 := pow_four_eq_neg_one_of_sq_eq_half h2 hd₂ he₂ hβ₂
  by_cases hQ : cliffB v v = 0
  · have hp7 : 7 ≤ p := by
      rcases mod_eight_of_sq_eq_half hp2 hβ₁ with h | h <;> omega
    exact sq_mul_sq_of_isotropic hp7 hGS hU0 hneg hvM hQ hv0 (G.mul_mem hd₁G he₁G)
      (G.mul_mem hd₂G he₂G) hxv hyv hx4 hy4
  · exact sq_mul_sq_of_nonisotropic hp2 hGS hq hZ hneg hU0 hvM hQ (G.mul_mem hd₁G he₁G)
      (G.mul_mem hd₂G he₂G) hxv hyv hx4 hy4

theorem mitchellNoFourPair_holds :
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ G : Subgroup (GL V₄ (ZMod p)),
      G ≤ StatedSp 2 (ZMod p) → CFSG.IsQuasisimple G → commutant G = ⊥ → IsIrreducibleOn G →
      (∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod p)) = 1 ∨ (z : GL V₄ (ZMod p)) = -1) →
      (-1 : GL V₄ (ZMod p)) ∈ G → (∀ x ∈ G, IsSqZero x → x = 1) →
      ∀ t : G, IsNCInv (t : GL V₄ (ZMod p)) → ∀ g : G,
        cliffB ((t : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p))
          (((g * t * g⁻¹ : G) : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) ^ 2 ≠ 2⁻¹ := by
  intro p _ hp5 G hGS hq _ _ hZ hneg hU0 t ht g hβ
  exact false_of_forall_sq_mul_sq (two_ne_zero_of_charP (p := p) (by omega)) hGS hq hZ hneg
    (sq_mul_sq_of_sq_eq_half hp5 hGS hq hZ hneg hU0) ht g hβ

end CFSG.RankThree.SubgroupLists
