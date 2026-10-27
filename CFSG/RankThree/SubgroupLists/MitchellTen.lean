module

public import CFSG.RankThree.SubgroupLists.MitchellIcosaSecond
public import Certificates.Certificate43
import CFSG.RankThree.SubgroupLists.MitchellIcosaIso
import CFSG.RankThree.SubgroupLists.MitchellIcosaPair
import CFSG.RankThree.SubgroupLists.MitchellNondegenerate
import CFSG.RankThree.SubgroupLists.MitchellPairOrder

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

local notation "⟪" x "⟫" => Units.val (Subtype.val x)

theorem cliffB_sq_eq_one_of_quartic {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    (hq : CFSG.IsQuasisimple G)
    (hZ : ∀ z ∈ Subgroup.center G, (z : GL V₄ (ZMod p)) = 1 ∨ (z : GL V₄ (ZMod p)) = -1)
    (hneg : (-1 : GL V₄ (ZMod p)) ∈ G) (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {t : G} (ht : IsNCInv (t : GL V₄ (ZMod p))) (g : G)
    (hθ : 16 * cliffB ((t : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p))
        (((g * t * g⁻¹ : G) : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) ^ 4 -
      12 * cliffB ((t : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p))
        (((g * t * g⁻¹ : G) : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) ^ 2 + 1 = 0) :
    cliffB ((t : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p))
      (((g * t * g⁻¹ : G) : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) ^ 2 = 1 := by
  rcases Nat.lt_or_ge p 7 with hp | hp7
  ·
    have hp' : p = 5 := by
      rcases (show p = 5 ∨ p = 6 by omega) with h | h
      · exact h
      · exact absurd (h ▸ (Fact.out : p.Prime)) (by norm_num)
    exact sq_eq_one_of_quartic_of_eq_five hp' hθ
  · by_contra hB
    have hp2 : p ≠ 2 := by omega
    have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_charP hp2
    have hβ : cliffB ⟪t⟫ ⟪g * t * g⁻¹⟫ * cliffB ⟪t⟫ ⟪g * t * g⁻¹⟫ ≠ 1 := by rwa [← sq]
    have hM : ∀ x : G, IsNCInv (x : GL V₄ (ZMod p)) → ⟪x⟫ ∈ (cliffSpace : Submodule (ZMod p) _) :=
      fun x hx => (mem_cliffSpace_of_involution h2 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2).1
    obtain ⟨g₁, hfP, hγ⟩ := exists_conj_not_mem_span hp2 hGS hq hZ hneg ht (g * t * g⁻¹) ⟨g, rfl⟩ hβ
    obtain ⟨g₂, hf₂S, hγ₂⟩ := exists_conj_not_mem_span_three hp2 hGS hq hZ hneg ht (g * t * g⁻¹)
      (g₁ * t * g₁⁻¹) ⟨g, rfl⟩ ⟨g₁, rfl⟩ hβ hfP hγ
    obtain ⟨v, hvM, hv0, hvt, hve, hvf, hvf₂⟩ := exists_ne_zero_orth_four h2 (hM t ht)
      (hM _ (conj_isNCInv hGS ht g)) (hM _ (conj_isNCInv hGS ht g₁)) (hM _ (conj_isNCInv hGS ht g₂))
    by_cases hQv : cliffB v v = 0
    ·
      exact false_of_icosa_pair_isotropic hp7 hGS hU0 hneg t.2 (g * t * g⁻¹).2
        (g₁ * t * g₁⁻¹).2 (g₂ * t * g₂⁻¹).2 ht (conj_isNCInv hGS ht g) (conj_isNCInv hGS ht g₁)
        (conj_isNCInv hGS ht g₂) hθ hB hfP hγ hf₂S hvM hvt hve hvf hvf₂ hQv hv0
    ·
      exact false_of_icosa_pair_nonisotropic hp5 hGS hq hZ hneg hU0 ht ⟨g, rfl⟩ ⟨g₁, rfl⟩
        ⟨g₂, rfl⟩ hθ hB hfP hγ hf₂S hγ₂ hvM hvt hve hvf hvf₂ hQv

end CFSG.RankThree.SubgroupLists
