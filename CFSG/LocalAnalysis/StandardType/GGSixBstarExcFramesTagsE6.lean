module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplitE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank ExcFrames

section TagE6


theorem ggSixBstarExcFrameOn_E6Split : GGSixBstarExcFrameOn .E6 GGExcE6SplitLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq, hp3⟩ := hP
  left
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hperf : commutator ↥ψ.range = ⊤ := by rw [hrange]; exact hctx.2.2.2.2.2.1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨χ, hχinj, hχrange⟩ := exists_injective_factor_E6 ψ hker hCψ
  have hBs : IsElemAbelian p Bs := hctx.2.1.2.1
  have hBsR : Bs ≤ χ.range := by
    rw [hχrange]
    intro b hb
    refine mem_range_of_innerDiag_E6 hp (Or.inl hp3) ψ hker hperf hCψ ?_ (hBs.2 b hb)
      (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hrange]
    exact hctx.2.2.2.2.2.2.1.1 hb
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hpq
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
  have h6 := rank_le_twoLocalRank (τ := .E6) (by decide) hp hpK
    (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E6
      ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))) χ hχinj
  have hr : p ^ Tag.E6.rank ≤ Nat.card Bs :=
    (Nat.pow_le_pow_right hp.pos h6).trans (by rw [← hBc]; exact Subgroup.card_le_of_le hctx.2.1.1)
  obtain ⟨ι, hι, hιr, hact⟩ := exists_weylFrame_E6 hp2 hp3 hpK χ hχinj hBsR hBs hr
  refine ⟨ι, hι, hιr, fun g hgM hgB hgp => hact g ?_ hgB hgp⟩
  have h : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
  have hset : (χ.range : Set G) = (ψ.range : Set G) := by rw [hχrange]
  rw [hset]
  exact h

end TagE6

end CFSG.StandardType
