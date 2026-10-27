module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.ClassicalInvolution.WeakCT.SpSpChartsTwo
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagClassical
public import CFSG.ClassicalInvolution.WeakCT.Blocks

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)


theorem ggSecFiveData_of_spSpCharts_two {G : Type} [Group G] [Finite G] {p : ℕ}
    {B : Subgroup G} {x : G} {L D J : Subgroup G} {s : ℕ} (hs : 1 ≤ s)
    (κ₁ κ₂ : StatedSp (s + 2) (GaloisField 2 1) →* G) (hκ₁ : Function.Injective κ₁)
    (hκ₂ : Function.Injective κ₂)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock (GaloisField 2 1) (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock (GaloisField 2 1)
          (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong : (κ₁.comp (longBlock (GaloisField 2 1) (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock (GaloisField 2 1) (s + 2) (Fin.last s).castSucc)).range)
    (hcross₁ : ∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 1)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock (GaloisField 2 1)
        (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range, a * b = b * a)
    (hcross₂ : ∀ a ∈ (κ₁.comp (shortBlock (GaloisField 2 1)
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (longBlock (GaloisField 2 1) (s + 2) (Fin.last (s + 1)))).range,
        a * b = b * a)
    (hG0 : ggG0 p B x L D J = κ₁.range ⊔ κ₂.range) :
    GGSecFiveData p B x L D J := by
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  obtain ⟨Ψ, hker, hrange⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_symplectic_two_of_spSpCharts hs hcard κ₁ κ₂ hκ₁ hκ₂
      hagree hlong hcross₁ hcross₂
  have hadm : StatedLieAdmissible .PSp (s + 3) 2 1 :=
    ⟨Nat.prime_two, by omega, by omega, by simp only [ne_eq, Prod.mk.injEq]; omega⟩
  refine Or.inr (Or.inr ⟨.PSp, s + 3, 1, ggSecFivePres_of_psi_PSp hadm ?_ Ψ hker
    (hrange.trans hG0.symm)⟩)
  simp only [bnRank]
  omega

end CFSG.StandardType

end
