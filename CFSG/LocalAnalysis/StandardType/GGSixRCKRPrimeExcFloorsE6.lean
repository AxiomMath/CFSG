module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.LocalAnalysis.StandardType.GGB36JExcE6Hard
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckExc_three_dvd_two_pow_pred_of_even {f : ℕ} (hf : Even f) : 3 ∣ 2 ^ f - 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h : ∀ j : ℕ, 2 ^ (j + j) % 3 = 1 := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [show j + 1 + (j + 1) = (j + j) + 2 by ring, pow_add]
      omega
  have hpos : 1 ≤ 2 ^ (k + k) := Nat.one_le_two_pow
  have := h k
  omega

theorem rckExc_E6_floor
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E6 n f ψ p G₀ A B₁ D J L R Rm K e) (hp3 : p = 3) (hfe : Even f) :
    3 ^ 5 ≤ Nat.card A := by
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, -⟩
  subst hp3
  have h3 : 3 ∣ 2 ^ f - 1 := rckExc_three_dvd_two_pow_pred_of_even hfe
  have hlab : GGHasLabel (⟨.E6, 0, f⟩ : LargeEvenLabel) (↥G₀ ⧸ Subgroup.center ↥G₀) := by
    have hc : ChevalleyExceptionalModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E6 2 f :=
      hGG.2.2.2.chevalleyExceptionalModel (by decide)
    obtain ⟨-, hc'⟩ := hc
    exact recipeChevalley_of_untwistedChevalleyModel .E6 hc'
  have h5 : 5 ≤ LargeEvenTwoLocalRank 3 ↥G₀ := ggE6TorusLiftFiveRank hGG.2.2.1 rfl h3 hlab
  have h5' : 5 ≤ LargeEvenTwoLocalRank 3 ↥(A ⊔ G₀) :=
    h5.trans (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective
      Nat.prime_three (Subgroup.inclusion (le_sup_right : G₀ ≤ A ⊔ G₀))
      (Subgroup.inclusion_injective _))
  calc 3 ^ 5 ≤ 3 ^ LargeEvenTwoLocalRank 3 ↥(A ⊔ G₀) := Nat.pow_le_pow_right (by norm_num) h5'
    _ ≤ Nat.card A := hrank2

end CFSG.StandardType.RCKRP
