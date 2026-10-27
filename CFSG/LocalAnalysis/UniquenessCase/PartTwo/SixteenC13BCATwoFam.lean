module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwoPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairSL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairOmMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem s16c13bcA_pair_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (hΓ : s16c13bcA_PairFixed ↥Γ (ι → K))
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    (hR : (FFModel.nat Γ).Realizes H J ⊥) : s16c13bcA_PairFix H J := by
  refine s16c13bcA_transfer_pair (FFModel.nat Γ) hR (FFModel.nat_faithful Γ) ?_
  intro m _ _
  let x : ι → K := Multiplicative.toAdd m
  obtain ⟨g₁, g₂, h₁, h₂, hc, hn, hg₁, hg₂⟩ := hΓ x
  have hfix : ∀ g : ↥Γ, g • x = x → natAct Γ g m = m := by
    intro g hg
    have hg' : ((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ x = x := hg
    show Multiplicative.ofAdd (((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ x) = m
    rw [hg']
    rfl
  exact ⟨g₁, g₂, h₁, h₂, hc, hn, hfix g₁ hg₁, hfix g₂ hg₂⟩

theorem s16c13bcA_pair_alt {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    {n : ℕ} (hn : 8 ≤ n) (hN : AlternatingNatural H J ⊥ n) : s16c13bcA_PairFix H J := by
  refine s16c13bcA_transfer_pair (FFModel.altDn n) hN (FFC.altDn_faithful (by omega)) ?_
  intro m _ _
  let f : Fin n → ZMod 2 := Multiplicative.toAdd m
  obtain ⟨g₁, g₂, h₁, h₂, hc, hne, hg₁, hg₂⟩ := s16c13bcA_pairFixed_altPerm hn f
  have hfix : ∀ g : ↥(alternatingGroup (Fin n)), g • f = f →
      G6.permAct n (g : Equiv.Perm (Fin n)) m = m := by
    intro g hg
    apply Multiplicative.toAdd.injective
    funext i
    exact congrFun hg i
  exact ⟨g₁, g₂, h₁, h₂, hc, hne, hfix g₁ hg₁, hfix g₂ hg₂⟩

theorem s16c13bcA_pair_sl {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    {a : ℕ} (hN : BinaryNaturalSL H J ⊥ 5 a) : s16c13bcA_PairFix H J := by
  obtain ⟨K, hKf, -, -, hR⟩ := hN
  letI := hKf
  exact s16c13bcA_pair_nat s16c13bcA_pairFixed_statedSL hR

theorem s16c13bcA_pair_sp {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    {n a : ℕ} (hn : 6 ≤ n) (hN : NatSpn H J ⊥ n a) : s16c13bcA_PairFix H J := by
  obtain ⟨-, K, hKf, -, -, hR⟩ := hN
  letI := hKf
  exact s16c13bcA_pair_nat (s16c13bcA_pairFixed_statedSp (by omega)) hR

theorem s16c13bcA_pair_omegaMinus {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {J : Subgroup W} {n a : ℕ} (hn : 8 ≤ n) (hN : NatOmegaMinus H J ⊥ n a) :
    s16c13bcA_PairFix H J := by
  obtain ⟨-, K, hKf, hKfin, b, c, hcard, -, hR⟩ := hN
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := a)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  exact s16c13bcA_pair_nat (s16c13bcA_pairFixed_statedOmegaMinus (by omega) b c) hR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
