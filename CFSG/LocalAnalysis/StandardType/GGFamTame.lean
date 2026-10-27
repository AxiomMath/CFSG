module

public import CFSG.LocalAnalysis.StandardType.GGFamTameInner
public import CFSG.LocalAnalysis.StandardType.GGFamTameSuN
public import CFSG.LocalAnalysis.StandardType.GGFamTameTwoDHigh
public import CFSG.LocalAnalysis.StandardType.GGFamTameD4
public import CFSG.LocalAnalysis.StandardType.GGFamTameExc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem langFamTame_of_prime
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a)) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  cases hk : twistKindM S.ρ (famCharHom a) i with
  | inner => exact langFamTame_inner hτ S hp hp2 hT hap h1 i hk
  | suN => exact langFamTame_suN hτ S hp hp2 hT hap h1 i hk
  | twoD =>
    obtain ⟨hnin, h4, hcard⟩ := twistKindM_twoD_unpack S.ρ hk
    by_cases h5 : 5 ≤ compRank (componentRoots (famCharHom a) i)
    · exact Or.inl (langFamTame_twoD_high hτ S hp hp2 hT hap h1 i hk h5)
    · have hr : compRank (componentRoots (famCharHom a) i) = 4 := by omega
      have hc : (componentRoots (famCharHom a) i).ncard = 24 := by rw [hcard, hr]
      exact Or.inl (langFamTame_twoD_four hτ S hp hp2 hT hap h1 i hr hc hnin)
  | exc => exact Or.inl (langFamTame_exc hτ S hp hp2 hT hap h1 i hk)

end CFSG.StandardType.TableCRes
