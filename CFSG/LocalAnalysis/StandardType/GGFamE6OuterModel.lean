module

public import CFSG.LocalAnalysis.StandardType.GGFamRatCompE6Outer

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

theorem fam_lieModel_rationalComponent_of_e6_outer
    {τ : Tag}
    [CFSG.RankThree.PartOne.KE6.M27Ok τ]
    [CFSG.RankThree.PartOne.KD4T.E6Sub τ]
    {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) (v : WeylGroup τ)
    (hΨ : componentRoots χ i =
      (fun α => v • α) ''
        parabolicRoots τ (CFSG.RankThree.PartOne.KE6.e6Nodes τ))
    (hΨρ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (hout : ¬ twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots χ i)])) :
    ∃ f : ℕ, 0 < f ∧ ringChar L ^ f = S.D.q ∧
      CFSG.Blueprint.LieModel
        (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
          Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i))
        .twistedE6 0 (ringChar L) f := by
  exact lieModelM_rationalComponent_of_e6_outer (S := S) (χ := χ) i v hΨ hΨρ hout

end CFSG.StandardType.TableCRes
