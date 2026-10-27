module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RLangLabel

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)
open CFSG.StandardType (GGLabelIso GGHasLabel)
open CFSG.Blueprint (LieModel)

section LabelsTw

theorem tc_lieModel_of_labAt_suN {G : Type} [Group G] {X : Subgroup G} {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)} {r e f : ℕ}
    (hr : compRank Ψ = r) (hk : twistKindOf ρ Ψ = .suN)
    (he : componentOrbitLength ρ Ψ = e) (hlab : GGCompLabelAt (LabAt ρ f Ψ) X) :
    LieModel (↥X ⧸ Subgroup.center ↥X) .PSU (r + 1) 2 (e * f) := by
  have hLab : LabAt ρ f Ψ = ⟨LargeEvenLieTag.twA, r, e * f⟩ := by
    unfold LabAt
    rw [hk, hr, he]
    simp [componentLabel]
  unfold GGCompLabelAt at hlab
  rw [hLab] at hlab
  obtain ⟨-, -, -, R, _, hR, ⟨θ⟩⟩ := hlab
  have hR' : LieModel R .PSU (r + 1) 2 (e * f) := hR
  exact lieModel_of_mulEquiv' θ.symm hR'

theorem tc_lieModel_of_labAt_exc {G : Type} [Group G] {X : Subgroup G} {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)} {e f : ℕ}
    (hr : compRank Ψ = 4) (hk : twistKindOf ρ Ψ = .exc)
    (he : componentOrbitLength ρ Ψ = e) (hlab : GGCompLabelAt (LabAt ρ f Ψ) X) :
    LieModel (↥X ⧸ Subgroup.center ↥X) .trialityD4 0 2 (e * f) := by
  have hLab : LabAt ρ f Ψ = ⟨LargeEvenLieTag.triD4, 0, e * f⟩ := by
    unfold LabAt
    rw [hk, hr, he]
    simp [componentLabel]
  unfold GGCompLabelAt at hlab
  rw [hLab] at hlab
  obtain ⟨-, -, -, R, _, hR, ⟨θ⟩⟩ := hlab
  have hR' : LieModel R .trialityD4 0 2 (e * f) := hR
  exact lieModel_of_mulEquiv' θ.symm hR'

end LabelsTw

end CFSG.StandardType.TableCRes

end
