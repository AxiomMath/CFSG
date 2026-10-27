module

public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import CFSG.LocalAnalysis.StandardType.GGLabelIsoField
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4E78
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
import CFSG.LocalAnalysis.StandardType.GGNbrPrimeFieldExcl
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGExclNoIso

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

section HalfSplit

theorem ggMarkingHalfSplit_dvd_or_exc {G : Type} [Group G] {X : Subgroup G} {p Q : ℕ}
    (hQ : GGCompFieldAt Q X)
    (hmk : CFSG.StandardType.LargeEvenMarking ↥X fun lab _ _ _ _ _ =>
      LargeEvenHalfSplit p lab (Subgroup.center ↥X = ⊥)) :
    p ∣ Q ^ 2 - 1 ∨ ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) ∧ p = 7 ∧
      (lab = ⟨.A, 8, 1⟩ ∨ lab = ⟨.E6, 0, 1⟩) := by
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hHS⟩ := largeEvenMarking_exists_hasLabel hmk
  rcases largeEvenHalfSplit_dvd hlab hHS with h | ⟨hp7, hex⟩
  · left
    obtain ⟨labQ, hlabQ, -, hQeq, -, -, -, hhasQ, -⟩ := hQ
    have hiso : GGLabelIso lab labQ := ggLabelRigidInput_holds lab labQ _ hlab hlabQ hhas hhasQ
    obtain ⟨k, hk⟩ := labelIso_dvd_markDeg hlab hiso
    subst hQeq
    refine h.trans ?_
    rw [hk, pow_mul]
    exact sq_sub_one_dvd_pow_sq_sub_one _ _
  · exact Or.inr ⟨lab, hlab, hhas, hp7, hex⟩

end HalfSplit

section Nonsplit

theorem ggNbr_not_primeField_known {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    {Bs K : Subgroup G} {x : G} (hx : x ∈ Bs) (hInn : GGInnerDiagOn Bs K) :
    ¬ CFSG.StandardType.LargeEvenMarking ↥K (fun lab _ _ I F θ =>
      LargeEvenPrimeField p lab I F (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) :=
  ggNbr_not_primeField ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))
    hp hp2 hx hInn

end Nonsplit

end CFSG.StandardType
