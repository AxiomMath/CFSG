module

public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSL
public import CFSG.LocalAnalysis.StandardType.StarFour.FrameNesting
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.ComponentClassification.EvenLieFieldExponent
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8RootTorus

public section

namespace CFSG.StandardType.StarFour

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V] {X : Type} [Group X]

theorem two_le_finrank_of_fieldExt
    {P : Type} [CommGroup P] (η : P →* SpecialLinearGroup F V)
    (fr : SemiFrame F (groupRep η)) (i : Fin fr.r) (hm : 3 ≤ fr.m i)
    (ψ : SpecialLinearGroup F V →* X) (hψ : Function.Injective ψ) (J : Subgroup X)
    (hJ : J = (fr.slOnBlock i).map ψ) (f : ℕ) (hF : Nat.card F = 2 ^ f)
    (hext : GGSixLSevenFieldExtCase J .PSL f) : 2 ≤ Module.finrank F (fr.E i) := by
  by_contra hcon
  have hpos : 0 < Module.finrank F (fr.E i) := Module.finrank_pos
  have hlt2 : Module.finrank F (fr.E i) < 2 := Nat.lt_of_not_le hcon
  have hfr : Module.finrank F (fr.E i) = 1 := by omega
  have hcard : Nat.card (fr.E i) = 2 ^ f := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := fr.E i), hfr, pow_one, hF]
  let e₂ : fr.slOnBlock i ≃* Matrix.SpecialLinearGroup (Fin (fr.m i)) (fr.E i) :=
    ((SemiFrame.blockMulEquiv fr i).symm).trans
      (Matrix.SpecialLinearGroup.toLin'_equiv).symm
  let φ : ↥J ≃* Matrix.SpecialLinearGroup (Fin (fr.m i)) (fr.E i) :=
    (MulEquiv.subgroupCongr hJ.symm).symm.trans
      ((Subgroup.equivMapOfInjective (fr.slOnBlock i) ψ hψ).symm.trans e₂)
  have hPSL : LieModel (↥J ⧸ Subgroup.center ↥J) .PSL (fr.m i) 2 f :=
    CFSG.SeitzReduction.LinearPilot.lieModel_quotient_center_of_mulEquiv_specialLinear hcard hm φ
  obtain ⟨t', m', f', hlt, hLie, -⟩ := hext
  obtain ⟨-, -, hf'⟩ :=
    CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hm hPSL hLie
  omega

end CFSG.StandardType.StarFour
