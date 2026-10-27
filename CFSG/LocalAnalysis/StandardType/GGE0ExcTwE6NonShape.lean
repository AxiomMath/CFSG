module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LocalAnalysis.StandardType.GGSteinbergCorrection
public import CFSG.LocalAnalysis.StandardType.GGE0TwE6Core
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtTwistedE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

theorem ggE0ModelDataAtOn_twistedE6
    : GGE0ModelDataAtOn .twistedE6 (fun f p => ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1)) := by
  intro n f hadm _
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = c ^ (2 ^ f) := fun c =>
    iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f).toRingHom = frobQ 2 f :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f c = frobQ 2 f c
      rw [hσ, frobQ_apply]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -⟩, -, hder, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) hσ
  have hH : ⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
      twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆ =
      twistedE6RootGroup (GaloisField 2 (2 * f))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f) := by
    rw [← hσθ]
    exact hder
  let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 f hf)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 f hf)
  have hπvalT : ∀ z, ((π z : twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) :=
    fun _ => rfl
  have hπker : π.ker = Subgroup.center (twistedE6Group 2 f) :=
    AutSt.ker_eq_center_of_surjective π hπ hZ (RootDetectTwE6.ker_le_center f π hπvalT)
  refine ⟨twistedE6RootGroup (GaloisField 2 (2 * f))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f), inferInstance, π,
    twistedE6Inn _ _ ⊔ twistedE6Diag _ _, hπ, hπker, hZ, le_sup_left, ?_, ?_⟩
  · intro G _ ψ hker' c _ hdiag
    exact ggOuterInv_twE6Marking f hf hσθ π hπ hπker hπvalT ψ hker' hdiag
  · exact ggE0Model_twistedE6 hf hK hσ

theorem ggE0AtOn_twistedE6_nonshape
    :
    GGE0AtOn .twistedE6 (fun f p => ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1)) :=
  ggE0AtOn_of_modelData (ggE0InG1At_of_steinberg ggSteinbergCorrectionAt_twistedE6)
    ggE0ModelDataAtOn_twistedE6

end CFSG.StandardType
