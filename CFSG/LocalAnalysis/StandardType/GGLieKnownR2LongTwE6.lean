module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6Datum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6Iso
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongLift
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.LieType.Steinberg.TwistedE6.Generation

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction
open scoped commutatorElement

open CFSG.ClassicalInvolution.ModelFacts in
private theorem longTwE6_isIrreducible_cartan : IsIrreducible (Tag.cartan .F4) :=
  @isIrreducible_of_parent (Fin 4) _ (Tag.cartan .F4) (0 : Fin 4) ![0, 0, 1, 2] ![0, 1, 2, 3]
    (by decide)

theorem coreOne_twistedE6_long
    {n f : ℕ} (hf : 1 ≤ f)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hl : GGLongRoot (ggU .twistedE6 n f).D β)
    (u : (ggU .twistedE6 n f).K) {Rr Rm Q : Subgroup (ggU .twistedE6 n f).K}
    (hRr : Rr = ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .twistedE6 n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  exact coreOne_long_of
    (twistedDatum_isCTGroupDatum (frobQ 2 f) (frobQ_frobQ 2 f hf)
      (iSup_twistedDatum_rootGroup (frobQ 2 f) (frobQ_frobQ 2 f hf)))
    (twistedDatum_steinbergExtras (frobQ 2 f) (frobQ_frobQ 2 f hf))
    rfl longTwE6_isIrreducible_cartan
    (fun γ hγ => isPGroup_two_twistedRootGroup (frobQ 2 f) hγ)
    (isHighestRoot_twistedE6 (frobQ 2 f))
    (fun γ₀ hγ₀ hmax => eq_highRoot_of_maxHeight_twistedE6 (frobQ 2 f) hγ₀ hmax)
    hl u hRr hRm hQ

theorem coreFour_twistedE6_long
    {n f : ℕ} (hf : 1 ≤ f)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hl : GGLongRoot (ggU .twistedE6 n f).D β)
    (u : (ggU .twistedE6 n f).K) {Rr Q : Subgroup (ggU .twistedE6 n f).K}
    (hRr : Rr = ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .twistedE6 n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .twistedE6 n f).K) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ (2 ^ f) := fun c => frobQ_apply 2 f c
  have hcf := coreFour_twistedE6_highest hf hK (frobQ 2 f) hσ
    (CFSG.StandardType.RootDetectTwE6.odd_card_ker f
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK (frobQ 2 f) hσ) (fun _ => rfl))
  exact coreFour_long_of_core
    (twistedDatum_isCTGroupDatum (frobQ 2 f) (frobQ_frobQ 2 f hf)
      (iSup_twistedDatum_rootGroup (frobQ 2 f) (frobQ_frobQ 2 f hf)))
    (r := highRoot .F4)
    (by
      change highRoot .F4 ∈ (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots
      rw [twistedDatum_roots]
      exact isRoot_highRoot .F4)
    (fun γ₀ hγ₀ hmax => eq_highRoot_of_maxHeight_twistedE6 (frobQ 2 f) hγ₀ hmax)
    hcf
    hl u hRr hQ

end CFSG.StandardType.LieKnownR2.Short
