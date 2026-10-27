module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
import CFSG.LocalAnalysis.StandardType.KGLangS1EFixedLiftAsm
import CFSG.LocalAnalysis.StandardType.KGLangS1EFixedLiftSplit
import CFSG.LocalAnalysis.StandardType.KGLangS1EFixedLiftTwisted

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.C14Exc

@[expose] def KGLangS1EFixedLiftAt
    (R : Type) [Group R] (L : Type) [Field L]
    (F₀ : ModGL .E6 L →* ModGL .E6 L) (ρ : R →* ModGL .E6 L)
    (Θ : ↥(ratPts .E6 L (endPow F₀ 3)) →* MulAut R) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ (α : MulAut K) (g : ↥(ratPts .E6 L (endPow F₀ 3))) (r : R) (x : K),
      θ (QuotientGroup.mk x) = r → kgInducedAut θ α = Θ g →
      (∃ c : ModGL .E6 L, c ∈ adjointGroup .E6 L ∧
        c * (g : ModGL .E6 L) * c⁻¹ ∈ torusGroup .E6 L ∧ c * ρ r * c⁻¹ ∈ torusGroup .E6 L) →
      α x = x

theorem kgLangS1E_fixedLift_split
    (k : Type) [Field k] [Finite k] [CharP k 2] (hk : 5 ≤ Nat.card k)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] [Algebra k L] [Algebra.IsAlgebraic k L]
    (R : Type) [Group R] (ε : R ≃* ↥(adjointGroup .E6 k)) (F₀ : ModGL .E6 L →* ModGL .E6 L)
    (Θ : ↥(ratPts .E6 L (endPow F₀ 3)) →* MulAut R)
    (hconjΘ : ∀ (g : ↥(ratPts .E6 L (endPow F₀ 3))) (r : R),
      (baseChangeGL (algebraMap k L)).comp ((adjointGroup .E6 k).subtype.comp ε.toMonoidHom)
          (Θ g r) =
        (g : ModGL .E6 L) *
          (baseChangeGL (algebraMap k L)).comp
            ((adjointGroup .E6 k).subtype.comp ε.toMonoidHom) r *
          (g : ModGL .E6 L)⁻¹) :
    KGLangS1EFixedLiftAt R L F₀
      ((baseChangeGL (algebraMap k L)).comp
        ((adjointGroup .E6 k).subtype.comp ε.toMonoidHom)) Θ := by
  intro K _ _ θ hK α g r x hx hg hc
  haveI : Group.IsPerfect ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup k) :=
    CFSG.LieType.CurtisTits.isPerfect_e6 k
  obtain ⟨κ, αU, hκ, hκε, hκα⟩ := kgLangS1EFixedLift_splitCover k hk R ε K θ hK α
  exact kgLangS1EFixedLift_assembly k L R ((adjointGroup .E6 k).subtype.comp ε.toMonoidHom) F₀ Θ
    hconjΘ K θ (MonoidHom.id _) Function.injective_id κ hκ hκε α αU hκα g hg r x hx hc

theorem kgLangS1E_fixedLift_twisted
    (k : Type) [Field k] [Finite k] {q : ℕ} (hq : 5 ≤ q) (hk : Nat.card k = q ^ 2)
    (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ q)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] [Algebra k L] [Algebra.IsAlgebraic k L]
    (R : Type) [Group R] (ε : R ≃* ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom))
    (F₀ : ModGL .E6 L →* ModGL .E6 L) (Θ : ↥(ratPts .E6 L (endPow F₀ 3)) →* MulAut R)
    (hconjΘ : ∀ (g : ↥(ratPts .E6 L (endPow F₀ 3))) (r : R),
      (baseChangeGL (τ := .E6) (algebraMap k L)).comp
          ((graphFixedRootGroup TwistTag.E6 k σ.toRingHom).subtype.comp ε.toMonoidHom) (Θ g r) =
        (g : ModGL .E6 L) *
          (baseChangeGL (τ := .E6) (algebraMap k L)).comp
            ((graphFixedRootGroup TwistTag.E6 k σ.toRingHom).subtype.comp ε.toMonoidHom) r *
          (g : ModGL .E6 L)⁻¹) :
    KGLangS1EFixedLiftAt R L F₀
      ((baseChangeGL (τ := .E6) (algebraMap k L)).comp
        ((graphFixedRootGroup TwistTag.E6 k σ.toRingHom).subtype.comp ε.toMonoidHom)) Θ := by
  intro K _ _ θ hK α g r x hx hg hc
  haveI : CharP k 2 := RingHom.charP (algebraMap k L) (algebraMap k L).injective 2
  haveI := kgLangS1EFixedLift_twisted_isPerfect k hq hk σ hσ
  obtain ⟨κ, αU, hκ, hκε, hκα⟩ := kgLangS1EFixedLift_twistedCover k hq hk σ hσ R ε K θ hK α
  exact kgLangS1EFixedLift_assembly k L R
    ((graphFixedRootGroup TwistTag.E6 k σ.toRingHom).subtype.comp ε.toMonoidHom) F₀ Θ hconjΘ K θ
    (CFSG.LieType.Steinberg.TwistedE6.fixedGroup k σ.toRingHom).subtype
    (Subgroup.subtype_injective _) κ hκ hκε α αU hκα g hg r x hx hc

end CFSG.StandardType
