module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLow2Z
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.HardMathSupport.Timmesfeld.CrossChar in
@[expose] def TwE6ScTableZAt
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (n : ℕ) : Prop :=
  ∀ δ : MulAut ↥(TwistedE6.fixedGroup K σ.toRingHom), δ ^ 3 = 1 → δ ≠ 1 →
    (∃ h ∈ twistedE6InndiagGL K σ, ∀ x,
      e6IsogenyFixed σ.toRingHom (δ x) = h * e6IsogenyFixed σ.toRingHom x * h⁻¹) →
    ∀ J : Subgroup ↥(TwistedE6.fixedGroup K σ.toRingHom), IsComponentOf J (ggAutFixedSubgroup δ) →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3 * n) →
        Subgroup.center J = ⊥

end CFSG.StandardType.TablePThreeKG

end
