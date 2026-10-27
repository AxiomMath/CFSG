module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNTUnivDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

@[expose] def TwE6A2CentreCont (n : ℕ) : LargeEvenRawCont := fun R _ I _ =>
  ∀ [Finite (HopfCover R)] (θ : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R)
    (δ : MulAut (HopfCover R)), δ ^ 3 = 1 → δ ≠ 1 → ggInducedAut θ δ ∈ I →
    ∀ J : Subgroup (HopfCover R), IsComponentOf J (ggAutFixedSubgroup δ) →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3 * n) →
        Subgroup.center J = ⊥

@[expose] def TwE6A2CentreInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ≤ lab.n → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab (TwE6A2CentreCont lab.n)

end CFSG.StandardType.TablePThreeKG

end
