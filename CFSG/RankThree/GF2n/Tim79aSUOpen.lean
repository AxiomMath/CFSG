module

public import CFSG.Timmesfeld.Transvection.ModelSURadical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Timmesfeld.Transvection.ModelRankBasic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Open

@[expose] def SUCoreStatement : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
      uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        pCoreOf 2 (Subgroup.normalizer (T : Set (SU (unitaryInvolution F 2 f) m))) =
          uRad (unitaryInvolution F 2 f) a

@[expose] def SUIrrStatement : Prop :=
  ∀ (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = (2 ^ f) ^ 2 →
    4 ≤ m → ∀ (a : Fin m → F) (T : Subgroup (SU (unitaryInvolution F 2 f) m)), a ≠ 0 →
      uForm (unitaryInvolution F 2 f) a a = 0 → IsUTransGroup (unitaryInvolution F 2 f) a T →
        ∀ R : Subgroup (SU (unitaryInvolution F 2 f) m), T ≤ R →
          R ≤ uRad (unitaryInvolution F 2 f) a →
          (∀ b ∈ uLine (unitaryInvolution F 2 f) a, ∀ r ∈ R, b * r * b⁻¹ ∈ R) →
            R = T ∨ R = uRad (unitaryInvolution F 2 f) a

end CFSG.RankThree.GF2n.Tim79a
