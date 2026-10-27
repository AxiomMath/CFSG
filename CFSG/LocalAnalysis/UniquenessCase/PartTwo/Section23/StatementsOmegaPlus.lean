module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def OmegaPlusFrame {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ)
    (S : Sylow 2 ↥H) (Tstar : Subgroup (MulAut W)) : Prop :=
  2 ≤ n ∧ NatOmegaPlus H ⊤ ⊥ 4 n ∧
    Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) ∧ IsPGroup 2 ↥Tstar ∧
    (S : Subgroup ↥H).map H.subtype ≤ Tstar ∧
    ∀ t ∈ Tstar, ∀ w ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype), t w = w

@[expose] def KOmPlus : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ) (S : Sylow 2 ↥H)
    (Tstar : Subgroup (MulAut W)), OmegaPlusFrame H n S Tstar →
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧ ∃ a ∈ H, ∃ b ∈ H, ∃ w ∈ H,
      orderOf a = r ∧ orderOf b = r ∧ a * b = b * a ∧
        (∀ x ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype), a x = x) ∧
        (CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype)).map
            (b : MulAut W).toMonoidHom =
          CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) ∧
        (∃ x ∈ CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype), b x ≠ x) ∧
        w * w = 1 ∧ w * a * w⁻¹ = a⁻¹ ∧ w * b * w⁻¹ = b⁻¹ ∧
        (CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype)).map
            (w : MulAut W).toMonoidHom ≠
          CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) ∧
        ((zpowers a : Set (MulAut W)) * (Tstar : Set (MulAut W)) =
          (Tstar : Set (MulAut W)) * (zpowers a : Set (MulAut W)))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
