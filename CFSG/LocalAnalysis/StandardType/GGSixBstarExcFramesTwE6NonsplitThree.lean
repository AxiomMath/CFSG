module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeylTransport
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedNormalForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

namespace ExcFrames

section TwE6NonsplitThreeHyp


@[expose] def TwistedE6ThreeSCUnique : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → ¬ 3 ∣ 2 ^ f + 1 →
    ∀ {A A' : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))},
      IsElemAbelian 3 A → 3 ^ 4 ≤ Nat.card A →
      (∀ c ∈ Subgroup.centralizer (A : Set
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
          c ∈ A) →
      IsElemAbelian 3 A' → 3 ^ 4 ≤ Nat.card A' →
      (∀ c ∈ Subgroup.centralizer (A' : Set
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
          c ∈ A') →
        ∃ c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
          A' = A.map (MulAut.conj c).toMonoidHom

@[expose] def TwistedE6ThreeRefFrame : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → ¬ 3 ∣ 2 ^ f + 1 →
    ∃ (A₀ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      IsElemAbelian 3 A₀ ∧ 3 ^ 4 ≤ Nat.card A₀ ∧
      (∀ c ∈ Subgroup.centralizer (A₀ : Set
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
          c ∈ A₀) ∧
      Function.Injective ι₀ ∧ ι₀.range = A₀ ∧
        ∀ β : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
          β ^ 3 = 1 → (∀ b ∈ A₀, β b ∈ A₀) →
            ∃ w : WeylGroup .F4, ∀ s : Fin Tag.F4.rank → ZMod 3,
              β (ι₀ (Multiplicative.ofAdd s)) =
                ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w s))

end TwE6NonsplitThreeHyp

section TwE6NonsplitThree


theorem exists_weylFrame_aut_twistedE6_three (hU : TwistedE6ThreeSCUnique)
    (hE : TwistedE6ThreeRefFrame) {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {A : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hA : IsElemAbelian 3 A) (h4 : 3 ^ 4 ≤ Nat.card A)
    (hSC : ∀ c ∈ Subgroup.centralizer (A : Set
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
        c ∈ A) :
    ∃ ι : Multiplicative (Fin Tag.F4.rank → ZMod 3) →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      Function.Injective ι ∧ ι.range = A ∧
        ∀ α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
          α ^ 3 = 1 → (∀ a ∈ A, α a ∈ A) →
            ∃ w : WeylGroup .F4, ∀ s : Fin Tag.F4.rank → ZMod 3,
              α (ι (Multiplicative.ofAdd s)) =
                ι (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w s)) := by
  obtain ⟨A₀, ι₀, hA₀, hA₀4, hA₀SC, hι₀, hrange, hframe⟩ := hE hf h3
  obtain ⟨c, hc⟩ := hU hf h3 hA₀ hA₀4 hA₀SC hA h4 hSC
  exact exists_weylFrame_of_conj (τ := .F4) (p := 3) ι₀ hι₀ hrange hc hframe

end TwE6NonsplitThree

end ExcFrames

end CFSG.StandardType
