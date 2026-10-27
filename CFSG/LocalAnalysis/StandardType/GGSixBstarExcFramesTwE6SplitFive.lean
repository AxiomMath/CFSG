module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeylTransport
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedNormalForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional

namespace ExcFrames

section TwE6SplitFiveHyp


@[expose] def TwistedE6FiveSCUnique : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → 5 ∣ 2 ^ f + 1 →
    ∀ {A A' : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))},
      IsElemAbelian 5 A → 5 ^ 4 ≤ Nat.card A →
      (∀ c ∈ Subgroup.centralizer (A : Set
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 5 = 1 →
          c ∈ A) →
      IsElemAbelian 5 A' → 5 ^ 4 ≤ Nat.card A' →
      (∀ c ∈ Subgroup.centralizer (A' : Set
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 5 = 1 →
          c ∈ A') →
        ∃ c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
          A' = A.map (MulAut.conj c).toMonoidHom

@[expose] def TwistedE6FiveRefFrame : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → 5 ∣ 2 ^ f + 1 →
    ∃ (A₀ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (ι₀ : Multiplicative (Fin Tag.E6.rank → ZMod 5) →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      IsElemAbelian 5 A₀ ∧ 5 ^ 4 ≤ Nat.card A₀ ∧
      (∀ c ∈ Subgroup.centralizer (A₀ : Set
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 5 = 1 →
          c ∈ A₀) ∧
      Function.Injective ι₀ ∧ ι₀.range = A₀ ∧
        ∀ β : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
          β ^ 5 = 1 → (∀ b ∈ A₀, β b ∈ A₀) →
            ∃ w : WeylGroup .E6, ∀ s : Fin Tag.E6.rank → ZMod 5,
              β (ι₀ (Multiplicative.ofAdd s)) =
                ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 w s))

end TwE6SplitFiveHyp

section TwE6SplitFive


theorem exists_weylFrame_aut_twistedE6_five (hU : TwistedE6FiveSCUnique)
    (hE : TwistedE6FiveRefFrame) {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1)
    {A : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hA : IsElemAbelian 5 A) (h4 : 5 ^ 4 ≤ Nat.card A)
    (hSC : ∀ c ∈ Subgroup.centralizer (A : Set
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 5 = 1 →
        c ∈ A) :
    ∃ ι : Multiplicative (Fin Tag.E6.rank → ZMod 5) →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      Function.Injective ι ∧ ι.range = A ∧
        ∀ α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
          α ^ 5 = 1 → (∀ a ∈ A, α a ∈ A) →
            ∃ w : WeylGroup .E6, ∀ s : Fin Tag.E6.rank → ZMod 5,
              α (ι (Multiplicative.ofAdd s)) =
                ι (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 w s)) := by
  obtain ⟨A₀, ι₀, hA₀, hA₀4, hA₀SC, hι₀, hrange, hframe⟩ := hE hf h5
  obtain ⟨c, hc⟩ := hU hf h5 hA₀ hA₀4 hA₀SC hA h4 hSC
  exact exists_weylFrame_of_conj (τ := .E6) (p := 5) ι₀ hι₀ hrange hc hframe

end TwE6SplitFive

end ExcFrames

end CFSG.StandardType
