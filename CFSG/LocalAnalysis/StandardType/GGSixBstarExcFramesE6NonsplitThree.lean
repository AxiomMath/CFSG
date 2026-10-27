module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeylTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

namespace ExcFrames

section E6ThreeHyp

def E6ThreeSCUnique : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K + 1 →
    ∀ {A A' : Subgroup (adjointGroup .E6 K)},
      IsElemAbelian 3 A → 3 ^ 4 ≤ Nat.card A →
      (∀ c ∈ Subgroup.centralizer (A : Set (adjointGroup .E6 K)), c ^ 3 = 1 → c ∈ A) →
      IsElemAbelian 3 A' → 3 ^ 4 ≤ Nat.card A' →
      (∀ c ∈ Subgroup.centralizer (A' : Set (adjointGroup .E6 K)), c ^ 3 = 1 → c ∈ A') →
        ∃ c : adjointGroup .E6 K, A' = A.map (MulAut.conj c).toMonoidHom

def E6ThreeRefFrame : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K + 1 →
    ∃ (A₀ : Subgroup (adjointGroup .E6 K))
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup .E6 K),
      IsElemAbelian 3 A₀ ∧ 3 ^ 4 ≤ Nat.card A₀ ∧
      (∀ c ∈ Subgroup.centralizer (A₀ : Set (adjointGroup .E6 K)), c ^ 3 = 1 → c ∈ A₀) ∧
      Function.Injective ι₀ ∧ ι₀.range = A₀ ∧
        ∀ β : MulAut (adjointGroup .E6 K), β ^ 3 = 1 → (∀ b ∈ A₀, β b ∈ A₀) →
          ∃ w : WeylGroup .F4, ∀ s : Fin Tag.F4.rank → ZMod 3,
            β (ι₀ (Multiplicative.ofAdd s)) =
              ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w s))

end E6ThreeHyp

section E6NonsplitThree

theorem exists_weylFrame_aut_E6_three (hU : E6ThreeSCUnique) (hE : E6ThreeRefFrame)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 3 ∣ Nat.card K + 1) {A : Subgroup (adjointGroup .E6 K)} (hA : IsElemAbelian 3 A)
    (h4 : 3 ^ 4 ≤ Nat.card A)
    (hSC : ∀ c ∈ Subgroup.centralizer (A : Set (adjointGroup .E6 K)), c ^ 3 = 1 → c ∈ A) :
    ∃ ι : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup .E6 K,
      Function.Injective ι ∧ ι.range = A ∧
        ∀ α : MulAut (adjointGroup .E6 K), α ^ 3 = 1 → (∀ a ∈ A, α a ∈ A) →
          ∃ w : WeylGroup .F4, ∀ s : Fin Tag.F4.rank → ZMod 3,
            α (ι (Multiplicative.ofAdd s)) = ι (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w s)) := by
  obtain ⟨A₀, ι₀, hA₀, hA₀4, hA₀SC, hι₀, hrange, hframe⟩ := hE hq
  obtain ⟨c, hc⟩ := hU hq hA₀ hA₀4 hA₀SC hA h4 hSC
  exact exists_weylFrame_of_conj (τ := .F4) (p := 3) ι₀ hι₀ hrange hc hframe

end E6NonsplitThree

end ExcFrames

end CFSG.StandardType
