module

public import CFSG.LocalAnalysis.StandardType.GGD5TwistFacts
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosAmb
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def lup10ab_tau : Fin 5 → Fin 5 := ![3, 2, 4, 1, 0]

@[expose] def lup10d_LabelData {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs : Subgroup G) (x : G) (L J : Subgroup G) {y : G} {K : Subgroup G}
    (M : GGQTwoAmbModel p Bs x y L (L ⊔ K)) : Prop :=
  p ∣ Nat.card J ∧
    Nat.Coprime p (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore p ↥J))) ∧
    ggAutomizer J Bs = Subgroup.closure (M.simple '' {k : M.ι | k ≠ M.a ∧ k ≠ M.b}) ∧
    (∀ b ∈ Bs, ∃ j ∈ J, ∀ k ∈ J, b * k * b⁻¹ = j * k * j⁻¹)

@[expose] def lup10d_SCData {G : Type} [Group G] (Bs J : Subgroup G) : Prop :=
  (Bs ⊓ J) ⊔ (Bs ⊓ Subgroup.centralizer (J : Set G)) = Bs ∧
    (Bs ⊓ J) ⊓ (Bs ⊓ Subgroup.centralizer (J : Set G)) = ⊥ ∧
    Nat.card ↥(Bs ⊓ J) = 27

end CFSG.StandardType

end
