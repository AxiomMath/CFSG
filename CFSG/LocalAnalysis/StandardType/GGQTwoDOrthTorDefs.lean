module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Assembly

section Tor

variable {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}

@[expose] def OrthFrameCore.torC (Φ : OrthFrameCore p Bs X) (t : Φ.V ≃ₗ[Φ.F] Φ.V) :
    Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
  orthDerived Φ.Q ⊓ Subgroup.centralizer ({t} : Set (Φ.V ≃ₗ[Φ.F] Φ.V))

@[expose] def OrthFrameCore.TorFactor (Φ : OrthFrameCore p Bs X)
    (P : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) : Prop :=
  Group.IsSolvable ↥P ∨
    (IsQuasisimple ↥P ∧
      (∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥P ⧸ Subgroup.center ↥P) ∧ lab.n = 1 ∧ lab.tag ≠ .A ∧
          (lab.tag = .twD → lab.rank ≠ 2)) ∧
      ∃ x y : OmPlusIdx Φ.r,
        omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x ∧ Φ.rank2 x y ≤ P)

@[expose] def OrthFrameCore.TorStruct (Φ : OrthFrameCore p Bs X)
    (t : Φ.V ≃ₗ[Φ.F] Φ.V) : Prop :=
  ∃ P₀ P₁ : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V), P₀ ≤ Φ.torC t ∧ P₁ ≤ Φ.torC t ∧
    (P₀.subgroupOf (Φ.torC t)).Normal ∧ (P₁.subgroupOf (Φ.torC t)).Normal ∧
    (∀ a ∈ P₀, ∀ b ∈ P₁, a * b = b * a) ∧
    (∀ K : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V), K ≤ Φ.torC t → ⁅K, K⁆ = K → K ≤ P₀ ⊔ P₁) ∧
    Φ.TorFactor P₀ ∧ Φ.TorFactor P₁

end Tor

end OrthTorus

end CFSG.StandardType

end
