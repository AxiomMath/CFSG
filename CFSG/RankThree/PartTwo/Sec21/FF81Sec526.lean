module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

section Conc

variable {G : Type} [Group G]

def FF81Conc5_2 (b b₁ b₂ b₃ s₀ : G) : Prop :=
  let A₁ := Subgroup.closure {b, b₁, b₂ * b₃}
  let H := CenS (Subgroup.closure {β' b₂ b₃, s₀}) ⊓ Nor A₁
  Nor A₁ = Subgroup.closure {β' b₂ b₃, s₀} ⊔ H ∧ A₁ ≤ H ∧ (CenS A₁).relIndex H = 48 ∧
    (∀ h ∈ H, ∀ x ∈ ({b * b₁, b * b₁ ^ 2, b₂ * b₃} : Set G), h * x * h⁻¹ ∈
      ({b * b₁, (b * b₁)⁻¹, b * b₁ ^ 2, (b * b₁ ^ 2)⁻¹, b₂ * b₃, (b₂ * b₃)⁻¹} : Set G)) ∧
    ∀ W : Subgroup G, W ≤ A₁ → IsElemAb 3 2 W → ∃ h ∈ H, h * b * h⁻¹ ∈ W

def FF81Conc5_4 (b b₁ b₂ b₃ s₀ : G) : Prop :=
  let J := OUp 3 (CenS (Subgroup.closure {b₂, b₃}))
  Nonempty (J ≃* Equiv.Perm (Fin 6)) ∧ J ≤ Cen s₀ ∧ b ∈ J ∧ b₁ ∈ J

def FF81Conc5_5 (s₀ : G) : Prop :=
  ∃ S₀ S₁ : Subgroup G, IsElemAb 2 6 S₀ ∧ IsExtraspecialPlus 4 S₁ ∧ S₀ ⊔ S₁ = Op 2 (Cen s₀) ∧
    S₀ ⊓ S₁ = ⊥ ∧ S₀ ≤ CenS S₁

def FF81Conc5_6 (b₂ b₃ s₀ : G) : Prop :=
  let J := OUp 3 (CenS (Subgroup.closure {b₂, b₃}))
  let S := Op 2 (Cen s₀)
  CenS (S ⊓ CenS S) = S ∧ IsElemAb 2 5 (S ⊓ Cen (b₂ * b₃)) ∧
    Cen s₀ ⊓ Cen (b₂ * b₃) = (S ⊓ Cen (b₂ * b₃)) ⊔ J ⊔ Subgroup.zpowers (b₂ * b₃)

end Conc

def FF81_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → ControlsFusionIn B → Opp 3 (Cen b) = ⊥ →
    FF81Conc5_2 b b₁ b₂ b₃ s₀

def FF81_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → ControlsFusionIn B → Opp 3 (Cen b) = ⊥ →
    FF81Conc5_2 b b₁ b₂ b₃ s₀ → FF81Conc5_4 b b₁ b₂ b₃ s₀ → FF81Conc5_5 s₀

def FF81_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → ControlsFusionIn B → Opp 3 (Cen b) = ⊥ →
    FF81Conc5_2 b b₁ b₂ b₃ s₀ → FF81Conc5_4 b b₁ b₂ b₃ s₀ → FF81Conc5_5 s₀ →
    FF81Conc5_6 b₂ b₃ s₀

theorem ff81_5_2_6_of (hKF : KF_Sp6Levi) (h2 : FF81_5_2) (h5 : FF81_5_5) (h6 : FF81_5_6) :
    FF81_5_2_6 := by
  intro G _ _ b L B b₁ b₂ b₃ t₀ s₀ hs h51
  have h53 := hs.opp_eq_bot
  have c2 := h2 G b L B b₁ b₂ b₃ t₀ s₀ hs h51 h53
  have c4 : FF81Conc5_4 b b₁ b₂ b₃ s₀ := hs.ff81_5_4 hKF
  have c5 := h5 G b L B b₁ b₂ b₃ t₀ s₀ hs h51 h53 c2 c4
  have c6 := h6 G b L B b₁ b₂ b₃ t₀ s₀ hs h51 h53 c2 c4 c5
  exact ⟨h53, c2, c4, c5, c6⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
