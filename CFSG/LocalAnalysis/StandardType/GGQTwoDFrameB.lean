module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameTau
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDFrame_not_c2 {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {n : ℕ} (hn : 3 ≤ n)
    (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs)
    (hmod : HdRo7C.C2CoordModel 3 Bs L n τ) : False := by
  let a₁ : Fin (n + 1) := ⟨1, by omega⟩
  let a₂ : Fin (n + 1) := ⟨2, by omega⟩
  have hne : a₁ ≠ a₂ := by
    intro h
    have hv : a₁.val = a₂.val := congrArg Fin.val h
    simp [a₁, a₂] at hv
  have ha₁ : 0 < a₁.val := by simp [a₁]
  have ha₂ : 0 < a₂.val := by simp [a₂]
  have hr₁A : ggLinInv (p := 3) (tauIota τ) (dNeg (n + 1) a₁) ∈
      ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (X := L) (Or.inl rfl)
      (ggLinInv_dNeg_mem_automizer_c2 τ hmod ha₁)
  have hr₂A : ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) false a₁ a₂) ∈
      ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (X := L) (Or.inl rfl)
      (ggLinInv_dTau_mem_automizer_c2 τ hmod false (a := a₁) (b := a₂) ha₁ ha₂ hne)
  have h₁ : ggLinInv (p := 3) (tauIota τ) (dNeg (n + 1) a₁) ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 hr₁A
      (ggIsReflection_ggLinInv_dNeg τ a₁)
  have h₂ : ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) false a₁ a₂) ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 hr₂A
      (ggIsReflection_ggLinInv_dTau τ false (a := a₁) (b := a₂) hne)
  exact not_pow_two_or_three_dNeg_mul_dTau τ (a := a₁) (b := a₂) hne
    (ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 h₁ h₂)

end CFSG.StandardType.QTwo

end
