module

public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Q8
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63ActCfg

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTwE6TwoThreeActionOddInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 →
    ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* TwE6Delta.RecipeR K 1),
      Function.Surjective ψ₁ → ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ →
      Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ φ ∈ TwE6Delta.RecipeI K 1, ∀ l : L₁, φ (ψ₁ l) = ψ₁ (a l)) →
        3 ^ 5 ≤ Nat.card A₁ → GGTorusSelfCent 3 A₁ → U63TB.ActConcl 3 A₁

theorem ggTableBActionSCrW_twE6Two (hO : GGTwE6TwoThreeActionOddInput) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    U63TB.GGTableBActionSCrW 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1) := by
  refine ⟨by norm_num, fun L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc => ?_⟩
  exact U63TB.actConclW_descent hker hψ hperf hA hAI hsc
    (fun L₁ _ _ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ hc hsc₁ =>
      hO K hK L₁ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ (by rw [hc]; exact hr) hsc₁)

section Certs


theorem largeEvenLabelAll_twE6TwoThree_actW {p : ℕ} {lab : LargeEvenLabel}
    (hO : GGTwE6TwoThreeActionOddInput) (h : GGTableBTwE6TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => U63TB.GGTableBActionSCrW 3 5 R I := by
  obtain ⟨ht, hn, -⟩ := h
  exact TwE6Delta.labelAll ht fun K _ _ hK' => by
    rw [hn] at hK' ⊢
    exact ggTableBActionSCrW_twE6Two hO hK'

theorem ggBstarInnerDiagLInputOn_twE6TwoThree :
    GGBstarInnerDiagLInputOn GGTableBTwE6TwoThreeLabel :=
  CorFourTwoOpen.ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds
    (S := GGTableBTwE6TwoThreeLabel) (fun p lab hp hlab hs => by
      obtain ⟨ht, hn, rfl⟩ := hs
      exact TwE6TB.largeEvenLabelAll_pow_mem hp (by norm_num) hlab ht (by rw [hn]; norm_num))

theorem ggTableBActionInputOn_twE6TwoThree
    (hB : GGTwE6ThreeBstarRankInput) (hO : GGTwE6TwoThreeActionOddInput) :
    GGTableBActionInputOn GGTableBTwE6TwoThreeLabel := by
  intro G _ _ p B Bs x L D J B₂ hcfg hM hMod
  have hMB := ggBstarInnerDiagLInputOn_twE6TwoThree G p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTableBTwE6TwoThreeLabel p lab)
    (P' := fun R _ I _ => U63TB.GGTableBActionSCrW 3 5 R I)
    (fun lab _ hs => largeEvenLabelAll_twE6TwoThree_actW hO hs)
    (fun _ _ _ _ _ _ hP => hP.1) hMB
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, -, hp3⟩, -, hBsN, h3⟩, hT⟩ :=
    largeEvenRawDatum_exists hraw
  subst hp3
  have h5 := hB G _ B Bs x L D J hcfg (hMB.mono fun p lab (h : GGTableBTwE6TwoThreeLabel p lab) =>
    (⟨h.1, h.2.2, by rw [h.2.1]; norm_num⟩ : GGTableBTwE6ThreeLabel p lab)) hBsN
  have h3' : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h5
  exact U63TB.ggTableBAction_of_cardW hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h5 h3' hT hMod

end Certs

end CFSG.StandardType

end
