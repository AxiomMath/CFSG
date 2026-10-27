module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRepNoSingle

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSLBstarFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
      GGSixStepOne p B Bs x L D J → p ∣ 2 ^ f - 1 →
        ∃ A₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
          ∀ b ∈ Bs, SLRep.GGFrameDiag (SLRep.ggFrame ψ A₀) b

@[expose] def GGSixRootFusionSLRepNonsplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
      GGSixStepOne p B Bs x L D J → GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .PSL (m + 1) f).D .PSL ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) → ¬ p ∣ 2 ^ f - 1 →
          ∀ l : ℕ, 2 ≤ l → 2 * l ≤ m + 1 →
            GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .PSL f r
              (ψ (ggInvSL (m + 1) l (GaloisField 2 f)))

@[expose] def GGSixRootFusionSLRepResidualInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSL (m + 1) f).D .PSL (m + 1) f ψ →
      GGSixStepOne p B Bs x L D J → GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .PSL (m + 1) f).D .PSL ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) → p ∣ 2 ^ f - 1 → p ∣ m + 1 →
          ∀ A₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
            (∀ b ∈ Bs, SLRep.GGFrameDiag (SLRep.ggFrame ψ A₀) b) →
            (∀ b ∈ Bs, ¬ SLRep.GGFrameSingle (SLRep.ggFrame ψ A₀) b) →
          ∀ l : ℕ, 2 ≤ l → m + 1 = 2 * l →
            GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .PSL f r
              (ψ (ggInvSL (m + 1) l (GaloisField 2 f)))

theorem ggSixRootFusionSLRepInput_of_frame (hF : GGSLBstarFrameInput)
    (hN : GGSixRootFusionSLRepNonsplitInput) (hR : GGSixRootFusionSLRepResidualInput) :
    GGSixRootFusionSLRepInput := by
  intro G _ _ p B Bs x L D J m f ψ hctx s1 s2 E r hch hC hodd l hl2 hlm
  by_cases hsplit : p ∣ 2 ^ f - 1
  swap
  · exact hN G p B Bs x L D J m f ψ hctx s1 s2 E r hch hC hodd hsplit l hl2 hlm
  obtain ⟨A₀, hframe⟩ := hF G p B Bs x L D J m f ψ hctx s1 hsplit
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hcardF]; exact hsplit
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hcardF]
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have h2 := Nat.le_of_dvd (by omega) hsplit
    have h3 := hp.two_le
    omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hc : SLRep.FrameCtx p B Bs (ggG0 p B x L D J) ψ A₀ :=
    ⟨hctx.2.1, hker, hrange, s1.1, hframe, hp, hp2, hpF, h4⟩
  have hle : ggG0 p B x L D J ≤ ggM p B x L D J := Subgroup.le_normalizer
  have hcent' : Subgroup.centralizer ((SLRep.ggFrame ψ A₀).range : Set G) = ⊥ := by
    have h := (SLRep.range_ggFrame ψ A₀).trans hrange
    rw [h]
    exact s1.1
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hm4 : 4 ≤ m := by
    have hBs := SLRep.card_le_of_frame hp hpF (SLRep.ker_ggFrame_le hker A₀) hcent' (X := Bs)
      (fun b hb => hctx.2.1.2.1.2 b hb) hframe (S := {0}) (i₀ := 0)
      (fun b _ D t _ _ i hi => by rw [Finset.mem_singleton.mp hi])
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton] at hBs
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hBs)
    omega
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpF
  rcases Nat.lt_or_ge (2 * l) (m + 1) with hk | hk
  · by_cases hpn : p ∣ m + 1
    · rcases Nat.lt_or_ge (2 * l + 1) (m + 1) with hk2 | hk2
      · exact SLRep.ggRootFusionWitnessAlt_mid_two hc hle hζ hl2 (by omega)
      · by_cases hsingle : ∃ b₁ ∈ Bs, SLRep.GGFrameSingle (SLRep.ggFrame ψ A₀) b₁
        · obtain ⟨b₁, hb₁, hs⟩ := hsingle
          exact SLRep.ggRootFusionWitnessAlt_single_mid hc hle hl2 hk hb₁ hs
        · simp only [not_exists, not_and] at hsingle
          have hn7 : 7 ≤ m + 1 := by
            have hBs := SLRep.card_le_of_frame_of_not_single hp hpF (SLRep.ker_ggFrame_le hker A₀)
              hcent' (X := Bs) (fun b hb => hctx.2.1.2.1.2 b hb) hframe (S := {0}) (i₀ := 0)
              (fun b _ D t _ _ i hi => by rw [Finset.mem_singleton.mp hi]) hsingle
              (j₀ := ⟨1, by omega⟩) (by simp [Fin.ext_iff])
            rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton] at hBs
            have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hBs)
            omega
          exact SLRep.ggRootFusionWitnessAlt_odd_nosingle hc hle hζ hl2 (by omega) hn7 hsingle
    · exact SLRep.ggRootFusionWitnessAlt_mid_coprime hc hle hζ hl2 hk hpn
  · have hn : m + 1 = 2 * l := by omega
    by_cases hpn : p ∣ m + 1
    · by_cases hsingle : ∃ b₁ ∈ Bs, SLRep.GGFrameSingle (SLRep.ggFrame ψ A₀) b₁
      · obtain ⟨b₁, hb₁, hs⟩ := hsingle
        exact SLRep.ggRootFusionWitnessAlt_single_pair hc hle hl2 hn (by omega) hb₁ hs
      · simp only [not_exists, not_and] at hsingle
        exact hR G p B Bs x L D J m f ψ hctx s1 s2 E r hch hC hodd hsplit hpn A₀ hframe
          hsingle l hl2 hn
    · exact SLRep.ggRootFusionWitnessAlt_pair_coprime hc hle hζ hl2 hn (by omega) hpn

end Inputs

end CFSG.StandardType
