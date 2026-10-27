module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Inputs

@[expose] def GGSUBstarFrameInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n (f + 1)).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ →
      GGSixStepOne p B Bs x L D J → p ∣ 2 ^ (f + 1) + 1 →
        ∃ (P : GL (Fin n) (GaloisField 2 (2 * (f + 1))))
          (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
              (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n),
          ∀ b ∈ Bs, SURep.GGFrameDiagU (SURep.ggFrameU
            (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) b

@[expose] def GGSixRootFusionSURepNonsplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n (f + 1)).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ →
      GGSixStepOne p B Bs x L D J → GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .PSU n (f + 1)).D .PSU ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) → ¬ p ∣ 2 ^ (f + 1) + 1 →
          ∀ l : ℕ, 2 ≤ l → 2 * l ≤ n →
            GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .PSU (f + 1) r
              (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n l))

@[expose] def GGSixRootFusionSURepResidualInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n (f + 1)).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ →
      GGSixStepOne p B Bs x L D J → GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .PSU n (f + 1)).D .PSU ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) → p ∣ 2 ^ (f + 1) + 1 → p ∣ n →
          ∀ (P : GL (Fin n) (GaloisField 2 (2 * (f + 1))))
            (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
              (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
                (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n),
            (∀ b ∈ Bs, SURep.GGFrameDiagU (SURep.ggFrameU
              (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) b) →
            (∀ b ∈ Bs, ¬ SURep.GGFrameSingleU (SURep.ggFrameU
              (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) b) →
          ∀ l : ℕ, 2 ≤ l → n = 2 * l →
            GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .PSU (f + 1) r
              (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n l))

theorem ggSixRootFusionSURepInput_of_frame (hF : GGSUBstarFrameInput)
    (hN : GGSixRootFusionSURepNonsplitInput) (hR : GGSixRootFusionSURepResidualInput) :
    GGSixRootFusionSURepInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 s2 E r hch hC hodd l hl2 hln
  by_cases hsplit : p ∣ 2 ^ (f + 1) + 1
  swap
  · exact hN G p B Bs x L D J n f ψ hctx s1 s2 E r hch hC hodd hsplit l hl2 hln
  obtain ⟨P, hP, hframe⟩ := hF G p B Bs x L D J n f ψ hctx s1 hsplit
  set hK := card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f) with hKdef
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hdata : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hn4 : 4 ≤ n := by omega
  have hrangeφ : (SURep.ggFrameU hK ψ P hP).range = ggG0 p B x L D J :=
    (SURep.range_ggFrameU hK ψ P hP).trans hrange
  have hcent' : Subgroup.centralizer ((SURep.ggFrameU hK ψ P hP).range : Set G) = ⊥ := by
    rw [hrangeφ]
    exact s1.1
  have hFk : SURep.GGFrameKer (SURep.ggFrameU hK ψ P hP) :=
    SURep.ggFrameKer_ggFrameU hK ψ P hP (by omega)
      (fun h => by have h1 : n = 3 := congrArg Prod.fst h; omega) hker
  have hpF : p ∣ Nat.card (GaloisField 2 (2 * (f + 1))) - 1 := by
    rw [hK, show (1 : ℕ) = 1 ^ 2 from rfl, Nat.sq_sub_sq]
    exact Dvd.dvd.mul_right hsplit _
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hn5 : 5 ≤ n := by
    have hBs := SURep.card_le_of_frameU hp hpF hdata (by omega) hFk hcent' (X := Bs)
      (fun b hb => hctx.2.1.2.1.2 b hb) hframe (S := {⟨0, by omega⟩}) (i₀ := ⟨0, by omega⟩)
      (fun b _ τ _ i hi => congrArg τ (Finset.mem_singleton.mp hi))
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton] at hBs
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hBs)
    omega
  have hc : SURep.FrameCtxU p B Bs (ggG0 p B x L D J) hK ψ P hP :=
    ⟨hdata, hctx.2.1, hker, hrange, s1.1, hframe, hp, hp2, hsplit, hn5⟩
  have hle : ggG0 p B x L D J ≤ ggM p B x L D J := Subgroup.le_normalizer
  obtain ⟨ζ, hζ, -⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hdata hp hsplit
  rcases Nat.lt_or_ge (2 * l) n with hk | hk
  · by_cases hpn : p ∣ n
    · rcases Nat.lt_or_ge (2 * l + 1) n with hk2 | hk2
      · exact SURep.ggRootFusionWitnessAlt_mid_twoU hc hle hζ hl2 (by omega)
      · by_cases hsingle : ∃ b₁ ∈ Bs, SURep.GGFrameSingleU (SURep.ggFrameU hK ψ P hP) b₁
        · obtain ⟨b₁, hb₁, hs⟩ := hsingle
          exact SURep.ggRootFusionWitnessAlt_single_midU hc hle hk hb₁ hs
        · simp only [not_exists, not_and] at hsingle
          have hn7 : 7 ≤ n := by
            have hBs := SURep.card_le_of_frameU_of_not_single hp hpF hdata (by omega) hFk hcent'
              (X := Bs) (fun b hb => hctx.2.1.2.1.2 b hb) hframe (S := {⟨0, by omega⟩})
              (i₀ := ⟨0, by omega⟩) (fun b _ τ _ i hi => congrArg τ (Finset.mem_singleton.mp hi))
              hsingle (j₀ := ⟨1, by omega⟩) (by simp [Fin.ext_iff])
            rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton] at hBs
            have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans hBs)
            omega
          exact SURep.ggRootFusionWitnessAlt_odd_nosingleU hc hle hζ (by omega) hn7 hsingle
    · exact SURep.ggRootFusionWitnessAlt_mid_coprimeU hc hle hζ hk hpn
  · have hn : n = 2 * l := by omega
    by_cases hpn : p ∣ n
    · by_cases hsingle : ∃ b₁ ∈ Bs, SURep.GGFrameSingleU (SURep.ggFrameU hK ψ P hP) b₁
      · obtain ⟨b₁, hb₁, hs⟩ := hsingle
        exact SURep.ggRootFusionWitnessAlt_single_pairU hc hle hl2 hn hb₁ hs
      · simp only [not_exists, not_and] at hsingle
        exact hR G p B Bs x L D J n f ψ hctx s1 s2 E r hch hC hodd hsplit hpn P hP hframe
          hsingle l hl2 hn
    · exact SURep.ggRootFusionWitnessAlt_pair_coprimeU hc hle hζ hl2 hn hpn

end Inputs

end CFSG.StandardType
