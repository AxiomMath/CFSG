module

import CFSG.RankThree.PartTwo.Sec17.Item17Res2ProofX
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofTwenty
public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofKb

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

namespace Proof17Res14

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem normalizer_le_M_of_mem_omegaA (h : Sec17Std G A c L Y₀)
    (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀) {b : G}
    (hbΩ : Subgroup.zpowers b ∈ omegaA A) :
    Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Y₀ : Set G) := by
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  rcases h1514 Y₀ h.mem_y0Star hMeets with
    ⟨-, -, hΩ, -, -⟩ | ⟨-, -, hT, -⟩ | ⟨-, -, -, -, hno, -⟩
  · rw [hΩ, Set.mem_singleton_iff] at hbΩ
    rw [hbΩ]
    exact h.normalizer_c_le
  · obtain ⟨w, hwA, hbw⟩ := hT.2 _ hbΩ
    have hwM : w ∈ M := h.normalizer_le hwA
    rw [hbw, ← Subgroup.map_equiv_normalizer_eq]
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hwM (h.normalizer_c_le hx)) (M.inv_mem hwM)
  · exact absurd h.le_y0 (hno Y₀ h.mem_y0Star)

end Proof17Res14

open Proof17Res14 in
theorem step174KbOOmega_holds (h146 : Item146S14) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) : Step174KbOOmega := by
  intro G _ _ A c L Y₀ h hA10 X hXΔ hX3 K hK _ _ hcen hAK _ b hb _ hbΩ _ _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  set J := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) with hJdef
  have hDM : D ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (delta_le _).trans ((centralizer_singleton_le_normalizer_zpowers b).trans
      (normalizer_le_M_of_mem_omegaA h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h) hbΩ))
  obtain ⟨-, hJD⟩ :=
    perfectResidual_mem_scriptQ h (h146 G A c L h.toSec14Std) hXΔ hX3 hK hAK hb.1
  have hJK : J ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  have hJC : J ≤ cQuot Y₀ := fun x hx => by
    rw [← SetLike.mem_coe, coe_cQuot]
    exact hcen (hJK hx)
  have hC3 := Proof17Res2.not_three_dvd_card_cQuot h hA10
  have hDC : D ≤ Subgroup.normalizer ((D ⊓ cQuot Y₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer
      (hDM.trans (HeadProof.normalizer_le_normalizer_cQuot Y₀))
  refine (le_inf hJD hJC).trans (le_pPrimeCoreOf inf_le_left hDC ?_)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
    hC3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))

end CFSG.RankThree.PartTwo.Sec17
