module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Rows
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Gen
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
public import CFSG.RankThree.PartTwo.Sec4.Item47Native
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.Sporadic.ONOddCore.OuterOrder
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Sporadic.Presentation.McLExact

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec6.BThreeCensus (suzukiOrder card_eq_suzukiOrder le_of_suzukiOrder_dvd)

theorem card_mulAut_dvd_of_outer_dvd {X : Type} [Group X] [Finite X] {k : ℕ}
    (hk : Nat.card (Outer X) ∣ k) : Nat.card (MulAut X) ∣ k * Nat.card X := by
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  have hinner :
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) ∣ Nat.card X := by
    have h1 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) =
        Nat.card (X ⧸ (MulAut.conj : X →* MulAut X).ker) :=
      (Nat.card_congr
        (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X)).toEquiv).symm
    rw [h1]
    exact Subgroup.card_quotient_dvd_card _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.ComponentClassification.OuterAutomorphisms.inner X)]
  exact mul_dvd_mul hk hinner

theorem card_outer_dvd_two_of_le_two {X : Type} [Group X] [Finite X]
    (h : Nat.card (Outer X) ≤ 2) : Nat.card (Outer X) ∣ 2 := by
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  rcases (by omega : Nat.card (Outer X) = 1 ∨ Nat.card (Outer X) = 2) with h1 | h1 <;>
    rw [h1] <;> norm_num

theorem noSzSection_of_suzukiOrder_spor {M : Type} [Group M]
    [Finite M] {N : ℕ} (hMN : Nat.card M ∣ N) (hN : ∀ a : ℕ, 1 ≤ a → ¬ suzukiOrder a ∣ N) :
    CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection M := by
  intro X L _ p f hS
  have hS2 : CFSG.Blueprint.SuzukiModel (X ⧸ L) 2 f := by
    unfold CFSG.Blueprint.SuzukiModel at hS ⊢
    obtain ⟨hp, hrest⟩ := hS
    subst hp
    exact ⟨rfl, hrest⟩
  obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder hS2
  apply hN a ha
  rw [← hcard]
  exact ((Subgroup.card_quotient_dvd_card L).trans (Subgroup.card_subgroup_dvd_card X)).trans hMN

theorem not_suzukiOrder_dvd_of_check {N B : ℕ} (hN0 : 0 < N) (hB : N < 2 ^ (4 * B + 6))
    (h : ∀ a ∈ Finset.Icc 1 B, ¬ suzukiOrder a ∣ N) : ∀ a : ℕ, 1 ≤ a → ¬ suzukiOrder a ∣ N :=
  fun a ha hdvd => h a (Finset.mem_Icc.mpr ⟨ha, le_of_suzukiOrder_dvd hN0 hB hdvd⟩) hdvd

section Row143


theorem rowOf143_of_outer_dvd {X : Type} [Group X] [Finite X] {k : ℕ}
    (hout : Nat.card (Outer X) ∣ k) (hN : ∀ a : ℕ, 1 ≤ a → ¬ suzukiOrder a ∣ k * Nat.card X) :
    RowOf143 X := by
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  intro S _ _ _ _ ⟨e⟩ _
  have hX : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection (MulAut X) :=
    noSzSection_of_suzukiOrder_spor (card_mulAut_dvd_of_outer_dvd hout) hN
  exact row143_of_noSzSection
    (CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_mulAut_of_mulEquiv e hX)

theorem rowOf143_spor_j3 :
    RowOf143 (Spor .J3) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .J3 ≃* Spor .J3 := b
  have hcard : Nat.card (Spor .J3) = 50232960 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  haveI : Finite (Spor .J3) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hle : Nat.card (Outer (Spor .J3)) ≤ 2 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.card_outer_J3
  refine rowOf143_of_outer_dvd (card_outer_dvd_two_of_le_two hle) ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 6) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_spor_j4 :
    RowOf143 (Spor .J4) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (Spor .J4) = 86775571046077562880 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  haveI : Finite (Spor .J4) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hout : Nat.card (Outer (Spor .J4)) = 1 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    exact CFSG.AGLEmbedding.card_outer_J4
  refine rowOf143_of_outer_dvd (k := 1) (by simp [hout]) ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 16) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_spor_ly :
    RowOf143 (Spor .Ly) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .Ly ≃* Spor .Ly := b
  have hcard : Nat.card (Spor .Ly) = 51765179004000000 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  haveI : Finite (Spor .Ly) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hle : Nat.card (Outer (Spor .Ly)) ≤ 2 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    rcases CFSG.RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> omega
  refine rowOf143_of_outer_dvd (card_outer_dvd_two_of_le_two hle) ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 13) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_spor_he
    : RowOf143 (Spor .He) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .He ≃* Spor .He := b
  have hcard : Nat.card (Spor .He) = 4030387200 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.He.card_He
  haveI : Finite (Spor .He) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hle : Nat.card (Outer (Spor .He)) ≤ 2 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    exact CFSG.Sporadic.Schreier.AT_He_Schreier.1
  refine rowOf143_of_outer_dvd (card_outer_dvd_two_of_le_two hle) ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 7) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_spor_on :
    RowOf143 (Spor .ONan) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .ONan ≃* Spor .ONan := b
  have hcard : Nat.card (Spor .ONan) = 460815505920 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  haveI : Finite (Spor .ONan) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : Nat.card (Outer (Spor .ONan)) ∣ 4 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    exact CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1
  refine rowOf143_of_outer_dvd hdvd ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 9) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_spor_co3 :
    RowOf143 (Spor .Co3) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .Co3 ≃* Spor .Co3 := b
  have hcard : Nat.card (Spor .Co3) = 495766656000 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.Co3.card_Co3
  haveI : Finite (Spor .Co3) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hout : Nat.card (Outer (Spor .Co3)) = 1 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    exact CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1
  refine rowOf143_of_outer_dvd (k := 1) (by simp [hout]) ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 9) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_spor_co2 :
    RowOf143 (Spor .Co2) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .Co2 ≃* Spor .Co2 := b
  have hcard : Nat.card (Spor .Co2) = 42305421312000 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.Co2.card_Co2
  haveI : Finite (Spor .Co2) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hout : Nat.card (Outer (Spor .Co2)) = 1 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    exact CFSG.RankThree.PartOne.SPOR.card_outer_Co2
  refine rowOf143_of_outer_dvd (k := 1) (by simp [hout]) ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 10) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_spor_hn :
    RowOf143 (Spor .HN) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .HN ≃* Spor .HN := b
  have hcard : Nat.card (Spor .HN) = 273030912000000 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.HN.card_HN
  haveI : Finite (Spor .HN) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hle : Nat.card (Outer (Spor .HN)) ≤ 2 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    exact (CFSG.RankThree.PartOne.SPOR.card_outer_HN).le
  refine rowOf143_of_outer_dvd (card_outer_dvd_two_of_le_two hle) ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 11) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_spor_mcl :
    RowOf143 (Spor .McL) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .McL ≃* Spor .McL := b
  have hcard : Nat.card (Spor .McL) = 898128000 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.McL.card_McL
  haveI : Finite (Spor .McL) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hle : Nat.card (Outer (Spor .McL)) ≤ 2 := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence b').toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.card_outer_McL
  refine rowOf143_of_outer_dvd (card_outer_dvd_two_of_le_two hle) ?_
  rw [hcard]
  exact not_suzukiOrder_dvd_of_check (B := 7) (by norm_num) (by norm_num) (by decide)

end Row143

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
