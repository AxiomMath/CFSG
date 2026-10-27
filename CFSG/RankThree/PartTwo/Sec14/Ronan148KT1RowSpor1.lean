module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Rows
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Gen
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.A38c9Out
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Bridge.M24Surj
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.PairJ2Pairs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.RankThree.PartTwo.Sec6.BThreeCensus (suzukiOrder le_of_suzukiOrder_dvd)

theorem card_eq_suzukiOrder_gen {T : Type} [Group T] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel T p f) : ∃ a, 1 ≤ a ∧ Nat.card T = suzukiOrder a := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  exact ⟨a, ha, by rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]; rfl⟩

theorem noSzSection_of_suzukiOrder_dvd {M : Type} [Group M] {N : ℕ}
    (hMN : Nat.card M ∣ N) (hN0 : 0 < N) (hN : N < 2 ^ (4 * 6 + 6))
    (h6 : ∀ a, 1 ≤ a → a ≤ 6 → ¬ suzukiOrder a ∣ N) :
    CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection M := by
  intro X Y _ p f hS
  obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder_gen hS
  have hdvd : suzukiOrder a ∣ N := by
    rw [← hcard]
    exact (Subgroup.card_quotient_dvd_card Y).trans ((Subgroup.card_subgroup_dvd_card X).trans hMN)
  exact h6 a ha (le_of_suzukiOrder_dvd hN0 hN hdvd) hdvd

theorem not_suzukiOrder_dvd_of_le_six {N : ℕ} (h13 : ¬ 13 ∣ N) (h31 : ¬ 31 ∣ N)
    (h127 : ¬ 127 ∣ N) (h73 : ¬ 73 ∣ N) (h89 : ¬ 89 ∣ N) (h8191 : ¬ 8191 ∣ N) (a : ℕ)
    (ha : 1 ≤ a) (ha6 : a ≤ 6) : ¬ suzukiOrder a ∣ N := by
  interval_cases a
  · exact fun h => h13 ((Nat.dvd_of_mod_eq_zero (by norm_num [suzukiOrder]) :
      13 ∣ suzukiOrder 1).trans h)
  · exact fun h => h31 ((Nat.dvd_of_mod_eq_zero (by norm_num [suzukiOrder]) :
      31 ∣ suzukiOrder 2).trans h)
  · exact fun h => h127 ((Nat.dvd_of_mod_eq_zero (by norm_num [suzukiOrder]) :
      127 ∣ suzukiOrder 3).trans h)
  · exact fun h => h73 ((Nat.dvd_of_mod_eq_zero (by norm_num [suzukiOrder]) :
      73 ∣ suzukiOrder 4).trans h)
  · exact fun h => h89 ((Nat.dvd_of_mod_eq_zero (by norm_num [suzukiOrder]) :
      89 ∣ suzukiOrder 5).trans h)
  · exact fun h => h8191 ((Nat.dvd_of_mod_eq_zero (by norm_num [suzukiOrder]) :
      8191 ∣ suzukiOrder 6).trans h)

theorem card_inner_dvd (X : Type) [Group X] :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) ∣ Nat.card X :=
  Subgroup.card_dvd_of_surjective (f := (MulAut.conj : X →* MulAut X).rangeRestrict)
    (MonoidHom.rangeRestrict_surjective _)

theorem card_mulAut_eq_inner_mul_outer (X : Type) [Group X] :
    Nat.card (MulAut X) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) * Nat.card (Outer X) :=
  (Subgroup.card_mul_index (CFSG.ComponentClassification.OuterAutomorphisms.inner X)).symm

theorem card_mulAut_dvd_two_mul_of_outer {X : Type} [Group X] [Finite X]
    (hO : Nat.card (Outer X) ≤ 2) : Nat.card (MulAut X) ∣ 2 * Nat.card X := by
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  haveI : Finite (Outer X) :=
    Finite.of_surjective (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X))
      (QuotientGroup.mk'_surjective _)
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  have hO2 : Nat.card (Outer X) ∣ 2 := by
    rcases (by omega : Nat.card (Outer X) = 1 ∨ Nat.card (Outer X) = 2) with h | h <;> simp [h]
  rw [card_mulAut_eq_inner_mul_outer X]
  calc Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) * Nat.card (Outer X)
      ∣ Nat.card X * 2 := Nat.mul_dvd_mul (card_inner_dvd X) hO2
    _ = 2 * Nat.card X := mul_comm _ _

theorem rowOf143_of_noSzSection_mulAut
    {X : Type} [Group X]
    (h : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection (MulAut X)) : RowOf143 X := by
  unfold RowOf143
  intro S _ _ _ _ ⟨e⟩ _
  exact row143_of_noSzSection
    (CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_mulAut_of_mulEquiv e h)

theorem rowOf143_of_card
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Nat.card X = n)
    (hO : Nat.card (Outer X) ≤ 2) (hn2 : 2 * n < 2 ^ (4 * 6 + 6))
    (hp : ¬ 13 ∣ 2 * n ∧ ¬ 31 ∣ 2 * n ∧ ¬ 127 ∣ 2 * n ∧ ¬ 73 ∣ 2 * n ∧ ¬ 89 ∣ 2 * n ∧
      ¬ 8191 ∣ 2 * n) : RowOf143 X := by
  subst hn
  have hpos : 0 < Nat.card X := Nat.card_pos
  refine rowOf143_of_noSzSection_mulAut (noSzSection_of_suzukiOrder_dvd
    (card_mulAut_dvd_two_mul_of_outer hO) (by omega) hn2 ?_)
  exact not_suzukiOrder_dvd_of_le_six hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2

theorem rowOf143_spor_m11 :
    RowOf143 (Spor .M11) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have b' : NativeSporadic.M11 ≃* Spor .M11 := b
  have hcard : Nat.card (Spor .M11) = 7920 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M11]
  have : Finite (Spor .M11) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (Spor .M11)) ≤ 2 := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.Sporadic.Schreier.at_m11_schreier.1
  exact rowOf143_of_card hcard hO (by norm_num) (by norm_num)

theorem rowOf143_spor_m12 :
    RowOf143 (Spor .M12) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : NativeSporadic.M12 ≃* Spor .M12 := b
  have hcard : Nat.card (Spor .M12) = 95040 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
  have : Finite (Spor .M12) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (Spor .M12)) ≤ 2 := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.ComponentClassification.M12Cover.card_outer.le
  exact rowOf143_of_card hcard hO (by norm_num) (by norm_num)

theorem rowOf143_spor_m22 :
    RowOf143 (Spor .M22) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : NativeSporadic.M22 ≃* Spor .M22 := b
  have hcard : Nat.card (Spor .M22) = 443520 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
  have : Finite (Spor .M22) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (Spor .M22)) ≤ 2 := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.RankThree.PartTwo.Sec4.card_outer_le_two_of_card_mulAut_le
      CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card
  exact rowOf143_of_card hcard hO (by norm_num) (by norm_num)

theorem rowOf143_spor_m23 :
    RowOf143 (Spor .M23) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : NativeSporadic.M23 ≃* Spor .M23 := b
  have hcard : Nat.card (Spor .M23) = 10200960 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Schreier.m23_card]
  have : Finite (Spor .M23) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (Spor .M23)) ≤ 2 := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.Sporadic.Schreier.at_m23_schreier.1
  exact rowOf143_of_card hcard hO (by norm_num) (by norm_num)

theorem rowOf143_spor_m24 :
    RowOf143 (Spor .M24) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .M24 ≃* Spor .M24 := b
  have hcard : Nat.card (Spor .M24) = 244823040 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
  have : Finite (Spor .M24) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (Spor .M24)) ≤ 2 := by
    rw [← Nat.card_congr (equivalence b').toEquiv, CFSG.Quasithin.A38c9.outer_card_M24]
    norm_num
  exact rowOf143_of_card hcard hO (by norm_num) (by norm_num)

theorem rowOf143_spor_j1 :
    RowOf143 (Spor .J1) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have b' : NativeSporadic.J1 ≃* Spor .J1 := b
  have hcard : Nat.card (Spor .J1) = 175560 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J1.card_J1]
  have : Finite (Spor .J1) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (Spor .J1)) ≤ 2 := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num)
  exact rowOf143_of_card hcard hO (by norm_num) (by norm_num)

theorem rowOf143_spor_j2 :
    RowOf143 (Spor .J2) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b' : NativeSporadic.J2 ≃* Spor .J2 := b
  have hcard : Nat.card (Spor .J2) = 604800 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.J2.card_J2]
  have : Finite (Spor .J2) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (Spor .J2)) ≤ 2 := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.Sporadic.Schreier.AT_J2_Schreier.1
  exact rowOf143_of_card hcard hO (by norm_num) (by norm_num)

theorem rowOf143_spor_hs :
    RowOf143 (Spor .HS) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .HS ≃* Spor .HS := b
  have hcard : Nat.card (Spor .HS) = 44352000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.HS.card_HS]
  have : Finite (Spor .HS) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (Spor .HS)) ≤ 2 := by
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.RankThree.PartOne.SPOR.card_outer_HS_le_two
  exact rowOf143_of_card hcard hO (by norm_num) (by norm_num)

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
