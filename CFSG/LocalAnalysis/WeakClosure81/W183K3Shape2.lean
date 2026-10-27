module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.GH74.E2.ComponentsShape
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder)

private lemma w183K3Shape2_isQuasisimple_of_open {J : Type} [Group J]
    (hq : CFSG.Open.IsQuasisimple J) : CFSG.IsQuasisimple J := by
  haveI : Group.IsPerfect J := ⟨hq.1⟩
  exact CFSG.RankThree.PartTwo.Sec4.Census.isQuasisimple_of_isPerfect hq.2

private lemma w183K3Shape2_models_of_blueprint {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (h : CFSG.Blueprint.LieModel X t n p f)
    (ht : t ∈ CFSG.Blueprint.classicalTags) : CFSG.Models.LieModel X t n p f := by
  have hc : StatedClassicalModel X t n p f := CFSG.Blueprint.LieModel.statedClassicalModel h ht
  exact ⟨hc.1, Or.inl hc⟩

private lemma w183K3Shape2_eq_three_of_dvd_two_pow_mul_three {N k : ℕ} (hodd : Odd N)
    (hne : N ≠ 1) (hdiv : N ∣ 2 ^ k * 3) : N = 3 := by
  have hcop : Nat.Coprime N (2 ^ k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact (Nat.coprime_pow_right_iff (n := k) hk N 2).mpr (Nat.coprime_two_right.mpr hodd)
  have h3 : N ∣ 3 := (Nat.Coprime.dvd_mul_left (n := 3) hcop).mp hdiv
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3
  · exact absurd h1 hne
  · exact h3

theorem kstar_card_center_three
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J X : Type} [Group J] [Finite J] [Group X] (hq : CFSG.Open.IsQuasisimple J)
    (hodd : Odd (Nat.card ↥(Subgroup.center J))) (hZ : Nontrivial ↥(Subgroup.center J))
    (e : J ⧸ Subgroup.center J ≃* X) (hX : IsAlt X 6 ∨ IsL3 X 2) :
    Nat.card ↥(Subgroup.center J) = 3 := by
  have hZ' : Nat.card ↥(Subgroup.center J) ≠ 1 := by
    haveI : Nontrivial ↥(Subgroup.center J) := hZ
    exact (Finite.one_lt_card (α := ↥(Subgroup.center J))).ne'
  have hq' : CFSG.IsQuasisimple J := w183K3Shape2_isQuasisimple_of_open hq
  rcases hX with hAlt | hL3
  ·
    have hmB : CFSG.Blueprint.LieModel X .PSL 2 3 2 :=
      CFSG.GH74.E2.lieModel_psl_two_nine_of_alt_six hAlt
    have hm : CFSG.Models.LieModel X .PSL 2 3 2 :=
      w183K3Shape2_models_of_blueprint hmB (by decide)
    have hdiv := CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA hq' e hm
    have htab : tableOrder .PSL 2 3 2 = 6 := by
      simp only [tableOrder, genericOrders, exceptionalOrders]
      norm_num
    rw [htab] at hdiv
    refine w183K3Shape2_eq_three_of_dvd_two_pow_mul_three (k := 1) hodd hZ' ?_
    rwa [show (6 : ℕ) = 2 ^ 1 * 3 by norm_num] at hdiv
  ·
    have hm : CFSG.Models.LieModel X .PSL 3 2 2 :=
      w183K3Shape2_models_of_blueprint hL3 (by decide)
    have hdiv := CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA hq' e hm
    have htab : tableOrder .PSL 3 2 2 = 48 := by
      simp only [tableOrder, genericOrders, exceptionalOrders]
      norm_num
    rw [htab] at hdiv
    refine w183K3Shape2_eq_three_of_dvd_two_pow_mul_three (k := 4) hodd hZ' ?_
    rwa [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] at hdiv

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
