module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltMult
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GH74.GLS.Stage2.Signalizer
open CFSG.Alternating.Multipliers CFSG.RankThree.PerfectCover

private theorem s15k_schur_quasisimple {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) :
    CFSG.IsQuasisimple X :=
  ((CFSG.Foundations.SteinbergCA.quasisimple_iff X).2.2.1).mpr hq

private theorem s15k_schur_odd_dvd_six {m : ℕ} (hd : m ∣ 6) (ho : Odd m) : m = 1 ∨ m = 3 := by
  have hle : m ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  interval_cases m <;> first | omega | (exfalso; revert hd ho; decide)

private theorem s15k_schur_isAlt_of_center_bot {X : Type} [Group X] {n : ℕ} (hc : center X = ⊥)
    (h : UC22.IsAlt (X ⧸ center X) n) : UC22.IsAlt X n := by
  obtain ⟨e⟩ := h
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)).trans
    e⟩

private theorem s15k_schur_isLn_of_center_bot {X : Type} [Group X] {n a : ℕ} (hc : center X = ⊥)
    (h : IsLn (X ⧸ center X) n a) : IsLn X n a :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)).symm h

theorem s15k_schur_alt_six {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (center X)))
    (h : UC22.IsAlt (X ⧸ center X) 6) : UC22.IsAlt X 6 ∨ F08.IsA6Z3 X := by
  have hq' := s15k_schur_quasisimple hq
  obtain ⟨e⟩ := h
  have hd := Ivk8.card_center_dvd_of_alt hq' (n := 6) (by norm_num) e
  rw [(hopfMultiplier_alternatingGroup_six).2] at hd
  rcases s15k_schur_odd_dvd_six hd hodd with h1 | h3
  · exact Or.inl (s15k_schur_isAlt_of_center_bot (Subgroup.card_eq_one.mp h1) ⟨e⟩)
  · exact Or.inr ⟨hq', h3, ⟨e⟩⟩

theorem s15k_schur_alt_seven {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hodd : Odd (Nat.card (center X)))
    (h : UC22.IsAlt (X ⧸ center X) 7) : UC22.IsAlt X 7 ∨ F08.IsA7Z3 X := by
  have hq' := s15k_schur_quasisimple hq
  obtain ⟨e⟩ := h
  have hd := Ivk8.card_center_dvd_of_alt hq' (n := 7) (by norm_num) e
  rw [(hopfMultiplier_alternatingGroup_seven).2] at hd
  rcases s15k_schur_odd_dvd_six hd hodd with h1 | h3
  · exact Or.inl (s15k_schur_isAlt_of_center_bot (Subgroup.card_eq_one.mp h1) ⟨e⟩)
  · exact Or.inr ⟨hq', h3, ⟨e⟩⟩

theorem s15k_schur_alt_eight {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (center X))) (h : UC22.IsAlt (X ⧸ center X) 8) : UC22.IsAlt X 8 := by
  have hq' := s15k_schur_quasisimple hq
  obtain ⟨e⟩ := h
  have hd := Ivk8.card_center_dvd_of_alt hq' (n := 8) (by norm_num) e
  rw [card_hopfMultiplier_alternatingGroup (le_refl 8)] at hd
  have h1 : Nat.card (center X) = 1 := by
    have hle : Nat.card (center X) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    obtain ⟨k, hk⟩ := hodd
    omega
  exact s15k_schur_isAlt_of_center_bot (Subgroup.card_eq_one.mp h1) ⟨e⟩

theorem s15k_schur_hopf_l5 {Y : Type} [Group Y] (hY : IsLn Y 5 1) :
    Subsingleton (CFSG.Open.griessHopfMultiplier Y) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hY
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card, hK]; norm_num
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_five_le
    (k := K) (n := 5) le_rfl
  have hg : Nat.gcd 5 (Fintype.card K - 1) = 1 := by rw [hcard]; norm_num
  have : Subsingleton (Multiplicative (ZMod (Nat.gcd 5 (Fintype.card K - 1)))) := by
    rw [hg]; infer_instance
  let e' : Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 K).symm
  have eC := CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e'
  exact (eC.trans eM).toEquiv.subsingleton

theorem s15k_schur_l5 {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    (h : IsLn (X ⧸ center X) 5 1) : IsLn X 5 1 := by
  have hq' := s15k_schur_quasisimple hq
  have hc : center X = ⊥ :=
    Odd87.center_eq_bot_of_hopf_subsingleton hq' (MulEquiv.refl _) (s15k_schur_hopf_l5 h)
  exact s15k_schur_isLn_of_center_bot hc h

theorem rSchur153_holds : RSchur153 :=
  fun _ _ _ hq hodd =>
    ⟨s15k_schur_alt_six hq hodd, s15k_schur_alt_seven hq hodd, s15k_schur_alt_eight hq hodd,
      s15k_schur_l5 hq⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
