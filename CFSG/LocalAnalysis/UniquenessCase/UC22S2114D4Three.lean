module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114D4Syl
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4RankBounds
import CFSG.Quasithin.H13.NQCatExceptional
import CFSG.Mathlib.Arithmetic.TwoPowSubOneSeven
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218X
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Milestones.ASVolI.I2
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3B
import CFSG.Quasithin.Background.SmithC27Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]


theorem uc22s2114_false_of_is3D4_of_three_dvd_three {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : Is3D4 (BarInf L) f)
    (hf : IsPowTwo f) (hn : 3 ∣ c.n) {p : ℕ} (hp : p ∈ D.sig)
    (hpL : CFSG.Open.pRank p L ≤ 1) : False := by
  classical
  have hLM : L ≤ D.M := hL.1.le
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have h7n : 7 ∣ 2 ^ c.n - 1 := (CFSG.three_dvd_iff_seven_dvd_two_pow_sub_one _).1 hn
  have h7σ : 7 ∉ D.sig := uc22s2114_not_mem_sig hSg hns hH c Nat.prime_seven h7n
  have hZ : center (Bar2 L) = ⊥ := center_bar2_eq_bot_of_is3D4 hL hX
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  have h3D4 : Is3D4 (Bar2 L) f := CFSG.Blueprint.LieModel.of_mulEquiv e hX
  obtain ⟨E, hEL, hEel, hEcard⟩ := uc22s2114_exists_fortyNine_of_is3D4 h3D4 hf
  have hEr : IsPGroup 7 E := hEel.isPGroup
  have hEc2 : Nat.card E = 7 ^ 2 := by rw [hEcard]; norm_num
  have hMN : D.M ≤ normalizer (L : Set G) := by
    by_contra hML
    have h := UC6S846.calCRankTwice D.M L hL hML 7 Nat.prime_seven (by norm_num)
      (by rw [hZ, card_bot]; norm_num) E hEL hEel 2 hEc2
    exact h7σ (hSg.four_mem 7 Nat.prime_seven (by norm_num) (by omega))
  have hab : ∀ P : Sylow 7 (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)) :=
    fun P => (uc22s2114_sylowSeven_of_is3D4 h3D4 hf P).1.1
  have hout : ¬ 7 ∣ (L ⊔ F08.CentOverO2 D.M L).relIndex D.M := by
    have hdvd := relIndex_centOverO2_dvd_card_outer hLM hMN
    rw [Inputs1719.card_outer_of_is3D4 h3D4] at hdvd
    obtain ⟨k, rfl⟩ := hf
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_seven).1 (h.trans hdvd) with h3 | h2
    · norm_num at h3
    · exact absurd (Nat.prime_seven.dvd_of_dvd_pow h2) (by norm_num)
  obtain ⟨R, hR, hEZ⟩ :=
    exists_sylow_le_centralizer_of_isMulCommutative Nat.prime_seven (by norm_num)
      hLM hMN hab hout hEL hEr
  have hp7 : p ≠ 7 := fun h => h7σ (h ▸ hp)
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hp
  have hOp : F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hpp hsp
  have hCEM := ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 h3D4).2
  obtain ⟨⟨-, hf1, -⟩, -⟩ := id hCEM
  have hcyc : IsCyclic (Outer (Bar2 L)) :=
    CFSG.Quasithin.H13.NQCat.outer_isCyclic_of_even_trialityD4_model hf1 hCEM
  have hbound := pRank_le_pRank_bar2_add_pRank_centOverO2 hLM hMN hZ hcyc hpp hp2 hOp
  have hbar := pRank_bar2_eq_of_odd (Y := L) hpp hp2
  have hCle := pRank_centOverO2_le_pRank_inf_centralizer hLM hMN hpp hp2 Nat.prime_seven
    (by norm_num) (Ne.symm hp7) hEL hEr
  have hp3 := hSg.three_le p hp
  exact uc22s217u3a_false_of_sp D Ch hH c Nat.prime_seven h7n
    (uc22s2114_strongly_of_two_le_pRank_centralizer hSg hns h76 h614 hp Nat.prime_seven
      (by norm_num) hR hEel hEc2 hEZ (by omega))

theorem s21_14D4_of_s21_14D4T {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (hD4T : S21_14D4T D Ch) : S21_14D4 D Ch := by
  intro hH c L hL hX hpow hD _ hn hBT hBL hfaith
  by_cases h2 : ∀ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L
  · exact hD4T hH c L hL hX hpow hD (Or.inl hn) (fun _ => ⟨hn, hBT⟩) hBL hfaith h2
  · simp only [not_forall, not_le] at h2
    obtain ⟨p, hp, hpL⟩ := h2
    obtain ⟨f, hf⟩ := hD
    exact (uc22s2114_false_of_is3D4_of_three_dvd_three hSg h614 h76 hH c hL hf
      (hpow f (Or.inr (Or.inr (Or.inr (Or.inl hf))))) (by omega) hp (by omega)).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
