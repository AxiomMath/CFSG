module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsEleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsNineFifteen
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsEleven
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.RankThree.PartTwo.Sec8.Hering418Lin
import CFSG.RankThree.PartTwo.KFacts.AutPSUInnDiag
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NE
import CFSG.LocalAnalysis.UniquenessCase.UC22S218NFour
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem uc22s23w6_dvd_of_not_inner_sp4 {X : Type} [Group X] {a r : ℕ} (hX : IsSp4 X a)
    (hr : r.Prime) (hr2 : r ≠ 2) {θ : MulAut X} (hθ : θ ^ r = 1)
    (hθN : θ ∉ (MulAut.conj : X →* MulAut X).range) : r ∣ a := by
  by_contra hra
  refine hθN (uc22p2214_inner_of_prime_Sp4 hX hr (fun h => ?_) hθ)
  rcases (Nat.Prime.dvd_mul hr).1 h with h2 | ha
  · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  · exact hra ha

theorem uc22s23w6_dvd_of_not_innDiag_u3 {X : Type} [Group X] {a r : ℕ} (hX : IsU3 X a)
    (hr : r.Prime) (hr2 : r ≠ 2) {θ : MulAut X} (hθ : θ ^ r = 1)
    (hθN : θ ∉ CFSG.ASVolI.ChA.innDiagSubgroup X) : r ∣ a := by
  by_contra hra
  by_cases hr3 : r = 3
  · subst hr3
    have hn : 2 ≤ a := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hX
    obtain ⟨-, K, hField, hFin, hK, ⟨e₁⟩⟩ :=
      CFSG.LocalAnalysis.EvenBN.GMSK.statedClassicalModel_of_lieModel_PSU3 hX
    let hu : @UnitaryFieldData 2 a K hField :=
      ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq : 2 < 2 ^ a :=
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hn
    let e : X ≃* @unitaryPSU 2 a K hField hu 3 :=
      e₁.trans (@unitaryPSUEquiv 2 a K hField hu 3 (by norm_num : 1 ≤ 3)).symm
    have hα : MulAut.congr e θ ^ 3 = 1 := by rw [← map_pow, hθ, map_one]
    have hmem := CFSG.RankThree.PartTwo.Sec8.Hering418.pow_three_mem_psuConj_range (h := hu) hq
      (by omega) hα
    have hmap := Subgroup.mem_map_of_mem (MulAut.congr e.symm).toMonoidHom hmem
    refine hθN ?_
    convert CFSG.RankThree.PartTwo.KFacts.map_range_psuConj_le_innDiagSubgroup hu e hmap using 1
    ext x
    simp [e, MulAut.congr_apply]
  · refine hθN (Subgroup.subset_closure (show CFSG.ASVolI.ChA.IsInnDiagAut X θ from
      Or.inl (uc22p2214_inner_of_prime_U3 hX hr (fun h => ?_) hθ)))
    rcases (Nat.Prime.dvd_mul hr).1 h with h6 | ha
    · rcases (Nat.Prime.dvd_mul hr).1 (show r ∣ 2 * 3 by simpa using h6) with h2 | h3
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
      · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3)
    · exact hra ha

variable {G : Type} [Group G] [Finite G]

theorem s21_11N_W2111_of_s21_9NFull_setup4 (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hB3 : BadNoStrongThree) (hG : GriessAllModelsStatement)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) {Ch : Choice2011 G} (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_9NFull (UC6.dataOfSetup4 hS hU S) Ch → S21_11N (UC6.dataOfSetup4 hS hU S) Ch W2111 := by
  intro h219 h1930 c L hL hLN b hbB hbN θ hInd hW
  exfalso
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hθeq : θ = inducedQuotInfAut L b hbN :=
    inducedQuotInf_unique L hbN hInd (inducedQuotInf_inducedQuotInfAut L b hbN)
  obtain ⟨hbodd, hbsq⟩ := orderOf_odd_and_squarefree_of_mem_calB1 c.hB hbB
  have key : ∀ N : Subgroup (MulAut (BarInf L ⧸ Subgroup.center (BarInf L))), θ ∉ N →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
        ∃ θ' : MulAut (BarInf L ⧸ Subgroup.center (BarInf L)), θ' ∉ N ∧ θ' ^ r = 1 := by
    intro N hθN
    let bN : ↥(Subgroup.normalizer (L : Set G)) := ⟨b, hbN⟩
    have hbN' : orderOf bN = orderOf b := (Subgroup.orderOf_coe bN).symm
    obtain ⟨b₀, hb₀, hb₀pr, hb₀N⟩ :=
      exists_prime_order_zpowers_of_not_mem (inducedQuotInfAutHom L) N bN
        (by rw [hbN']; exact hbsq) (by rw [hθeq] at hθN; exact hθN)
    refine ⟨orderOf b₀, hb₀pr, fun h2 => ?_, inducedQuotInfAutHom L b₀, hb₀N, ?_⟩
    · have hodd : Odd (orderOf b₀) :=
        hbodd.of_dvd_nat (hbN' ▸ orderOf_dvd_of_mem_zpowers hb₀)
      rw [h2] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    · rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hnpow : ∀ {a r : ℕ}, r.Prime → r ≠ 2 → r ∣ a → ¬ IsPowTwo a := by
    rintro a r hr hr2 hra ⟨k, rfl⟩
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hra))
  rcases hW with ⟨⟨a, hSp4X⟩, hnotInn⟩ | ⟨⟨a, hU3X⟩, hnotDiag⟩
  · obtain ⟨r, hr, hr2, θ', hθ'N, hθ'⟩ := key _ hnotInn
    have hna := hnpow hr hr2 (uc22s23w6_dvd_of_not_inner_sp4 hSp4X hr hr2 hθ' hθ'N)
    have hSp4bar : IsSp4 (BarInf L) a :=
      CFSG.Blueprint.LieModel.of_quotient_center (center_barInf_eq_bot hq) hSp4X
    have hC76 := PartOne.Section7.c76Three_of_inputs hSE hK3 hB3 hS hU S
    have h76 : ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig,
        IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M →
          Conclusion76 (UC6.dataOfSetup4 hS hU S).M p := fun p hp hsp => by
      by_cases h3 : 3 ∈ uniqueFourBeta G
      · exact hC76 hMS h3 p hp hsp
      · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
    have h3 := uc22s218n_pRank_le_three _ Ch (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
      ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1) h211 h76 h1930 c hL
      (uc22s218n_isSp4_bar2 hG hL hSp4bar) hna S.hp
    have h4 : 4 ≤ CFSG.Open.pRank S.p (UC6.dataOfSetup4 hS hU S).M :=
      UC6.four_le_pRank_of_sigma S.hp
    omega
  · obtain ⟨r, hr, hr2, θ', hθ'N, hθ'⟩ := key _ hnotDiag
    have hna := hnpow hr hr2 (uc22s23w6_dvd_of_not_innDiag_u3 hU3X hr hr2 hθ' hθ'N)
    obtain ⟨-, ⟨-, he3⟩, -⟩ := h219 h1930 c L hL hLN a (isSU3_bar2_of_isU3 hq hU3X) hna
    have := hS.rank
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
