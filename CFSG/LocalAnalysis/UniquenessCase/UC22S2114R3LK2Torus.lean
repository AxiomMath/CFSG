module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LDefs
public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag1
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Uc
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)
open Matrix (SpecialLinearGroup)
open CFSG.Blueprint.Multiplier (exceptionalOrders genericOrders)

variable {G : Type} [Group G] [Finite G]

theorem center_bar2_eq_bot_of_isL4 (hGA : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hX : LieModel (BarInf L) .PSL 4 2 n) (hn : n ≠ 1) :
    Subgroup.center (Bar2 L) = ⊥ := by
  have hn0 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hX).2.1
  have hex : exceptionalOrders .PSL 4 2 n = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : genericOrders .PSL 4 2 n = (1, 1) := by
    have hodd : Odd (2 ^ n - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
    have hcop : Nat.Coprime (2 ^ 2) (2 ^ n - 1) :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
    show (Nat.gcd 4 (2 ^ n - 1), 1) = (1, 1)
    rw [show Nat.gcd 4 (2 ^ n - 1) = 1 from hcop]
  exact center_bar2_eq_bot_of_row hL hg hex (griessRow_of_lieModel_classical hGA hX (by decide))

theorem exists_mulEquiv_sl4_of_isL4 (hGA : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hX : LieModel (BarInf L) .PSL 4 2 n) (hn : n ≠ 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (Bar2 L ≃* SpecialLinearGroup (Fin 4) K) := by
  obtain ⟨eI⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 (center_bar2_eq_bot_of_isL4 hGA hL hX hn)
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hX
  have : CharP K 2 := uc22pwlie_charP_two hK
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨eI.symm.trans (e₁.trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLFourEquivSL K))⟩⟩

theorem s21_14R3LK2_dataOfSetup_of_datum
    (hdat : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 ^ n →
      UC22pwR1Datum (SpecialLinearGroup (Fin 4) K)
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 4 K) n)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (S : Setup G) (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)) :
    S21_14R3LK2 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) := by
  intro hH c L hL _ _ f hfo hf3 hX _ _ _ _ hML _ _ _
  exfalso
  set D := PartTwo.Three.dataOfSetup hS S with hD
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := exists_mulEquiv_sl4_of_isL4 hGA hL hX (by omega)
  have : CharP K 2 := uc22pwlie_charP_two hK
  have h1 : 2 ^ f - 1 ≠ 1 := by
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
    omega
  obtain ⟨s, hs, hsd⟩ := Nat.exists_prime_and_dvd h1
  have hs7 : 7 ≤ s := uc22s218u_seven_le hfo hs hsd
  have hs2 : s ≠ 2 := by omega
  have hLM : L ≤ D.M := hL.1.le
  have hrank : 3 ≤ CFSG.Open.pRank s D.M := by
    have ha := CFSG.ClassicalGroups.SpecialLinear.three_le_pRank_diagTorus (n := 4) le_rfl
      (F := K) hs (by rw [hK]; exact hsd)
    have hb := CFSG.SectionRank.pRank_mono hs.one_lt
      (le_top : CFSG.ClassicalGroups.SpecialLinear.diagTorus 4 K ≤ ⊤)
    have hc := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hs.one_lt e₀
    have hd := pRank_bar2_eq_of_odd (Y := L) hs hs2
    have he := CFSG.SectionRank.pRank_mono hs.one_lt hLM
    omega
  have hsσ : s ∈ D.sig :=
    PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC S.witness.maxLocal hs hs7 hrank
  have hsp : IsStronglyPEmbedded s D.M :=
    UC6S846.sp_of_mem_sig (UC6S846.sigmaStd_dataOfSetup hS S) (UC6S846.not_solvable_of_mem_calC hL)
      hsσ
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hTL : D.T ≤ normalizer (L : Set G) := D.sylowM.le.trans hML
  have hTS : IsSylowOf 2 (D.T ⊓ L) L := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact uc22p2214_isSylowOf_inf D.sylowM hL.1
  obtain ⟨P, hP⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 4)
      (by norm_num)
  have hdatP : UC22pwR1Datum (SpecialLinearGroup (Fin 4) K) (P : Subgroup _) f := by
    rw [hP]
    exact hdat K f hK
  obtain ⟨x, hxL, hxo, hxN⟩ := uc22ine229_exists_mem_normalizer_of_concl hTL hTS (n := f)
    (s := f) (r := s) (by omega) hfo dvd_rfl hs hsd
    fun U hψ _ _ hm' hnem => uc22pwr1_concl_of_datum_sylow e₀ U P hdatP hT2 _ hψ hm' hnem
  have hXc : Nat.card (zpowers x) = s := by rw [Nat.card_zpowers, hxo]
  have hXM : zpowers x ≤ D.M := (zpowers_le.2 hxL).trans hLM
  have hXN : zpowers x ≤ normalizer (D.T : Set G) := zpowers_le.2 hxN
  have hXnotU : zpowers x ∉ uniqueSet D.M :=
    not_mem_uniqueSet_of_le_normalizer D _ h211 hH c (by rw [hXc]; exact hs)
      (by rw [hXc]; exact hs.odd_of_ne_two hs2) hXM hXN
  have hXne : zpowers x ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hXc
    exact hs.ne_one hXc.symm
  exact hXnotU (mem_uniqueSet_of_isStronglyPEmbedded hs hsp hXM hXne
    (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])))

end CFSG.LocalAnalysis.UniquenessCase.UC22
