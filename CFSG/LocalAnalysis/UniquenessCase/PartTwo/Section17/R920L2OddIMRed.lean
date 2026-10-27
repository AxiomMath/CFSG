module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMRed
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2EvenStrong
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
import CFSG.RankThree.PartOne.S11d.FinalLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsChiefFactorUnder)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem r920imred_false_of_isSylow_le_chief_factor {r : ℕ} [Fact r.Prime]
    {Y U W P : Subgroup G} (hUW : IsChiefFactorUnder r Y U W) (hP : IsSylowOf r P U)
    (hPW : P ≤ W) : False := by
  have hUnor : U ≤ normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro u hu w hw
    exact hUW.2.2.2.1 u hu w hw
  haveI hWn : (W.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUW.1.le).mpr hUnor
  have hPquot : IsPGroup r (↥U ⧸ W.subgroupOf U) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) g
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr
      (by simpa using (hUW.2.2.2.2.2.1 (x : G) x.2))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := r)).mp hPquot
  have hWidx : (W.subgroupOf U).index = r ^ k := by
    rw [Subgroup.index_eq_card, hk]
  have hdvd : (W.subgroupOf U).index ∣ (P.subgroupOf U).index :=
    Subgroup.index_dvd_of_le fun _ hx => hPW hx
  have hodd : ¬ r ∣ (P.subgroupOf U).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.2
  have hk0 : k = 0 := by
    by_contra hk0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    exact hodd (dvd_trans (hWidx ▸ dvd_pow_self r (Nat.succ_ne_zero j)) hdvd)
  have hWtop : W.subgroupOf U = ⊤ :=
    (Subgroup.index_eq_one).mp (by rw [hWidx, hk0, pow_zero])
  exact absurd (le_antisymm (Subgroup.subgroupOf_eq_top.mp hWtop) hUW.1.le)
    (ne_of_gt hUW.1)

theorem false_of_chief_factor_prime {M Y U W A : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hM : rankThreeIsMaxTwoLocal M) (hAY : A ≤ Y) (hAr : Nat.card A = r)
    (hAu : A ∈ uniqueSet M) (hUW : IsChiefFactorUnder r Y U W) (hUM : U ⊓ M ≤ W) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hApg : IsPGroup r ↥A := IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])
  obtain ⟨P, hPsyl, hAP⟩ :=
    CFSG.RankThree.PartOne.exists_isSylowOf_ge (K := U ⊔ A) le_sup_right hApg
  have hPM : P ≤ M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      hM hAu hAP hPsyl.isPGroup
  have hPU : IsSylowOf r (P ⊓ U) U :=
    hPsyl.inf_of_le_normalizer le_sup_left
      (sup_le Subgroup.le_normalizer (hAY.trans hUW.2.1))
  exact r920imred_false_of_isSylow_le_chief_factor hUW hPU
    ((le_inf inf_le_right (inf_le_left.trans hPM)).trans hUM)

private theorem r920imred_pow_mem_pCoreOf_of_minimal_chief_factor {r n : ℕ} [Fact r.Prime]
    {Y L U W M : Subgroup G} (hL : L ∈ calC M) (hL2 : IsL2 (Bar2 L) n) (hLY : L ≤ Y)
    (hUW : IsChiefFactorUnder r Y U W) (hWM : W ≤ M) (hW3 : ¬ 3 ∣ Nat.card W)
    (hcomm : ⁅U, L⁆ = U) :
    ∀ u ∈ U, ∃ k : ℕ, u ^ r ^ k ∈ pCoreOf 2 W := by
  have hWinv : W ∈ F09.Inv9' M L 3 := ⟨hWM, hW3, hLY.trans hUW.2.2.1⟩
  have hWL : ⁅W, L⁆ ≤ pCoreOf 2 W :=
    commutator_le_pCoreOf_of_mem_inv9'_of_isL2 hL hL2 hWinv
  have hT_le_W : pCoreOf 2 W ≤ W := CFSG.LieType.BorelTits.pCoreOf_le 2 W
  have hW_le_U : W ≤ U := hUW.1.le
  have hU_norm_W : U ≤ normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro u hu w hw
    exact hUW.2.2.2.1 u hu w hw
  have hU_norm_T : U ≤ normalizer (pCoreOf 2 W : Set G) :=
    hU_norm_W.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
  have hL_norm_U : L ≤ normalizer (U : Set G) := hLY.trans hUW.2.1
  have hL_norm_W : L ≤ normalizer (W : Set G) := hLY.trans hUW.2.2.1
  have hL_norm_T : L ≤ normalizer (pCoreOf 2 W : Set G) :=
    hL_norm_W.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
  exact exists_pow_mem_of_commutator_action hT_le_W hW_le_U hU_norm_T hU_norm_W hL_norm_U
    hL_norm_W hL_norm_T hcomm hWL hUW.2.2.2.2.1 hUW.2.2.2.2.2.1

private theorem r920imred_not_dvd_card_of_pow_mem_pCoreOf {r s : ℕ} [Fact r.Prime] (hs : s.Prime)
    (hs2 : s ≠ 2) (hrs : r ≠ s) {U W : Subgroup G}
    (hpows : ∀ u ∈ U, ∃ k : ℕ, u ^ r ^ k ∈ pCoreOf 2 W) : ¬ s ∣ Nat.card U := by
  intro hsU
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' s (hp := ⟨hs⟩) hsU
  obtain ⟨k, hk⟩ := hpows (u : G) u.2
  have hcopsr : (s : ℕ).Coprime r :=
    (hs.coprime_iff_not_dvd).mpr fun hdvd =>
      hrs ((Nat.prime_dvd_prime_iff_eq hs Fact.out).mp hdvd).symm
  have hcopsrk : (s : ℕ).Coprime (r ^ k) := hcopsr.pow_right k
  have horder_u : orderOf ((u : G)) = s := by
    rw [Subgroup.orderOf_coe u, huord]
  have horder : orderOf ((u : G) ^ (r ^ k)) = s := by
    have hcop : (orderOf ((u : G))).Coprime (r ^ k) := by
      rw [horder_u]
      exact hcopsrk
    exact (Nat.Coprime.orderOf_pow hcop).trans horder_u
  obtain ⟨n, hn⟩ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W).exists_orderOf_eq_pow
      ⟨(u : G) ^ (r ^ k), hk⟩
  have h2 : 2 ^ n = s := by
    rw [← hn]
    exact (Subgroup.orderOf_coe ⟨(u : G) ^ (r ^ k), hk⟩).symm.trans horder
  have hdvd : s ∣ 2 ^ n := by rw [h2]
  exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow hdvd))

theorem not_dvd_card_of_minimal_chief_factor_L2 {r s n : ℕ} [Fact r.Prime] (hs : s.Prime)
    (hs2 : s ≠ 2) (hrs : r ≠ s) {Y L U W D₃ M O : Subgroup G} (hL : L ∈ calC M)
    (hL2 : IsL2 (Bar2 L) n) (hLY : L ≤ Y) (hYL : Y ≤ normalizer (L : Set G)) (hD₃L : D₃ ≤ L)
    (hUW : IsChiefFactorUnder r Y U W) (hUO : U ≤ O) (hWM : W ≤ M) (hW3 : ¬ 3 ∣ Nat.card W)
    (hUM : U ⊓ M ≤ W) (hfix : ∀ u ∈ U, (∀ x ∈ D₃, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    (hmin : ∀ V : Subgroup G, V ≤ O → Y ≤ normalizer (V : Set G) → ¬ V ≤ M →
      Nat.card U ≤ Nat.card V) : ¬ s ∣ Nat.card U := by
  have hcomm : ⁅U, L⁆ = U :=
    commutator_eq_of_minimal_chief_factor hLY hYL hD₃L hUW hUO hWM hUM hfix hmin
  have hpows : ∀ u ∈ U, ∃ k : ℕ, u ^ r ^ k ∈ pCoreOf 2 W :=
    r920imred_pow_mem_pCoreOf_of_minimal_chief_factor hL hL2 hLY hUW hWM hW3 hcomm
  exact r920imred_not_dvd_card_of_pow_mem_pCoreOf hs hs2 hrs hpows

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
