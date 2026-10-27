module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res3Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99FourSz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100SzPair
import CFSG.LocalAnalysis.UniquenessCase.UC6R77Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem r8100_sp_of_lift_prime {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hsn : s ∣ n)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2)
    (h76p : Conclusion76 D.M p)
    (hlift : ∀ K₁ ∈ conjSetOf D.M L, ∀ K₂ ∈ conjSetOf D.M L, K₁ ≠ K₂ →
      ∀ a₁ a₂ : G, a₁ ∈ K₁ → a₂ ∈ K₂ → orderOf a₁ = r → orderOf a₂ = r →
        ∃ A : Subgroup G, A ≤ D.M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
          ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 D.M) :
    IsStronglyPEmbedded r D.M := by
  by_contra hnot
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hrσ : r ∉ D.sig := fun h => hnot (UC6S846.sp_of_mem_sig hSg hns h)
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨K₁, K₂, hne, hS⟩ := Set.ncard_eq_two.1 hc2
  have h1S : K₁ ∈ conjSetOf D.M L := by
    rw [hS]
    exact Set.mem_insert _ _
  have h2S : K₂ ∈ conjSetOf D.M L := by
    rw [hS]
    exact Set.mem_insert_of_mem _ rfl
  have h1C := uc22p2214_calC_of_mem_conjSetOf hL h1S
  have h2C := uc22p2214_calC_of_mem_conjSetOf hL h2S
  have hshape : ∀ A ∈ conjSetOf D.M L, IsL2 (Bar2 A) n ∨ IsSz (Bar2 A) n := fun A hA =>
    uc22s21r899_shape_of_mem hA hLS
  have hZ : ∀ A ∈ conjSetOf D.M L, center (Bar2 A) = ⊥ := fun A hA =>
    uc22s21r899_center_bot hL hA hLS
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf r D.M
  have hRp : IsPGroup r R := hR.isPGroup
  have hRM : R ≤ D.M := hR.le
  have hRN : ∀ A ∈ conjSetOf D.M L, R ≤ normalizer (A : Set G) := fun A hA g hg => by
    obtain ⟨k, hk⟩ := hRp ⟨g, hg⟩
    have hg3 : g ^ r ^ k = 1 := congrArg Subtype.val hk
    exact uc22p2214_mem_normalizer_of_odd (by rw [uc22p2214_conjSetOf_eq hA]; exact hc2)
      (hRM hg) ((hr.odd_of_ne_two hr2).pow.of_dvd_nat (orderOf_dvd_of_pow_eq_one hg3))
  have hRK : ∀ A ∈ conjSetOf D.M L, R ⊓ A ≠ ⊥ := by
    intro A hA hbot
    have hAM : A ≤ D.M := uc22p22a_le_of_isSubnormal (uc22p2214_calC_of_mem_conjSetOf hL hA).1
    have hRA := (hR.of_le (le_inf hRM (hRN A hA)) inf_le_left).inf_of_le_normalizer
      (le_inf hAM Subgroup.le_normalizer) inf_le_right
    have hrA : r ∣ Nat.card A :=
      (PartTwo.s13_dvd_card_of_isL2_or_isSz (hshape A hA) hsn hr hrs).trans
        (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥A))
    have hv : 1 ≤ (Nat.card A).factorization r :=
      (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1 hrA
    have hc := hRA.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have h1 : r ^ 1 ≤ r ^ (Nat.card A).factorization r := Nat.pow_le_pow_right hr.pos hv
    rw [pow_one] at h1
    have := hr.two_le
    omega
  have hZR : ∀ A ∈ conjSetOf D.M L,
      ∃ a ∈ R ⊓ A, orderOf a = r ∧ a ∈ centralizer (R : Set G) := fun A hA =>
    CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer hr hRp
      inf_le_left ((le_inf Subgroup.le_normalizer (hRN A hA)).trans
        Subgroup.inf_normalizer_le_normalizer_inf) (hRK A hA)
  obtain ⟨a₁, ha₁, ha₁o, ha₁c⟩ := hZR K₁ h1S
  obtain ⟨a₂, ha₂, ha₂o, ha₂c⟩ := hZR K₂ h2S
  have hna : a₂ ∉ zpowers a₁ := by
    intro h
    have h1 : a₂ = 1 := uc22p2213e_eq_one_of_mem_inf h1C h2C hne (hZ K₁ h1S) hr hr2
      (zpowers_le.2 (Subgroup.mem_inf.1 ha₁).2 h) (Subgroup.mem_inf.1 ha₂).2
      (by rw [← ha₂o]; exact pow_orderOf_eq_one a₂)
    rw [h1, orderOf_one] at ha₂o
    have := hr.one_lt
    omega
  obtain ⟨hEel', hEc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card ha₁o
      ha₂o (Subgroup.mem_centralizer_iff.1 ha₂c a₁ (Subgroup.mem_inf.1 ha₁).1) hna
  set E : Subgroup G := zpowers a₁ ⊔ zpowers a₂
  have hEel : IsElemAbelian r E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r E).1 hEel'
  have hEZ : E ≤ R ⊓ centralizer (R : Set G) :=
    sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₁).1, ha₁c⟩))
      (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₂).1, ha₂c⟩))
  have hEM : E ≤ D.M := hEZ.trans (inf_le_left.trans hRM)
  obtain ⟨A, hAM, hAel, hAc, hAcomm⟩ := hlift K₁ h1S K₂ h2S hne a₁ a₂
    (Subgroup.mem_inf.1 ha₁).2 (Subgroup.mem_inf.1 ha₂).2 ha₁o ha₂o
  have hMO : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf D.M)
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hr hr2 hpp hp2
    (pCoreOf 2 D.M) A E (UC6S846.isPGroup_pCoreOf D.M) (hAM.trans hMO)
    (hEM.trans hMO) hAel.isPGroup hEel.isPGroup hAcomm
  have hA'M : A' ≤ D.M := hA'le.trans (sup_le hAM (Subgroup.map_subtype_le _))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = p ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
  have hΓ := h76p r hr E hEM hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp (le_inf hA'M hA'C) hA'el hA'c))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp
      (le_inf hA'M (hA'C.trans ((Subgroup.centralizer_le hXE).trans
        (Subgroup.centralizer_le_normalizer _)))) hA'el hA'c))
  exact hnot (h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R hR E hEZ hEel hEc hΓ)

theorem r8100_eq_of_not_sp {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : F07.R76 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) {p : ℕ} (hp : p ∈ D.sig)
    (hnot : ¬ IsStronglyPEmbedded r D.M) :
    n = p ∧ ((IsL2 (Bar2 L) 3 ∧ p = 3) ∨ (IsSz (Bar2 L) 5 ∧ p = 5)) := by
  have h76s : ∀ q ∈ D.sig, IsStronglyPEmbedded q D.M → Conclusion76 D.M q :=
    fun q hq hsp => F07.R76Sig_of_R76 D h76 q hq (D.sig_prime q hq).2 hsp
  have h77 : F07.R77E2 D := UC6.r77E2_of_conclusion76 D h76s
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  have hcong := uc22ine229_cong_of_ncard_two hSg h77 h614 hL hc2 hLS hr hr2 hrn hnot hp
  have hn2 : 2 ≤ n := by
    rcases hLS with hX | hX
    · exact uc22p20g_two_le_of_isL2 hX
    · have := (PartTwo.s13_odd_three_le_of_isSz hX).2
      omega
  have hpn : p ∣ n := by
    by_contra h
    exact hnot (uc22s21r8100_sp_of_not_dvd hSg hfour h614 h76s hL hc2 hLS dvd_rfl hr hr2 hrn
      hp h)
  obtain ⟨m, hm⟩ := hpn
  have hm1 : m = 1 := by
    by_contra hm1
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      omega
    have h4m : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
    have hq2 : q ≠ 2 := by
      rintro rfl
      have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 hm0
      omega
    have hmn : m ∣ n := ⟨p, by rw [hm, mul_comm]⟩
    have hqn : q ∣ 2 ^ n - 1 := hqm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hmn)
    have hspq : IsStronglyPEmbedded q D.M := by
      rcases hcong with ⟨hL2, hc⟩ | ⟨hSz, hc⟩
      · exact uc22s21r8100_sp_of_odd_factor hSg hfour h614 h76s hL hc2 hL2 hmn hq hq2 hqm hp
          hm (uc22r8100b_dvd_of_modEq hc) hqm
      · exact uc22s21r8100_sp_of_odd_factor_Sz hSg hfour h614 h76s hL hc2 hSz hmn hq hq2 hqm hp
          hm (uc22r8100b_dvd_of_modEq hc) hqm
    refine hnot (r8100_sp_of_lift_prime hSg h614 hL hc2 hLS dvd_rfl hr hr2 hrn hq hq2
      (h76 q hq hq2 hspq) ?_)
    intro K₁ h1S K₂ h2S hne a₁ a₂ ha₁ ha₂ ha₁o ha₂o
    have h1C := uc22p2214_calC_of_mem_conjSetOf hL h1S
    have h2C := uc22p2214_calC_of_mem_conjSetOf hL h2S
    rcases hLS with hL2 | hSz
    · exact exists_lift_of_isL2_torus h1C h2C hne (uc22s21r899_isL2_of_mem h1S hL2)
        (uc22s21r899_isL2_of_mem h2S hL2) hq hq2 hqn hr hr2 hrn ha₁ ha₂ ha₁o ha₂o
    · have hSzK : ∀ K ∈ conjSetOf D.M L, IsSz (Bar2 K) n := by
        rintro K ⟨g, -, rfl⟩
        obtain ⟨e⟩ := uc22p20d_bar2_conj g L
        exact CFSG.Blueprint.LieModel.of_mulEquiv e hSz
      exact exists_lift_of_isSz_torus h1C h2C hne (hSzK K₁ h1S) (hSzK K₂ h2S) hq hq2 hqn hr
        hr2 hrn ha₁ ha₂ ha₁o ha₂o
  subst hm1
  rw [mul_one] at hm
  subst hm
  exact ⟨rfl, uc22r8100r3_shape_of_eq hpp hcong⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
