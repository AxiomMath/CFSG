module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Sz
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22s21r899_shape_of_mem {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n := by
  obtain ⟨g, -, rfl⟩ := hK
  obtain ⟨e⟩ := uc22p20d_bar2_conj g L
  exact hLS.imp (fun h => CFSG.Blueprint.LieModel.of_mulEquiv e h)
    (fun h => CFSG.Blueprint.LieModel.of_mulEquiv e h)

theorem uc22s21r899_isL2_of_mem {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) {n : ℕ}
    (h : IsL2 (Bar2 L) n) : IsL2 (Bar2 K) n := by
  obtain ⟨g, -, rfl⟩ := hK
  obtain ⟨e⟩ := uc22p20d_bar2_conj g L
  exact CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem uc22s21r899_center_bot {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ conjSetOf M L)
    {n : ℕ} (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) : center (Bar2 K) = ⊥ := by
  rcases uc22s21r899_shape_of_mem hK hLS with hX | hX
  · exact uc22p22g_center_bot hX
  · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
    exact uc22p21k_center_eq_bot (uc22p2214_calC_of_mem_conjSetOf hL hK).2.2

theorem uc22s21r899_sp_of_lift {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p ≠ 3)
    (hlift : ∀ K₁ ∈ conjSetOf D.M L, ∀ K₂ ∈ conjSetOf D.M L, K₁ ≠ K₂ →
      ∀ A₀ : Subgroup G, A₀ ≤ D.M → IsElemAbelian p A₀ → Nat.card A₀ = p ^ 4 →
      (∀ A ∈ conjSetOf D.M L, A₀ ≤ normalizer (A : Set G)) →
      ∀ a₁ a₂ : G, a₁ ∈ K₁ → a₂ ∈ K₂ → orderOf a₁ = r → orderOf a₂ = r →
        ∃ A : Subgroup G, A ≤ D.M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
          ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 D.M) :
    IsStronglyPEmbedded r D.M := by
  by_contra hnot
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hrσ : r ∉ D.sig := fun h => hnot (UC6S846.sp_of_mem_sig hSg hns h)
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have h76p := h76 p hp (UC6S846.sp_of_mem_sig hSg hns hp)
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have hr3 : r ≠ 3 := fun h =>
    CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.not_three_dvd_pow_sub_one hs (h ▸ hrs)
  obtain ⟨K₁, K₂, K₃, hne, -, -, hS⟩ := Set.ncard_eq_three.1 hc3
  have h1S : K₁ ∈ conjSetOf D.M L := by
    rw [hS]
    exact Set.mem_insert _ _
  have h2S : K₂ ∈ conjSetOf D.M L := by
    rw [hS]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hshape : ∀ A ∈ conjSetOf D.M L, IsL2 (Bar2 A) n ∨ IsSz (Bar2 A) n := fun A hA =>
    uc22s21r899_shape_of_mem hA hLS
  have hZ : ∀ A ∈ conjSetOf D.M L, center (Bar2 A) = ⊥ := fun A hA =>
    uc22s21r899_center_bot hL hA hLS
  obtain ⟨A₀, hA₀M, hA₀el, hA₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hfour p hp)
  have hA₀N : ∀ A ∈ conjSetOf D.M L, A₀ ≤ normalizer (A : Set G) := fun A hA g hg =>
    uc22r899_mem_normalizer_of_fix hc3 (hA₀M hg) hpp hp2 (k := 1)
      (by rw [pow_one]; exact hA₀el.2 g hg) (fun h => absurd h hp3) A hA
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf r D.M
  have hRp : IsPGroup r R := hR.isPGroup
  have hRM : R ≤ D.M := hR.le
  have hRN : ∀ A ∈ conjSetOf D.M L, R ≤ normalizer (A : Set G) := fun A hA g hg => by
    obtain ⟨k, hk⟩ := hRp ⟨g, hg⟩
    have hg3 : g ^ r ^ k = 1 := congrArg Subtype.val hk
    exact uc22r899_mem_normalizer_of_fix hc3 (hRM hg) hr hr2 hg3 (fun h => absurd h hr3) A hA
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
  have h1C := uc22p2214_calC_of_mem_conjSetOf hL h1S
  have h2C := uc22p2214_calC_of_mem_conjSetOf hL h2S
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
  obtain ⟨A, hAM, hAel, hAc, hAcomm⟩ := hlift K₁ h1S K₂ h2S hne A₀ hA₀M hA₀el hA₀c hA₀N a₁ a₂
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

theorem uc22s21r899_sp_of_not_dvd {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p ≠ 3)
    (hpn : ¬ p ∣ n) : IsStronglyPEmbedded r D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  refine uc22s21r899_sp_of_lift hSg hfour h614 h76 hL hc3 hLS hs hsn hr hrs hp hp3 ?_
  rintro K₁ h1S K₂ h2S - A₀ hA₀M hA₀el hA₀c hA₀N a₁ a₂ ha₁ ha₂ - -
  have h1C := uc22p2214_calC_of_mem_conjSetOf hL h1S
  have h2C := uc22p2214_calC_of_mem_conjSetOf hL h2S
  have hcb : ∀ A ∈ conjSetOf D.M L, ∀ B : Subgroup G, IsElemAbelian p B →
      B ≤ normalizer (A : Set G) → ∃ C : Subgroup G, C ≤ B ∧
        (∀ c ∈ C, CentralizesBar c A) ∧ Nat.card B ≤ p * Nat.card C := by
    intro A hA B hB hBN
    rcases uc22s21r899_shape_of_mem hA hLS with hX | hX
    · exact uc22p2213e_exists_centralizesBar hX hpp hp2 hpn hB hBN
    · exact uc22s21r8100_exists_centralizesBar_Sz hX (uc22s21r899_center_bot hL hA hLS) hpp hp2
        hpn hB hBN
  obtain ⟨B₁, hB₁, hB₁c, hB₁card⟩ := hcb K₁ h1S A₀ hA₀el (hA₀N K₁ h1S)
  obtain ⟨B₂, hB₂, hB₂c, hB₂card⟩ :=
    hcb K₂ h2S B₁ (hA₀el.mono hB₁) (hB₁.trans (hA₀N K₂ h2S))
  have hB₂p : p ^ 2 ≤ Nat.card B₂ := by
    rw [hA₀c] at hB₁card
    have h4 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card B₂ :=
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ p * Nat.card B₁ := hB₁card
        _ ≤ p * (p * Nat.card B₂) := Nat.mul_le_mul_left _ hB₂card
        _ = p ^ 2 * Nat.card B₂ := by ring
    exact Nat.le_of_mul_le_mul_left h4 (pow_pos hpp.pos 2)
  obtain ⟨A, hAB, hAel, hAc⟩ := UC6S846.exists_card_p_sq hpp (hA₀el.mono (hB₂.trans hB₁)) hB₂p
  refine ⟨A, hAB.trans (hB₂.trans (hB₁.trans hA₀M)), hAel, hAc, fun e he a ha => ?_⟩
  exact uc22p2213e_comm_mem_pCoreOf h1C h2C (hB₁c a (hB₂ (hAB ha))) (hB₂c a (hAB ha))
    (sup_le_sup (zpowers_le.2 ha₁) (zpowers_le.2 ha₂) he)

end CFSG.LocalAnalysis.UniquenessCase.UC22
