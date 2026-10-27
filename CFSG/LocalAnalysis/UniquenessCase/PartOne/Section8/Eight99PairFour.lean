module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem r899_sp_of_pair_centralizing {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) {K₁ K₂ : Subgroup G}
    (h1C : K₁ ∈ calC D.M) (h2C : K₂ ∈ calC D.M) (hne : K₁ ≠ K₂) {n₁ n₂ s r : ℕ}
    (h1S : IsL2 (Bar2 K₁) n₁ ∨ IsSz (Bar2 K₁) n₁) (h2S : IsL2 (Bar2 K₂) n₂ ∨ IsSz (Bar2 K₂) n₂)
    (hs₁ : s ∣ n₁) (hs₂ : s ∣ n₂) (hr : r.Prime) (hr2 : r ≠ 2) (hrs : r ∣ 2 ^ s - 1)
    (hRN : ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R D.M →
      R ≤ normalizer (K₁ : Set G) ∧ R ≤ normalizer (K₂ : Set G))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h76p : Conclusion76 D.M p)
    {A : Subgroup G} (hAM : A ≤ D.M) (hAel : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hA : ∀ a ∈ A, CentralizesBar a K₁ ∧ CentralizesBar a K₂) :
    IsStronglyPEmbedded r D.M := by
  classical
  have hns := UC6S846.not_solvable_of_mem_calC h1C
  by_cases hrσ : r ∈ D.sig
  · exact UC6S846.sp_of_mem_sig hSg hns hrσ
  have : Fact r.Prime := ⟨hr⟩
  have hZ : center (Bar2 K₁) = ⊥ := by
    rcases h1S with hX | hX
    · exact uc22p22g_center_bot hX
    · have := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
      exact uc22p21k_center_eq_bot h1C.2.2
  have hdvd₁ : r ∣ Nat.card K₁ :=
    (PartTwo.s13_dvd_card_of_isL2_or_isSz h1S hs₁ hr hrs).trans
      (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₁))
  have hdvd₂ : r ∣ Nat.card K₂ :=
    (PartTwo.s13_dvd_card_of_isL2_or_isSz h2S hs₂ hr hrs).trans
      (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K₂))
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf r D.M
  have hRp : IsPGroup r R := hR.isPGroup
  have hRM : R ≤ D.M := hR.le
  have hRN₁ : R ≤ normalizer (K₁ : Set G) := (hRN R hR).1
  have hRN₂ : R ≤ normalizer (K₂ : Set G) := (hRN R hR).2
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal h1C.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal h2C.1
  have hRK₁ : R ⊓ K₁ ≠ ⊥ := by
    intro hbot
    have hRA := (hR.of_le (le_inf hRM hRN₁) inf_le_left).inf_of_le_normalizer
      (le_inf hK₁M Subgroup.le_normalizer) inf_le_right
    have hv : 1 ≤ (Nat.card K₁).factorization r :=
      (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1 hdvd₁
    have hc := hRA.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have h1 : r ^ 1 ≤ r ^ (Nat.card K₁).factorization r := Nat.pow_le_pow_right hr.pos hv
    rw [pow_one] at h1
    have := hr.two_le
    omega
  have hRK₂ : R ⊓ K₂ ≠ ⊥ := by
    intro hbot
    have hRA := (hR.of_le (le_inf hRM hRN₂) inf_le_left).inf_of_le_normalizer
      (le_inf hK₂M Subgroup.le_normalizer) inf_le_right
    have hv : 1 ≤ (Nat.card K₂).factorization r :=
      (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1 hdvd₂
    have hc := hRA.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have h1 : r ^ 1 ≤ r ^ (Nat.card K₂).factorization r := Nat.pow_le_pow_right hr.pos hv
    rw [pow_one] at h1
    have := hr.two_le
    omega
  obtain ⟨a₁, ha₁, ha₁o, ha₁c⟩ :=
    CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer hr hRp inf_le_left
      ((le_inf Subgroup.le_normalizer hRN₁).trans Subgroup.inf_normalizer_le_normalizer_inf) hRK₁
  obtain ⟨a₂, ha₂, ha₂o, ha₂c⟩ :=
    CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer hr hRp inf_le_left
      ((le_inf Subgroup.le_normalizer hRN₂).trans Subgroup.inf_normalizer_le_normalizer_inf) hRK₂
  have hna : a₂ ∉ zpowers a₁ := by
    intro h
    have h1 : a₂ = 1 := uc22p2213e_eq_one_of_mem_inf h1C h2C hne hZ hr hr2
      (zpowers_le.2 (Subgroup.mem_inf.1 ha₁).2 h) (Subgroup.mem_inf.1 ha₂).2
      (by rw [← ha₂o]; exact pow_orderOf_eq_one a₂)
    rw [h1, orderOf_one] at ha₂o
    have := hr.one_lt
    omega
  obtain ⟨hEel', hEc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card ha₁o
      ha₂o (Subgroup.mem_centralizer_iff.1 ha₂c a₁ (Subgroup.mem_inf.1 ha₁).1) hna
  set E : Subgroup G := zpowers a₁ ⊔ zpowers a₂ with hE
  have hEel : IsElemAbelian r E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r E).1 hEel'
  have hEZ : E ≤ R ⊓ centralizer (R : Set G) :=
    sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₁).1, ha₁c⟩))
      (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₂).1, ha₂c⟩))
  have hEK : E ≤ K₁ ⊔ K₂ :=
    sup_le_sup (zpowers_le.2 (Subgroup.mem_inf.1 ha₁).2)
      (zpowers_le.2 (Subgroup.mem_inf.1 ha₂).2)
  have hEM : E ≤ D.M := hEZ.trans (inf_le_left.trans hRM)
  have hMO : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf D.M)
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hr hr2 hp hp2
    (pCoreOf 2 D.M) A E (UC6S846.isPGroup_pCoreOf D.M) (hAM.trans hMO) (hEM.trans hMO)
    hAel.isPGroup hEel.isPGroup (fun e he a ha =>
      uc22p2213e_comm_mem_pCoreOf h1C h2C (hA a ha).1 (hA a ha).2 (hEK he))
  have hA'M : A' ≤ D.M := hA'le.trans (sup_le hAM (Subgroup.map_subtype_le _))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = p ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
  have hΓ := h76p r hr E hEM hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hp (le_inf hA'M hA'C) hA'el hA'c))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hp
      (le_inf hA'M (hA'C.trans ((Subgroup.centralizer_le hXE).trans
        (Subgroup.centralizer_le_normalizer _)))) hA'el hA'c))
  exact h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R hR E hEZ hEel hEc hΓ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
