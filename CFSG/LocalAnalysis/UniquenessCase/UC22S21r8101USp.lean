module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UBar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XI
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem u81_sp_of_two_le_pRank (u : U4X D L K n)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h2 : 2 ≤ CFSG.Open.pRank n (centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)))) :
    IsStronglyPEmbedded (2 ^ n - 1) D.M := by
  by_contra hnot
  have hns := UC6S846.not_solvable_of_mem_calC u.hL
  have hr := u.prime_r
  have hr2 := u.r_ne_two
  have hn := u.prime_n
  have hn2 : n ≠ 2 := by rcases u.hLS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : Fact (2 ^ n - 1).Prime := ⟨hr⟩
  have hrσ : 2 ^ n - 1 ∉ D.sig := fun h => hnot (UC6S846.sp_of_mem_sig hSg hns h)
  have h76n := h76 n u.hσ (UC6S846.sp_of_mem_sig hSg hns u.hσ)
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf (2 ^ n - 1) D.M
  have hZR : ∀ {Y Y' : Subgroup G}, U4X D Y Y' n →
      ∃ a ∈ R ⊓ Y, orderOf a = 2 ^ n - 1 ∧ a ∈ centralizer (R : Set G) := by
    intro Y Y' v
    have hYM : Y ≤ D.M := v.hL.1.le
    have hRN : R ≤ normalizer (Y : Set G) := fun g hg => by
      obtain ⟨k, hk⟩ := hR.isPGroup ⟨g, hg⟩
      have hg3 : g ^ (2 ^ n - 1) ^ k = 1 := congrArg Subtype.val hk
      exact uc22p2214_mem_normalizer_of_odd v.hc2 (hR.le hg)
        ((hr.odd_of_ne_two hr2).pow.of_dvd_nat (orderOf_dvd_of_pow_eq_one hg3))
    have hRY := (hR.of_le (le_inf hR.le hRN) inf_le_left).inf_of_le_normalizer
      (le_inf hYM Subgroup.le_normalizer) inf_le_right
    have hne : R ⊓ Y ≠ ⊥ := by
      intro hbot
      have hv : 1 ≤ (Nat.card Y).factorization (2 ^ n - 1) :=
        (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1
          ((u81_dvd_card v.hLS).1.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥Y)))
      have hc := hRY.card_eq
      rw [hbot, Subgroup.card_bot] at hc
      have h1 : (2 ^ n - 1) ^ 1 ≤ (2 ^ n - 1) ^ (Nat.card Y).factorization (2 ^ n - 1) :=
        Nat.pow_le_pow_right hr.pos hv
      rw [pow_one] at h1
      exact lt_irrefl 1 (lt_of_lt_of_le hr.one_lt (h1.trans hc.symm.le))
    exact CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer hr hR.isPGroup
      inf_le_left ((le_inf Subgroup.le_normalizer hRN).trans
        Subgroup.inf_normalizer_le_normalizer_inf) hne
  obtain ⟨a₁, ha₁, ha₁o, ha₁c⟩ := hZR u
  obtain ⟨a₂, ha₂, ha₂o, ha₂c⟩ := hZR u.symm
  have hZL : center (Bar2 L) = ⊥ := by
    rcases u.shape with hX | hX
    · exact uc22p22g_center_bot hX
    · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
      exact uc22p21k_center_eq_bot u.hL.2.2
  have hna : a₂ ∉ zpowers a₁ := by
    intro h
    have h1 : a₂ = 1 := uc22p2213e_eq_one_of_mem_inf u.hL u.hK u.hne.symm hZL hr hr2
      (zpowers_le.2 (Subgroup.mem_inf.1 ha₁).2 h) (Subgroup.mem_inf.1 ha₂).2
      (by rw [← ha₂o]; exact pow_orderOf_eq_one a₂)
    rw [h1, orderOf_one] at ha₂o
    exact hr.one_lt.ne ha₂o
  obtain ⟨hEel', hEc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card ha₁o
      ha₂o (Subgroup.mem_centralizer_iff.1 ha₂c a₁ (Subgroup.mem_inf.1 ha₁).1) hna
  set E : Subgroup G := zpowers a₁ ⊔ zpowers a₂
  have hEel : IsElemAbelian (2 ^ n - 1) E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian _ E).1 hEel'
  have hEZ : E ≤ R ⊓ centralizer (R : Set G) :=
    sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₁).1, ha₁c⟩))
      (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₂).1, ha₂c⟩))
  have hEK : E ≤ L ⊔ K :=
    sup_le_sup (zpowers_le.2 (Subgroup.mem_inf.1 ha₁).2) (zpowers_le.2 (Subgroup.mem_inf.1 ha₂).2)
  have hEM : E ≤ D.M := hEZ.trans (inf_le_left.trans hR.le)
  obtain ⟨Eb, hEbC, hEbel, hEbc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hn h2
  have hker : IsPGroup 2 (uc22p21cPi D.M).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, -, hQmap, hQdisj⟩ := UC6S846.exists_lift_pGroup (uc22p21cPi D.M)
    (uc22p21c_pi_surjective D.M) hker hn hn2 Eb hEbel.isPGroup
  have hQel : IsElemAbelian n Q :=
    UC6S846.isElemAbelian_of_disjoint_ker _ Q hQdisj (by rw [hQmap]; exact hEbel)
  have hAel : IsElemAbelian n (Q.map D.M.subtype) := hQel.map D.M.subtype
  have hAc : Nat.card (Q.map D.M.subtype) = n ^ 2 := by
    rw [Subgroup.card_map_of_injective D.M.subtype_injective,
      ← UC6S846.card_map_of_disjoint_ker _ Q hQdisj, hQmap, hEbc]
  have hLK : barImage D.M (L ⊔ K) = barImage D.M L ⊔ barImage D.M K :=
    u4x_barImage_sup u.hL.1.le u.hK.1.le
  have hcomm : ∀ e ∈ E, ∀ a ∈ Q.map D.M.subtype, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 D.M := by
    intro e he a ha
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 ha
    have hqC : uc22p21cPi D.M q ∈ centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) :=
      hEbC (hQmap ▸ Subgroup.mem_map_of_mem _ hq)
    set m : ↥D.M := ⟨e, hEM he⟩
    have hmX : uc22p21cPi D.M m ∈ barImage D.M L ⊔ barImage D.M K :=
      hLK ▸ uc22p21c_mem_barImage.2 ⟨m, hEK he, rfl⟩
    have h1 : uc22p21cPi D.M (m * q * m⁻¹ * q⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [mem_centralizer_iff.1 hqC _ hmX]
      group
    exact ⟨m * q * m⁻¹ * q⁻¹, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hMO : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf D.M)
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hr hr2 hn hn2
    (pCoreOf 2 D.M) (Q.map D.M.subtype) E (UC6S846.isPGroup_pCoreOf D.M)
    ((map_subtype_le Q).trans hMO) (hEM.trans hMO) hAel.isPGroup hEel.isPGroup hcomm
  have hA'M : A' ≤ D.M := hA'le.trans (sup_le (map_subtype_le Q) (map_subtype_le _))
  have hA'el : IsElemAbelian n A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = n ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
  have hΓ := h76n (2 ^ n - 1) hr E hEM hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hn (le_inf hA'M hA'C) hA'el hA'c))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hn
      (le_inf hA'M (hA'C.trans ((Subgroup.centralizer_le hXE).trans
        (Subgroup.centralizer_le_normalizer _)))) hA'el hA'c))
  exact hnot (h614 (UC6S846.sig_subset_sig1 hSg hns) _ hr hr2 hrσ R hR E hEZ hEel hEc hΓ)

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
