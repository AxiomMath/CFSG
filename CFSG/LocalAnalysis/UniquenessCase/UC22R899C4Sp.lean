module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Pow
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c4_sp_of_scalar {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig)
    (hscalar : ∀ K₁ ∈ conjSetOf D.M L, ∀ K₂ ∈ conjSetOf D.M L, K₁ ≠ K₂ →
      ∀ a₁ a₂ : ↥D.M, (a₁ : G) ∈ K₁ → (a₂ : G) ∈ K₂ → orderOf (a₁ : G) = r →
        orderOf (a₂ : G) = r → ∃ B : Subgroup (Bar2 D.M), IsElemAbelian p B ∧
          Nat.card B = p ^ 2 ∧
          (∀ b ∈ B, ∃ k : ℕ, ∀ u ∈ zpowers (uc22p21cPi D.M a₁) ⊔ zpowers (uc22p21cPi D.M a₂),
            b * u * b⁻¹ = u ^ k) ∧
          ∃ z ∈ B, z ≠ 1 ∧
            ∀ u ∈ zpowers (uc22p21cPi D.M a₁) ⊔ zpowers (uc22p21cPi D.M a₂), z * u = u * z) :
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
  have ha₁M : a₁ ∈ D.M := hEM (Subgroup.mem_sup_left (mem_zpowers a₁))
  have ha₂M : a₂ ∈ D.M := hEM (Subgroup.mem_sup_right (mem_zpowers a₂))
  obtain ⟨B, hBel, hBc, hBpow, z, hzB, hz1, hzc⟩ := hscalar K₁ h1S K₂ h2S hne ⟨a₁, ha₁M⟩
    ⟨a₂, ha₂M⟩ (Subgroup.mem_inf.1 ha₁).2 (Subgroup.mem_inf.1 ha₂).2 ha₁o ha₂o
  set U : Subgroup (Bar2 D.M) :=
    zpowers (uc22p21cPi D.M ⟨a₁, ha₁M⟩) ⊔ zpowers (uc22p21cPi D.M ⟨a₂, ha₂M⟩) with hU
  have hEU : ∀ X ≤ E, barImage D.M X ≤ U := by
    intro X hXE y hy
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hy
    have hE : E ≤ (U.comap (uc22p21cPi D.M)).map D.M.subtype :=
      sup_le (zpowers_le.2 ⟨⟨a₁, ha₁M⟩, Subgroup.mem_sup_left (mem_zpowers _), rfl⟩)
        (zpowers_le.2 ⟨⟨a₂, ha₂M⟩, Subgroup.mem_sup_right (mem_zpowers _), rfl⟩)
    obtain ⟨m', hm'U, hm'⟩ := hE (hXE hm)
    obtain rfl : m' = m := Subtype.ext hm'
    exact hm'U
  have hBN : ∀ X ≤ E, B ≤ normalizer (barImage D.M X : Set (Bar2 D.M)) := fun X hXE =>
    uc22r899c4_le_normalizer_of_pow hBpow (hEU X hXE)
  have hNX : ∀ X ≤ E, 2 ≤ CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE
    obtain ⟨A, hA, hAel, hAc, -⟩ := uc22r899c4_exists_normalizing_copy hpp hp2 hr hr2
      (hXE.trans hEM) (hEel.isPGroup.to_le hXE) hBel (hBN X hXE)
    exact UC6S846.le_pRank' hpp hA hAel (hAc.trans hBc)
  have hzo : orderOf z = p := orderOf_eq_prime (hBel.2 z hzB) hz1
  obtain ⟨A, hA, hAel, hAc, hAD⟩ := uc22r899c4_exists_normalizing_copy hpp hp2 hr hr2 hEM
    hEel.isPGroup (hBel.mono (zpowers_le.2 hzB)) ((zpowers_le.2 hzB).trans (hBN E le_rfl))
  have hAM : A ≤ D.M := hA.trans inf_le_left
  have hAcomm : ∀ e ∈ E, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 D.M := by
    intro e he a ha
    have hu : uc22p21cPi D.M ⟨e, hEM he⟩ ∈ U :=
      hEU E le_rfl (uc22p21c_mem_barImage.2 ⟨_, he, rfl⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hAD ⟨a, hAM ha⟩ ha)
    refine uc22r8100b_comm_mem_pCoreOf (x := ⟨e, hEM he⟩) (k := ⟨a, hAM ha⟩) ?_
    change uc22p21cPi D.M ⟨e, hEM he⟩ * uc22p21cPi D.M ⟨a, hAM ha⟩ =
      uc22p21cPi D.M ⟨a, hAM ha⟩ * uc22p21cPi D.M ⟨e, hEM he⟩
    rw [← hj]
    exact (show Commute _ z from (hzc _ hu).symm).zpow_right j
  have hMO : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf D.M)
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hr hr2 hpp hp2
    (pCoreOf 2 D.M) A E (UC6S846.isPGroup_pCoreOf D.M) (hAM.trans hMO)
    (hEM.trans hMO) hAel.isPGroup hEel.isPGroup hAcomm
  have hA'M : A' ≤ D.M := hA'le.trans (sup_le hAM (Subgroup.map_subtype_le _))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = p ^ 1 := by
    rw [Nat.card_congr eA.toEquiv, hAc, Nat.card_zpowers, hzo, pow_one]
  have hΓ := h76p r hr E hEM hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp (le_inf hA'M hA'C) hA'el hA'c))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (hNX X hXE))
  exact hnot (h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R hR E hEZ hEel hEc hΓ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
