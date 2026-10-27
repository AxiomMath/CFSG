module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13
import CFSG.CGT.Timmesfeld75.Sec3OddSubgroup
import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c3_sp_of_lift_prime {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2)
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

theorem uc22r899c3_sp_of_lift {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig)
    (hlift : ∀ K₁ ∈ conjSetOf D.M L, ∀ K₂ ∈ conjSetOf D.M L, K₁ ≠ K₂ →
      ∀ a₁ a₂ : G, a₁ ∈ K₁ → a₂ ∈ K₂ → orderOf a₁ = r → orderOf a₂ = r →
        ∃ A : Subgroup G, A ≤ D.M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
          ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 D.M) :
    IsStronglyPEmbedded r D.M := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  exact uc22r899c3_sp_of_lift_prime hSg h614 hL hc3 hLS hs hsn hr hrs hpp hp2
    (h76 p hp (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp)) hlift

theorem uc22r899c3_exists_lift {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D : Subgroup (Bar2 M)} (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) {a₁ a₂ : G}
    (ha₁ : a₁ ∈ M) (ha₂ : a₂ ∈ M)
    (hDa : ∀ d ∈ D, d * uc22p21cPi M ⟨a₁, ha₁⟩ = uc22p21cPi M ⟨a₁, ha₁⟩ * d ∧
      d * uc22p21cPi M ⟨a₂, ha₂⟩ = uc22p21cPi M ⟨a₂, ha₂⟩ * d) :
    ∃ A : Subgroup G, A ≤ M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPn : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hpo : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨K, hKc, hKD, hKinj⟩ := CFSG.CGT.Timmesfeld75.osg_exists_lift (CFSG.pCore 2 ↥M)
    CFSG.pCore_isPGroup D (by rw [hDc]; exact hpo.pow)
  have hKel : IsElemAbelian p K := by
    refine UC6S846.isElemAbelian_of_disjoint_ker (uc22p21cPi M) K ?_ (hD.mono ?_)
    · exact Subgroup.disjoint_def.2 fun {x} hxK hxk => hKinj x hxK (MonoidHom.mem_ker.1 hxk)
    · rintro _ ⟨x, hx, rfl⟩
      exact hKD x hx
  refine ⟨K.map M.subtype, Subgroup.map_subtype_le K, hKel.map M.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective M.subtype_injective, hKc, hDc]
  ·
    rintro e he _ ⟨k, hk, rfl⟩
    have hc := hDa _ (hKD k hk)
    let P : Subgroup ↥M :=
      (Subgroup.centralizer {uc22p21cPi M k}).comap (uc22p21cPi M)
    have hx₁ : (⟨a₁, ha₁⟩ : ↥M) ∈ P := Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hc.1
    have hx₂ : (⟨a₂, ha₂⟩ : ↥M) ∈ P := Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hc.2
    have hE : zpowers a₁ ⊔ zpowers a₂ ≤ P.map M.subtype :=
      sup_le (zpowers_le.2 (Subgroup.mem_map.2 ⟨_, hx₁, rfl⟩))
        (zpowers_le.2 (Subgroup.mem_map.2 ⟨_, hx₂, rfl⟩))
    obtain ⟨y, hyP, rfl⟩ := hE he
    exact uc22r8100b_comm_mem_pCoreOf (x := y) (k := k)
      (Subgroup.mem_centralizer_iff.1 hyP _ (Set.mem_singleton _)).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
