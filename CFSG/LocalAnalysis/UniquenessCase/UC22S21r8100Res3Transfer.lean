module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Cert13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.EvenBN.Common
open scoped MatrixGroups
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem isL2_exists_orderOf_commute {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2 X n)
    {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) (hq : q.Prime)
    (hqn : q ∣ 2 ^ n - 1) {a : X} (ha : orderOf a = r) :
    ∃ b : X, orderOf b = q ∧ a * b = b * a := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e₁⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  let e : X ≃* SL(2, K) := e₁.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K))
  have hea : orderOf (e a) = r := by rw [MulEquiv.orderOf_eq]; exact ha
  have hea1 : e a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hea
    exact hr.one_lt.ne hea
  have heaK : (e a) ^ (Nat.card K - 1) = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    rw [hea, hK]
    exact hrn
  obtain ⟨x, μ, hμ, hx⟩ := exists_conj_eq_diagSL hea1 heaK
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(torusSL K)) q
    (by rw [card_torusSL, hK]; exact hqn)
  have hT : ∀ s ∈ torusSL K, ∀ u ∈ torusSL K, s * u = u * s := by
    intro s hs u hu
    obtain ⟨σ, rfl⟩ := mem_torusSL_iff.1 hs
    obtain ⟨υ, rfl⟩ := mem_torusSL_iff.1 hu
    rw [diagSL_mul, diagSL_mul, mul_comm σ υ]
  have heq : e a = x⁻¹ * diagSL μ * x := by
    rw [← hx]
    group
  have hdt : diagSL μ * (t : SL(2, K)) = (t : SL(2, K)) * diagSL μ :=
    hT _ (diagSL_mem_torusSL μ) _ t.2
  have hcomm : e a * (x⁻¹ * (t : SL(2, K)) * x) =
      (x⁻¹ * (t : SL(2, K)) * x) * e a := by
    rw [heq]
    calc x⁻¹ * diagSL μ * x * (x⁻¹ * (t : SL(2, K)) * x)
        = x⁻¹ * (diagSL μ * (t : SL(2, K))) * x := by group
      _ = x⁻¹ * ((t : SL(2, K)) * diagSL μ) * x := by rw [hdt]
      _ = x⁻¹ * (t : SL(2, K)) * x * (x⁻¹ * diagSL μ * x) := by group
  have hconj : x⁻¹ * (t : SL(2, K)) * x = MulAut.conj x⁻¹ (t : SL(2, K)) := by
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨e.symm (x⁻¹ * (t : SL(2, K)) * x), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hconj, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ht]
  · apply e.injective
    simpa using hcomm

theorem isL2_exists_orderOf_commute_mem {Γ : Type} [Group Γ] [Finite Γ] {K : Subgroup Γ}
    {n : ℕ}
    (hK : IsL2 K n) {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1)
    (hq : q.Prime) (hqn : q ∣ 2 ^ n - 1) {a : Γ} (haK : a ∈ K) (ha : orderOf a = r) :
    ∃ b ∈ K, orderOf b = q ∧ a * b = b * a := by
  obtain ⟨b, hbo, hab⟩ := isL2_exists_orderOf_commute hK hr hr2 hrn hq hqn (a := ⟨a, haK⟩)
    ((Subgroup.orderOf_coe (⟨a, haK⟩ : K)).symm.trans ha)
  exact ⟨b, b.2, (Subgroup.orderOf_coe b).trans hbo, congrArg Subtype.val hab⟩

theorem exists_lift_of_isL2_torus {M K₁ K₂ : Subgroup G} {n q r : ℕ} (h₁ : K₁ ∈ calC M)
    (h₂ : K₂ ∈ calC M) (hne : K₁ ≠ K₂) (hS₁ : IsL2 (Bar2 K₁) n) (hS₂ : IsL2 (Bar2 K₂) n)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ n - 1) {a₁ a₂ : G} (ha₁ : a₁ ∈ K₁) (ha₂ : a₂ ∈ K₂)
    (ha₁o : orderOf a₁ = r) (ha₂o : orderOf a₂ = r) :
    ∃ A : Subgroup G, A ≤ M ∧ IsElemAbelian q A ∧ Nat.card A = q ^ 2 ∧
      ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  have hPn : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hK₁M : K₁ ≤ M := uc22p22a_le_of_isSubnormal h₁.1
  have hK₂M : K₂ ≤ M := uc22p22a_le_of_isSubnormal h₂.1
  have hord : ∀ {a : G} (ha : a ∈ M), orderOf a = r → orderOf (uc22p21cPi M ⟨a, ha⟩) = r := by
    intro a ha hao
    have hx : orderOf (⟨a, ha⟩ : ↥M) = r := (Subgroup.orderOf_coe (⟨a, ha⟩ : ↥M)).symm.trans hao
    have hdvd : orderOf (uc22p21cPi M ⟨a, ha⟩) ∣ r := by
      rw [← hx]
      exact orderOf_map_dvd (uc22p21cPi M) _
    refine ((Nat.dvd_prime hr).1 hdvd).resolve_left fun h1 => ?_
    have hxq : (⟨a, ha⟩ : ↥M) ^ r = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
    have h2 := uc22r8100b_eq_one_of_mem_pCore
      ((QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)) (hr.odd_of_ne_two hr2) hxq
    rw [h2, orderOf_one] at hx
    exact hr.one_lt.ne hx
  obtain ⟨e₁, -⟩ := uc22p22l_barImage_equiv h₁
  obtain ⟨e₂, -⟩ := uc22p22l_barImage_equiv h₂
  have hT₁ : IsL2 (barImage M K₁) n := CFSG.Blueprint.LieModel.of_mulEquiv e₁ hS₁
  have hT₂ : IsL2 (barImage M K₂) n := CFSG.Blueprint.LieModel.of_mulEquiv e₂ hS₂
  have hx₁ : uc22p21cPi M ⟨a₁, hK₁M ha₁⟩ ∈ barImage M K₁ :=
    uc22p21c_mem_barImage.2 ⟨⟨a₁, hK₁M ha₁⟩, ha₁, rfl⟩
  have hx₂ : uc22p21cPi M ⟨a₂, hK₂M ha₂⟩ ∈ barImage M K₂ :=
    uc22p21c_mem_barImage.2 ⟨⟨a₂, hK₂M ha₂⟩, ha₂, rfl⟩
  obtain ⟨b₁, hb₁, hb₁o, hb₁c⟩ :=
    isL2_exists_orderOf_commute_mem hT₁ hr hr2 hrn hq hqn hx₁ (hord (hK₁M ha₁) ha₁o)
  obtain ⟨b₂, hb₂, hb₂o, hb₂c⟩ :=
    isL2_exists_orderOf_commute_mem hT₂ hr hr2 hrn hq hqn hx₂ (hord (hK₂M ha₂) ha₂o)
  have hcomm := uc22p22l_barImage_commute h₁ h₂ hne
  have hZ₁ : center (Bar2 K₁) = ⊥ := uc22p22g_center_bot hS₁
  have hna : b₂ ∉ zpowers b₁ := by
    intro hb
    have hb₂K₁ : b₂ ∈ barImage M K₁ := zpowers_le.2 hb₁ hb
    have hcen : e₁.symm ⟨b₂, hb₂K₁⟩ ∈ center (Bar2 K₁) := by
      refine Subgroup.mem_center_iff.2 fun y => e₁.injective ?_
      rw [map_mul, map_mul, e₁.apply_symm_apply]
      exact Subtype.ext (hcomm _ (e₁ y).2 b₂ hb₂)
    rw [hZ₁, Subgroup.mem_bot] at hcen
    have h1 : b₂ = 1 := by
      have h' := congrArg (fun z => ((e₁ z : barImage M K₁) : Bar2 M)) hcen
      simpa using h'
    rw [h1, orderOf_one] at hb₂o
    exact hq.one_lt.ne hb₂o
  obtain ⟨hDel', hDc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card hb₁o
      hb₂o (hcomm b₁ hb₁ b₂ hb₂) hna
  have hDel : IsElemAbelian q (zpowers b₁ ⊔ zpowers b₂) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q _).1 hDel'
  have hle : zpowers b₁ ⊔ zpowers b₂ ≤ centralizer {uc22p21cPi M ⟨a₁, hK₁M ha₁⟩} ⊓
      centralizer {uc22p21cPi M ⟨a₂, hK₂M ha₂⟩} :=
    sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hb₁c.symm,
        Subgroup.mem_centralizer_singleton_iff.2 (hcomm b₁ hb₁ _ hx₂)⟩))
      (zpowers_le.2 (Subgroup.mem_inf.2
        ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm _ hx₁ b₂ hb₂).symm,
          Subgroup.mem_centralizer_singleton_iff.2 hb₂c.symm⟩))
  refine uc22r899c3_exists_lift hq hq2 hDel hDc (hK₁M ha₁) (hK₂M ha₂) fun d hd => ?_
  obtain ⟨hd₁, hd₂⟩ := Subgroup.mem_inf.1 (hle hd)
  exact ⟨Subgroup.mem_centralizer_singleton_iff.1 hd₁,
    Subgroup.mem_centralizer_singleton_iff.1 hd₂⟩

theorem uc22s21r8100_sp_of_lift_prime {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) (hpr : p ≠ r)
    (h76p : Conclusion76 D.M p)
    (hlift : ∀ K₁ ∈ conjSetOf D.M L, ∀ K₂ ∈ conjSetOf D.M L, K₁ ≠ K₂ →
      ∀ a₁ a₂ : G, a₁ ∈ K₁ → a₂ ∈ K₂ → orderOf a₁ = r → orderOf a₂ = r →
        ∃ A : Subgroup G, A ≤ D.M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
          ∀ e ∈ zpowers a₁ ⊔ zpowers a₂, ∀ a ∈ A, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 D.M) :
    IsStronglyPEmbedded r D.M := by
  by_contra hnot
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hrσ : r ∉ D.sig := fun h => hnot (UC6S846.sp_of_mem_sig hSg hns h)
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
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

theorem r8100Res3_of_r76 {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : F07.R76 D) : R8100Res3 D := by
  intro _ L n s r p k hL hc2 hL2 hs hsn hr hrs hp hk hn hcong
  have h76s : ∀ q ∈ D.sig, IsStronglyPEmbedded q D.M → Conclusion76 D.M q :=
    fun q hq hsp => F07.R76Sig_of_R76 D h76 q hq (D.sig_prime q hq).2 hsp
  have h2n : 2 ∣ n := by
    rw [hn]
    refine Dvd.dvd.mul_right ?_ p
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ']
    exact dvd_mul_right 2 (2 ^ j)
  have hn3 : 3 ∣ 2 ^ n - 1 := by
    simpa using Nat.pow_sub_one_dvd_pow_sub_one 2 h2n
  have h3k : 3 ∣ 2 ^ (2 ^ k) - 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h4 : 2 ^ (2 ^ (j + 1)) = 4 ^ (2 ^ j) := by
      rw [pow_succ' 2 j, pow_mul]
      norm_num
    rw [h4]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 (2 ^ j)
  have hpn : p ∣ 2 ^ n + 1 := by
    have h1 : (p : ℤ) ∣ (2 : ℤ) ^ n + 1 := by
      have h2 := Int.modEq_iff_dvd.mp hcong
      rw [show -1 - (2 : ℤ) ^ n = -((2 : ℤ) ^ n + 1) by ring] at h2
      exact dvd_neg.1 h2
    exact Int.natCast_dvd_natCast.1 (by push_cast; exact h1)
  have h3sp : IsStronglyPEmbedded 3 D.M :=
    uc22s21r8100_sp_of_odd_factor hSg hfour h614 h76s hL hc2 hL2 ⟨p, hn⟩
      Nat.prime_three (by norm_num) h3k hp (by rw [hn, mul_comm]) hpn h3k
  have h763 : Conclusion76 D.M 3 := h76 3 Nat.prime_three (by norm_num) h3sp
  rcases eq_or_ne r 3 with rfl | hr3
  · exact h3sp
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  refine uc22s21r8100_sp_of_lift_prime hSg h614 hL hc2 (Or.inl hL2) hs hsn hr hrs
    Nat.prime_three (by norm_num) (Ne.symm hr3) h763 ?_
  intro K₁ h1S K₂ h2S hne a₁ a₂ ha₁ ha₂ ha₁o ha₂o
  exact exists_lift_of_isL2_torus (uc22p2214_calC_of_mem_conjSetOf hL h1S)
    (uc22p2214_calC_of_mem_conjSetOf hL h2S) hne (uc22s21r899_isL2_of_mem h1S hL2)
    (uc22s21r899_isL2_of_mem h2S hL2) Nat.prime_three (by norm_num) hn3 hr hr2 hrn
    ha₁ ha₂ ha₁o ha₂o

end CFSG.LocalAnalysis.UniquenessCase.UC22
