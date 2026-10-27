module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Sz
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

theorem isSz_exists_orderOf_commute {X : Type} [Group X] {n : ℕ}
    (h : IsSz X n) {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1)
    (hq : q.Prime) (hqn : q ∣ 2 ^ n - 1) {a : X} (ha : orderOf a = r) :
    ∃ b : X, orderOf b = q ∧ a * b = b * a := by
  obtain ⟨-, -, k, -, K, _, _, rfl, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel h
  have hea : orderOf (e a) = r := by rw [MulEquiv.orderOf_eq]; exact ha
  obtain ⟨g, hg⟩ := CFSG.LieType.Ree.exists_conj_mem_suzukiT hK hr hr2 hrn hea
  have hT := CFSG.LieType.Ree.suzuki_borel_structure hK
  have : Fact q.Prime := ⟨hq⟩
  have := CFSG.LieType.Ree.finite_suzukiGroup hK
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.LieType.Ree.suzukiT k K)) q
    (by rw [hT.2.2.1]; exact hqn)
  have hcomm : e a * (g * (t : _) * g⁻¹) = g * (t : _) * g⁻¹ * e a := by
    have hc := hT.2.1 _ hg _ t.2
    calc e a * (g * (t : _) * g⁻¹) = g * ((g⁻¹ * e a * g) * (t : _)) * g⁻¹ := by group
      _ = g * ((t : _) * (g⁻¹ * e a * g)) * g⁻¹ := by rw [hc]
      _ = g * (t : _) * g⁻¹ * e a := by group
  refine ⟨e.symm (g * (t : _) * g⁻¹), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, ht]
  · apply e.injective
    rw [map_mul e, map_mul e, e.apply_symm_apply]
    exact hcomm

theorem isSz_exists_orderOf_commute_mem {Γ : Type} [Group Γ]
    {K : Subgroup Γ} {n : ℕ} (hK : IsSz K n) {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ n - 1) (hq : q.Prime) (hqn : q ∣ 2 ^ n - 1) {a : Γ} (haK : a ∈ K)
    (ha : orderOf a = r) : ∃ b ∈ K, orderOf b = q ∧ a * b = b * a := by
  obtain ⟨b, hbo, hab⟩ := isSz_exists_orderOf_commute hK hr hr2 hrn hq hqn (a := ⟨a, haK⟩)
    ((Subgroup.orderOf_coe (⟨a, haK⟩ : K)).symm.trans ha)
  exact ⟨b, b.2, (Subgroup.orderOf_coe b).trans hbo, congrArg Subtype.val hab⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_of_isSz_torus {M K₁ K₂ : Subgroup G}
    {n q r : ℕ} (h₁ : K₁ ∈ calC M) (h₂ : K₂ ∈ calC M) (hne : K₁ ≠ K₂)
    (hS₁ : IsSz (Bar2 K₁) n) (hS₂ : IsSz (Bar2 K₂) n) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqn : q ∣ 2 ^ n - 1) (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1)
    {a₁ a₂ : G} (ha₁ : a₁ ∈ K₁) (ha₂ : a₂ ∈ K₂) (ha₁o : orderOf a₁ = r)
    (ha₂o : orderOf a₂ = r) :
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
  have hT₁ : IsSz (barImage M K₁) n := CFSG.Blueprint.LieModel.of_mulEquiv e₁ hS₁
  have hT₂ : IsSz (barImage M K₂) n := CFSG.Blueprint.LieModel.of_mulEquiv e₂ hS₂
  have hx₁ : uc22p21cPi M ⟨a₁, hK₁M ha₁⟩ ∈ barImage M K₁ :=
    uc22p21c_mem_barImage.2 ⟨⟨a₁, hK₁M ha₁⟩, ha₁, rfl⟩
  have hx₂ : uc22p21cPi M ⟨a₂, hK₂M ha₂⟩ ∈ barImage M K₂ :=
    uc22p21c_mem_barImage.2 ⟨⟨a₂, hK₂M ha₂⟩, ha₂, rfl⟩
  obtain ⟨b₁, hb₁, hb₁o, hb₁c⟩ :=
    isSz_exists_orderOf_commute_mem hT₁ hr hr2 hrn hq hqn hx₁ (hord (hK₁M ha₁) ha₁o)
  obtain ⟨b₂, hb₂, hb₂o, hb₂c⟩ :=
    isSz_exists_orderOf_commute_mem hT₂ hr hr2 hrn hq hqn hx₂ (hord (hK₂M ha₂) ha₂o)
  have hcomm := uc22p22l_barImage_commute h₁ h₂ hne
  have hZ₁ : center (Bar2 K₁) = ⊥ :=
    uc22s21r899_center_bot h₁ (K := K₁) ⟨1, M.one_mem, by ext y; simp⟩ (Or.inr hS₁)
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

theorem sp_of_isSz_torus {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1)
    (h76q : Conclusion76 D.M q) : IsStronglyPEmbedded r D.M := by
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hshape : ∀ K ∈ conjSetOf D.M L, IsSz (Bar2 K) n := by
    rintro K ⟨g, -, rfl⟩
    obtain ⟨e⟩ := uc22p20d_bar2_conj g L
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hSz
  refine uc22r899c3_sp_of_lift_prime hSg h614 hL hc3 (Or.inr hSz) hs hsn hr hrs hq hq2 h76q ?_
  intro K₁ h1S K₂ h2S hne a₁ a₂ ha₁ ha₂ ha₁o ha₂o
  exact exists_lift_of_isSz_torus (uc22p2214_calC_of_mem_conjSetOf hL h1S)
    (uc22p2214_calC_of_mem_conjSetOf hL h2S) hne (hshape K₁ h1S) (hshape K₂ h2S) hq hq2 hqn hr
    hr2 hrn ha₁ ha₂ ha₁o ha₂o

theorem sp_of_isSz_cyclic {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : F07.R76 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ} (hSz : IsSz (Bar2 L) n) {s r : ℕ}
    (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig)
    (hp3 : p % 3 = 1) (hpn : p ∣ n) (hp2n : p ∣ 2 ^ (2 * n) + 1) :
    IsStronglyPEmbedded r D.M := by
  obtain ⟨m, hn⟩ := hpn
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  have h76s : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p :=
    fun p hp hsp => F07.R76Sig_of_R76 D h76 p hp (D.sig_prime p hp).2 hsp
  have hnodd : Odd n := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
  have hmodd : Odd m := by
    rw [hn] at hnodd
    exact (Nat.odd_mul.1 hnodd).2
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hn
    subst hn
    have : Fact n.Prime := ⟨hpp⟩
    have h5 : n ∣ 5 := by
      rw [← ZMod.natCast_eq_zero_iff] at hp2n ⊢
      push_cast at hp2n ⊢
      rw [pow_mul, ZMod.pow_card] at hp2n
      linear_combination hp2n
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).1 h5
    omega
  have hm2 : 2 ≤ m := by
    obtain ⟨k, hk⟩ := hmodd
    omega
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
  have hq2 : q ≠ 2 := uc22ine229_ne_two hmodd hqm
  have hmn : m ∣ n := ⟨p, by rw [hn, mul_comm]⟩
  have hqn : q ∣ 2 ^ n - 1 := hqm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hmn)
  have hspq : IsStronglyPEmbedded q D.M :=
    uc22r899c3_sp_of_odd_factor_Sz hSg hfour h614 h76s hL hc3 hSz hmodd hmn hq hqm hp hn hp2n
      hqm
  exact sp_of_isSz_torus hSg h614 hL hc3 hSz hs hsn hr hrs hq hq2 hqn (h76 q hq hq2 hspq)

end CFSG.LocalAnalysis.UniquenessCase.UC22
