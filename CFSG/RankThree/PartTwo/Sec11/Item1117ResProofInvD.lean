module

public import CFSG.RankThree.PartTwo.Sec11.Item1117ResProofChoose
import CFSG.RankThree.PartTwo.Sec11.Item1119ProofBasic
import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofInv
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow
public import CFSG.RankThree.PartTwo.Sec11.Item119K

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item1117ResProof

theorem three_pow_succ_dvd_pow_three_pow_sub_one {v : ℤ} (hv : (3 : ℤ) ∣ v - 1) (j : ℕ) :
    (3 : ℤ) ^ (j + 1) ∣ v ^ 3 ^ j - 1 := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    set w := v ^ 3 ^ j with hw
    have hw1 : (3 : ℤ) ∣ w - 1 := (dvd_pow_self 3 (by omega)).trans ih
    have h3 : (3 : ℤ) ∣ w ^ 2 + w + 1 := by
      obtain ⟨t, ht⟩ := hw1
      refine ⟨3 * t ^ 2 + 3 * t + 1, ?_⟩
      have : w = 3 * t + 1 := by linarith
      rw [this]
      ring
    have e : v ^ 3 ^ (j + 1) - 1 = (w - 1) * (w ^ 2 + w + 1) := by
      rw [hw, pow_succ, pow_mul]
      ring
    rw [e, pow_succ]
    exact mul_dvd_mul ih h3

section Group

variable {X : Type} [Group X] [Finite X]

theorem mem_centralizer_of_conj_eq_zpow {Q : Sylow 3 X} {y n : X}
    (hQy : (Q : Subgroup X) = Subgroup.zpowers y)
    (hn : n ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X)) {v : ℤ} (hv : n * y * n⁻¹ = y ^ v)
    (hv1 : (3 : ℤ) ∣ v - 1) : n * y = y * n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyQ : y ∈ (Q : Subgroup X) := hQy ▸ Subgroup.mem_zpowers y
  obtain ⟨k, hk⟩ := Item1119Proof.exists_orderOf_eq_three_pow'
    (by
      obtain ⟨j, hj⟩ := Q.isPGroup' ⟨y, hyQ⟩
      exact ⟨j, by simpa using congrArg Subtype.val hj⟩)
  set C := Subgroup.centralizer ({y} : Set X) with hC
  have h1 : n ^ 3 ^ k ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 := Item1119Proof.pow_conj_eq_zpow_pow hv (3 ^ k)
    have h3 : y ^ (v ^ 3 ^ k) = y := by
      have hdvd : ((orderOf y : ℕ) : ℤ) ∣ v ^ 3 ^ k - 1 := by
        rw [hk]
        push_cast
        exact (pow_dvd_pow 3 (Nat.le_succ k)).trans (three_pow_succ_dvd_pow_three_pow_sub_one hv1 k)
      have h4 : y ^ (v ^ 3 ^ k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp hdvd
      calc y ^ (v ^ 3 ^ k) = y ^ (v ^ 3 ^ k - 1) * y := by rw [← zpow_add_one]; congr 1; ring
        _ = y := by rw [h4, one_mul]
    rw [h3] at h2
    calc n ^ 3 ^ k * y = (n ^ 3 ^ k * y * (n ^ 3 ^ k)⁻¹) * n ^ 3 ^ k := by group
      _ = y * n ^ 3 ^ k := by rw [h2]
  obtain ⟨f, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos_iff.mpr (isOfFinOrder_of_finite n)).ne' 3 (by norm_num)
  have h5 : n ^ m ∈ C := by
    have hnmQ : n ^ m ∈ (Q : Subgroup X) := by
      have hp : IsPGroup 3 (Subgroup.zpowers (n ^ m)) := by
        refine IsPGroup.of_card (n := f) ?_
        rw [Nat.card_zpowers, orderOf_pow' n (by omega), hnm]
        rw [Nat.gcd_mul_left_left]
        exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (by omega))
      have hle : Subgroup.zpowers (n ^ m) ≤
          Subgroup.normalizer ((Q : Subgroup X) : Set X) :=
        Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hn m)
      have hsup := Q.isPGroup'.to_sup_of_normal_left' hp hle
      have heq := Q.is_maximal' hsup le_sup_left
      rw [← heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [hQy] at hnmQ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hnmQ
    rw [Subgroup.mem_centralizer_singleton_iff, ← hj]
    exact (Commute.self_zpow y j).symm.eq
  have hcop : IsCoprime (m : ℤ) ((3 : ℤ) ^ k) := by
    have : IsCoprime (3 : ℤ) (m : ℤ) :=
      (Prime.coprime_iff_not_dvd Int.prime_three).mpr (by exact_mod_cast hm3)
    exact this.symm.pow_right
  obtain ⟨α, β, hαβ⟩ := hcop
  have hnC : n ∈ C := by
    have e : n = (n ^ m) ^ α * (n ^ 3 ^ k) ^ β := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
      conv_lhs => rw [← zpow_one n]
      congr 1
      push_cast
      linarith
    rw [e]
    exact C.mul_mem (C.zpow_mem h5 α) (C.zpow_mem h1 β)
  exact Subgroup.mem_centralizer_singleton_iff.mp hnC

theorem not_dvd_card_of_normalizer_le_centralizer (hperf : Group.IsPerfect X) (Q : Sylow 3 X)
    [IsMulCommutative (Q : Subgroup X)]
    (hP : Subgroup.normalizer ((Q : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((Q : Subgroup X) : Set X)) : ¬ 3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := MonoidHom.not_dvd_card_ker_transferSylow Q hP
  have h2 : (MonoidHom.transferSylow Q hP).ker = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker _
  rw [h2, Subgroup.card_top] at h1
  exact h1

theorem exists_conj_inv_of_isCyclic_sylow (hperf : Group.IsPerfect X)
    (hcyc : ∀ Q : Sylow 3 X, IsCyclic Q) {δ : X} (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1) :
    ∃ w : X, w * δ * w⁻¹ = δ⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hδp : IsPGroup 3 (Subgroup.zpowers δ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hδ3 hδ1, pow_one]
  obtain ⟨Q, hQ⟩ := hδp.exists_le_sylow
  have hδQ : δ ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers δ)
  have hQc := hcyc Q
  obtain ⟨⟨y, hyQ⟩, hy⟩ := IsCyclic.exists_generator (α := (Q : Subgroup X))
  have hQy : (Q : Subgroup X) = Subgroup.zpowers y := by
    apply le_antisymm
    · intro z hz
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨z, hz⟩)
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_zpow] at this
      rw [← this]
      exact Subgroup.zpow_mem_zpowers y j
    · exact Subgroup.zpowers_le.mpr hyQ
  have hy3 : ∃ j : ℕ, y ^ 3 ^ j = 1 := by
    obtain ⟨j, hj⟩ := Q.isPGroup' ⟨y, hyQ⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  obtain ⟨k, hk⟩ := Item1119Proof.exists_orderOf_eq_three_pow' hy3
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    apply hδ1
    rw [hQy, hk, Subgroup.zpowers_one_eq_bot] at hδQ
    exact Subgroup.mem_bot.mp hδQ
  have h3y : (3 : ℤ) ∣ (orderOf y : ℤ) := by
    rw [hk]
    push_cast
    exact dvd_pow_self 3 hk0
  set V := Subgroup.zpowers (y ^ 3) with hV
  have hyV : y ∉ V := by
    intro hyV
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hyV
    have h1 : y ^ (3 * t - 1) = 1 := by
      have e : y ^ (3 * t) = (y ^ 3) ^ t := by rw [zpow_mul]; norm_cast
      rw [zpow_sub_one, e, ht, mul_inv_cancel]
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    have h3 := h3y.trans h2
    omega
  have hy3V : y ^ 3 ∈ V := Subgroup.mem_zpowers _
  have hNV : ∀ n ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X),
      n ∈ Subgroup.normalizer (V : Set X) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨t, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hny : n * y * n⁻¹ ∈ Subgroup.zpowers y := by
      rw [← hQy]
      exact (Subgroup.mem_normalizer_iff.mp hn y).mp hyQ
    obtain ⟨v, hv⟩ := Subgroup.mem_zpowers_iff.mp hny
    rw [SetLike.mem_coe, ← conj_zpow, ← conj_pow, ← hv]
    have e : ((y ^ v) ^ 3) ^ t = ((y ^ 3) ^ v) ^ t := by
      congr 1
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    rw [e]
    exact V.zpow_mem (V.zpow_mem hy3V v) t
  have hNy : ∀ n ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X),
      n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set X) := fun n hn => hQy ▸ hn
  have hinvV : ∃ n ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X), n * y * n⁻¹ * y ∈ V := by
    by_contra hne
    push Not at hne
    apply not_dvd_card_of_normalizer_le_centralizer hperf Q
    · intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hcen : n * y * n⁻¹ * y⁻¹ ∈ V :=
        (Inverter1118Proof.conj_inv_or_conj (hNy n hn) (hNV n hn) hy3V hyV).resolve_right
          (hne n hn)
      obtain ⟨v, hv⟩ := Subgroup.mem_zpowers_iff.mp
        (Item1119Proof.conj_mem_zpowers_of_mem_normalizer (hNy n hn))
      have hv1 : (3 : ℤ) ∣ v - 1 := by
        obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hcen
        rw [← hv] at ht
        have h1 : y ^ (v - 1 - 3 * t) = 1 := by
          rw [zpow_sub, zpow_sub_one, ← ht, zpow_mul]
          · simp
        have h2 := h3y.trans (orderOf_dvd_iff_zpow_eq_one.mpr h1)
        omega
      have hny := mem_centralizer_of_conj_eq_zpow hQy hn hv.symm hv1
      rw [hQy] at hz
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_right hny j).eq.symm
    · have h1 := orderOf_dvd_natCard δ
      rwa [orderOf_eq_prime hδ3 hδ1] at h1
  obtain ⟨n, hn, hninv⟩ := hinvV
  obtain ⟨e, m, hm2, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos_iff.mpr (isOfFinOrder_of_finite n)).ne' 2 (by norm_num)
  obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
  have hyNV : y ∈ Subgroup.normalizer (V : Set X) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨u, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [SetLike.mem_coe, ← conj_zpow, (Commute.self_pow y 3).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ u
  have hj := Inverter1118Proof.conj_pow_odd_inv (hNV n hn) hyNV hninv t
  set j := n ^ (2 * t + 1) with hjdef
  have hj2 : ∃ e' : ℕ, j ^ 2 ^ e' = 1 :=
    ⟨e, by rw [hjdef, ← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]⟩
  have hjy : j ∈ Subgroup.normalizer (Subgroup.zpowers y : Set X) :=
    Subgroup.pow_mem _ (hNy n hn) _
  have hjinv := Inverter1118Proof.conj_eq_inv_of_two_element hy3 hj2 hjy hyV hj
  rw [hQy] at hδQ
  exact ⟨j, Inverter1118Proof.inverts_of_mem_zpowers hjinv hδQ⟩

omit [Finite X] in
theorem mem_normalizer_of_normal {N : Subgroup X} [hN : N.Normal] (z : X) :
    z ∈ Subgroup.normalizer (N : Set X) :=
  Subgroup.mem_normalizer_iff.mpr fun y => by
    constructor
    · intro hy
      exact hN.conj_mem y hy z
    · intro hy
      have := hN.conj_mem _ hy z⁻¹
      simpa [mul_assoc] using this

theorem exists_conj_inv_of_quotient {N : Subgroup X} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {δ : X} (hδ3 : δ ^ 3 = 1) (hδN : δ ∉ N)
    (hw : ∃ w : X ⧸ N, w * (δ : X ⧸ N) * w⁻¹ = (δ : X ⧸ N)⁻¹) :
    ∃ t : X, t * δ * t⁻¹ = δ⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw⟩ := hw
  obtain ⟨t₁, rfl⟩ := QuotientGroup.mk_surjective w
  set δ' := t₁ * δ * t₁⁻¹ with hδ'
  have hδ1 : δ ≠ 1 := fun h1 => hδN (h1 ▸ N.one_mem)
  have hδo : orderOf δ = 3 := orderOf_eq_prime hδ3 hδ1
  have hδ'N : δ' * δ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hδ', QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, hw, inv_mul_cancel]
  set H := Subgroup.zpowers δ ⊔ N with hH
  have hδH : δ ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers δ)
  have hδ'H : δ' ∈ H := by
    have e : δ' = (δ' * δ) * δ⁻¹ := by group
    rw [e]
    exact H.mul_mem (Subgroup.mem_sup_right hδ'N) (H.inv_mem hδH)
  have hinf : Subgroup.zpowers δ ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro z ⟨hz, hzN⟩
    by_contra hz1
    have hzo : orderOf z = 3 := by
      have h1 := orderOf_dvd_of_mem_zpowers hz
      rw [hδo] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h1
    apply hN
    rw [← hzo]
    exact Subgroup.orderOf_dvd_natCard N hzN
  have hcardH : Nat.card H = 3 * Nat.card N := by
    have h1 := Sec6.card_sup_mul_card_inf (X := Subgroup.zpowers δ) (N := N)
      (fun z _ => mem_normalizer_of_normal z)
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hδo] at h1
    exact h1
  have hfac : (Nat.card H).factorization 3 = 1 := by
    rw [hcardH, Nat.factorization_mul (by norm_num) (by
      intro h0
      rw [h0] at hN
      exact hN (dvd_zero 3)), Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd hN]
  have hδ'3 : orderOf δ' = 3 := by
    have e : δ' = MulAut.conj t₁ δ := by rw [hδ', MulAut.conj_apply]
    rw [e, MulEquiv.orderOf_eq, hδo]
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers δ) H :=
    CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.zpowers_le.mpr hδH)
      (by rw [Nat.card_zpowers, hδo, hfac, pow_one])
  have hS' : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers δ') H :=
    CFSG.ABGLocalTools.isSylowOf_of_card (Subgroup.zpowers_le.mpr hδ'H)
      (by rw [Nat.card_zpowers, hδ'3, hfac, pow_one])
  obtain ⟨SP, hSP⟩ := hS
  obtain ⟨SQ, hSQ⟩ := hS'
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq H SQ SP
  have huδ' : (u : X) * δ' * (u : X)⁻¹ ∈ Subgroup.zpowers δ := by
    have hmem : (⟨δ', hδ'H⟩ : H) ∈ (SQ : Subgroup H) := by
      have : δ' ∈ (SQ : Subgroup H).map H.subtype := hSQ ▸ Subgroup.mem_zpowers δ'
      obtain ⟨z, hz, hzeq⟩ := this
      have : z = ⟨δ', hδ'H⟩ := Subtype.ext hzeq
      rw [← this]
      exact hz
    have hmem' : u * ⟨δ', hδ'H⟩ * u⁻¹ ∈ (SP : Subgroup H) := by
      rw [← hu, Sylow.coe_subgroup_smul]
      exact ⟨_, hmem, rfl⟩
    rw [← hSP]
    exact ⟨_, hmem', rfl⟩
  obtain ⟨i, ν, hν, hui⟩ := Item1119Proof.exists_zpow_mul_of_mem_sup
    (mem_normalizer_of_normal δ) u.2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp huδ'
  have hmod : δ ^ (m + 1) ∈ N := by
    have h1 : (u : X) * δ' * (u : X)⁻¹ * δ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      have hν1 : (ν : X ⧸ N) = 1 := (QuotientGroup.eq_one_iff ν).mpr hν
      have hw' : (δ' : X ⧸ N) = (δ : X ⧸ N)⁻¹ := by
        rw [hδ', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hw]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        hui, QuotientGroup.mk_mul, hν1, mul_one, hw', QuotientGroup.mk_zpow]
      group
    rw [zpow_add_one, hm]
    exact h1
  have h3 : (3 : ℤ) ∣ m + 1 := by
    by_contra h3
    exact hδN (ActOnA.mem_of_zpow_mem hδ3 hmod h3)
  refine ⟨(u : X) * t₁, ?_⟩
  have e : (u : X) * t₁ * δ * ((u : X) * t₁)⁻¹ = (u : X) * δ' * (u : X)⁻¹ := by
    rw [hδ']; group
  rw [e, ← hm]
  calc δ ^ m = δ ^ (m + 1) * δ⁻¹ := by rw [zpow_add_one]; group
    _ = δ⁻¹ := by rw [ActOnA.zpow_eq_one_of_dvd hδ3 h3, one_mul]

end Group

theorem isCyclic_sylow_three_of_isType424 {X : Type} [Group X] [Finite X] (hX : IsType424 X)
    (hQ : IsQuasisimple X) (P : Sylow 3 X) : IsCyclic P :=
  CFSG.RankThree.PartTwo.Sec11.KS11LieProof.isCyclic_sylow_three_of_isType424 hX hQ P

end Item1117ResProof

section Main

open Item1117ResProof in
theorem kFact1118InvD : KFact1118InvD := by
  intro G _ _ A c L a R Y h d hdL hA
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := sec11K L a with hK
  obtain ⟨haN, ha3, hZ, hQ⟩ := h.a_facts
  have hKq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
    isQuasisimple_sec11K_quotient haN ha3 hQ hZ
  have hT := kType119 G A c L a R Y h d hdL hA
  have hcyc := isCyclic_sylow_three_of_isType424 hT hKq
  have hdK : d ∈ K := h.d_mem_sec11K hdL
  have hdA : d ∈ A := by
    have hd : d ∈ A ⊓ L := by
      rw [hdL]
      exact Subgroup.mem_zpowers d
    exact hd.1
  have hd3 : d ^ 3 = 1 := h.mem_partTwoF.1.2 d hdA
  have hd1 : d ≠ 1 := (h.not_mem_facts hdL hA).2.2
  set δ : K := ⟨d, hdK⟩ with hδ
  have hδ3 : δ ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hδ1 : δ ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 K) :=
    (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  have hδθ : δ ∉ aschbacherSolvableCore 3 K := by
    intro hm
    apply hθ
    have h1 := Subgroup.orderOf_dvd_natCard _ hm
    rwa [orderOf_eq_prime hδ3 hδ1] at h1
  have hδb3 : (δ : K ⧸ aschbacherSolvableCore 3 K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hδ3, QuotientGroup.mk_one]
  have hδb1 : (δ : K ⧸ aschbacherSolvableCore 3 K) ≠ 1 := fun h1 =>
    hδθ ((QuotientGroup.eq_one_iff δ).mp h1)
  obtain ⟨t, ht⟩ := exists_conj_inv_of_quotient hθ hδ3 hδθ
    (exists_conj_inv_of_isCyclic_sylow hKq.1 hcyc hδb3 hδb1)
  refine ⟨t, t.2, ?_⟩
  have := congrArg Subtype.val ht
  simpa [hδ] using this

end Main

section MainList

theorem kFact1118Inverter_of_elt (h45 : Sec4.Item4_5) (h117 : Item117)
    (hE : KFact1118InvElt) : KFact1118Inverter :=
  kFact1118Inverter_of h45 h117 kFact1118InvD hE

end MainList

end CFSG.RankThree.PartTwo.Sec11
