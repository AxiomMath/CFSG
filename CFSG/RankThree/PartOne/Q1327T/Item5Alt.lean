module

public import CFSG.RankThree.PartOne.Q1327T.ItemBasic
public import CFSG.RankThree.PartOne.Mult.Alternating
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne Equiv Equiv.Perm

section Std

def s1 : Perm (Fin 10) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

def s2 : Perm (Fin 10) := swap 5 6 * swap 6 7 * swap 7 8 * swap 8 9

def ιs : Perm (Fin 10) := swap 1 4 * swap 2 3 * swap 6 9 * swap 7 8

theorem s1_pow : s1 ^ 5 = 1 := by decide

theorem s2_pow : s2 ^ 5 = 1 := by decide

theorem s1_ne : s1 ≠ 1 := by decide

theorem s2_ne : s2 ≠ 1 := by decide

theorem s12_comm : s1 * s2 = s2 * s1 := by decide

theorem ιs_s1 : ιs * s1 * ιs⁻¹ = s1⁻¹ := by decide

theorem ιs_s2 : ιs * s2 * ιs⁻¹ = s2⁻¹ := by decide

theorem sign_s1 : sign s1 = 1 := by decide

theorem sign_s2 : sign s2 = 1 := by decide

theorem sign_ιs : sign ιs = 1 := by decide

def P10 : Subgroup (Perm (Fin 10)) := Subgroup.zpowers s1 ⊔ Subgroup.zpowers s2

theorem card_P10 : Nat.card P10 = 5 ^ 2 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h1 : orderOf s1 = 5 := orderOf_eq_prime s1_pow s1_ne
  have h2 : orderOf s2 = 5 := orderOf_eq_prime s2_pow s2_ne
  have hz1 : Nat.card (Subgroup.zpowers s1) = 5 := by rw [Nat.card_zpowers, h1]
  have hz2 : Nat.card (Subgroup.zpowers s2) = 5 := by rw [Nat.card_zpowers, h2]
  have hne : Subgroup.zpowers s1 ≠ Subgroup.zpowers s2 := by
    intro heq
    have hmem : s1 ∈ Subgroup.zpowers s2 := heq ▸ Subgroup.mem_zpowers s1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h0 : s2 0 = 0 := by decide
    have := zpow_apply_eq_self_of_apply_eq_self h0 k
    rw [hk] at this
    have h3 : s1 0 = 1 := by decide
    rw [h3] at this
    exact absurd this (by decide)
  have hdisj := inf_eq_bot_of_card_eq_prime Nat.prime_five hz1 hz2 hne
  rw [P10, Torsion37.card_sup_of_commute_disjoint (fun k hk l hl => by
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    exact (Commute.zpow_zpow (show Commute s1 s2 from s12_comm) a b).eq) (disjoint_iff.2 hdisj),
    hz1, hz2, pow_two]

theorem ιs_inv : ∀ y ∈ P10, ιs * y * ιs⁻¹ = y⁻¹ := by
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
    (fun k hk l hl => by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
      exact (Commute.zpow_zpow (show Commute s1 s2 from s12_comm) a b).eq) hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have e1 : ιs * s1 ^ i * ιs⁻¹ = (s1 ^ i)⁻¹ := by
    rw [← zpow_neg, ← conj_zpow, show ιs * s1 * ιs⁻¹ = s1⁻¹ from ιs_s1, inv_zpow, zpow_neg]
  have e2 : ιs * s2 ^ j * ιs⁻¹ = (s2 ^ j)⁻¹ := by
    rw [← zpow_neg, ← conj_zpow, show ιs * s2 * ιs⁻¹ = s2⁻¹ from ιs_s2, inv_zpow, zpow_neg]
  have hc : s1 ^ i * s2 ^ j = s2 ^ j * s1 ^ i := (Commute.zpow_zpow (show Commute s1 s2 from
    s12_comm) i j).eq
  calc ιs * (s1 ^ i * s2 ^ j) * ιs⁻¹ = (ιs * s1 ^ i * ιs⁻¹) * (ιs * s2 ^ j * ιs⁻¹) := by group
    _ = (s1 ^ i)⁻¹ * (s2 ^ j)⁻¹ := by rw [e1, e2]
    _ = (s2 ^ j * s1 ^ i)⁻¹ := (mul_inv_rev _ _).symm
    _ = (s1 ^ i * s2 ^ j)⁻¹ := by rw [hc]

end Std

section Ext

def finLE (n : ℕ) (hn : 10 ≤ n) : Fin 10 ≃ {x : Fin n // x.val < 10} where
  toFun i := ⟨⟨i.val, lt_of_lt_of_le i.2 hn⟩, i.2⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def embHom (n : ℕ) (hn : 10 ≤ n) : Perm (Fin 10) →* Perm (Fin n) :=
  Equiv.Perm.extendDomainHom (finLE n hn)

theorem embHom_injective (n : ℕ) (hn : 10 ≤ n) : Function.Injective (embHom n hn) :=
  Equiv.Perm.extendDomainHom_injective (finLE n hn)

theorem sign_embHom (n : ℕ) (hn : 10 ≤ n) (σ : Perm (Fin 10)) :
    sign (embHom n hn σ) = sign σ :=
  sign_extendDomain σ (finLE n hn)

theorem P10_map_le (n : ℕ) (hn : 10 ≤ n) :
    P10.map (embHom n hn) ≤ alternatingGroup (Fin n) := by
  have hker : ∀ σ ∈ P10, sign σ = 1 := by
    intro σ hσ
    obtain ⟨a, ha, b, hb, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
      (fun k hk l hl => by
        obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
        obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
        exact (Commute.zpow_zpow (show Commute s1 s2 from s12_comm) a b).eq) hσ
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [map_mul, map_zpow, map_zpow, sign_s1, sign_s2, one_zpow, one_zpow, mul_one]
  rintro _ ⟨σ, hσ, rfl⟩
  rw [mem_alternatingGroup, sign_embHom]
  exact hker σ hσ

def Pstd (n : ℕ) (hn : 10 ≤ n) : Subgroup ↥(alternatingGroup (Fin n)) :=
  (P10.map (embHom n hn)).subgroupOf (alternatingGroup (Fin n))

theorem card_Pstd (n : ℕ) (hn : 10 ≤ n) : Nat.card (Pstd n hn) = 5 ^ 2 := by
  have h1 : Nat.card (Pstd n hn) = Nat.card (P10.map (embHom n hn)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P10_map_le n hn)).toEquiv
  rw [h1, Subgroup.card_map_of_injective (embHom_injective n hn), card_P10]

def ιA (n : ℕ) (hn : 10 ≤ n) : ↥(alternatingGroup (Fin n)) :=
  ⟨embHom n hn ιs, mem_alternatingGroup.2 (by rw [sign_embHom, sign_ιs])⟩

theorem ιA_inv (n : ℕ) (hn : 10 ≤ n) : ∀ y ∈ Pstd n hn, ιA n hn * y * (ιA n hn)⁻¹ = y⁻¹ := by
  intro y hy
  obtain ⟨y₀, hy₀, hyy⟩ : (y : Perm (Fin n)) ∈ P10.map (embHom n hn) := Subgroup.mem_subgroupOf.1 hy
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ιA]
  rw [← hyy, ← map_inv, ← map_mul, ← map_inv, ← map_mul, ιs_inv y₀ hy₀]

theorem factorization_card_alt (n : ℕ) (h10 : 10 ≤ n) (h12 : n ≤ 12) :
    (Nat.card (alternatingGroup (Fin n))).factorization 5 = 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcard : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h5 : Nat.Prime 5 := Nat.prime_five
  have key : ∀ N : ℕ, N ≠ 0 → 5 ^ 2 ∣ N → ¬ 5 ^ 3 ∣ N → N.factorization 5 = 2 := by
    intro N hN h2 h3
    have a1 := (h5.pow_dvd_iff_le_factorization hN).1 h2
    have a2 : ¬ 3 ≤ N.factorization 5 := fun h => h3 ((h5.pow_dvd_iff_le_factorization hN).2 h)
    omega
  rw [hcard]
  interval_cases n <;> exact key _ (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
    (by norm_num [Nat.factorial])

theorem exists_inv_alt (n : ℕ) (h10 : 10 ≤ n) (h12 : n ≤ 12)
    {E : Subgroup ↥(alternatingGroup (Fin n))} (hE : IsPGroup 5 E) :
    ∃ g : ↥(alternatingGroup (Fin n)), ∀ e ∈ E, g * e * g⁻¹ = e⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let P₀ : Sylow 5 ↥(alternatingGroup (Fin n)) :=
    Sylow.ofCard (Pstd n h10) (by rw [card_Pstd, factorization_card_alt n h10 h12])
  exact exists_inv_of_sylow P₀ (g₀ := ιA n h10) (fun y hy => ιA_inv n h10 y hy) hE

end Ext

set_option synthInstance.maxSize 1024 in
theorem prime_sq_dvd_factorial : ∀ n < 13, ∀ q < 13, 5 ≤ n → 5 ≤ q → q.Prime →
    q ^ 2 ∣ n.factorial → q = 5 ∧ 10 ≤ n := by decide

theorem row8U3Item_four : Row8U3Item 4 := by
  classical
  intro Q _ _ p g Ē hX h
  obtain ⟨n, hn5, hn12, ⟨e⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect Q := h.quasisimple.1
  have hZ : Subgroup.center Q = ⊥ := by
    have hnd := Mult.alternating_center_small_primes (K := Q) hn5 e hp (by omega)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.center_p
    rw [← Subgroup.card_eq_one]
    rw [hk] at hnd ⊢
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero]
    · exact absurd (dvd_pow_self p hpos.ne') hnd
  refine ⟨hZ, fun hW => ?_⟩
  exfalso
  let eQ : Q ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))).trans e
  have hEel := h.elem
  set E' : Subgroup ↥(alternatingGroup (Fin n)) := Ē.map eQ.toMonoidHom with hE'
  have hE'p : IsPGroup p E' := (IsElementaryAbelian.isPGroup p Ē).map eQ.toMonoidHom
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective eQ.injective, h.card]
  have hdvd : p ^ 2 ∣ n.factorial := by
    have h1 : p ^ 2 ∣ Nat.card (alternatingGroup (Fin n)) :=
      hE'card ▸ Subgroup.card_subgroup_dvd_card E'
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1.trans (Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) (by omega)))
  have hpn : p = 5 ∧ 10 ≤ n := by
    have hple : p ≤ n := (hp.dvd_factorial).1 (dvd_trans (dvd_pow_self p two_ne_zero) hdvd)
    exact prime_sq_dvd_factorial n (by omega) p (by omega) hn5 hp5 hp hdvd
  obtain ⟨rfl, h10⟩ := hpn
  obtain ⟨gA, hgA⟩ := exists_inv_alt n h10 hn12 hE'p
  have hinv : ∀ x ∈ Ē, eQ.symm gA * x * (eQ.symm gA)⁻¹ = x⁻¹ := by
    intro x hx
    apply eQ.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    exact hgA (eQ x) (Subgroup.mem_map_of_mem _ hx)
  have hnorm : eQ.symm gA ∈ Subgroup.normalizer (Ē : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hinv y hy]
      exact Ē.inv_mem hy
    · intro hy
      have h1 := hinv _ hy
      have h2 : eQ.symm gA * (eQ.symm gA * y * (eQ.symm gA)⁻¹) * (eQ.symm gA)⁻¹ =
          eQ.symm gA * y⁻¹ * (eQ.symm gA)⁻¹ := by
        rw [h1]
        group
      have h3 : eQ.symm gA * y * (eQ.symm gA)⁻¹ = y⁻¹ := mul_left_cancel (mul_right_cancel h2)
      rw [h3] at hy
      simpa using Ē.inv_mem hy
  exact not_nonempty_perm3_of_inv hp (by omega) h.elem (by rw [h.card]; norm_num) hnorm hinv hW

end CFSG.RankThree.PartOne.Q1327T
