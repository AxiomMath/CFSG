module

public import CFSG.RankThree.PartOne.S11.PlaneData
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique

theorem exists_prime_dvd_two_pow_sub_one_ne_three {n : ℕ} (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ p ≠ 3 := by
  by_contra hall
  push Not at hall
  have hpos : 2 ^ n - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  obtain ⟨k, h3⟩ : ∃ k : ℕ, 2 ^ n - 1 = 3 ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos fun hp hd => hall _ hp hd⟩
  have h8 : (2 ^ n - 1) % 8 = 7 := by
    have : 2 ^ n = 8 * 2 ^ (n - 3) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, Nat.add_sub_cancel' hn]
    have h1 : 1 ≤ 2 ^ (n - 3) := Nat.one_le_two_pow
    omega
  have h9 : ∀ j : ℕ, 3 ^ j % 8 = 1 ∨ 3 ^ j % 8 = 3 := by
    intro j
    induction j with
    | zero => left; rfl
    | succ j ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> simp
  rw [h3] at h8
  rcases h9 k with h | h <;> omega

theorem padicValNat_lt_padicValNat_two_pow_sub_one {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hn : n ≠ 0) (hpd : p ∣ 2 ^ n - 1) : padicValNat p n < padicValNat p (2 ^ n - 1) := by
  have hp1 : Odd p := hp.out.odd_of_ne_two hp2
  set d := orderOf (2 : ZMod p) with hd
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  have h2n : (2 : ZMod p) ^ n = 1 := by
    have h1 : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
    have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    push_cast [h4] at h1
    exact sub_eq_zero.mp h1
  have hdn : d ∣ n := orderOf_dvd_of_pow_eq_one h2n
  have hdp : d ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hdn
    exact hn hdn
  have hpd' : ¬ p ∣ d := by
    intro h
    have h2p := hp.out.two_le
    have h1 := Nat.le_of_dvd (by omega) (h.trans hdp)
    omega
  obtain ⟨m, rfl⟩ := hdn
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hn
  have h2d : (2 : ZMod p) ^ d = 1 := pow_orderOf_eq_one _
  have hpd2 : p ∣ 2 ^ d - 1 := by
    have h4 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [h4]
    rw [h2d, sub_self]
  have hlt : 1 < 2 ^ d := Nat.one_lt_two_pow hd0
  have hLTE := padicValNat.pow_sub_pow (p := p) (x := 2 ^ d) (y := 1) hp1 hlt hpd2
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
      (hp.out.dvd_of_dvd_pow h))) hm0
  rw [one_pow, ← pow_mul] at hLTE
  rw [hLTE, padicValNat.mul hd0 hm0, padicValNat.eq_zero_of_not_dvd hpd', zero_add]
  have : 0 < padicValNat p (2 ^ d - 1) :=
    one_le_padicValNat_of_dvd (by omega) hpd2
  omega

theorem pow_ne_one_of_orderOf {M : Type*} [Monoid M] {p n c : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : n ≠ 0) (hpd : p ∣ 2 ^ n - 1) (hc : ¬ p ∣ c) {z : M}
    (hz : orderOf z = p ^ padicValNat p (2 ^ n - 1)) : z ^ (c * n) ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hz] at hd
  have hcop : Nat.Coprime (p ^ padicValNat p (2 ^ n - 1)) c :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hc)
  have hd' := hcop.dvd_of_dvd_mul_left hd
  have hle := (padicValNat_dvd_iff_le hn).mp hd'
  have hlt := padicValNat_lt_padicValNat_two_pow_sub_one hp2 hn hpd
  omega

theorem exists_pow_orderOf_eq {G H : Type*} [Group G] [Group H] [Finite G] (φ : G →* H) {p a : ℕ}
    (hp : p.Prime) {g : G} (hg : orderOf (φ g) = p ^ a) :
    ∃ k b : ℕ, orderOf (g ^ k) = p ^ b ∧ orderOf (φ (g ^ k)) = p ^ a := by
  set v := (orderOf g).factorization p with hv
  have hpos := orderOf_pos g
  have hdv : p ^ v ∣ orderOf g := Nat.ordProj_dvd _ _
  refine ⟨orderOf g / p ^ v, v, orderOf_pow_orderOf_div hpos.ne' hdv, ?_⟩
  rw [map_pow]
  have hcop : Nat.Coprime (orderOf g / p ^ v) (orderOf (φ g)) := by
    rw [hg]
    exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp (Nat.coprime_ordCompl hp hpos.ne'))
  rw [(Nat.Coprime.symm hcop).orderOf_pow, hg]

section Split

variable {G : Type} [Group G] {L : Subgroup G}

open CFSG.RankThree.PartOne

theorem mul_inv_mem_centralizer_of_eq_conj [Group.IsPerfect L] {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) (ℓ : L)
    (h : centerQuotientConj L ⟨y, hy⟩ = MulAut.conj (ℓ : L ⧸ Subgroup.center L)) :
    y * (ℓ : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  have hℓN : (ℓ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer ℓ.2
  have hcN : y * (ℓ : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hℓN)
  have hℓ : centerQuotientConj L ⟨ℓ, hℓN⟩ = MulAut.conj (ℓ : L ⧸ Subgroup.center L) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      change ((L.normalizerMonoidHom ⟨ℓ, hℓN⟩ l : L) : L ⧸ Subgroup.center L) = _
      rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
  have h1 : centerQuotientAction (le_refl (Subgroup.normalizer (L : Set G)))
      ⟨y * (ℓ : G)⁻¹, hcN⟩ = 1 := by
    have e : (⟨y * (ℓ : G)⁻¹, hcN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨y, hy⟩ * (⟨ℓ, hℓN⟩)⁻¹ := rfl
    change centerQuotientConj L _ = 1
    rw [e, map_mul, map_inv, h, hℓ, mul_inv_cancel]
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (commute_of_centerQuotientAction_eq_one (le_refl _) ⟨y * (ℓ : G)⁻¹, hcN⟩ h1
    ⟨l, hl⟩).symm

theorem exists_orderOf_eq_or_mem [Finite G] (hZ : IsPGroup 2 ↥(Subgroup.center ↥L)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {y : G} {b : ℕ} (hyb : y ^ p ^ b = 1) {ℓ : G} (hℓ : ℓ ∈ L)
    (hc : y * ℓ⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    (∃ x ∈ Subgroup.zpowers (y * ℓ⁻¹), orderOf x = p) ∨ y ∈ L := by
  set c := y * ℓ⁻¹ with hcdef
  have hcℓ : c * ℓ = ℓ * c := (Subgroup.mem_centralizer_iff.mp hc ℓ hℓ).symm
  have hy : y = c * ℓ := by rw [hcdef]; group
  have hcpb : c ^ p ^ b = (ℓ ^ p ^ b)⁻¹ := by
    have h1 : (c * ℓ) ^ p ^ b = c ^ p ^ b * ℓ ^ p ^ b := (Commute.mul_pow hcℓ _)
    rw [← hy, hyb] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hcZ : c ^ p ^ b ∈ L ∧ ∀ l ∈ L, l * c ^ p ^ b = c ^ p ^ b * l := by
    refine ⟨by rw [hcpb]; exact L.inv_mem (L.pow_mem hℓ _), fun l hl => ?_⟩
    exact (Commute.pow_right (Subgroup.mem_centralizer_iff.mp hc l hl) _).eq
  obtain ⟨j, hj⟩ := hZ ⟨⟨c ^ p ^ b, hcZ.1⟩, Subgroup.mem_center_iff.mpr fun l =>
    Subtype.ext (hcZ.2 l l.2)⟩
  have hcj : c ^ (p ^ b * 2 ^ j) = 1 := by
    rw [pow_mul]
    have := congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : G)) hj
    simpa using this
  by_cases hc2 : c ^ 2 ^ j = 1
  ·
    right
    have h1 : y ^ 2 ^ j = ℓ ^ 2 ^ j := by
      rw [hy, Commute.mul_pow hcℓ, hc2, one_mul]
    have hcop : Nat.Coprime (2 ^ j) (orderOf y) := by
      refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hyb) ?_
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm, h1]
    exact L.pow_mem (L.pow_mem hℓ _) m
  ·
    left
    set c₂ := c ^ 2 ^ j with hc₂
    have hc₂p : c₂ ^ p ^ b = 1 := by
      rw [hc₂, ← pow_mul, mul_comm, hcj]
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hc₂p)
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hio
      exact hc2 hio
    refine ⟨c₂ ^ (orderOf c₂ / p),
      Subgroup.pow_mem _ (Subgroup.npow_mem_zpowers _ _) _,
      orderOf_pow_orderOf_div (orderOf_pos c₂).ne' ?_⟩
    rw [hio]
    exact dvd_pow_self p hi0

end Split

end CFSG.Quasithin.E6
