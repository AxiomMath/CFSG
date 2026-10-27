module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Timmesfeld

namespace IsPrimitivePrimeDivisor

theorem three_lt_of_two_lt {p k : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk : 2 < k) :
    3 < p := by
  have hk0 : 0 < k := by omega
  have hp2 : p ≠ 2 := hp.ne_two hk0
  have hp3 : p ≠ 3 := by
    intro h3
    have hk2 : k = 2 := hp.eq_two_of_dvd_three hk0 (by simpa [h3])
    omega
  have hp2le : 2 ≤ p := hp.prime.two_le
  omega

variable {K : Type*} [Field K] [Finite K] {k p : ℕ}

theorem subfield_closure_eq_top_of_orderOf (hk : 0 < k) (hK : Nat.card K = 2 ^ k)
    (hp : IsPrimitivePrimeDivisor p k) {y : K} (hy : orderOf y = p) :
    Subfield.closure ({y} : Set K) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := k) (by rwa [Fintype.card_eq_nat_card])
  set F : Subfield K := Subfield.closure ({y} : Set K)
  haveI : CharP ↥F 2 := Subfield.charP F 2
  letI : Algebra (ZMod 2) ↥F := ZMod.algebra ↥F 2
  set m : ℕ := Module.finrank (ZMod 2) ↥F with hm
  have hFcard : Nat.card ↥F = 2 ^ m := by
    rw [hm]
    exact (FiniteField.pow_finrank_eq_natCard 2 ↥F).symm
  have hyF : y ∈ F := Subfield.subset_closure (Set.mem_singleton y)
  have hyF0 : (⟨y, hyF⟩ : ↥F) ≠ 0 := by
    intro h0
    have hy0 : y = 0 := congrArg Subtype.val h0
    have hpow : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    rw [hy0, zero_pow hp.prime.pos.ne'] at hpow
    exact zero_ne_one hpow
  let u : (↥F)ˣ := Units.mk0 (⟨y, hyF⟩ : ↥F) hyF0
  have hord : orderOf (⟨y, hyF⟩ : ↥F) = p := by
    have h := orderOf_injective (F.subtype : ↥F →* K) F.subtype_injective ⟨y, hyF⟩
    rw [show (F.subtype : ↥F →* K) ⟨y, hyF⟩ = y from rfl] at h
    rw [← h]
    exact hy
  have huord : orderOf u = p := by
    rw [← orderOf_units (y := u), Units.val_mk0]
    exact hord
  have hpdvd : p ∣ 2 ^ m - 1 := by
    have h1 : p ∣ Nat.card (↥F)ˣ := by
      simpa [huord] using orderOf_dvd_natCard u
    rwa [Nat.card_units, hFcard] at h1
  have hkm : k ∣ m := (hp.dvd_sub_one_iff hk m).mp hpdvd
  have hdvd_units : Nat.card (↥F)ˣ ∣ Nat.card Kˣ :=
    Subgroup.card_dvd_of_injective (Units.map F.subtype.toMonoidHom)
      (Units.map_injective F.subtype_injective)
  have hmk : m ∣ k := by
    have h1 : 2 ^ m - 1 ∣ 2 ^ k - 1 := by
      have h2 := hdvd_units
      rwa [Nat.card_units, Nat.card_units, hFcard, hK] at h2
    have hg : Nat.gcd (2 ^ m - 1) (2 ^ k - 1) = 2 ^ m - 1 :=
      Nat.gcd_eq_left_iff_dvd.mpr h1
    rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
    have hm_eq : m = Nat.gcd m k := by
      have h2 : 2 ^ m - 1 + 1 = 2 ^ Nat.gcd m k - 1 + 1 := by rw [hg]
      rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n := m)),
        Nat.sub_add_cancel (Nat.one_le_two_pow (n := Nat.gcd m k))] at h2
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
    rw [hm_eq]
    exact Nat.gcd_dvd_right m k
  have hmk' : m = k := Nat.dvd_antisymm hmk hkm
  have hcardKF : Nat.card ↥F = Nat.card K := by
    rw [hFcard, hK, hmk']
  have huniv : (F : Set K) = Set.univ := by
    rw [Set.eq_univ_iff_ncard, ← Nat.card_coe_set_eq]
    exact hcardKF
  rw [eq_top_iff]
  intro x _
  rw [← SetLike.mem_coe, huniv]
  exact Set.mem_univ x

theorem exists_orderOf_eq (hk : 0 < k) (hK : Nat.card K = 2 ^ k)
    (hp : IsPrimitivePrimeDivisor p k) : ∃ y : K, orderOf y = p := by
  haveI : Fact p.Prime := ⟨hp.prime⟩
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hp.dvd
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨(u : K), by rw [orderOf_units, hu]⟩

theorem orderOf_pow_eq_of_not_dvd {y : K} (hp : IsPrimitivePrimeDivisor p k)
    (hy : orderOf y = p) {i : ℕ} (hi : ¬ p ∣ i) : orderOf (y ^ i) = p := by
  have hcop : Nat.Coprime p i := hp.prime.coprime_iff_not_dvd.mpr hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hi (dvd_zero p)
  rw [orderOf_pow' (x := y) (n := i) hi0, hy,
    Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.div_one]

end IsPrimitivePrimeDivisor

end CFSG.Timmesfeld

