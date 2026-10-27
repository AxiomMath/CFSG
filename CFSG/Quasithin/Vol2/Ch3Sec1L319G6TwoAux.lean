module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.AutOnBasics

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Quasithin

theorem exists_pow_threePower_eq {A B : Type*} [Group A] [Group B] (φ : A →* B) {x : A}
    (hx : IsOfFinOrder x) (h3 : (φ x) ^ 3 = 1) :
    ∃ n a : ℕ, (x ^ n) ^ (3 ^ a) = 1 ∧ φ (x ^ n) = φ x := by
  have hopos : 0 < orderOf x := hx.orderOf_pos
  obtain ⟨a, m, hm, hoa⟩ := Nat.exists_eq_pow_mul_and_not_dvd hopos.ne' 3 (by norm_num)
  have hm3 : Nat.Coprime m 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm
  have hdvd : orderOf (φ x) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime m (orderOf (φ x)) := Nat.Coprime.coprime_dvd_right hdvd hm3
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, n ≡ 0 [MOD m] ∧ n ≡ 1 [MOD orderOf (φ x)] :=
    ⟨Nat.chineseRemainder hcop 0 1, (Nat.chineseRemainder hcop 0 1).2.1,
      (Nat.chineseRemainder hcop 0 1).2.2⟩
  refine ⟨n, a, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := (Nat.modEq_zero_iff_dvd).mp hn1
    rw [← pow_mul, hc, show m * c * 3 ^ a = c * orderOf x by rw [hoa]; ring, pow_mul',
      pow_orderOf_eq_one, one_pow]
  · have h3' : (φ x) ^ n = (φ x) ^ 1 := pow_eq_pow_iff_modEq.mpr hn2
    rw [map_pow, h3', pow_one]

theorem card_autOn_zpowers_three {G : Type} [Group G] {V : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hy3 : y ^ 3 ∈ Subgroup.centralizer (V : Set G))
    (hy1 : y ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card (autOn (Subgroup.zpowers y) V) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ : ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) = y := ⟨⟨y, hyN⟩, rfl⟩
  have hK : (Subgroup.zpowers y).subgroupOf (Subgroup.normalizer (V : Set G)) =
      Subgroup.zpowers g := by
    ext k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by rw [Subgroup.coe_zpow, hg]; exact hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, Subgroup.coe_zpow, hg]⟩
  have hA : autOn (Subgroup.zpowers y) V = Subgroup.zpowers (CFSG.Quasithin.conjAct V g) := by
    unfold CFSG.Quasithin.autOn
    rw [hK, MonoidHom.map_zpowers]
  have ha3 : CFSG.Quasithin.conjAct V g ^ 3 = 1 := by
    rw [← map_pow (CFSG.Quasithin.conjAct V)]
    apply (CFSG.Quasithin.AutOn.conjAct_eq_one_iff _).2
    rw [Subgroup.coe_pow, hg]
    exact hy3
  have ha1 : CFSG.Quasithin.conjAct V g ≠ 1 := by
    intro h
    have h' := (CFSG.Quasithin.AutOn.conjAct_eq_one_iff _).1 h
    rw [hg] at h'
    exact hy1 h'
  rw [hA, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]

end CFSG.Quasithin.H13.L319
