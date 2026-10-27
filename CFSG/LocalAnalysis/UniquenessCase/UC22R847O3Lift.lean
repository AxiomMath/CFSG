module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847O3Pair
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251d
import CFSG.LocalAnalysis.UniquenessCase.UC6Mod
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R847O3

open CFSG.Open Subgroup

variable {G : Type} [Group G]

private theorem mem_normalizer_zpowers_of_mul_comm {a u : G} (h : u * a = a * u) :
    u ∈ normalizer ((zpowers a : Subgroup G) : Set G) := by
  refine centralizer_le_normalizer _ (mem_centralizer_iff.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ((show Commute u a from h).zpow_right k).eq.symm

private theorem mem_normalizer_zpowers_of_conj_eq_inv {a b : G} (h : b * a * b⁻¹ = a⁻¹) :
    b ∈ normalizer ((zpowers a : Subgroup G) : Set G) := by
  have h1 : b * a⁻¹ * b⁻¹ = a := by simpa [mul_assoc] using congrArg (·⁻¹) h
  have h' : b⁻¹ * a * b = a⁻¹ := by
    calc b⁻¹ * a * b = b⁻¹ * (b * a⁻¹ * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ := by group
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    refine mem_zpowers_iff.2 ⟨-k, ?_⟩
    rw [← conj_zpow, h, inv_zpow, zpow_neg]
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
    have hc := conj_zpow (a := b⁻¹) (b := a) (i := k)
    rw [inv_inv, h', inv_zpow, ← zpow_neg, hk] at hc
    exact mem_zpowers_iff.2 ⟨-k, hc.trans (by group)⟩

private theorem two_dvd_orderOf_of_conj_eq_inv {a b : G} (ha : ¬ orderOf a ∣ 2)
    (h : b * a * b⁻¹ = a⁻¹) : 2 ∣ orderOf b := by
  by_contra hb
  have h1 : b * a⁻¹ * b⁻¹ = a := by simpa [mul_assoc] using congrArg (·⁻¹) h
  have hc : Commute (b ^ 2) a := by
    show b ^ 2 * a = a * b ^ 2
    calc b ^ 2 * a = b * (b * a * b⁻¹) * b⁻¹ * b ^ 2 := by rw [pow_two]; group
      _ = a * b ^ 2 := by rw [h, h1]
  obtain ⟨m, hm⟩ : Odd (orderOf b) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hb)
  have hb' : (b ^ 2) ^ (m + 1) = b := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf b + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hcb : Commute b a := hb' ▸ hc.pow_left (m + 1)
  have haa : a = a⁻¹ := by rw [← h, hcb.eq, mul_inv_cancel_right]
  have ha2 : a ^ 2 = 1 := by
    calc a ^ 2 = a * a := pow_two a
      _ = a * a⁻¹ := by rw [← haa]
      _ = 1 := mul_inv_cancel a
  exact ha (orderOf_dvd_of_pow_eq_one ha2)

variable [Finite G]

theorem exists_involution_of_fixed_invPair {K : Subgroup G} {p q : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G}
    (hQN : Q ≤ normalizer (K : Set G)) (hQ : IsElemAbelian p Q) {xb gb : Bar2 K}
    (hxb : orderOf xb = q) (hgxb : gb * xb * gb⁻¹ = xb⁻¹) {Q₀ : Subgroup ↥Q} (hQ₀ : Q₀.index ≤ p)
    (hfix : ∀ u ∈ Q₀, UC6S846.rhoL K (inclusion hQN u) xb = xb ∧
      UC6S846.rhoL K (inclusion hQN u) gb = gb) :
    ∃ Q' : Subgroup G, Q' ≤ Q ∧ Nat.card Q ≤ p * Nat.card Q' ∧ ∃ x ∈ K, orderOf x = q ∧
      ∃ t ∈ K ⊓ normalizer ((zpowers x : Subgroup G) : Set G), orderOf t = 2 ∧
        ∀ u ∈ Q', u * x = x * u ∧ u * t = t * u := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hQ'Q : Q₀.map Q.subtype ≤ Q := map_subtype_le _
  have hQ'p : IsPGroup p (Q₀.map Q.subtype) := hQ.isPGroup.to_le hQ'Q
  have hcard : Nat.card Q ≤ p * Nat.card (Q₀.map Q.subtype) := by
    rw [card_map_of_injective Q.subtype_injective, ← Q₀.card_mul_index, mul_comm]
    exact Nat.mul_le_mul_right _ hQ₀
  have hO : ∀ u ∈ Q₀.map Q.subtype, ∀ f ∈ pCoreOf 2 K, u * f * u⁻¹ ∈ pCoreOf 2 K :=
    fun u hu f hf => (mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hQN (hQ'Q hu))) f).1 hf
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective xb
  obtain ⟨n, hln, hn⟩ := UC6.exists_fixed_in_coset_uc6 (Q₀.map Q.subtype) (pCoreOf 2 K) hQ'p
    (P2251c.not_dvd_card_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hp hp2)
    hO (l : G) (by
      rintro _ ⟨v, hv, rfl⟩
      exact P2251d.inv_mul_conj_mem_of_rhoL (inclusion hQN v) l.2 (hfix v hv).1)
  have hnK : n ∈ K := by simpa using mul_mem l.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 K hln)
  have hln' : ((l : ↥K) : Bar2 K) = ((⟨n, hnK⟩ : ↥K) : Bar2 K) := by
    have h : K.subtype (l⁻¹ * ⟨n, hnK⟩) ∈ pCoreOf 2 K := hln
    exact QuotientGroup.eq.2 ((mem_map_iff_mem K.subtype_injective).1 h)
  have h3n : q ∣ orderOf n := by
    have hdvd := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨n, hnK⟩
    rwa [QuotientGroup.mk'_apply, Subgroup.orderOf_mk, ← hln', hxb] at hdvd
  set m := orderOf n / q with hm
  have hxK : n ^ m ∈ K := pow_mem hnK m
  have hx3 : orderOf (n ^ m) = q := orderOf_pow_orderOf_div (orderOf_pos n).ne' h3n
  have hxc : ∀ u ∈ Q₀.map Q.subtype, u * n ^ m = n ^ m * u := fun u hu =>
    mul_inv_eq_iff_eq_mul.1 (by rw [← conj_pow, hn u hu])
  have hxN : ∀ u ∈ Q₀.map Q.subtype, u ∈ normalizer ((zpowers (n ^ m) : Subgroup G) : Set G) :=
    fun u hu => mem_normalizer_zpowers_of_mul_comm (hxc u hu)
  have hxbar : ((⟨n ^ m, hxK⟩ : ↥K) : Bar2 K) = ((l : ↥K) : Bar2 K) ^ m := by
    rw [hln', ← QuotientGroup.mk_pow]
    congr 1
  have hsub : (zpowers (n ^ m)).subgroupOf K = zpowers (⟨n ^ m, hxK⟩ : ↥K) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (zpowers_le.2 hxK), MonoidHom.map_zpowers]
    rfl
  have hmap : ((zpowers (n ^ m)).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) =
      zpowers (((l : ↥K) : Bar2 K) ^ m) := by
    rw [hsub, MonoidHom.map_zpowers, QuotientGroup.mk'_apply, hxbar]
  have hgx : gb * ((l : ↥K) : Bar2 K) ^ m * gb⁻¹ = (((l : ↥K) : Bar2 K) ^ m)⁻¹ := by
    rw [← conj_pow, hgxb, inv_pow]
  obtain ⟨⟨y, hyK⟩, hyN, hyg⟩ := uc22ine229_exists_lift (zpowers_le.2 hxK) hq hq2
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3, pow_one]))
    (w := gb) (by rw [hmap]; exact mem_normalizer_zpowers_of_conj_eq_inv hgx)
  have hyg' : ((⟨y, hyK⟩ : ↥K) : Bar2 K) = gb := hyg
  obtain ⟨t₀, hyt, ht₀⟩ := UC6.exists_fixed_in_coset_uc6 (Q₀.map Q.subtype)
    (pCoreOf 2 K ⊓ normalizer ((zpowers (n ^ m) : Subgroup G) : Set G)) hQ'p
    (P2251c.not_dvd_card_of_isPGroup_two
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left) hp hp2)
    (fun u hu f hf => mem_inf.2 ⟨hO u hu f (mem_inf.1 hf).1,
      mul_mem (mul_mem (hxN u hu) (mem_inf.1 hf).2) (inv_mem (hxN u hu))⟩)
    y (by
      rintro _ ⟨v, hv, rfl⟩
      refine mem_inf.2 ⟨P2251d.inv_mul_conj_mem_of_rhoL (inclusion hQN v) hyK
        ((congrArg (UC6S846.rhoL K (inclusion hQN v)) hyg').trans
          ((hfix v hv).2.trans hyg'.symm)), ?_⟩
      have hvN := hxN _ ⟨v, hv, rfl⟩
      exact mul_mem (inv_mem hyN) (mul_mem (mul_mem hvN hyN) (inv_mem hvN)))
  obtain ⟨hytO, hytN⟩ := mem_inf.1 hyt
  have ht₀K : t₀ ∈ K := by simpa using mul_mem hyK (CFSG.LieType.BorelTits.pCoreOf_le 2 K hytO)
  have ht₀N : t₀ ∈ normalizer ((zpowers (n ^ m) : Subgroup G) : Set G) := by
    simpa using mul_mem hyN hytN
  have htg : ((⟨t₀, ht₀K⟩ : ↥K) : Bar2 K) = gb := by
    have h : K.subtype ((⟨y, hyK⟩ : ↥K)⁻¹ * ⟨t₀, ht₀K⟩) ∈ pCoreOf 2 K := hytO
    rw [← hyg']
    exact (QuotientGroup.eq.2 ((mem_map_iff_mem K.subtype_injective).1 h)).symm
  have h2t : 2 ∣ orderOf t₀ := by
    have hdvd := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨t₀, ht₀K⟩
    rw [QuotientGroup.mk'_apply, Subgroup.orderOf_mk, htg] at hdvd
    exact (two_dvd_orderOf_of_conj_eq_inv (by
      rw [hxb]
      exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)) hgxb).trans hdvd
  refine ⟨Q₀.map Q.subtype, hQ'Q, hcard, n ^ m, hxK, hx3, t₀ ^ (orderOf t₀ / 2),
    mem_inf.2 ⟨pow_mem ht₀K _, pow_mem ht₀N _⟩, orderOf_pow_orderOf_div (orderOf_pos t₀).ne' h2t,
    fun u hu => ⟨hxc u hu, mul_inv_eq_iff_eq_mul.1 (by rw [← conj_pow, ht₀ u hu])⟩⟩

theorem exists_involution_of_lossPairAt {K : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hloss : R847O3.LossPairAt (Bar2 K) p) {Q : Subgroup G}
    (hQN : Q ≤ normalizer (K : Set G)) (hQ : IsElemAbelian p Q) :
    ∃ Q' : Subgroup G, Q' ≤ Q ∧ Nat.card Q ≤ p * Nat.card Q' ∧ ∃ x ∈ K, orderOf x = 3 ∧
      ∃ t ∈ K ⊓ normalizer ((zpowers x : Subgroup G) : Set G), orderOf t = 2 ∧
        ∀ u ∈ Q', u * x = x * u ∧ u * t = t * u := by
  obtain ⟨xb, gb, hxb3, hgxb, Q₀, hQ₀, hfix⟩ := hloss ↥Q
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hQ.2 _ x.2))
    (fun x y => Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hQ.comm x.2 y.2))
    ((UC6S846.rhoL K).comp (inclusion hQN))
  exact exists_involution_of_fixed_invPair hp hp2 Nat.prime_three (by norm_num) hQN hQ hxb3 hgxb
    hQ₀ hfix

end CFSG.LocalAnalysis.UniquenessCase.UC22.R847O3

end
