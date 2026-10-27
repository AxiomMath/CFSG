module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter
public import CFSG.Quasithin.Vol2.Ch3E213MFam
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Ch3E215M.Sp4

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M CFSG.Timmesfeld
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp card_antiSp)

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem exists_mem_orderOf_ppd {F₀ : Type} [Field F₀] [Finite F₀] [CharP F₀ 2] {e : ℕ}
    (hq : Nat.card F₀ = 2 ^ e) (he : 1 ≤ e) (ψ : ↥X →* antiSp F₀)
    (hψs : Function.Surjective ψ) :
    ∃ (r : ℕ) (x : G), IsPrimitivePrimeDivisor r (4 * e) ∧ x ∈ X ∧ orderOf x = r := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * e) (by omega) (by omega)
  have : Fact r.Prime := ⟨hr.prime⟩
  have hdvd1 : r ∣ Nat.card (antiSp F₀) := by
    rw [card_antiSp hq]
    refine (primitive_dvd_sq_add_one he hr).trans ?_
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have h4 : (2 ^ e) ^ 4 - 1 = ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 2 + 1) := by
      have h1 : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      zify [h1, Nat.one_le_pow 4 (2 ^ e) (by positivity)]
      ring
    rw [h4]
    exact Dvd.intro_left _ rfl
  have hdvd2 : Nat.card (antiSp F₀) ∣ Nat.card X := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv]
    exact Subgroup.card_quotient_dvd_card ψ.ker
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r (hdvd1.trans hdvd2)
  exact ⟨r, x, hr, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem not_forall_mem_Z (h : E2.Pair X T M V g) (hchar : CharTwo X) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {x : G} (hx : x ∈ X) (hxo : orderOf x = r) :
    ¬ ∀ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V),
      x * p * x⁻¹ * p⁻¹ ∈ V ⊓ B6.conjSub g V := by
  intro hall
  obtain ⟨n, hn⟩ := isTwo_of_centralizes h hchar hx hall
  have hdvd : r ∣ 2 ^ n := hxo ▸ orderOf_dvd_of_pow_eq_one hn
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))

theorem two_pow_mul_card_le {N Y : Subgroup G} (hN : IsPGroup 2 N) {x : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) {r k : ℕ} (hk : 0 < k)
    (hr : IsPrimitivePrimeDivisor r k) (hxo : orderOf x = r)
    (hmove : ∃ n ∈ N, x * n * x⁻¹ ≠ n) (hYN : Y ≤ N) (hY : ∀ y ∈ Y, x * y * x⁻¹ = y) :
    2 ^ k * Nat.card Y ≤ Nat.card N := by
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hN
  set c : Subgroup.normalizer (N : Set G) := ⟨x, hxN⟩ with hc
  have hco : orderOf c = r ^ (0 + 1) := by
    rw [hc, Subgroup.orderOf_mk, hxo, zero_add, pow_one]
  have hc0 : c ^ r ^ 0 = c := by rw [pow_zero, pow_one]
  have hne : N.normalizerMonoidHom (c ^ r ^ 0) ≠ 1 := by
    rw [hc0]
    intro h1
    obtain ⟨n, hn, hxn⟩ := hmove
    apply hxn
    have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨n, hn⟩)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
    exact h2
  have hZ : ∀ z ∈ Y.subgroupOf N, N.normalizerMonoidHom (c ^ r ^ 0) z = z := by
    intro z hz
    rw [hc0]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hY _ (Subgroup.mem_subgroupOf.mp hz)
  obtain ⟨m, hm0, hmle, hmdvd⟩ := exists_two_pow_of_orderOf N.normalizerMonoidHom hd hr.prime
    (hr.ne_two hk) hco hne (Y.subgroupOf N) hZ
  have hkm : k ∣ m := (hr.dvd_sub_one_iff hk m).1 (by rwa [zero_add, pow_one] at hmdvd)
  have hYc : Nat.card (Y.subgroupOf N) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv
  rw [hYc, ← hd] at hmle
  calc 2 ^ k * Nat.card Y ≤ 2 ^ m * Nat.card Y :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hm0 hkm))
    _ ≤ Nat.card N := hmle

omit [Finite G] in
theorem conj_eq_of_mem_Z (h : E2.Pair X T M V g) {x : G} (hx : x ∈ X) {z : G}
    (hz : z ∈ V ⊓ B6.conjSub g V) : x * z * x⁻¹ = z := by
  rw [← h.mem_center hz hx, mul_inv_cancel_right]

theorem exists_mem_P_ne (h : E2.Pair X T M V g) (hchar : CharTwo X) {r k : ℕ} (hk : 0 < k)
    (hr : IsPrimitivePrimeDivisor r k) {x : G} (hx : x ∈ X) (hxo : orderOf x = r) :
    ∃ p ∈ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V), x * p * x⁻¹ ≠ p := by
  by_contra hno
  push Not at hno
  exact not_forall_mem_Z h hchar hr.prime (hr.ne_two hk) hx hxo fun p hp => by
    rw [hno p hp, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem card_P_le (h : E2.Pair X T M V g) {k : ℕ}
    (hPZ : (V ⊓ B6.conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) ≤ 2 ^ k) :
    Nat.card ↥((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) ≤
      2 ^ k * Nat.card ↥(V ⊓ B6.conjSub g V) := by
  have h1 := Subgroup.relIndex_mul_card (V ⊓ B6.conjSub g V)
    ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V))
  rw [inf_eq_left.2 h.inf_conj_le_P] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ hPZ

theorem eq_or_eq_of_le_normalizer (h : E2.Pair X T M V g) (hchar : CharTwo X) {r k : ℕ}
    (hk : 0 < k) (hr : IsPrimitivePrimeDivisor r k) {x : G} (hx : x ∈ X) (hxo : orderOf x = r)
    (hPZ : (V ⊓ B6.conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) ≤ 2 ^ k)
    {N : Subgroup G} (hZN : V ⊓ B6.conjSub g V ≤ N)
    (hNP : N ≤ (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V))
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    N = V ⊓ B6.conjSub g V ∨ N = (kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V) := by
  have hP2 : IsPGroup 2 ↥((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have hPcard := card_P_le h hPZ
  by_cases hc : ∀ n ∈ N, x * n * x⁻¹ = n
  · left
    have h1 := two_pow_mul_card_le hP2 (h.le_normalizer_P hx) hk hr hxo
      (exists_mem_P_ne h hchar hk hr hx hxo) hNP hc
    have h2 : Nat.card N ≤ Nat.card ↥(V ⊓ B6.conjSub g V) :=
      Nat.le_of_mul_le_mul_left (h1.trans hPcard) (by positivity)
    exact (Subgroup.eq_of_le_of_card_ge hZN h2).symm
  · right
    push Not at hc
    have h1 := two_pow_mul_card_le (hP2.to_le hNP) (hXN hx) hk hr hxo hc hZN
      (fun z hz => conj_eq_of_mem_Z h hx hz)
    exact Subgroup.eq_of_le_of_card_ge hNP (hPcard.trans h1)

theorem relIndex_P_eq_two_pow (h : E2.Pair X T M V g) (hchar : CharTwo X) {r k : ℕ}
    (hk : 0 < k) (hr : IsPrimitivePrimeDivisor r k) {x : G} (hx : x ∈ X) (hxo : orderOf x = r)
    (hPZ : (V ⊓ B6.conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) ≤ 2 ^ k) :
    (V ⊓ B6.conjSub g V).relIndex ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) = 2 ^ k := by
  have hP2 : IsPGroup 2 ↥((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have h1 := two_pow_mul_card_le hP2 (h.le_normalizer_P hx) hk hr hxo
    (exists_mem_P_ne h hchar hk hr hx hxo) h.inf_conj_le_P (fun z hz => conj_eq_of_mem_Z h hx hz)
  have h2 := Subgroup.relIndex_mul_card (V ⊓ B6.conjSub g V)
    ((kerIn M X ⊓ V) ⊔ B6.conjSub g (kerIn M X ⊓ V))
  rw [inf_eq_left.2 h.inf_conj_le_P] at h2
  refine le_antisymm hPZ ?_
  rw [← h2] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

end CFSG.Quasithin.Ch3E215M.Sp4
