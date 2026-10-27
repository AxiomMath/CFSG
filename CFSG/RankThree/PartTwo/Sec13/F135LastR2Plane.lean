module

public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

theorem r2a_mem_sup {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, y, hy, by simp⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, H.mul_mem hy₁ hy₂, z₁ * z₂, K.mul_mem hz₁ hz₂, ?_⟩
    have h := hc y₂ hy₂ z₁ hz₁
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by simp only [mul_assoc]
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [h]
      _ = y₁ * z₁ * (y₂ * z₂) := by simp only [mul_assoc]
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, H.inv_mem hy, z⁻¹, K.inv_mem hz, ?_⟩
    rw [mul_inv_rev]
    exact (show Commute y z from hc y hy z hz).inv_inv

theorem r2a_card_sup_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card (H ⊔ K : Subgroup G) ≤ Nat.card H * Nat.card K := by
  let f : H × K → (H ⊔ K : Subgroup G) :=
    fun q => ⟨(q.1 : G) * (q.2 : G), Subgroup.mul_mem_sup q.1.2 q.2.2⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨h, hh, k, hk, hx⟩ := r2a_mem_sup hc x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hx⟩
  have h := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod] at h
  exact h

theorem r2a_mem_of_pow_mem {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (K : Subgroup G)
    {y : G} (hy : y ^ p = 1) {i : ℤ} (hi : ¬ (p : ℤ) ∣ i) (h : y ^ i ∈ K) : y ∈ K := by
  obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.2 hi
  have hpu : (y ^ (p : ℤ)) ^ u = 1 := by rw [zpow_natCast, hy, one_zpow]
  have key : y = (y ^ i) ^ v * (y ^ (p : ℤ)) ^ u := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add,
      show i * v + (p : ℤ) * u = 1 by linear_combination huv, zpow_one]
  have h2 : (y ^ i) ^ v * (y ^ (p : ℤ)) ^ u ∈ K := by
    rw [hpu, mul_one]
    exact K.zpow_mem h v
  rw [key]
  exact h2

theorem r2a_zpow_eq_one {G : Type*} [Group G] {p : ℕ} {y : G} (hy : y ^ p = 1) {j : ℤ}
    (hj : (p : ℤ) ∣ j) : y ^ j = 1 := by
  obtain ⟨c, rfl⟩ := hj
  rw [zpow_mul, zpow_natCast, hy, one_zpow]

theorem r2a_pow_zpowers {G : Type*} [Group G] {p : ℕ} {a : G} (ha : a ^ p = 1) :
    ∀ x ∈ Subgroup.zpowers a, x ^ p = 1 := by
  intro x hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

theorem r2a_comm_zpowers {G : Type*} [Group G] {a b : G} (hab : Commute a b) :
    ∀ h ∈ Subgroup.zpowers a, ∀ k ∈ Subgroup.zpowers b, h * k = k * h := by
  intro h hh k hk
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  exact ((hab.zpow_left m).zpow_right n).eq

theorem r2a_comm_mem {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Dp : Subgroup G}
    (hDp : IsPGroup p Dp) (hexp : ∀ x ∈ Dp, x ^ p = 1) {a b : G} (ha : a ∈ Dp) (hb : b ∈ Dp) :
    ⁅a, b⁆ ∈ (frattini ↥Dp).map Dp.subtype := by
  have hexp' : ∀ x : ↥Dp, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hfr := CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hexp'
  have hmem : (⁅(⟨a, ha⟩ : ↥Dp), (⟨b, hb⟩ : ↥Dp)⁆ : ↥Dp) ∈ frattini ↥Dp := by
    rw [hfr, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h := Subgroup.mem_map_of_mem Dp.subtype hmem
  rw [map_commutatorElement] at h
  exact h

theorem r2a_exists_y1 {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {P Φ : Subgroup G} (hPmap : p ^ 2 ≤ Φ.relIndex (P ⊔ Φ)) : ∃ y₁ ∈ P, y₁ ∉ Φ := by
  by_contra hcon
  push Not at hcon
  have heq : P ⊔ Φ = Φ := le_antisymm (sup_le hcon le_rfl) le_sup_right
  rw [heq, Subgroup.relIndex_self] at hPmap
  nlinarith [hp.two_le]

theorem r2a_exists_y2 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Dp P Φ : Subgroup G} (hΦc : ∀ x ∈ Φ, ∀ d ∈ Dp, x * d = d * x) (hPD : P ≤ Dp)
    (hPexp : ∀ y ∈ P, y ^ p = 1) (hPmap : p ^ 2 ≤ Φ.relIndex (P ⊔ Φ))
    {y₁ : G} (hy₁P : y₁ ∈ P) (hy₁Φ : y₁ ∉ Φ) :
    ∃ y₂ ∈ P, y₂ ∉ Subgroup.zpowers y₁ ⊔ Φ := by
  by_contra hcon
  push Not at hcon
  have hPK : P ⊔ Φ ≤ Subgroup.zpowers y₁ ⊔ Φ := sup_le hcon le_sup_right
  have hc : ∀ h ∈ Subgroup.zpowers y₁, ∀ k ∈ Φ, h * k = k * h := by
    intro h hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hyk : Commute y₁ k := (hΦc k hk y₁ (hPD hy₁P)).symm
    exact (hyk.zpow_left m).eq
  have hK : Nat.card (Subgroup.zpowers y₁ ⊔ Φ : Subgroup G) ≤
      Nat.card (Subgroup.zpowers y₁) * Nat.card Φ :=
    r2a_card_sup_le hc
  have hord : Nat.card (Subgroup.zpowers y₁) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hPexp y₁ hy₁P))
  have hrel : Φ.relIndex (P ⊔ Φ) * Nat.card Φ = Nat.card (P ⊔ Φ : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := Φ) (K := P ⊔ Φ)
    rwa [inf_eq_left.mpr le_sup_right] at h
  have hQ : Nat.card (P ⊔ Φ : Subgroup G) ≤ Nat.card (Subgroup.zpowers y₁ ⊔ Φ : Subgroup G) :=
    Subgroup.card_le_of_le hPK
  have hc0 : 0 < Nat.card Φ := by
    haveI : Nonempty Φ := ⟨⟨1, Φ.one_mem⟩⟩
    exact Nat.card_pos
  have h1 : p ^ 2 * Nat.card Φ ≤ p * Nat.card Φ :=
    calc p ^ 2 * Nat.card Φ ≤ Φ.relIndex (P ⊔ Φ) * Nat.card Φ := Nat.mul_le_mul_right _ hPmap
      _ = Nat.card (P ⊔ Φ : Subgroup G) := hrel
      _ ≤ Nat.card (Subgroup.zpowers y₁ ⊔ Φ : Subgroup G) := hQ
      _ ≤ Nat.card (Subgroup.zpowers y₁) * Nat.card Φ := hK
      _ ≤ p * Nat.card Φ := Nat.mul_le_mul_right _ hord
  have h2 : p ^ 2 ≤ p := Nat.le_of_mul_le_mul_right h1 hc0
  nlinarith [hp.two_le]

theorem r2a_elem_sup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {a b : G}
    (hab : Commute a b) (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hind : ∀ i j : ℤ, a ^ i * b ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    CFSG.Open.IsElemAbelian p (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hao : orderOf a = p := orderOf_eq_prime ha ha1
  have hbo : orderOf b = p := orderOf_eq_prime hb hb1
  have hc : ∀ h ∈ Subgroup.zpowers a, ∀ k ∈ Subgroup.zpowers b, h * k = k * h :=
    r2a_comm_zpowers hab
  have hcA : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.refl a).zpow_zpow m n).eq
  have hcB : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.refl b).zpow_zpow m n).eq
  let f : Subgroup.zpowers a × Subgroup.zpowers b →
      (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) :=
    fun q => ⟨(q.1 : G) * (q.2 : G), Subgroup.mul_mem_sup q.1.2 q.2.2⟩
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨h, hh, k, hk, hx⟩ := r2a_mem_sup hc x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hx⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ hfeq
    have heq' : u * v = u' * v' := congrArg Subtype.val hfeq
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    obtain ⟨n', rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    have h1 : a ^ (m - m') * b ^ (n - n') = 1 := by
      have e : a ^ (m - m') * b ^ (n - n') = (a ^ m')⁻¹ * (a ^ m * b ^ n) * (b ^ n')⁻¹ := by
        group
      rw [e, heq']
      group
    obtain ⟨hm, hn⟩ := hind _ _ h1
    have ham : a ^ (m - m') = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hao]; exact hm)
    have hbn : b ^ (n - n') = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rw [hbo]; exact hn)
    have hA : a ^ m = a ^ m' := by
      rw [show a ^ m = a ^ m' * a ^ (m - m') by rw [← zpow_add]; congr 1; ring, ham, mul_one]
    have hB : b ^ n = b ^ n' := by
      rw [show b ^ n = b ^ n' * b ^ (n - n') by rw [← zpow_add]; congr 1; ring, hbn, mul_one]
    exact Prod.ext (Subtype.ext hA) (Subtype.ext hB)
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  have hcard : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = p ^ 2 := by
    rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hao, hbo, sq]
  have hel : CFSG.Open.IsElemAbelian p (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · apply Subtype.ext
      show (x : G) * (y : G) = (y : G) * (x : G)
      obtain ⟨h1, hh1, k1, hk1, e1⟩ := r2a_mem_sup hc x.2
      obtain ⟨h2, hh2, k2, hk2, e2⟩ := r2a_mem_sup hc y.2
      rw [← e1, ← e2]
      have c1 : h2 * k1 = k1 * h2 := hc h2 hh2 k1 hk1
      have c2 : h1 * k2 = k2 * h1 := hc h1 hh1 k2 hk2
      have cH : h1 * h2 = h2 * h1 := hcA h1 hh1 h2 hh2
      have cK : k1 * k2 = k2 * k1 := hcB k1 hk1 k2 hk2
      calc h1 * k1 * (h2 * k2) = h1 * (k1 * h2) * k2 := by simp only [mul_assoc]
        _ = h1 * (h2 * k1) * k2 := by rw [c1]
        _ = (h1 * h2) * (k1 * k2) := by simp only [mul_assoc]
        _ = (h2 * h1) * (k2 * k1) := by rw [cH, cK]
        _ = h2 * (h1 * k2) * k1 := by simp only [mul_assoc]
        _ = h2 * (k2 * h1) * k1 := by rw [c2]
        _ = h2 * k2 * (h1 * k1) := by simp only [mul_assoc]
    · intro x hx
      obtain ⟨h, hh, k, hk, rfl⟩ := r2a_mem_sup hc hx
      rw [(show Commute h k from hc h hh k hk).mul_pow, r2a_pow_zpowers ha h hh,
        r2a_pow_zpowers hb k hk, one_mul]
  exact ⟨hel, hcard⟩

theorem exists_E_two {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (Dp : Subgroup G) (hDp : IsPGroup p Dp) (hexp : ∀ x ∈ Dp, x ^ p = 1)
    (hΦc : ∀ x ∈ (frattini ↥Dp).map Dp.subtype, ∀ d ∈ Dp, x * d = d * x)
    (P : Subgroup G) (hPD : P ≤ Dp)
    (hPmap : p ^ 2 ≤ ((frattini ↥Dp).map Dp.subtype).relIndex
      (P ⊔ (frattini ↥Dp).map Dp.subtype)) :
    ∃ A : Subgroup G, A ≤ P ∧ CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      Nat.card (A ⊓ (frattini ↥Dp).map Dp.subtype : Subgroup G) ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Φ : Subgroup G := (frattini ↥Dp).map Dp.subtype with hΦdef
  have hPexp : ∀ y ∈ P, y ^ p = 1 := fun y hy => hexp y (hPD hy)
  have hcomm_mem : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ Φ := fun a ha b hb =>
    r2a_comm_mem hDp hexp (hPD ha) (hPD hb)
  obtain ⟨y₁, hy₁P, hy₁Φ⟩ := r2a_exists_y1 hp hPmap
  obtain ⟨y₂, hy₂P, hy₂K⟩ := r2a_exists_y2 hp hΦc hPD hPexp hPmap hy₁P hy₁Φ
  have hy₁ne : y₁ ≠ 1 := fun h => hy₁Φ (by rw [h]; exact Φ.one_mem)
  have hord1 : orderOf y₁ = p := orderOf_eq_prime (hPexp y₁ hy₁P) hy₁ne
  by_cases hint : P ⊓ Φ = ⊥
  ·
    have hcomm : Commute y₁ y₂ := by
      have hmem : ⁅y₁, y₂⁆ ∈ P ⊓ Φ := by
        refine ⟨?_, hcomm_mem y₁ hy₁P y₂ hy₂P⟩
        rw [commutatorElement_def]
        exact P.mul_mem (P.mul_mem (P.mul_mem hy₁P hy₂P) (P.inv_mem hy₁P)) (P.inv_mem hy₂P)
      rw [hint, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    have hy2ne : y₂ ≠ 1 := fun h => hy₂K (by rw [h]; exact (Subgroup.zpowers y₁ ⊔ Φ).one_mem)
    have hind : ∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
      intro i j h
      have hj : y₂ ^ j ∈ Subgroup.zpowers y₁ ⊔ Φ := by
        rw [eq_inv_of_mul_eq_one_right h]
        exact (Subgroup.zpowers y₁ ⊔ Φ).inv_mem
          (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers y₁ i))
      have hjp : (p : ℤ) ∣ j := by
        by_contra hj'
        exact hy₂K (r2a_mem_of_pow_mem hp _ (hPexp y₂ hy₂P) hj' hj)
      have hyj : y₂ ^ j = 1 := r2a_zpow_eq_one (hPexp y₂ hy₂P) hjp
      have hyi : y₁ ^ i = 1 := by rw [hyj, mul_one] at h; exact h
      refine ⟨?_, hjp⟩
      have := orderOf_dvd_iff_zpow_eq_one.mpr hyi
      rwa [hord1] at this
    have hA := r2a_elem_sup hp hcomm (hPexp y₁ hy₁P) (hPexp y₂ hy₂P) hy₁ne hy2ne hind
    have hAP : Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ ≤ P :=
      sup_le (Subgroup.zpowers_le.mpr hy₁P) (Subgroup.zpowers_le.mpr hy₂P)
    refine ⟨Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂, hAP, hA.1, hA.2, ?_⟩
    have hAΦ : (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂) ⊓ Φ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxP : x ∈ P ⊓ Φ := ⟨hAP hx.1, hx.2⟩
      rw [hint] at hxP
      exact hxP
    rw [hAΦ, Subgroup.card_bot]
    exact hp.one_lt.le
  ·
    obtain ⟨z, hzPΦ, hz1⟩ : ∃ z ∈ P ⊓ Φ, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hint (eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hcon z hz))
    have hzP : z ∈ P := hzPΦ.1
    have hzΦ : z ∈ Φ := hzPΦ.2
    have hzord : orderOf z = p := orderOf_eq_prime (hPexp z hzP) hz1
    have hcomm : Commute y₁ z := (hΦc z hzΦ y₁ (hPD hy₁P)).symm
    have hind : ∀ i j : ℤ, y₁ ^ i * z ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
      intro i j h
      have hyi : y₁ ^ i ∈ Φ := by
        rw [eq_inv_of_mul_eq_one_left h]
        exact Φ.inv_mem (Φ.zpow_mem hzΦ j)
      have hip : (p : ℤ) ∣ i := by
        by_contra hi
        exact hy₁Φ (r2a_mem_of_pow_mem hp Φ (hPexp y₁ hy₁P) hi hyi)
      have hyi1 : y₁ ^ i = 1 := r2a_zpow_eq_one (hPexp y₁ hy₁P) hip
      have hzj : z ^ j = 1 := by rw [hyi1, one_mul] at h; exact h
      refine ⟨hip, ?_⟩
      have := orderOf_dvd_iff_zpow_eq_one.mpr hzj
      rwa [hzord] at this
    have hA := r2a_elem_sup hp hcomm (hPexp y₁ hy₁P) (hPexp z hzP) hy₁ne hz1 hind
    have hAP : Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z ≤ P :=
      sup_le (Subgroup.zpowers_le.mpr hy₁P) (Subgroup.zpowers_le.mpr hzP)
    refine ⟨Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z, hAP, hA.1, hA.2, ?_⟩
    have hsub : (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z) ⊓ Φ ≤ Subgroup.zpowers z := by
      intro x hx
      obtain ⟨hxA, hxΦ⟩ := hx
      obtain ⟨u, hu, v, hv, huv⟩ := r2a_mem_sup (r2a_comm_zpowers hcomm) hxA
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      have hvΦ : z ^ n ∈ Φ := Φ.zpow_mem hzΦ n
      have huΦ : u ∈ Φ := by
        have hu_eq : u = x * (z ^ n)⁻¹ := by rw [← huv, mul_inv_cancel_right]
        rw [hu_eq]
        exact Φ.mul_mem hxΦ (Φ.inv_mem hvΦ)
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hm : (p : ℤ) ∣ m := by
        by_contra hm
        exact hy₁Φ (r2a_mem_of_pow_mem hp Φ (hPexp y₁ hy₁P) hm huΦ)
      have hu1 : y₁ ^ m = 1 := r2a_zpow_eq_one (hPexp y₁ hy₁P) hm
      rw [← huv, hu1, one_mul]
      exact hv
    calc Nat.card ((Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z) ⊓ Φ : Subgroup G)
        ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hsub
      _ = p := by rw [Nat.card_zpowers, hzord]

end CFSG.RankThree.PartTwo.Sec13.F135Last
