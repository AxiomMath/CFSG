module

public import CFSG.Quasithin.EmptyFaithful.S146B3
public import CFSG.Quasithin.EmptyFaithful.S1421L2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack

section Aux

variable {Q : Type*} [Group Q]

theorem eq_self_of_iterate_eq_of_card_eq_three (hQ : Nat.card Q = 3) (ψ : Q →* Q) {m : ℕ}
    (hm : Odd m) (hψ : ∀ q : Q, ψ^[m] q = q) (q : Q) : ψ q = q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  obtain ⟨g, hg1⟩ : ∃ g : Q, g ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Nat.card Q = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  have hg3 : g ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Q) (x := g)
    rwa [hQ] at this
  have hog : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hzp : Subgroup.zpowers g = ⊤ := zpowers_eq_top_of_prime_card hQ hg1
  have hall : ∀ q : Q, ∃ i : ℕ, g ^ i = q := by
    intro q
    have hq : q ∈ Subgroup.zpowers g := by rw [hzp]; trivial
    rw [mem_zpowers_iff_mem_range_orderOf] at hq
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hq
    exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := hall (ψ g)
  have hit : ∀ j : ℕ, ψ^[j] g = g ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, map_pow, ← hk, ← pow_mul, pow_succ']
  obtain ⟨t, rfl⟩ := hm
  have hm1 : (g : Q) = g ^ (k ^ (2 * t + 1)) := by
    rw [← hit]
    exact (hψ g).symm
  have hk3 : k < 3 ∨ 3 ≤ k := lt_or_ge k 3
  have hkmod : g ^ k = g ^ (k % 3) := by
    rw [← pow_mod_orderOf, hog]
  have hk' : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hpowmod : ∀ n : ℕ, g ^ n = g ^ (n % 3) := fun n => by rw [← pow_mod_orderOf, hog]
  have hkm : ∀ n : ℕ, (k ^ n) % 3 = (k % 3) ^ n % 3 := fun n => Nat.pow_mod k n 3
  rcases hk' with h0 | h1 | h2
  · exfalso
    have hkp : (k ^ (2 * t + 1)) % 3 = 0 := by
      rw [hkm, h0]
      simp
    rw [hpowmod (k ^ (2 * t + 1)), hkp, pow_zero] at hm1
    exact hg1 hm1
  · have hgk : ψ g = g := by rw [← hk, hkmod, h1, pow_one]
    obtain ⟨i, rfl⟩ := hall q
    rw [map_pow, hgk]
  · exfalso
    have hkp : (k ^ (2 * t + 1)) % 3 = 2 := by
      rw [hkm, h2, pow_succ, pow_mul]
      have : (2 ^ 2) ^ t % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      rw [Nat.mul_mod, this]
    rw [hpowmod (k ^ (2 * t + 1)), hkp] at hm1
    have : g = 1 := by
      have h3 : g ^ 2 * g⁻¹ = 1 := by rw [← hm1]; group
      calc g = g ^ 2 * g⁻¹ := by group
        _ = 1 := h3
    exact hg1 this

end Aux

section Odd

variable {G : Type*} [Group G]

theorem commutator_mem_of_odd_orderOf {Y N : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hidx : N.relIndex Y = 3) {x : G}
    (hxY : x ∈ Subgroup.normalizer (Y : Set G)) (hxN : x ∈ Subgroup.normalizer (N : Set G))
    (hodd : Odd (orderOf x)) {y : G} (hy : y ∈ Y) : x * y * x⁻¹ * y⁻¹ ∈ N := by
  classical
  have hN' : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  have hQ : Nat.card (↥Y ⧸ N.subgroupOf Y) = 3 := hidx
  let c : ↥Y →* ↥Y :=
    { toFun := fun a => ⟨x * a * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxY a).mp a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hc : N.subgroupOf Y ≤ (N.subgroupOf Y).comap c := fun a ha => by
    show c a ∈ N.subgroupOf Y
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
  let ψ : (↥Y ⧸ N.subgroupOf Y) →* (↥Y ⧸ N.subgroupOf Y) := QuotientGroup.map _ _ c hc
  have hψmk : ∀ a : ↥Y, ψ (QuotientGroup.mk a) = QuotientGroup.mk (c a) := fun a => rfl
  have hit : ∀ j : ℕ, ∀ a : ↥Y, ∃ b : ↥Y, (b : G) = x ^ j * a * (x ^ j)⁻¹ ∧
      ψ^[j] (QuotientGroup.mk a) = QuotientGroup.mk b := by
    intro j
    induction j with
    | zero => exact fun a => ⟨a, by simp, rfl⟩
    | succ j ih =>
      intro a
      obtain ⟨b, hb, hbq⟩ := ih a
      refine ⟨c b, ?_, ?_⟩
      · show x * (b : G) * x⁻¹ = _
        rw [hb, pow_succ']
        group
      · rw [Function.iterate_succ_apply', hbq, hψmk]
  have hfix : ∀ q : ↥Y ⧸ N.subgroupOf Y, ψ^[orderOf x] q = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨b, hb, hbq⟩ := hit (orderOf x) a
      have : b = a := by
        apply Subtype.ext
        rw [hb, pow_orderOf_eq_one]
        simp
      rw [hbq, this]
  have hψ := eq_self_of_iterate_eq_of_card_eq_three hQ ψ hodd hfix (QuotientGroup.mk ⟨y, hy⟩)
  rw [hψmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hψ
  have h0 : x * (y⁻¹ * (x⁻¹ * y)) ∈ N := by simpa [c, mul_assoc] using hψ
  have h1 : y⁻¹ * x * y * x⁻¹ ∈ N := by
    have := N.inv_mem h0
    have e : (x * (y⁻¹ * (x⁻¹ * y)))⁻¹ = y⁻¹ * x * y * x⁻¹ := by group
    rwa [e] at this
  have h2 := (Subgroup.mem_normalizer_iff.mp (hYN hy) _).mp h1
  have e : y * (y⁻¹ * x * y * x⁻¹) * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
  rwa [e] at h2

theorem commutator_mem_of_mem_oTwoUpper {Y N A M : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hidx : N.relIndex Y = 3) (hAM : A ≤ M)
    (hMY : M ≤ Subgroup.normalizer (Y : Set G)) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ oTwoUpper A) {y : G} (hy : y ∈ Y) : x * y * x⁻¹ * y⁻¹ ∈ N := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    exact commutator_mem_of_odd_orderOf hNY hYN hidx (hMY (hAM hx.1)) (hMN (hAM hx.1)) hx.2 hy
  | one => simp
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
    have hx₁M : x₁ ∈ M := hAM (oTwoUpper_le A hx₁)
    have h1 := (Subgroup.mem_normalizer_iff.mp (hMN hx₁M) _).mp ih₂
    have e : x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹ =
        (x₁ * (x₂ * y * x₂⁻¹ * y⁻¹) * x₁⁻¹) * (x₁ * y * x₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact N.mul_mem h1 ih₁
  | inv x hx ih =>
    have hxM : x ∈ M := hAM (oTwoUpper_le A hx)
    have h1 := (Subgroup.mem_normalizer_iff.mp (hMN (M.inv_mem hxM)) _).mp (N.inv_mem ih)
    have e : x⁻¹ * ((x * y * x⁻¹ * y⁻¹)⁻¹) * x⁻¹⁻¹ = x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ := by group
    rwa [e] at h1

end Odd

section Normalizes

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_commutator_mem_s1461 {X Ly R : Subgroup G} (hX : oTwoUpper X = X)
    (hR : IsPGroup 2 R) (hRn : R ≤ Subgroup.normalizer (X : Set G))
    (hLR : Ly ≤ Subgroup.normalizer (R : Set G))
    (hcomm : ∀ x ∈ X, ∀ l ∈ Ly, x * l * x⁻¹ * l⁻¹ ∈ R) :
    Ly ≤ Subgroup.normalizer (X : Set G) := by
  have hmul : ((X ⊔ R : Subgroup G) : Set G) = X * R :=
    Subgroup.coe_mul_of_right_le_normalizer_left X R hRn
  have hXeq : X = oTwoUpper (X ⊔ R) := by
    refine eq_oTwoUpper_of_pow_mem le_sup_left (fun w hw => ?_) hX.symm
    have hw' : w ∈ ((X ⊔ R : Subgroup G) : Set G) := hw
    rw [hmul] at hw'
    obtain ⟨x, hx, r, hr, rfl⟩ := hw'
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    have hk' : r ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨x', hx', h⟩ := A4.exists_pow_mul_eq hx (hRn hr) (2 ^ k)
    exact ⟨k, by rw [h, hk', mul_one]; exact hx'⟩
  have hconj : ∀ g ∈ Ly, B6.conjSub g (X ⊔ R) ≤ X ⊔ R := by
    intro g hg
    rw [OrderIso.map_sup]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [B6.mem_conjSub] at hy
      have hr : (g⁻¹ * y * g)⁻¹ * g * (g⁻¹ * y * g)⁻¹⁻¹ * g⁻¹ ∈ R := by
        simpa using hcomm _ (X.inv_mem hy) g hg
      have e : y = (g⁻¹ * y * g) * ((g⁻¹ * y * g)⁻¹ * g * (g⁻¹ * y * g)⁻¹⁻¹ * g⁻¹) := by group
      rw [e]
      exact (X ⊔ R).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hr)
    · rw [B6.mem_conjSub] at hy
      have := (Subgroup.mem_normalizer_iff.mp (hLR hg) _).mp hy
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [e] at this
      exact Subgroup.mem_sup_right this
  intro g hg
  have hgS : g ∈ Subgroup.normalizer ((X ⊔ R : Subgroup G) : Set G) :=
    B6.mem_normalizer_of_conjSub_le (hconj g hg) (hconj g⁻¹ (Ly.inv_mem hg))
  have := normalizer_le_normalizer_oTwoUpper (X ⊔ R) hgS
  rwa [← hXeq] at this

end Normalizes

section PCore

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_ne_bot_of_eq_oTwoUpper {H X : Subgroup G} (hH : CharTwo H) (hXH : X ≤ H)
    (hQX : pCoreOf 2 H ≤ Subgroup.normalizer (X : Set G)) (hX : oTwoUpper X = X) (hX0 : X ≠ ⊥) :
    pCoreOf 2 X ≠ ⊥ := by
  intro hP
  apply hX0
  have hQH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hnorm : X ≤ Subgroup.normalizer ((X ⊓ pCoreOf 2 H : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hQH (hXH hx)⟩
  have hXQ : X ⊓ pCoreOf 2 H ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  rw [hP, le_bot_iff] at hXQ
  have hcent : X ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : x * q * x⁻¹ * q⁻¹ ∈ pCoreOf 2 H :=
      (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hQH (hXH hx)) q).mp hq)
        ((pCoreOf 2 H).inv_mem hq)
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ X := by
      have := X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hQX hq) x⁻¹).mp (X.inv_mem hx))
      simpa [mul_assoc] using this
    have h3 : x * q * x⁻¹ * q⁻¹ ∈ X ⊓ pCoreOf 2 H := ⟨h2, h1⟩
    rw [hXQ, Subgroup.mem_bot] at h3
    have h4 : x * q = q * x := by
      calc x * q = (x * q * x⁻¹ * q⁻¹) * (q * x) := by group
        _ = q * x := by rw [h3, one_mul]
    exact h4.symm
  have hXP : X ≤ pCoreOf 2 H := fun x hx => hH ⟨hXH hx, hcent hx⟩
  have hle : oTwoUpper X ≤ ⊥ := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x, hXP hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  rw [hX] at hle
  exact le_bot_iff.mp hle

end PCore

section Core

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem pCoreOf_yOfL22_le (S : Setting146 G T M) : pCoreOf 2 (yOfL22 T M) ≤ T := by
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hTsyl : IsSylowTwoOf T M := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTM
  exact (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (yOfL22_le T M))
    (F7.le_normalizer_pCoreOf_of_le_normalizer (le_normalizer_yOfL22 T M))
    (pCoreOf_isPGroup 2 _)).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)

theorem normalizer_oTwoUpper_le (S : Setting146 G T M) {A : Subgroup G} (hAM : A ≤ M)
    (hTA : T ≤ Subgroup.normalizer (A : Set G)) (hX : pCoreOf 2 (oTwoUpper A) ≠ ⊥) :
    Subgroup.normalizer (oTwoUpper A : Set G) ≤ M := by
  have hyp := S.hyp
  have F := S.facts
  set Ly := yOfL22 T M with hLy
  set X := oTwoUpper A with hXdef
  have hMLy : M ≤ Subgroup.normalizer (Ly : Set G) := le_normalizer_yOfL22 T M
  have hMR : M ≤ Subgroup.normalizer (pCoreOf 2 Ly : Set G) :=
    F7.le_normalizer_pCoreOf_of_le_normalizer hMLy
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := hTA.trans (normalizer_le_normalizer_oTwoUpper A)
  have hRX : pCoreOf 2 Ly ≤ Subgroup.normalizer (X : Set G) := (pCoreOf_yOfL22_le S).trans hTX
  have hcomm : ∀ x ∈ X, ∀ l ∈ Ly, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 Ly := fun x hx l hl =>
    commutator_mem_of_mem_oTwoUpper (pCoreOf_le 2 Ly) (le_normalizer_pCoreOf 2 Ly)
      (S1421.relIndex_pCoreOf_y hyp F) hAM hMLy hMR hx hl
  have hLyX : Ly ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_commutator_mem_s1461 (oTwoUpper_oTwoUpper A) (pCoreOf_isPGroup 2 Ly) hRX
      (le_normalizer_pCoreOf 2 Ly) hcomm
  have hK : pCoreOf 2 (Subgroup.normalizer (X : Set G)) ≠ ⊥ := by
    intro h
    apply hX
    have := le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 X).trans Subgroup.le_normalizer)
      (normalizer_le_normalizer_pCoreOf 2 X) (pCoreOf_isPGroup 2 X)
    rw [h] at this
    exact le_bot_iff.mp this
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hK
  have hM'LT : InM (Ly ⊔ T) M' := ⟨hM'.1, (sup_le hLyX hTX).trans hM'.2⟩
  exact hM'.2.trans (F.unique.2 M' hM'LT).le

end Core

section OddPower

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_orderOf_mem_zpowers_not_mem {Y Q : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q) (hY2 : ∀ x ∈ Y, ∃ k : ℕ, x ^ p ^ k ∈ Q) {x : G} (hx : x ∈ Y)
    (hxQ : x ∉ Q) : ∃ y ∈ Subgroup.zpowers x, Odd (orderOf y) ∧ y ∉ Q := by
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have h2b : (2 ^ b : ℕ) ≠ 0 := by positivity
  have hord : orderOf (x ^ 2 ^ b) = m := by
    rw [orderOf_pow' _ h2b, hbm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  refine ⟨x ^ 2 ^ b, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, hord ▸ hm, fun hyQ => hxQ ?_⟩
  obtain ⟨j, hj⟩ := hQ2 ⟨x ^ 2 ^ b, hyQ⟩
  have hj' : (x ^ 2 ^ b) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hdvd : m ∣ 2 ^ j := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hj'
  have hm1 : m = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hm)) hdvd
  have hox : orderOf x = 2 ^ b := by rw [hbm, hm1, mul_one]
  obtain ⟨k, hk⟩ := hY2 x hx
  have hcop : Nat.Coprime (p ^ k) (orderOf x) := by
    rw [hox]
    exact Nat.Coprime.pow k b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

end OddPower

section Bridge

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoPIn_props (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    oTwoPIn p H ≤ H ∧ pCoreOf 2 H ≤ oTwoPIn p H ∧ H ≤ Subgroup.normalizer (oTwoPIn p H : Set G) ∧
      ∀ x ∈ oTwoPIn p H, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : oTwoPIn p H ≤ H := Subgroup.map_subtype_le _
  have hEq : oTwoPIn p H = preimH H (CFSG.pCore p (OTwoQuot H)) := by
    ext x
    rw [mem_preimH]
    constructor
    · intro hx
      exact ⟨hle hx, mem_pCore_of_mem_oTwoPIn (hle hx) hx⟩
    · rintro ⟨hxH, h⟩
      exact mem_oTwoPIn_of_mem_pCore hxH h
  have hNn : (CFSG.pCore p (OTwoQuot H)).Normal := CFSG.BaerSuzuki.Helpers.pCore_normal p
  refine ⟨hle, ?_, ?_, ?_⟩
  · rw [hEq]
    exact pCoreOf_le_preimH H _
  · rw [hEq]
    exact normalizer_preimH
  · intro x hx
    rw [hEq, mem_preimH] at hx
    obtain ⟨hxH, hx⟩ := hx
    obtain ⟨k, hk⟩ := CFSG.BaerSuzuki.Helpers.pCore_isPGroup p ⟨_, hx⟩
    refine ⟨k, ?_⟩
    have h1 : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) ⟨x, hxH⟩) ^ p ^ k = 1 :=
      congrArg Subtype.val hk
    rw [← map_pow] at h1
    have h2 : (⟨x, hxH⟩ : ↥H) ^ p ^ k ∈ CFSG.Open.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, by simp⟩

end Bridge

end C1Pack

open C1Pack in
theorem stage1461Two : Stage1461Two := by
  intro G _ _ T M S H hH p hp hp2
  classical
  have hyp := S.hyp
  have hTM : T ≤ M := hyp.m_max.1.2
  have hTH : T ≤ H := hH.1.1
  have hHM : ¬ H ≤ M := hH.2
  have hHchar : CharTwo H := charTwo_of_inH' hyp.qtke hyp.sylow hH.1
  have hQT : pCoreOf 2 H ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH)
  obtain ⟨hYH, hQY, hHY, hY2⟩ := oTwoPIn_props H hp
  have hQH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  set Q := pCoreOf 2 H with hQ
  set Yp := oTwoPIn p H with hYp
  refine le_antisymm ?_ (le_inf hQY (hQT.trans hTM))
  by_contra hcon
  have hex : ∃ x ∈ Yp ⊓ M, x ∉ Q := by
    by_contra h
    push Not at h
    exact hcon fun x hx => h x hx
  obtain ⟨x, hxP, hxQ⟩ := hex
  set P := Yp ⊓ M with hP
  have hQP : Q ≤ P := le_inf hQY (hQT.trans hTM)
  have hPT : T ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHY (hTH ht), Subgroup.le_normalizer (hTM ht)⟩
  obtain ⟨y, hyz, hyodd, hyQ⟩ := exists_odd_orderOf_mem_zpowers_not_mem hp hp2 hQ2 hY2 hxP.1 hxQ
  have hyP : y ∈ P := (Subgroup.zpowers_le.mpr hxP) hyz
  have hX1 : oTwoUpper P ≠ ⊥ := by
    intro h
    have := mem_oTwoUpper_of_odd hyP hyodd
    rw [h, Subgroup.mem_bot] at this
    exact hyQ (this ▸ Q.one_mem)
  have hX1c : pCoreOf 2 (oTwoUpper P) ≠ ⊥ :=
    pCoreOf_ne_bot_of_eq_oTwoUpper hHchar ((oTwoUpper_le P).trans (inf_le_left.trans hYH))
      (hQP.trans (le_normalizer_oTwoUpper P)) (oTwoUpper_oTwoUpper P) hX1
  have hN1 : Subgroup.normalizer (oTwoUpper P : Set G) ≤ M :=
    normalizer_oTwoUpper_le S inf_le_right hPT hX1c
  set Y0 := centralizerSection Yp Yp Q with hY0
  have hY0Y : Y0 ≤ Yp := centralizerSection_le_left _ _ _
  have hHY0 : H ≤ Subgroup.normalizer (Y0 : Set G) := fun h hh =>
    A4.mem_normalizer_of_conj_mem fun m hm =>
      conj_mem_centralizerSection (hHY hh) (hHY hh) (hQH hh) hm
  have hY0P : Y0 ≤ Subgroup.normalizer (P : Set G) := by
    intro y hy
    refine A4.mem_normalizer_of_conj_mem fun a ha => ?_
    have hc : y * a * y⁻¹ * a⁻¹ ∈ Q := by
      have h1 := Q.inv_mem (hy.2.2.2 a ha.1)
      have e : (a * y * a⁻¹ * y⁻¹)⁻¹ = y * a * y⁻¹ * a⁻¹ := by group
      rwa [e] at h1
    have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact P.mul_mem (hQP hc) ha
  have hY0M : Y0 ≤ M := fun y hy =>
    hN1 (normalizer_le_normalizer_oTwoUpper P (hY0P hy))
  have hQN : Yp ≤ Subgroup.normalizer (Q : Set G) := hYH.trans hQH
  have hQnorm : (Q.subgroupOf Yp).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQY).mpr hQN
  have hRp : IsPGroup p (↥Yp ⧸ Q.subgroupOf Yp) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨k, hk⟩ := hY2 a a.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
  have hRnt : Nontrivial (↥Yp ⧸ Q.subgroupOf Yp) :=
    ⟨⟨QuotientGroup.mk ⟨x, hxP.1⟩, 1, fun h => hxQ (by
      have := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
      exact this)⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcenter : Nontrivial (Subgroup.center (↥Yp ⧸ Q.subgroupOf Yp)) := hRp.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (↥Yp ⧸ Q.subgroupOf Yp))
  obtain ⟨a, haz⟩ := QuotientGroup.mk_surjective (z : ↥Yp ⧸ Q.subgroupOf Yp)
  have haQ : (a : G) ∉ Q := by
    intro h
    apply hz1
    apply Subtype.ext
    rw [← haz]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h)
  have haY0 : (a : G) ∈ Y0 := by
    refine (mem_centralizerSection_iff_of_le hQY).mpr ⟨a.2, fun u hu => ?_⟩
    have hcomm : (QuotientGroup.mk ⟨u, hu⟩ : ↥Yp ⧸ Q.subgroupOf Yp) * QuotientGroup.mk a =
        QuotientGroup.mk a * QuotientGroup.mk ⟨u, hu⟩ := by
      rw [haz]
      exact Subgroup.mem_center_iff.mp z.2 _
    have h1 : (QuotientGroup.mk (⟨u, hu⟩ * a * ⟨u, hu⟩⁻¹ * a⁻¹ : ↥Yp) :
        ↥Yp ⧸ Q.subgroupOf Yp) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  obtain ⟨w, hwz, hwodd, hwQ⟩ :=
    exists_odd_orderOf_mem_zpowers_not_mem hp hp2 hQ2 hY2 a.2 haQ
  have hw0 : w ∈ Y0 := (Subgroup.zpowers_le.mpr haY0) hwz
  have hX2 : oTwoUpper Y0 ≠ ⊥ := by
    intro h
    have := mem_oTwoUpper_of_odd hw0 hwodd
    rw [h, Subgroup.mem_bot] at this
    exact hwQ (this ▸ Q.one_mem)
  have hHX2 : H ≤ Subgroup.normalizer (oTwoUpper Y0 : Set G) :=
    hHY0.trans (normalizer_le_normalizer_oTwoUpper Y0)
  have hX2c : pCoreOf 2 (oTwoUpper Y0) ≠ ⊥ :=
    pCoreOf_ne_bot_of_eq_oTwoUpper hHchar ((oTwoUpper_le Y0).trans (hY0Y.trans hYH))
      (fun q hq => hHX2 (pCoreOf_le 2 H hq)) (oTwoUpper_oTwoUpper Y0) hX2
  have hN2 : Subgroup.normalizer (oTwoUpper Y0 : Set G) ≤ M :=
    normalizer_oTwoUpper_le S hY0M (fun t ht => hHY0 (hTH ht)) hX2c
  exact hHM (hHX2.trans hN2)

end CFSG.Quasithin
