module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9GrpOne

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem odd_mem_cenW₂ (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) {x₁ : MulAut W}
    (hx₁ : x₁ ∈ S.A₁) (hx₁2 : orderOf x₁ = 2) {g : MulAut W} (hg : g ∈ Mb)
    (hfix : ∀ z ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁), g z = z) (hodd : Odd (orderOf g)) :
    g ∈ S.cenW₂ := by
  obtain ⟨z, hzL, hz1⟩ : ∃ z ∈ S.W₁ ⊓ fixV (Subgroup.zpowers x₁), z ≠ 1 := by
    by_contra hcon
    have hbot : S.W₁ ⊓ fixV (Subgroup.zpowers x₁) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr fun x hx => by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h1 := Subgroup.card_eq_one.mpr hbot
    have h4 := S.card_fix_reflection₁ hW hcard hx₁ hx₁2
    omega
  obtain ⟨hs1, hs2⟩ := S.stab_of_mem_of_fix₁ hW hnorm hg ⟨z, hzL.1, hz1, hfix z hzL⟩
  have hc₁ : g * S.a₁ = S.a₁ * g :=
    commute_of_conj_odd_five151b S.orderOf_a₁_five
      (S.mem_zpowers_a₁_conj hW hcard (hnorm g hg) ⟨hs1, hs2⟩) hodd
  have hc₂ : g * S.a₂ = S.a₂ * g :=
    commute_of_conj_odd_five151b S.orderOf_a₂_five
      (S.mem_zpowers_a₂_conj hW hcard (hnorm g hg) ⟨hs1, hs2⟩) hodd
  have hgW₁ : ∀ w ∈ S.W₁, g w = w :=
    S.fix_W₁_of_commute hW hcard hc₁ hzL.1 hz1 (hfix z hzL)
  exact ⟨hgW₁, hc₂, hs2⟩

theorem exists_zpow_eq (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {ε g : MulAut W}
    (hε : ε ∈ S.cenW₂) (hε3 : orderOf ε = 3) (hg : g ∈ S.cenW₂) :
    ∃ k : ℤ, g = ε ^ k * S.a₂ ^ k := by
  have hcomm : Commute ε S.a₂ := hε.2.1
  have heq := S.cenW₂_eq_zpowers hW hcard hε hε3
  rw [heq] at hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ⟨k, by rw [← hk, hcomm.mul_zpow]⟩

theorem mem_zpowers_a₂_of_pow_five (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {ε g : MulAut W} (hε : ε ∈ S.cenW₂) (hε3 : orderOf ε = 3) (hg : g ∈ S.cenW₂)
    (hg5 : g ^ 5 = 1) : g ∈ Subgroup.zpowers S.a₂ := by
  have hcomm : Commute ε S.a₂ := hε.2.1
  have heq := S.cenW₂_eq_zpowers hW hcard hε hε3
  rw [heq] at hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hord : orderOf (ε * S.a₂) = 15 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime, hε3, S.orderOf_a₂_five]
    rw [hε3, S.orderOf_a₂_five]
    norm_num
  have h1 : (ε * S.a₂) ^ (k * 5) = 1 := by
    rw [zpow_mul, hk]
    exact hg5
  obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 3 * m := by
    have h2 : ((15 : ℕ) : ℤ) ∣ k * 5 := by
      rw [← hord]
      exact orderOf_dvd_iff_zpow_eq_one.mpr h1
    obtain ⟨j, hj⟩ := h2
    exact ⟨j, by push_cast at hj; omega⟩
  have hε3' : ε ^ 3 = 1 := by
    have := pow_orderOf_eq_one ε
    rwa [hε3] at this
  have hc3 : (ε * S.a₂) ^ (3 : ℤ) = S.a₂ ^ (3 : ℤ) := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_natCast, hcomm.mul_pow, hε3',
      one_mul]
  rw [← hk, hm, zpow_mul, hc3, ← zpow_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

theorem pow_fifteen_eq_one (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {ε g : MulAut W}
    (hε : ε ∈ S.cenW₂) (hε3 : orderOf ε = 3) (hg : g ∈ S.cenW₂) : g ^ 15 = 1 := by
  have hcomm : Commute ε S.a₂ := hε.2.1
  have heq := S.cenW₂_eq_zpowers hW hcard hε hε3
  rw [heq] at hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hord : orderOf (ε * S.a₂) = 15 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime, hε3, S.orderOf_a₂_five]
    rw [hε3, S.orderOf_a₂_five]
    norm_num
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hord,
    pow_orderOf_eq_one, one_zpow]

theorem pow_five_eq_one_of_pow (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {ε g : MulAut W} (hε : ε ∈ S.cenW₂) (hε3 : orderOf ε = 3) (hg : g ∈ S.cenW₂) {m : ℕ}
    (hgm : g ^ 5 ^ m = 1) : g ^ 5 = 1 := by
  have h15 : g ^ 15 = 1 := S.pow_fifteen_eq_one hW hcard hε hε3 hg
  have hd1 : orderOf g ∣ 5 ^ m := orderOf_dvd_of_pow_eq_one hgm
  have hd2 : orderOf g ∣ 15 := orderOf_dvd_of_pow_eq_one h15
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hd1
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h2j : 2 ≤ j := by omega
    have h25 : 5 ^ 2 ∣ 5 ^ j := pow_dvd_pow 5 h2j
    rw [← hj'] at h25
    have h25' := h25.trans hd2
    omega
  have h5 : orderOf g ∣ 5 := by
    rw [hj']
    interval_cases j <;> simp
  exact orderOf_dvd_iff_pow_eq_one.mp h5

end CFSG.Quasithin.SixData151b

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem odd_orderOf_of_isPGroup_five_e9 {Y : Subgroup G} (hY : IsPGroup 5 Y) :
    ∀ y ∈ Y, Odd (orderOf y) := by
  intro y hy
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hY) ⟨y, hy⟩
  have h1 : orderOf y = 5 ^ k := by
    rw [← Subgroup.orderOf_coe (⟨y, hy⟩ : ↥Y)] at hk
    exact hk
  rw [h1]
  exact Odd.pow (by decide)

theorem factor_of_e9 {T Mc M Z₁ Z₂ V₁ V₂ Y : Subgroup G}
    (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (hE : E9Pre T Mc M Z₁ Z₂ V₁ V₂)
    (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M) (h14 : Lemma15114Concl T Mc M)
    (h113 : Lemma15113Four T Mc M) (hYM : Y ≤ M ⊓ g1_1516 Z₁) (hY5 : IsPGroup 5 Y)
    (hVY : ⁅V₂, Y⁆ = V₂) :
    ∀ n ∈ M ⊓ g1_1516 Z₁, Odd (orderOf n) → ∃ y ∈ Y, y⁻¹ * n ∈ mZ1516 Mc Z₁ := by
  obtain ⟨hVe, d, hV₁, hV₂⟩ := hE.data
  have h5 := hE.h5
  obtain ⟨x₁, x₂, r⟩ := exists_reflData d h5 h113
  obtain ⟨-, ε₂, -, ⟨hε₂M, hε₂3, hε₂₁, hε₂a, hε₂f, hε₂s1, hε₂s2⟩⟩ := exists_torus r hE.e9
  have hC1 := vZ_mc_eq_vE hq hM hCE h5 hE.e9 h15 h19 h14 h113
  have hW : ∀ w : IntMod (V154 T Mc M) hVe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hZ₁ := r.z₁_eq hE.z₁ hV₁
  have hεC : ε₂ ∈ d.S.cenW₂ := ⟨hε₂₁, hε₂a, hε₂s2⟩
  have key : ∀ n ∈ M ⊓ g1_1516 Z₁, Odd (orderOf n) →
      ∃ hN : n ∈ Subgroup.normalizer (V154 T Mc M : Set G),
        convI hVe ⟨n, hN⟩ ∈ d.S.cenW₂ := by
    intro n hn hodd
    have hN : n ∈ Subgroup.normalizer (V154 T Mc M : Set G) := d.hMN hn.1
    refine ⟨hN, ?_⟩
    have hMb : convI hVe ⟨n, hN⟩ ∈ autI hVe M := convI_mem_autI hVe hn.1 hN
    have hfix : ∀ z ∈ d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁), convI hVe ⟨n, hN⟩ z = z :=
      (mem_centralizer_map_iff hN).1 (by rw [← hZ₁]; exact hn.2)
    have hodd' : Odd (orderOf (convI hVe ⟨n, hN⟩)) := by
      have h1 : orderOf (convI hVe ⟨n, hN⟩) ∣ orderOf (⟨n, hN⟩ :
          Subgroup.normalizer (V154 T Mc M : Set G)) := orderOf_map_dvd _ _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hodd h1
    exact d.S.odd_mem_cenW₂ hW d.hcard d.hnorm r.x₁_mem.1 r.x₁_two hMb hfix hodd'
  have hYa : ∀ y ∈ Y, ∃ hN : y ∈ Subgroup.normalizer (V154 T Mc M : Set G),
      convI hVe ⟨y, hN⟩ ∈ Subgroup.zpowers d.S.a₂ := by
    intro y hy
    obtain ⟨hN, hC⟩ := key y (hYM hy) (odd_orderOf_of_isPGroup_five_e9 hY5 y hy)
    refine ⟨hN, ?_⟩
    obtain ⟨m, hm⟩ := hY5 ⟨y, hy⟩
    have hym : y ^ 5 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 : convI hVe ⟨y, hN⟩ ^ 5 ^ m = 1 := by
      have h2 : (⟨y, hN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) ^ 5 ^ m = 1 :=
        Subtype.ext (by simpa using hym)
      rw [← map_pow, h2, map_one]
    exact d.S.mem_zpowers_a₂_of_pow_five hW d.hcard hεC hε₂3 hC
      (d.S.pow_five_eq_one_of_pow hW d.hcard hεC hε₂3 hC h1)
  have hYne : ∃ y ∈ Y, ∃ hN : y ∈ Subgroup.normalizer (V154 T Mc M : Set G),
      convI hVe ⟨y, hN⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hcomm : ⁅V₂, Y⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have hyN := d.hMN (hYM hy).1
      have h1 := (convI_eq_one_iff hVe ⟨y, hyN⟩).1 (hcon y hy hyN)
      have hvV : v ∈ V154 T Mc M := by
        rw [hV₂] at hv
        exact d.V₂_le_V hv
      exact ((Subgroup.mem_centralizer_iff.mp h1) v hvV).symm
    rw [hcomm] at hVY
    have hcard : Nat.card V₂ = 16 := by
      rw [hV₂]
      exact d.card_V₂
    have h1 : Nat.card V₂ = 1 := by
      rw [← hVY]
      exact Subgroup.card_bot
    omega
  have hcover : ∀ k : ℤ, ∃ y ∈ Y, ∃ hN : y ∈ Subgroup.normalizer (V154 T Mc M : Set G),
      convI hVe ⟨y, hN⟩ = d.S.a₂ ^ k := by
    obtain ⟨y₀, hy₀, hN₀, hne⟩ := hYne
    obtain ⟨hN₀', hz₀⟩ := hYa y₀ hy₀
    have hord5 : orderOf (convI hVe ⟨y₀, hN₀⟩) = 5 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hz₀
      have hd : orderOf (convI hVe ⟨y₀, hN₀⟩) ∣ 5 := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          d.S.a₂_pow (Or.inr rfl), one_zpow]
      rcases (Nat.dvd_prime Nat.prime_five).1 hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    have hzp : Subgroup.zpowers (convI hVe ⟨y₀, hN₀⟩) = Subgroup.zpowers d.S.a₂ := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz₀) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hord5, d.S.orderOf_a₂_five]
    intro k
    have hmem : d.S.a₂ ^ k ∈ Subgroup.zpowers (convI hVe ⟨y₀, hN₀⟩) := by
      rw [hzp]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hys : y₀ ^ s ∈ Y := Subgroup.zpow_mem _ hy₀ s
    have hysN : y₀ ^ s ∈ Subgroup.normalizer (V154 T Mc M : Set G) := d.hMN (hYM hys).1
    refine ⟨y₀ ^ s, hys, hysN, ?_⟩
    have e : (⟨y₀ ^ s, hysN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
        (⟨y₀, hN₀⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) ^ s := rfl
    rw [e, map_zpow, hs]
  intro n hn hodd
  obtain ⟨hN, hC⟩ := key n hn hodd
  obtain ⟨k, hk⟩ := d.S.exists_zpow_eq hW d.hcard hεC hε₂3 hC
  obtain ⟨y, hyY, hNy, hyk⟩ := hcover k
  refine ⟨y, hyY, ?_⟩
  have hm : y⁻¹ * n ∈ M ⊓ g1_1516 Z₁ := mul_mem (inv_mem (hYM hyY)) hn
  have hmN : y⁻¹ * n ∈ Subgroup.normalizer (V154 T Mc M : Set G) := d.hMN hm.1
  have hcomm : Commute (ε₂ ^ k) (d.S.a₂ ^ k) := (show Commute ε₂ d.S.a₂ from hε₂a).zpow_zpow k k
  have hconv : convI hVe ⟨y⁻¹ * n, hmN⟩ = ε₂ ^ k := by
    have e : (⟨y⁻¹ * n, hmN⟩ : Subgroup.normalizer (V154 T Mc M : Set G)) =
        (⟨y, hNy⟩ : Subgroup.normalizer (V154 T Mc M : Set G))⁻¹ * ⟨n, hN⟩ := rfl
    rw [e, map_mul, map_inv, hyk, hk]
    calc (d.S.a₂ ^ k)⁻¹ * (ε₂ ^ k * d.S.a₂ ^ k) = (d.S.a₂ ^ k)⁻¹ * (d.S.a₂ ^ k * ε₂ ^ k) := by
          rw [hcomm.eq]
      _ = ε₂ ^ k := by group
  have hstab : ε₂ ^ k ∈ SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂) :=
    Subgroup.zpow_mem _ hε₂M k
  have hs : ∀ w, w ∈ d.S.vEMod x₁ x₂ ↔ convI hVe ⟨y⁻¹ * n, hmN⟩ w ∈ d.S.vEMod x₁ x₂ := by
    rw [hconv]
    exact hstab.2
  have hnorm := mem_normalizer_map hmN hs
  have hMc : y⁻¹ * n ∈ Mc := by
    rw [← r.vE] at hnorm
    rw [hC1.2]
    exact hnorm
  exact ⟨hm.2, hMc⟩

end CFSG.Quasithin.E9
