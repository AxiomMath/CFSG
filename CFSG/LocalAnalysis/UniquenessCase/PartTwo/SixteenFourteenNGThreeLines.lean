module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeShift
public import CFSG.LargeExtraspecial.AS35QThXa

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open scoped IsMulCommutative

private theorem s1614_li_conj_conj {G : Type*} [Group G] {t : G} (ht : t * t = 1) (a : G) :
    t * (t * a * t⁻¹) * t⁻¹ = a := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
    _ = a := by rw [ht, htinv, ht, one_mul, mul_one]

private theorem s1614_li_cube {G : Type*} [Group G] {x : G} (h : x ^ 3 = 1) : x * x * x = 1 := by
  rw [show x * x * x = x ^ 3 by rw [pow_succ, pow_succ, pow_one]]
  exact h

private theorem s1614_li_conj_mem_zpowers {G : Type*} [Group G] {u z x : G}
    (h : u * z * u⁻¹ = z) (hx : x ∈ Subgroup.zpowers z) :
    u * x * u⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h]

private theorem s1614_li_mem_zpowers_pow {G : Type*} [Group G] {z x : G} (hz : z ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers z) : ∃ b : ℕ, x = z ^ b := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨(k % 3).toNat, ?_⟩
  have hnonneg : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
  have hk' : z ^ k = z ^ (k % (3 : ℤ)).toNat := by
    rw [zpow_eq_zpow_emod' k (n := 3) hz,
      ← zpow_natCast (n := (k % (3 : ℤ)).toNat), Int.toNat_of_nonneg hnonneg]
    rfl
  rw [← hk]
  exact hk'

private theorem s1614_li_mod_sq {c : ℕ} (hc : ¬ 3 ∣ c) : c * c % 3 = 1 := by
  have hc0 : c % 3 ≠ 0 := fun h => hc (Nat.dvd_of_mod_eq_zero h)
  have hlt : c % 3 < 3 := Nat.mod_lt c (by norm_num)
  have hcases : c % 3 = 1 ∨ c % 3 = 2 := by omega
  have hm := Nat.mul_mod c c 3
  rcases hcases with h | h
  · rw [h] at hm
    norm_num at hm
    exact hm
  · rw [h] at hm
    norm_num at hm
    exact hm

private theorem s1614_li_comm_pow {Q : Type*} [CommGroup Q] {a b : Q}
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) {c : ℕ} (hc : ¬ 3 ∣ c) :
    (a * b ^ c) ^ c = b * a ^ c := by
  have hc2 : c * c % 3 = 1 := s1614_li_mod_sq hc
  have hbc : b ^ (c * c) = b := by
    rw [pow_eq_pow_mod (c * c) hb3, hc2, pow_one]
  rw [mul_pow, ← pow_mul, hbc, mul_comm]

private theorem s1614_li_noncomm {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hL : IsPOnePlusTwo 3 ↥L) :
    ∃ a b : ↥L, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hcard : Nat.card ↥L = 27 := by rw [hL.2.1]; norm_num
  have hZ : Nat.card (Subgroup.center ↥L) = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥L
  by_contra h
  have htop : Subgroup.center ↥L = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    by_contra hyx
    exact h ⟨y, x, hyx⟩
  have : Nat.card (Subgroup.center ↥L) = 27 := by rw [htop, Subgroup.card_top, hcard]
  omega

private theorem s1614_li_center_eq_zpowers {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hL : IsPOnePlusTwo 3 ↥L) {ℓ : ↥L}
    (hℓ : ℓ ∈ Subgroup.center ↥L) (hℓ1 : ℓ ≠ 1) :
    Subgroup.zpowers ℓ = Subgroup.center ↥L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hZ : Nat.card (Subgroup.center ↥L) = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥L
  have h3 : ℓ ^ 3 = 1 := hL.2.2 ℓ
  have hle : Subgroup.zpowers ℓ ≤ Subgroup.center ↥L := Subgroup.zpowers_le.mpr hℓ
  have hcard : Nat.card ↥(Subgroup.zpowers ℓ) = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf ℓ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hℓ1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  simp [hcard, hZ]

private theorem s1614_li_conj_center {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ x : W, x * x = 1) (hcard : Nat.card W = 2 ^ 6) {L M : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut W))) {ℓ : ↥L}
    (hℓ : ℓ ∈ Subgroup.center ↥L) (hℓ1 : ℓ ≠ 1) {t : MulAut W} (ht : t ∈ M)
    (ht2 : t * t = 1) :
    ∃ e : ℕ, ¬ 3 ∣ e ∧ t * (ℓ : MulAut W) * t⁻¹ = (ℓ : MulAut W) ^ e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥L
  have hℓ3 : (ℓ : MulAut W) ^ 3 = 1 := by
    have h := congrArg (fun x : ↥L => (x : MulAut W)) (hL.2.2 ℓ)
    simpa [Subgroup.coe_pow] using h
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := hMN ht
  have htNiff : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L := Subgroup.mem_normalizer_iff.mp htN
  let z : MulAut W := t * (ℓ : MulAut W) * t⁻¹
  have hzL : z ∈ L := (htNiff (ℓ : MulAut W)).mp ℓ.2
  have hzcent : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : MulAut W) * z = z * (y : MulAut W)
    have hy'L : t * (y : MulAut W) * t⁻¹ ∈ L := (htNiff (y : MulAut W)).mp y.2
    have hcomm := Subgroup.mem_center_iff.1 hℓ ⟨t * (y : MulAut W) * t⁻¹, hy'L⟩
    have hcomm' : (MulAut.conj t) (y : MulAut W) * (ℓ : MulAut W) =
        (ℓ : MulAut W) * (MulAut.conj t) (y : MulAut W) := by
      have h := congrArg (fun w : ↥L => (w : MulAut W)) hcomm
      simpa [MulAut.conj_apply] using h
    have hz_eq : z = (MulAut.conj t) (ℓ : MulAut W) := by simp [z, MulAut.conj_apply]
    have hconj_y : (MulAut.conj t) ((MulAut.conj t) (y : MulAut W)) = (y : MulAut W) :=
      s1614_li_conj_conj ht2 (y : MulAut W)
    calc (y : MulAut W) * z
        = ((MulAut.conj t) ((MulAut.conj t) (y : MulAut W))) *
            ((MulAut.conj t) (ℓ : MulAut W)) := by rw [hconj_y, hz_eq]
      _ = (MulAut.conj t) (((MulAut.conj t) (y : MulAut W)) * (ℓ : MulAut W)) := by
            rw [map_mul]
      _ = (MulAut.conj t) ((ℓ : MulAut W) * ((MulAut.conj t) (y : MulAut W))) := by
            rw [hcomm']
      _ = (MulAut.conj t) (ℓ : MulAut W) *
            (MulAut.conj t) ((MulAut.conj t) (y : MulAut W)) := by rw [map_mul]
      _ = z * (y : MulAut W) := by rw [← hz_eq, hconj_y]
  have hz1 : z ≠ 1 := by
    intro h
    apply hℓ1
    have h1 := s1614_li_conj_conj ht2 (ℓ : MulAut W)
    rw [← show z = t * (ℓ : MulAut W) * t⁻¹ from rfl, h, mul_one, mul_inv_cancel] at h1
    exact Subtype.ext h1.symm
  have hmem : (⟨⟨z, hzL⟩, hzcent⟩ : Subgroup.center ↥L) ∈
      Submonoid.powers (⟨ℓ, hℓ⟩ : Subgroup.center ↥L) :=
    mem_powers_of_prime_card (G := Subgroup.center ↥L) hZcard
      (g := (⟨ℓ, hℓ⟩ : Subgroup.center ↥L)) (g' := (⟨⟨z, hzL⟩, hzcent⟩ : Subgroup.center ↥L))
      (by intro h; exact hℓ1 (by simpa using congrArg Subtype.val h))
  obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff _ _).1 hmem
  have he' : (ℓ : MulAut W) ^ e = z := by
    have h := congrArg (fun w : Subgroup.center ↥L => ((w : ↥L) : MulAut W)) he
    simpa [Subgroup.coe_pow] using h
  refine ⟨e, ?_, ?_⟩
  · intro h3
    apply hz1
    rw [← he']
    obtain ⟨m, rfl⟩ := h3
    rw [pow_mul, hℓ3, one_pow]
  · rw [he']

theorem s1614_lines {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    (hcard : Nat.card W = 2 ^ 6) {L M : Subgroup (MulAut W)} (hL : IsPOnePlusTwo 3 ↥L)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut W))) {ℓ : ↥L}
    (hℓ : ℓ ∈ Subgroup.center ↥L) (hℓ1 : ℓ ≠ 1)
    (hA : ∃ A : Subgroup (MulAut W), A ≤ M ∧ IsElemAbelian 3 A ∧ Nat.card ↥A = 27)
    {t : MulAut W} (ht : t ∈ M) (ht2 : t * t = 1) :
    (∃ e : ℕ, ¬ 3 ∣ e ∧ t * (ℓ : MulAut W) * t⁻¹ = (ℓ : MulAut W) ^ e) ∧
      ∃ A : Subgroup (MulAut W), A ≤ M ∧ IsElemAbelian 3 A ∧ Nat.card ↥A = 27 ∧
        (ℓ : MulAut W) ∈ A ∧ ∃ g : MulAut W, g ∈ A ∧ g ∈ L ∧
          g ∉ Subgroup.zpowers (ℓ : MulAut W) ∧
          ∃ a b : ℕ, ¬ 3 ∣ a ∧ t * g * t⁻¹ = g ^ a * (ℓ : MulAut W) ^ b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hExtra : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hLcard : Nat.card ↥L = 27 := by rw [hL.2.1]; norm_num
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥L
  have hZeq : Subgroup.zpowers ℓ = Subgroup.center ↥L := s1614_li_center_eq_zpowers hL hℓ hℓ1
  have hncL : ∃ a b : ↥L, a * b ≠ b * a := s1614_li_noncomm hL
  obtain ⟨e₀, he₀, hconj_ℓ⟩ := s1614_li_conj_center hW hcard hL hMN hℓ hℓ1 ht ht2
  refine ⟨⟨e₀, he₀, hconj_ℓ⟩, ?_⟩
  obtain ⟨A₀, hA₀M, hA₀ab, hA₀27⟩ := hA
  obtain ⟨hPLcard, hZmemA₀⟩ := s1614_inf_card hW hcard hL hMN hA₀M hA₀ab hA₀27
  have hℓA₀ : (ℓ : MulAut W) ∈ A₀ := hZmemA₀ ℓ hℓ
  have hℓ3 : (ℓ : MulAut W) ^ 3 = 1 := by
    have h := congrArg (fun x : ↥L => (x : MulAut W)) (hL.2.2 ℓ)
    simpa [Subgroup.coe_pow] using h
  have hℓne : (ℓ : MulAut W) ≠ 1 := fun h => hℓ1 (Subtype.ext h)
  have hℓord : orderOf (ℓ : MulAut W) = 3 := by
    have hdvd : orderOf (ℓ : MulAut W) ∣ 3 := orderOf_dvd_of_pow_eq_one hℓ3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hℓne
    · exact h
  set P : Subgroup (MulAut W) := A₀ ⊓ L with hPdef
  have hPcard : Nat.card ↥P = 9 := hPLcard
  have hℓP : (ℓ : MulAut W) ∈ P := ⟨hℓA₀, ℓ.2⟩
  have hPab : IsElemAbelian 3 P :=
    ⟨⟨⟨fun x y => Subtype.ext (show x.1 * y.1 = y.1 * x.1 from
        congrArg Subtype.val (hA₀ab.1.is_comm.comm ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩))⟩⟩,
      fun x hx => hA₀ab.2 x hx.1⟩
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hPab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  by_cases hPnorm : ∀ p ∈ P, t * p * t⁻¹ ∈ P
  ·
    have hnotle : ¬ P ≤ Subgroup.zpowers (ℓ : MulAut W) := by
      intro hle
      have h1 : Nat.card ↥P ≤ Nat.card ↥(Subgroup.zpowers (ℓ : MulAut W)) :=
        Subgroup.card_le_of_le hle
      rw [hPcard, Nat.card_zpowers, hℓord] at h1
      omega
    obtain ⟨g₀, hg₀P, hg₀notz⟩ : ∃ g₀, g₀ ∈ P ∧ g₀ ∉ Subgroup.zpowers (ℓ : MulAut W) := by
      by_contra h
      exact hnotle (fun x hx => by
        by_contra hxz
        exact h ⟨x, hx, hxz⟩)
    have hg₀A₀ : g₀ ∈ A₀ := hg₀P.1
    have hg₀L : g₀ ∈ L := hg₀P.2
    have hg₀3 : g₀ ^ 3 = 1 := hA₀ab.2 g₀ hg₀A₀
    have hg₀P' : t * g₀ * t⁻¹ ∈ P := hPnorm g₀ hg₀P
    let c : MulAut W := g₀ * (t * g₀ * t⁻¹)
    have hcP : c ∈ P := P.mul_mem hg₀P hg₀P'
    have hc_eq : t * c * t⁻¹ = c := by
      have h1 : t * (g₀ * (t * g₀ * t⁻¹)) * t⁻¹ =
          (t * g₀ * t⁻¹) * (t * (t * g₀ * t⁻¹) * t⁻¹) := by group
      have h2 : t * (t * g₀ * t⁻¹) * t⁻¹ = g₀ := by
        calc t * (t * g₀ * t⁻¹) * t⁻¹ = (t * t) * g₀ * (t⁻¹ * t⁻¹) := by group
          _ = g₀ := by rw [ht2, inv_eq_of_mul_eq_one_right ht2, ht2, one_mul, mul_one]
      rw [show c = g₀ * (t * g₀ * t⁻¹) from rfl, h1, h2]
      exact (hPcomm g₀ hg₀P (t * g₀ * t⁻¹) hg₀P').symm
    by_cases hcz : c ∈ Subgroup.zpowers (ℓ : MulAut W)
    · obtain ⟨b, hb⟩ := s1614_li_mem_zpowers_pow hℓ3 hcz
      have hg₀inv : g₀⁻¹ = g₀ ^ 2 := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← pow_succ', hg₀3]
      have htg : t * g₀ * t⁻¹ = g₀ ^ 2 * (ℓ : MulAut W) ^ b := by
        calc t * g₀ * t⁻¹ = g₀⁻¹ * (g₀ * (t * g₀ * t⁻¹)) := by group
          _ = g₀⁻¹ * (ℓ : MulAut W) ^ b := by rw [show g₀ * (t * g₀ * t⁻¹) = c from rfl, hb]
          _ = g₀ ^ 2 * (ℓ : MulAut W) ^ b := by rw [hg₀inv]
      refine ⟨A₀, hA₀M, hA₀ab, hA₀27, hℓA₀, g₀, hg₀A₀, hg₀L, hg₀notz, 2, b,
        by norm_num, ?_⟩
      exact htg
    · refine ⟨A₀, hA₀M, hA₀ab, hA₀27, hℓA₀, c, hcP.1, hcP.2, hcz, 1, 0,
        by norm_num, ?_⟩
      rw [pow_one, pow_zero, mul_one]
      exact hc_eq
  ·
    obtain ⟨x₀, hx₀imp⟩ := not_forall.mp hPnorm
    obtain ⟨hx₀P, hx₀not⟩ := not_imp.mp hx₀imp
    have hx₀A₀ : x₀ ∈ A₀ := hx₀P.1
    have hx₀L : x₀ ∈ L := hx₀P.2
    let x₁ : MulAut W := t * x₀ * t⁻¹
    have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := hMN ht
    have htNiff : ∀ h, h ∈ L ↔ t * h * t⁻¹ ∈ L := Subgroup.mem_normalizer_iff.mp htN
    have hx₁L : x₁ ∈ L := (htNiff x₀).mp hx₀L
    have hx₀Z : (⟨x₀, hx₀L⟩ : ↥L) ∉ Subgroup.center ↥L := by
      intro hmem
      apply hx₀not
      have hzp : (⟨x₀, hx₀L⟩ : ↥L) ∈ Subgroup.zpowers ℓ := by rw [hZeq]; exact hmem
      obtain ⟨b, hb⟩ := s1614_li_mem_zpowers_pow (hL.2.2 ℓ) hzp
      have hx₀pow : x₀ = (ℓ : MulAut W) ^ b := by
        have h := congrArg (fun w : ↥L => (w : MulAut W)) hb
        simpa [Subgroup.coe_pow] using h
      have hconj_pow : t * (ℓ : MulAut W) ^ b * t⁻¹ = (ℓ : MulAut W) ^ (e₀ * b) := by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hconj_ℓ, ← pow_mul]
      have hmemP : x₁ ∈ P := by
        rw [show x₁ = (ℓ : MulAut W) ^ (e₀ * b) by
              rw [show x₁ = t * x₀ * t⁻¹ from rfl, hx₀pow, hconj_pow]]
        exact Subgroup.zpowers_le.mpr hℓP (Subgroup.npow_mem_zpowers (ℓ : MulAut W) (e₀ * b))
      exact hmemP
    have hx₀notz : x₀ ∉ Subgroup.zpowers (ℓ : MulAut W) := by
      intro hxz
      apply hx₀Z
      rw [← hZeq]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [Subgroup.coe_zpow] using hk)⟩
    let C : Subgroup (MulAut W) := Subgroup.centralizer ({x₀} : Set (MulAut W)) ⊓ L
    have hPC : P ≤ C := by
      intro p hp
      refine ⟨?_, hp.2⟩
      show p ∈ Subgroup.centralizer ({x₀} : Set (MulAut W))
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hPcomm p hp x₀ hx₀P
    have hCeqP : C = P := by
      have hdiv : Nat.card ↥C ∣ 27 := by
        have h := Subgroup.card_dvd_of_le (show C ≤ L from inf_le_right)
        rwa [hLcard] at h
      have h9dvd : 9 ∣ Nat.card ↥C := by
        have h := Subgroup.card_dvd_of_le hPC
        rwa [hPcard] at h
      have hge9 : 9 ≤ Nat.card ↥C := Nat.le_of_dvd (Nat.card_pos) h9dvd
      have hmem : Nat.card ↥C ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdiv, by norm_num⟩
      rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h
      · omega
      · omega
      · exact (Subgroup.eq_of_le_of_card_ge hPC (by simp [h, hPcard])).symm
      · exfalso
        have hCL : C = L := Subgroup.eq_of_le_of_card_ge inf_le_right (by simp [h, hLcard])
        apply hx₀Z
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : (g : MulAut W) ∈ C := by rw [hCL]; exact g.2
        have hgc : (g : MulAut W) ∈ Subgroup.centralizer ({x₀} : Set (MulAut W)) := hg.1
        rw [Subgroup.mem_centralizer_singleton_iff] at hgc
        exact Subtype.ext hgc
    have hx₀x₁ : x₀ * x₁ ≠ x₁ * x₀ := by
      intro hcomm
      have hx₁C : x₁ ∈ C := by
        refine ⟨?_, hx₁L⟩
        show x₁ ∈ Subgroup.centralizer ({x₀} : Set (MulAut W))
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcomm.symm
      rw [hCeqP] at hx₁C
      exact hx₀not hx₁C
    have hnotleA₀ : ¬ A₀ ≤ L := by
      intro hle
      have hinf : A₀ ⊓ L = A₀ := le_antisymm inf_le_left (le_inf le_rfl hle)
      have hcardeq : Nat.card ↥(A₀ ⊓ L) = Nat.card ↥A₀ :=
        congrArg (fun H : Subgroup (MulAut W) => Nat.card ↥H) hinf
      rw [hPLcard, hA₀27] at hcardeq
      omega
    obtain ⟨u₀, hu₀A₀, hu₀notL⟩ : ∃ u₀, u₀ ∈ A₀ ∧ u₀ ∉ L := by
      by_contra h
      exact hnotleA₀ (fun x hx => by
        by_contra hx'
        exact h ⟨x, hx, hx'⟩)
    let u₁ : MulAut W := t * u₀ * t⁻¹
    have hu₁M : u₁ ∈ M := M.mul_mem (M.mul_mem ht (hA₀M hu₀A₀)) (M.inv_mem ht)
    have hu₁L : ∀ y ∈ L, u₁ * y * u₁⁻¹ ∈ L :=
      fun y hy => (Subgroup.mem_normalizer_iff.mp (hMN hu₁M) y).mp hy
    have hu₀3 : u₀ ^ 3 = 1 := hA₀ab.2 u₀ hu₀A₀
    have hu₁3 : u₁ * u₁ * u₁ = 1 := by
      apply s1614_li_cube
      have h := map_pow (MulAut.conj t) u₀ 3
      rw [hu₀3, map_one] at h
      have heq : (MulAut.conj t) u₀ = u₁ := by simp [u₁, MulAut.conj_apply]
      rw [heq] at h
      exact h.symm
    have hu₁notL : u₁ ∉ L := by
      intro h
      apply hu₀notL
      have hc : t * u₁ * t⁻¹ = u₀ := by
        rw [show u₁ = t * u₀ * t⁻¹ from rfl]
        exact s1614_li_conj_conj ht2 u₀
      have hmem : t * u₁ * t⁻¹ ∈ L := (htNiff u₁).mp h
      rwa [hc] at hmem
    have hu₁x₁ : u₁ * x₁ = x₁ * u₁ := by
      have hux : u₀ * x₀ = x₀ * u₀ :=
        congrArg Subtype.val (hA₀ab.1.is_comm.comm (⟨u₀, hu₀A₀⟩ : ↥A₀)
          (⟨x₀, hx₀A₀⟩ : ↥A₀))
      rw [show u₁ = (MulAut.conj t) u₀ by simp [u₁, MulAut.conj_apply],
          show x₁ = (MulAut.conj t) x₀ by simp [x₁, MulAut.conj_apply]]
      rw [← map_mul, ← map_mul, hux]
    have hu₁ℓ : u₁ * (ℓ : MulAut W) = (ℓ : MulAut W) * u₁ := by
      have hconj_u₀ℓ : (MulAut.conj u₀) (ℓ : MulAut W) = (ℓ : MulAut W) := by
        rw [MulAut.conj_apply]
        have hcomm : u₀ * (ℓ : MulAut W) = (ℓ : MulAut W) * u₀ :=
          congrArg Subtype.val (hA₀ab.1.is_comm.comm (⟨u₀, hu₀A₀⟩ : ↥A₀)
            (⟨(ℓ : MulAut W), hℓA₀⟩ : ↥A₀))
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have hcu : MulAut.conj u₁ = MulAut.conj t * MulAut.conj u₀ * MulAut.conj t⁻¹ := by
        rw [show u₁ = t * u₀ * t⁻¹ from rfl,
            show t * u₀ * t⁻¹ = t * (u₀ * t⁻¹) by group, map_mul, map_mul]
        group
      have hconj_u₁ : (MulAut.conj u₁) (ℓ : MulAut W) = (ℓ : MulAut W) := by
        rw [hcu, MulAut.mul_apply, MulAut.mul_apply]
        rw [show (MulAut.conj t⁻¹) (ℓ : MulAut W) = (ℓ : MulAut W) ^ e₀ by
              rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht2, MulAut.conj_apply]
              exact hconj_ℓ]
        rw [show (MulAut.conj u₀) ((ℓ : MulAut W) ^ e₀) = (ℓ : MulAut W) ^ e₀ by
              rw [map_pow, hconj_u₀ℓ]]
        rw [map_pow, MulAut.conj_apply, hconj_ℓ, ← pow_mul,
            pow_eq_pow_mod (e₀ * e₀) hℓ3, s1614_li_mod_sq he₀, pow_one]
      have h1 : u₁ * (ℓ : MulAut W) * u₁⁻¹ = (ℓ : MulAut W) := by
        rw [show u₁ * (ℓ : MulAut W) * u₁⁻¹ = (MulAut.conj u₁) (ℓ : MulAut W) from
              (MulAut.conj_apply u₁ (ℓ : MulAut W)).symm, hconj_u₁]
      calc u₁ * (ℓ : MulAut W) = (u₁ * (ℓ : MulAut W) * u₁⁻¹) * u₁ := by group
        _ = (ℓ : MulAut W) * u₁ := by rw [h1]
    obtain ⟨c, e, hc3, hshift⟩ := s1614_shift hW hcard hL hℓ hℓ1
      (x₀ := ⟨x₀, hx₀L⟩) (x₁ := ⟨x₁, hx₁L⟩) (u := u₁)
      (fun h => hx₀x₁ (congrArg Subtype.val h)) hu₁3 hu₁L hu₁notL hu₁x₁ hu₁ℓ
    let A : Subgroup (MulAut W) := A₀.map (MulAut.conj u₁).toMonoidHom
    let g : MulAut W := u₁ * x₀ * u₁⁻¹
    have hconj_apply : ∀ a : MulAut W, (MulAut.conj u₁).toMonoidHom a = u₁ * a * u₁⁻¹ :=
      fun a => MulAut.conj_apply u₁ a
    have hAM : A ≤ M := by
      intro x hx
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
      rw [← hax, hconj_apply]
      exact M.mul_mem (M.mul_mem hu₁M (hA₀M ha)) (M.inv_mem hu₁M)
    have hAcard : Nat.card ↥A = 27 := by
      have h := Subgroup.card_map_of_injective (K := A₀) (f := (MulAut.conj u₁).toMonoidHom)
        (MulAut.conj u₁).injective
      rw [h, hA₀27]
    have hAab : IsElemAbelian 3 A := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
      · apply Subtype.ext
        show x.1 * y.1 = y.1 * x.1
        obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
        obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
        have hax' : x.1 = u₁ * a * u₁⁻¹ := by rw [← hax, hconj_apply]
        have hby' : y.1 = u₁ * b * u₁⁻¹ := by rw [← hby, hconj_apply]
        have hab : a * b = b * a :=
          congrArg Subtype.val (hA₀ab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        rw [hax', hby',
            show (u₁ * a * u₁⁻¹) * (u₁ * b * u₁⁻¹) = u₁ * (a * b) * u₁⁻¹ by group,
            show (u₁ * b * u₁⁻¹) * (u₁ * a * u₁⁻¹) = u₁ * (b * a) * u₁⁻¹ by group,
            hab]
      · intro x hx
        obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
        have hax' : x = u₁ * a * u₁⁻¹ := by rw [← hax, hconj_apply]
        have h3 : (u₁ * a * u₁⁻¹) ^ 3 = 1 := by
          rw [show u₁ * a * u₁⁻¹ = (MulAut.conj u₁) a from (MulAut.conj_apply u₁ a).symm,
              ← map_pow, hA₀ab.2 a ha, map_one]
        rw [hax', h3]
    have hℓA : (ℓ : MulAut W) ∈ A := by
      refine Subgroup.mem_map.mpr ⟨(ℓ : MulAut W), hℓA₀, ?_⟩
      rw [hconj_apply, hu₁ℓ, mul_assoc, mul_inv_cancel, mul_one]
    have hgA : g ∈ A := by
      refine Subgroup.mem_map.mpr ⟨x₀, hx₀A₀, ?_⟩
      rw [hconj_apply]
    have hgL : g ∈ L := by
      have := hu₁L x₀ hx₀L
      rwa [show u₁ * x₀ * u₁⁻¹ = g from rfl] at this
    have hgnotz : g ∉ Subgroup.zpowers (ℓ : MulAut W) := by
      intro hgz
      apply hx₀notz
      have hx₀eq : x₀ = u₁⁻¹ * g * u₁ := by
        rw [show g = u₁ * x₀ * u₁⁻¹ from rfl]; group
      have hconjℓ : u₁⁻¹ * (ℓ : MulAut W) * u₁ = (ℓ : MulAut W) := by
        rw [show u₁⁻¹ * (ℓ : MulAut W) * u₁ = u₁⁻¹ * ((ℓ : MulAut W) * u₁) by group,
            ← hu₁ℓ, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hx₀eq]
      exact s1614_li_conj_mem_zpowers hconjℓ hgz
    have hg_eq : g = x₀ * x₁ ^ c * (ℓ : MulAut W) ^ e := by
      rw [show g = u₁ * x₀ * u₁⁻¹ from rfl, hshift]
    have hx₁eq : x₁ = (MulAut.conj t) x₀ := by simp [x₁, MulAut.conj_apply]
    have hconj_x₁ : (MulAut.conj t) x₁ = x₀ := by
      rw [hx₁eq]
      calc (MulAut.conj t) ((MulAut.conj t) x₀)
          = ((MulAut.conj t) * (MulAut.conj t)) x₀ := rfl
        _ = (MulAut.conj (t * t)) x₀ := by rw [← map_mul]
        _ = x₀ := by rw [ht2, map_one]; rfl
    have hpowa : ∀ {a : MulAut W} (n : ℕ), t * a ^ n * t⁻¹ = (t * a * t⁻¹) ^ n := by
      intro a n
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
    have hconj_g : t * g * t⁻¹ = x₁ * x₀ ^ c * (ℓ : MulAut W) ^ (e₀ * e) := by
      rw [hg_eq]
      have h1 : t * (x₀ * x₁ ^ c * (ℓ : MulAut W) ^ e) * t⁻¹ =
          (t * x₀ * t⁻¹) * (t * x₁ * t⁻¹) ^ c * (t * (ℓ : MulAut W) * t⁻¹) ^ e := by
        rw [show t * (x₀ * x₁ ^ c * (ℓ : MulAut W) ^ e) * t⁻¹ =
              (t * x₀ * t⁻¹) * (t * x₁ ^ c * t⁻¹) * (t * (ℓ : MulAut W) ^ e * t⁻¹) by group]
        rw [hpowa c, hpowa e]
      rw [h1,
        show (t * x₀ * t⁻¹) = x₁ from rfl,
        show (t * x₁ * t⁻¹) = x₀ from hconj_x₁,
        show (t * (ℓ : MulAut W) * t⁻¹) = (ℓ : MulAut W) ^ e₀ from hconj_ℓ,
        ← pow_mul]
    let Z : Subgroup ↥L := Subgroup.center ↥L
    let Q := ↥L ⧸ Z
    haveI : IsMulCommutative Q :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := Q)
        (by
          have h := CFSG.LargeExtraspecial.AS35QTh.card_quotient_center hLcard hncL
          simpa [Q, Z] using h)
    let x₀L : ↥L := ⟨x₀, hx₀L⟩
    let x₁L : ↥L := ⟨x₁, hx₁L⟩
    let gL : ↥L := ⟨g, hgL⟩
    let tLg : ↥L := ⟨t * g * t⁻¹, (htNiff g).mp hgL⟩
    have hℓQ : (ℓ : Q) = 1 := (QuotientGroup.eq_one_iff ℓ).mpr hℓ
    have hx₀L3 : x₀L ^ 3 = 1 := by
      apply Subtype.ext
      simpa [x₀L, Subgroup.coe_pow] using hA₀ab.2 x₀ hx₀A₀
    have hx₁L3 : x₁L ^ 3 = 1 := by
      apply Subtype.ext
      have h3 : x₁ ^ 3 = 1 := by
        have h := map_pow (MulAut.conj t) x₀ 3
        rw [hA₀ab.2 x₀ hx₀A₀, map_one] at h
        rw [hx₁eq]
        exact h.symm
      simpa [x₁L, Subgroup.coe_pow] using h3
    have hx₀Q3 : (x₀L : Q) ^ 3 = 1 := by
      have h := congrArg (fun y : ↥L => (y : Q)) hx₀L3
      simpa [QuotientGroup.mk_pow] using h
    have hx₁Q3 : (x₁L : Q) ^ 3 = 1 := by
      have h := congrArg (fun y : ↥L => (y : Q)) hx₁L3
      simpa [QuotientGroup.mk_pow] using h
    have hga : (gL : Q) = (x₀L : Q) * (x₁L : Q) ^ c := by
      have hval : (gL : ↥L) = x₀L * x₁L ^ c * ℓ ^ e := by
        apply Subtype.ext
        show g = x₀ * x₁ ^ c * (ℓ : MulAut W) ^ e
        exact hg_eq
      rw [hval]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow]
      rw [hℓQ, one_pow, mul_one]
    have hgt : (tLg : Q) = (x₁L : Q) * (x₀L : Q) ^ c := by
      have hval : (tLg : ↥L) = x₁L * x₀L ^ c * ℓ ^ (e₀ * e) := by
        apply Subtype.ext
        show t * g * t⁻¹ = x₁ * x₀ ^ c * (ℓ : MulAut W) ^ (e₀ * e)
        exact hconj_g
      rw [hval]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow]
      rw [hℓQ, one_pow, mul_one]
    have hgtc : (tLg : Q) = (gL : Q) ^ c := by
      rw [hga, hgt]
      exact (s1614_li_comm_pow hx₀Q3 hx₁Q3 hc3).symm
    have hone : ((tLg * (gL ^ c)⁻¹ : ↥L) : Q) = 1 := by
      have h1 : ((tLg * (gL ^ c)⁻¹ : ↥L) : Q) = (tLg : Q) * ((gL : Q) ^ c)⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
      rw [h1, hgtc, mul_inv_cancel]
    have hZmem : tLg * (gL ^ c)⁻¹ ∈ Subgroup.zpowers ℓ := by
      rw [hZeq]
      exact (QuotientGroup.eq_one_iff (tLg * (gL ^ c)⁻¹)).mp hone
    obtain ⟨b, hb⟩ := s1614_li_mem_zpowers_pow (hL.2.2 ℓ) hZmem
    have htLgeq : tLg = gL ^ c * ℓ ^ b := by
      have h1 : tLg = ℓ ^ b * gL ^ c := by
        rw [← hb]
        group
      rw [h1]
      have hcomm_c : Commute (gL ^ c) (ℓ : ↥L) := Subgroup.mem_center_iff.1 hℓ (gL ^ c)
      exact (hcomm_c.pow_right b).symm
    have hfinal : t * g * t⁻¹ = g ^ c * (ℓ : MulAut W) ^ b := by
      have h := congrArg (fun w : ↥L => (w : MulAut W)) htLgeq
      simpa [tLg, gL, Subgroup.coe_mul, Subgroup.coe_pow] using h
    exact ⟨A, hAM, hAab, hAcard, hℓA, g, hgA, hgL, hgnotz, c, b, hc3, hfinal⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
