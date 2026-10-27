module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

variable {G : Type} [Group G] {Bs : Subgroup G} [Finite ↥Bs] {p : ℕ}

private def invMulAutHom {H : Type*} [Group H] (h : IsMulCommutative H) (r : MulAut H) :
    H →* H where
  toFun b := b⁻¹ * r b
  map_one' := by simp
  map_mul' a b := by
    have hb : b⁻¹ * (a⁻¹ * r a) = (a⁻¹ * r a) * b⁻¹ :=
      h.is_comm.comm (b⁻¹) (a⁻¹ * r a)
    calc (a * b)⁻¹ * r (a * b)
        = (b⁻¹ * a⁻¹) * (r a * r b) := by rw [map_mul, mul_inv_rev]
      _ = b⁻¹ * (a⁻¹ * (r a * r b)) := by rw [mul_assoc]
      _ = b⁻¹ * ((a⁻¹ * r a) * r b) := by
            rw [← mul_assoc a⁻¹ (r a) (r b)]
      _ = (b⁻¹ * (a⁻¹ * r a)) * r b :=
            (mul_assoc b⁻¹ (a⁻¹ * r a) (r b)).symm
      _ = ((a⁻¹ * r a) * b⁻¹) * r b := by rw [hb]
      _ = (a⁻¹ * r a) * (b⁻¹ * r b) := by
            rw [mul_assoc (a⁻¹ * r a) b⁻¹ (r b)]

private theorem ker_invMulAutHom {H : Type*} [Group H] (h : IsMulCommutative H)
    (r : MulAut H) :
    Nat.card (invMulAutHom h r).ker = Nat.card {b : H // r b = b} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
  change b⁻¹ * r b = 1 ↔ r b = b
  rw [inv_mul_eq_one]
  exact eq_comm

private theorem apply_eq_inv_of_mem_zpowers {H : Type*} [Group H] {s : MulAut H} {g : H}
    (hs : s g = g⁻¹) {x : H} (hx : x ∈ Subgroup.zpowers g) : s x = x⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← hk, map_zpow, hs, inv_zpow]

private theorem mem_zpowers_of_inv_mul_inv_mem {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {x g : H} (hxp : x ^ p = 1)
    (h : x⁻¹ * x⁻¹ ∈ Subgroup.zpowers g) : x ∈ Subgroup.zpowers g := by
  have hp : p.Prime := Fact.out
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have ha1 : x⁻¹ * x⁻¹ ≠ 1 := by
    intro ha
    apply hx1
    have hxeq : x = x⁻¹ := inv_mul_eq_one.mp ha
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two, hxeq]
      exact ha
    have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
    have hgg : x ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨hx2, hxp⟩
    rw [hcop.gcd_eq_one, pow_one] at hgg
    exact hgg
  have hamem : x⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  have haord : orderOf (x⁻¹ * x⁻¹) = p := by
    have hdvd : orderOf (x⁻¹ * x⁻¹) ∣ p := hxord ▸ orderOf_dvd_of_mem_zpowers hamem
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact h1
  have hzeq : Subgroup.zpowers (x⁻¹ * x⁻¹) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hamem)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hxord, haord])
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers g := by
    rw [← hzeq]
    exact Subgroup.zpowers_le.mpr h
  exact hle (Subgroup.mem_zpowers x)

theorem inv_mul_apply_mem_zpowers_of_isReflection [Fact p.Prime] (hp : p ≠ 2)
    (hBs : IsElemAbelian p Bs) {r : MulAut ↥Bs} (hr : GGIsReflection p r) {g : ↥Bs}
    (hg1 : g ≠ 1) (hg : r g = g⁻¹) (b : ↥Bs) : b⁻¹ * r b ∈ Subgroup.zpowers g := by
  have hpow : ∀ x : ↥Bs, x ^ p = 1 := fun x => Subtype.ext (by
    simpa using hBs.2 (x : G) x.2)
  let δ : ↥Bs →* ↥Bs := invMulAutHom hBs.1 r
  have hδg : δ g = g⁻¹ * g⁻¹ := by
    change g⁻¹ * r g = g⁻¹ * g⁻¹
    rw [hg]
  have hδg_ne : δ g ≠ 1 := by
    intro h
    rw [hδg] at h
    have hginv : g = g⁻¹ := inv_mul_eq_one.mp h
    have hg2 : g ^ 2 = 1 := by
      rw [pow_two, hginv]
      exact h
    have hcop : Nat.Coprime 2 p :=
      Nat.coprime_two_left.mpr ((Fact.out : p.Prime).odd_of_ne_two hp)
    have hgg : g ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨hg2, hpow g⟩
    rw [hcop.gcd_eq_one, pow_one] at hgg
    exact hg1 hgg
  have hδgp : (δ g) ^ p = 1 := by
    rw [← map_pow, hpow, map_one]
  have hord : orderOf (δ g) = p := orderOf_eq_prime hδgp hδg_ne
  have hcard_zp : Nat.card ↥(Subgroup.zpowers (δ g)) = p := by
    rw [Nat.card_zpowers]
    exact hord
  have hker : Nat.card δ.ker = Nat.card {b : ↥Bs // r b = b} := ker_invMulAutHom hBs.1 r
  have hrange : Nat.card δ.range = p := by
    have hmul := Subgroup.card_ker_mul_card_range δ
    rw [hker] at hmul
    have hpos : 0 < Nat.card δ.ker := Nat.card_pos
    rw [hker] at hpos
    exact Nat.eq_of_mul_eq_mul_left hpos (hmul.trans hr.2.symm)
  have hle : Subgroup.zpowers (δ g) ≤ δ.range := Subgroup.zpowers_le.mpr ⟨g, rfl⟩
  have heq : Subgroup.zpowers (δ g) = δ.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hcard_zp])
  have hmem : δ b ∈ Subgroup.zpowers g := by
    have hb : δ b ∈ Subgroup.zpowers (δ g) :=
      heq.symm ▸ (⟨b, rfl⟩ : δ b ∈ δ.range)
    have hzle : Subgroup.zpowers (δ g) ≤ Subgroup.zpowers g := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [hδg]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g))
        (Subgroup.inv_mem _ (Subgroup.mem_zpowers g))
    exact hzle hb
  simpa [δ, invMulAutHom] using hmem

theorem isTransvection_mul_of_apply_eq_inv [Fact p.Prime] (hp : p ≠ 2)
    (hBs : IsElemAbelian p Bs) {r r' : MulAut ↥Bs} (hr : GGIsReflection p r)
    (hr' : GGIsReflection p r') (hne : r ≠ r') {g : ↥Bs} (hg1 : g ≠ 1) (hg : r g = g⁻¹)
    (hg' : r' g = g⁻¹) : GGIsTransvection p (r * r') := by
  have hpow : ∀ x : ↥Bs, x ^ p = 1 := fun x => Subtype.ext (by
    simpa using hBs.2 (x : G) x.2)
  let δ : ↥Bs →* ↥Bs := invMulAutHom hBs.1 r
  let δ' : ↥Bs →* ↥Bs := invMulAutHom hBs.1 r'
  let φ : MulAut ↥Bs := r * r'
  let ε : ↥Bs →* ↥Bs := invMulAutHom hBs.1 φ
  have hδmem : ∀ b, δ b ∈ Subgroup.zpowers g := fun b =>
    inv_mul_apply_mem_zpowers_of_isReflection hp hBs hr hg1 hg b
  have hδ'mem : ∀ b, δ' b ∈ Subgroup.zpowers g := fun b =>
    inv_mul_apply_mem_zpowers_of_isReflection hp hBs hr' hg1 hg' b
  have hrinv : ∀ x ∈ Subgroup.zpowers g, r x = x⁻¹ := fun x hx =>
    apply_eq_inv_of_mem_zpowers hg hx
  have hrinv' : ∀ x ∈ Subgroup.zpowers g, r' x = x⁻¹ := fun x hx =>
    apply_eq_inv_of_mem_zpowers hg' hx
  have hφfix : ∀ x ∈ Subgroup.zpowers g, φ x = x := by
    intro x hx
    have hxinv : x⁻¹ ∈ Subgroup.zpowers g := Subgroup.inv_mem _ hx
    calc φ x = r (r' x) := rfl
      _ = r (x⁻¹) := by rw [hrinv' x hx]
      _ = (r x)⁻¹ := map_inv r x
      _ = (x⁻¹)⁻¹ := by rw [hrinv x hx]
      _ = x := inv_inv x
  have hεmem : ∀ b, ε b ∈ Subgroup.zpowers g := by
    intro b
    have h1 : r' b = b * δ' b := by
      change r' b = b * (b⁻¹ * r' b)
      group
    have h2 : r b = b * δ b := by
      change r b = b * (b⁻¹ * r b)
      group
    have h3 : r (δ' b) = (δ' b)⁻¹ := hrinv (δ' b) (hδ'mem b)
    have hε : ε b = δ b * (δ' b)⁻¹ := by
      change b⁻¹ * (r * r') b = δ b * (δ' b)⁻¹
      rw [MulAut.mul_apply, h1, map_mul, h3, h2]
      group
    rw [hε]
    exact Subgroup.mul_mem _ (hδmem b) (Subgroup.inv_mem _ (hδ'mem b))
  have hrange_le : ε.range ≤ Subgroup.zpowers g := by
    rintro _ ⟨b, rfl⟩
    exact hεmem b
  have hcard_g : Nat.card ↥(Subgroup.zpowers g) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hpow g) hg1
  have hdvd : Nat.card ε.range ∣ p := by
    have h := Subgroup.card_dvd_of_le hrange_le
    rwa [hcard_g] at h
  have hφne : φ ≠ 1 := by
    intro hφ1
    have h1 : r' = r⁻¹ := eq_inv_of_mul_eq_one_right hφ1
    have hsq : r * r = 1 := by rw [← pow_two]; exact hr.1
    have hrinv1 : r⁻¹ = r := inv_eq_of_mul_eq_one_right hsq
    exact hne (h1.trans hrinv1).symm
  have hne_bot : ε.range ≠ ⊥ := by
    have hbex : ∃ b : ↥Bs, φ b ≠ b := by
      by_contra hcon
      refine hφne (MulEquiv.ext fun b => ?_)
      have hb := (not_exists.mp hcon) b
      simpa using hb
    obtain ⟨b, hb⟩ := hbex
    intro hbot
    have hmem : ε b ∈ ε.range := ⟨b, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hεb : ε b ≠ 1 := by
      intro h
      have h1 : b⁻¹ * φ b = 1 := by
        simpa [ε, invMulAutHom] using h
      exact hb (inv_mul_eq_one.mp h1).symm
    exact hεb hmem
  have hrange : Nat.card ε.range = p := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (Nat.card ε.range) hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hne_bot
    · exact h1
  have hker : Nat.card ε.ker = Nat.card {b : ↥Bs // φ b = b} :=
    ker_invMulAutHom hBs.1 φ
  refine ⟨?_, ?_⟩
  · have hmul := Subgroup.card_ker_mul_card_range ε
    rw [hker, hrange] at hmul
    exact hmul
  · intro b
    have hmem : ε b ∈ Subgroup.zpowers g := hrange_le ⟨b, rfl⟩
    have hfix := hφfix (ε b) hmem
    simpa [ε, φ, invMulAutHom] using hfix

theorem apply_eq_self_of_commute_of_isReflection [Fact p.Prime] (hp : p ≠ 2)
    (hBs : IsElemAbelian p Bs) {r r' : MulAut ↥Bs} (hr : GGIsReflection p r)
    (hr' : GGIsReflection p r') (hcomm : r * r' = r' * r) (hne : r ≠ r') {g : ↥Bs}
    (hg : r' g = g⁻¹) : r g = g := by
  have hpow : ∀ x : ↥Bs, x ^ p = 1 := fun x => Subtype.ext (by
    simpa using hBs.2 (x : G) x.2)
  by_cases hg1 : g = 1
  · rw [hg1, map_one]
  have hr'r : r' (r g) = (r g)⁻¹ := by
    calc r' (r g) = (r' * r) g := rfl
      _ = (r * r') g := by rw [← hcomm]
      _ = r (r' g) := rfl
      _ = r (g⁻¹) := by rw [hg]
      _ = (r g)⁻¹ := map_inv r g
  have hxmem : r g ∈ Subgroup.zpowers g := by
    have h1 := inv_mul_apply_mem_zpowers_of_isReflection (p := p) hp hBs hr' hg1 hg (r g)
    have ha : (r g)⁻¹ * (r g)⁻¹ ∈ Subgroup.zpowers g := by
      simpa [hr'r] using h1
    exact mem_zpowers_of_inv_mul_inv_mem hp (hpow (r g)) ha
  have hr2 : r (r g) = g := by
    have h := congrArg (fun f : MulAut ↥Bs => f g) hr.1
    simpa [pow_two, MulAut.mul_apply] using h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hkk : g ^ (k * k) = g := by
    have h1 : r (g ^ k) = (r g) ^ k := map_zpow r g k
    have h2 : r (g ^ k) = g := by rw [hk, hr2]
    rw [zpow_mul, hk, ← h1, h2]
  have hord : orderOf g = p := orderOf_eq_prime (hpow g) hg1
  have h1 : g ^ (k * k - 1) = 1 := by
    rw [zpow_sub_one, hkk, mul_inv_cancel]
  have h2 : (p : ℤ) ∣ (k - 1) * (k + 1) := by
    rw [← hord, orderOf_dvd_iff_zpow_eq_one]
    rw [show (k - 1) * (k + 1) = k * k - 1 by ring]
    exact h1
  have hcases : g ^ k = g ∨ g ^ k = g⁻¹ := by
    rcases Int.Prime.dvd_mul' (Fact.out : p.Prime) h2 with h | h
    · left
      have h3 : g ^ (k - 1) = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one, hord]
        exact h
      rw [show k = (k - 1) + 1 by ring, zpow_add, h3, one_mul, zpow_one]
    · right
      have h3 : g ^ (k + 1) = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one, hord]
        exact h
      rw [show k = (k + 1) - 1 by ring, zpow_sub, h3, one_mul, zpow_one]
  rcases hcases with h | h
  · rw [← hk]
    exact h
  · exfalso
    have hrg : r g = g⁻¹ := hk.symm.trans h
    have hφtv := isTransvection_mul_of_apply_eq_inv hp hBs hr hr' hne hg1 hrg hg
    have hφ2 : (r * r') ^ 2 = 1 := by
      rw [Commute.mul_pow (show Commute r r' from hcomm), hr.1, hr'.1, one_mul]
    have hφeq1 : r * r' = 1 := by
      ext b
      have hc := hφtv.2 b
      have hφφ : (r * r') ((r * r') b) = b := by
        have h := congrArg (fun f : MulAut ↥Bs => f b) hφ2
        simpa [pow_two, MulAut.mul_apply] using h
      have h1 : (r * r') (b⁻¹ * (r * r') b) = ((r * r') b)⁻¹ * b := by
        rw [map_mul, map_inv, hφφ]
      have hcinv : ((r * r') b)⁻¹ * b = b⁻¹ * (r * r') b := h1.symm.trans hc
      have hc' : (b⁻¹ * (r * r') b)⁻¹ = b⁻¹ * (r * r') b := by
        rw [mul_inv_rev, inv_inv]
        exact hcinv
      have hsq : (b⁻¹ * (r * r') b) * (b⁻¹ * (r * r') b) = 1 :=
        eq_inv_iff_mul_eq_one.mp hc'.symm
      have hc1 : b⁻¹ * (r * r') b = 1 := by
        have hsq2 : (b⁻¹ * (r * r') b) ^ 2 = 1 := by rwa [pow_two]
        have hcop : Nat.Coprime 2 p :=
          Nat.coprime_two_left.mpr ((Fact.out : p.Prime).odd_of_ne_two hp)
        have hgg : (b⁻¹ * (r * r') b) ^ Nat.gcd 2 p = 1 :=
          pow_gcd_eq_one.mpr ⟨hsq2, hpow (b⁻¹ * (r * r') b)⟩
        rwa [hcop.gcd_eq_one, pow_one] at hgg
      simpa using (inv_mul_eq_one.mp hc1).symm
    rw [hφeq1] at hφtv
    have hfix : Nat.card {b : ↥Bs // (1 : MulAut ↥Bs) b = b} = Nat.card ↥Bs :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
    have hcard := hφtv.1
    rw [hfix] at hcard
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hpeq : p = 1 := Nat.eq_of_mul_eq_mul_left hpos (by simpa using hcard)
    exact hp1.ne' hpeq

end CFSG.StandardType.QTwo

end
