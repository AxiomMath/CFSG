module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Str
public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts
public import CFSG.RankThree.PartTwo.Sec21.FF79KFactsZ
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma44
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped Pointwise

variable {G : Type} [Group G]

private lemma z_mem_of_two_pow_mem {J' : Subgroup G} :
    ∀ (n : ℕ) (a : G) (m : ℕ), Odd m → a ^ m = 1 → a ^ (2 ^ n) ∈ J' → a ∈ J' := by
  intro n
  induction n with
  | zero => intro a m _ _ h; simpa using h
  | succ n ih =>
    intro a m hm ha h
    have h2 : a ^ 2 ∈ J' := by
      refine ih (a ^ 2) m hm ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
      · rwa [← pow_mul, ← pow_succ']
    obtain ⟨k, hk⟩ := exists_pow_eq_pow_two_mul ha hm 1
    rw [pow_one, pow_mul] at hk
    rw [hk]
    exact J'.pow_mem h2 k

private lemma z_mem_J_of_two_power {x : G} {X J' : Subgroup G} (hx : x ^ 3 = 1)
    (hXc : X ≤ Cen x) (hJc : J' ≤ Cen x) (hXodd : Odd (Nat.card X))
    (hXJ : ∀ u ∈ X, ∀ v ∈ J', u * v = v * u) {g : G}
    (hg : ∃ i : ℤ, ∃ u ∈ X, ∃ v ∈ J', g = x ^ i * u * v) {n : ℕ} (hn : g ^ (2 ^ n) = 1) :
    g ∈ J' := by
  obtain ⟨i, u, hu, v, hv, rfl⟩ := hg
  have hxu : Commute x u := (Subgroup.mem_centralizer_singleton_iff.mp (hXc hu)).symm
  have hxv : Commute x v := (Subgroup.mem_centralizer_singleton_iff.mp (hJc hv)).symm
  have huv : Commute u v := hXJ u hu v hv
  have hau : Commute (x ^ i) u := hxu.zpow_left i
  have hav : Commute (x ^ i * u) v := (hxv.zpow_left i).mul_left huv
  set m := 3 * Nat.card X with hm
  have hmodd : Odd m := (by decide : Odd 3).mul hXodd
  have hxm : (x ^ i) ^ m = 1 := by
    have : x ^ m = 1 := by rw [hm, pow_mul, hx, one_pow]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this, one_zpow]
  have hum : u ^ m = 1 := by
    have : u ^ Nat.card X = 1 := by
      have := pow_card_eq_one' (x := (⟨u, hu⟩ : X))
      exact congrArg Subtype.val this
    rw [hm, mul_comm, pow_mul, this, one_pow]
  have ham : (x ^ i * u) ^ m = 1 := by rw [hau.mul_pow, hxm, hum, one_mul]
  have h1 : (x ^ i * u) ^ (2 ^ n) ∈ J' := by
    have h2 : (x ^ i * u) ^ (2 ^ n) * v ^ (2 ^ n) = 1 := by rw [← hav.mul_pow]; exact hn
    have : (x ^ i * u) ^ (2 ^ n) = (v ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [this]
    exact J'.inv_mem (J'.pow_mem hv _)
  exact J'.mul_mem (z_mem_of_two_pow_mem n _ m hmodd ham h1) hv

private lemma z_op2_pow {t y : G} (hy : y ∈ Op 2 (Cen t)) : ∃ n : ℕ, y ^ (2 ^ n) = 1 := by
  obtain ⟨n, hn⟩ := op2_isPGroup t ⟨y, hy⟩
  exact ⟨n, congrArg Subtype.val hn⟩

private lemma z_card_closure_le [Finite G] {b x z : G} (hb : b ^ 3 = 1) (hx : x ^ 3 = 1)
    (hbx : b * x = x * b) (hz : z ∈ Subgroup.zpowers b) :
    Nat.card (Subgroup.closure ({b, x, z} : Set G)) ≤ 9 := by
  have hle : Subgroup.closure ({b, x, z} : Set G) ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers x := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left hz
  have hnorm : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    have hc : ∀ h ∈ Subgroup.zpowers x, b * h * b⁻¹ = h := by
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right (show Commute b x from hbx) k).mul_inv_cancel
    have hc' : ∀ h ∈ Subgroup.zpowers x, b⁻¹ * h * b = h := by
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right (show Commute b x from hbx) k).inv_mul_cancel
    constructor
    · intro hh; rw [hc h hh]; exact hh
    · intro hh
      have h3 := hc' _ hh
      rw [show b⁻¹ * (b * h * b⁻¹) * b = h by group] at h3
      rw [h3]; exact hh
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hcb : Nat.card (Subgroup.zpowers b) ≤ 3 :=
    (Nat.card_zpowers b ▸ Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb))
  have hcx : Nat.card (Subgroup.zpowers x) ≤ 3 :=
    (Nat.card_zpowers x ▸ Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx))
  have hsurj : Function.Surjective
      (fun p : Subgroup.zpowers b × Subgroup.zpowers x =>
        (⟨p.1.1 * p.2.1, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
          ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers x))) := by
    rintro ⟨s, hs⟩
    have hs' : s ∈ ((Subgroup.zpowers b : Set G) * (Subgroup.zpowers x : Set G)) := by
      rw [← hset]; exact hs
    obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.mp hs'
    exact ⟨(⟨a, ha⟩, ⟨d, hd⟩), rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod] at h1
  calc Nat.card (Subgroup.closure ({b, x, z} : Set G))
      ≤ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (Subgroup.zpowers b) * Nat.card (Subgroup.zpowers x) := h1
    _ ≤ 3 * 3 := Nat.mul_le_mul hcb hcx

private lemma z_sec4_facts [Finite G] {b : G} {J B : Subgroup G} {b₁ b₂ : G}
    (h4 : FF79Sec4 b J B b₁ b₂) :
    b ^ 3 = 1 ∧ b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b * b₁ = b₁ * b ∧ b * b₂ = b₂ * b ∧
      b₁ * b₂ = b₂ * b₁ ∧ b₁ ∉ Subgroup.zpowers b ∧ b₂ ∉ Subgroup.zpowers b := by
  obtain ⟨hEA, hBeq, -⟩ := h4.mono
  have hbB : b ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  have hb₂B : b₂ ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  haveI : IsMulCommutative B := hEA.1.toIsMulCommutative
  have hcomm : ∀ u v : G, u ∈ B → v ∈ B → u * v = v * u := fun u v hu hv =>
    congrArg Subtype.val (hEA.1.is_comm.comm (⟨u, hu⟩ : B) ⟨v, hv⟩)
  have hcube : ∀ u : G, u ∈ B → u ^ 3 = 1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hEA.1.exponent_dvd_p
    have : (⟨u, hu⟩ : B) ^ 3 = 1 := by
      rw [hk, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
    exact congrArg Subtype.val this
  have h27 : Nat.card B = 27 := by rw [hEA.2]; norm_num
  have hb3 := hcube b hbB
  have hb₁3 := hcube b₁ hb₁B
  have hb₂3 := hcube b₂ hb₂B
  refine ⟨hb3, hb₁3, hb₂3, hcomm _ _ hbB hb₁B, hcomm _ _ hbB hb₂B, hcomm _ _ hb₁B hb₂B, ?_, ?_⟩
  · intro hz
    have := z_card_closure_le (x := b₂) hb3 hb₂3 (hcomm _ _ hbB hb₂B) hz
    have hs : ({b, b₂, b₁} : Set G) = {b, b₁, b₂} := by rw [Set.pair_comm b₂ b₁]
    rw [hs, ← hBeq, h27] at this
    omega
  · intro hz
    have := z_card_closure_le (x := b₁) hb3 hb₁3 (hcomm _ _ hbB hb₁B) hz
    rw [← hBeq, h27] at this
    omega

private lemma z_card_cent_transport {J' : Subgroup G} {K : Type} [Group K] (e : J' ≃* K) (b : G)
    (hb : b ∈ J') :
    Nat.card ↥(Subgroup.centralizer ({e ⟨b, hb⟩} : Set K)) = Nat.card ↥(J' ⊓ Cen b) := by
  set b' : J' := ⟨b, hb⟩
  have h1 : (Subgroup.centralizer ({e b'} : Set K)).map e.symm.toMonoidHom =
      Subgroup.centralizer ({b'} : Set J') := by
    ext g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.symm_symm]
    constructor
    · intro h
      apply e.injective
      rw [map_mul, map_mul]; exact h
    · intro h
      have := congrArg e h
      rwa [map_mul, map_mul] at this
  have h2 : (Subgroup.centralizer ({b'} : Set J')).map J'.subtype = J' ⊓ Cen b := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.subtype_apply]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, congrArg Subtype.val hc⟩
    · rintro ⟨hg, hc⟩
      exact ⟨⟨g, hg⟩, Subtype.ext hc, rfl⟩
  rw [← h2, Subgroup.card_map_of_injective J'.subtype_injective, ← h1,
    Subgroup.card_map_of_injective e.symm.injective]

private theorem z_exists_zpow_of_comm_A5 (hA5 : FF79KCentA5) {K : Subgroup G}
    (e : K ≃* alternatingGroup (Fin 5)) {w k : G} (hw : w ∈ K) (hk : k ∈ K)
    (ho : orderOf w = 3) (hc : k * w = w * k) : ∃ n : ℤ, k = w ^ n := by
  have ho' : orderOf (e ⟨w, hw⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ho
  have hc' : e ⟨k, hk⟩ * e ⟨w, hw⟩ = e ⟨w, hw⟩ * e ⟨k, hk⟩ := by
    rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext hc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hA5 _ _ ho' hc')
  refine ⟨n, ?_⟩
  have : (⟨k, hk⟩ : K) = (⟨w, hw⟩ : K) ^ n := e.injective (by rw [map_zpow]; exact hn.symm)
  simpa using congrArg Subtype.val this

private structure ZA5L3Dec (x b w : G) (X K L : Subgroup G) : Prop where
  hXx : X ≤ Cen x
  hKx : K ≤ Cen x
  hLx : L ≤ Cen x
  hXodd : Odd (Nat.card X)
  eK : Nonempty (K ≃* alternatingGroup (Fin 5))
  eL : Nonempty (L ≃* GL (Fin 3) (ZMod 2))
  hXK : ∀ u ∈ X, ∀ v ∈ K, u * v = v * u
  hXL : ∀ u ∈ X, ∀ v ∈ L, u * v = v * u
  hKL : ∀ u ∈ K, ∀ v ∈ L, u * v = v * u
  hdec : ∀ g ∈ Cen x, ∃ i : ℤ, ∃ u ∈ X, ∃ k ∈ K, ∃ l ∈ L, g = x ^ i * u * k * l
  hwK : w ∈ K
  hbL : b ∈ L

private theorem z_exists_dec {x b w : G} (hs : FF79CentA5L3 x b w) :
    ∃ X K L, ZA5L3Dec x b w X K L := by
  obtain ⟨X, K, L, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hs.exists_decomp
  exact ⟨X, K, L, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

private theorem z_cen_comm {x g : G} (hg : g ∈ Cen x) : x * g = g * x :=
  Subgroup.mem_centralizer_iff.mp hg x rfl

private theorem z_mem_cen_of {x g : G} (h : x * g = g * x) : g ∈ Cen x := by
  rw [Subgroup.mem_centralizer_iff]
  intro h' hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact h

private theorem z_mem_of_pow_mem {a : G} {H : Subgroup G} {N m : ℕ} (hN : a ^ N = 1)
    (hcop : Nat.Coprime m N) (h : a ^ m ∈ H) : a ∈ H := by
  have hd : orderOf a ∣ N := orderOf_dvd_of_pow_eq_one hN
  obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime (hcop.coprime_dvd_right hd)
  rw [← hs]
  exact H.pow_mem h s

private theorem z_pow_eq_one_of_dvd {a : G} {n N : ℕ} (ha : a ^ n = 1) (h : n ∣ N) : a ^ N = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul, ha, one_pow]

private theorem z_zpow_pow_eq_one {a : G} {n N : ℕ} (i : ℤ) (ha : a ^ n = 1) (h : n ∣ N) :
    (a ^ i) ^ N = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, z_pow_eq_one_of_dvd ha h,
    one_zpow]

private theorem z_prod_pow_eq_one {x u k : G} {m : ℕ} (i : ℤ) (hx : x ^ 3 = 1) (hu : u ^ m = 1)
    (hk : k ^ 3 = 1) (hxu : x * u = u * x) (hxk : x * k = k * x) (huk : u * k = k * u) :
    (x ^ i * u * k) ^ (3 * m) = 1 := by
  have h1 : Commute (x ^ i) u := (show Commute x u from hxu).zpow_left i
  have h2 : Commute (x ^ i) k := (show Commute x k from hxk).zpow_left i
  have h3 : Commute u k := huk
  rw [(h2.mul_left h3 : Commute (x ^ i * u) k).mul_pow, h1.mul_pow,
    z_zpow_pow_eq_one i hx (dvd_mul_right 3 m), one_mul,
    z_pow_eq_one_of_dvd hu (dvd_mul_left m 3), z_pow_eq_one_of_dvd hk (dvd_mul_right 3 m), mul_one]

private theorem z_t_mem_L (hA5 : FF79KCentA5) {x b w t : G} {X K L : Subgroup G}
    (d : ZA5L3Dec x b w X K L) (hx3 : orderOf x = 3) (hw3 : orderOf w = 3)
    (ht2 : orderOf t = 2) (htx : t * x = x * t) (htw : t * w = w * t) : t ∈ L := by
  obtain ⟨eK⟩ := d.eK
  have hx3' : x ^ 3 = 1 := by simpa [hx3] using pow_orderOf_eq_one x
  have hw3' : w ^ 3 = 1 := by simpa [hw3] using pow_orderOf_eq_one w
  have ht2' : t ^ 2 = 1 := by simpa [ht2] using pow_orderOf_eq_one t
  obtain ⟨i, u, hu, k, hk, l, hl, ht⟩ := d.hdec t (z_mem_cen_of htx.symm)
  have hxu : x * u = u * x := z_cen_comm (d.hXx hu)
  have hxk : x * k = k * x := z_cen_comm (d.hKx hk)
  have hxl : x * l = l * x := z_cen_comm (d.hLx hl)
  have huk := d.hXK u hu k hk
  have hul := d.hXL u hu l hl
  have hkl := d.hKL k hk l hl
  have hwx : x * w = w * x := z_cen_comm (d.hKx d.hwK)
  have hwu : u * w = w * u := d.hXK u hu w d.hwK
  have hwl : w * l = l * w := d.hKL w d.hwK l hl
  have hcw : (x ^ i * u) * w = w * (x ^ i * u) := by
    have h1 : Commute (x ^ i) w := (show Commute x w from hwx).zpow_left i
    exact (h1.mul_left (show Commute u w from hwu)).eq
  subst ht
  have key : (x ^ i * u) * (k * w) * l = (x ^ i * u) * (w * k) * l := by
    calc (x ^ i * u) * (k * w) * l = (x ^ i * u) * k * (w * l) := by simp only [mul_assoc]
      _ = (x ^ i * u) * k * (l * w) := by rw [hwl]
      _ = (x ^ i * u * k * l) * w := by simp only [mul_assoc]
      _ = w * (x ^ i * u * k * l) := htw
      _ = (w * (x ^ i * u)) * k * l := by simp only [mul_assoc]
      _ = ((x ^ i * u) * w) * k * l := by rw [hcw]
      _ = (x ^ i * u) * (w * k) * l := by simp only [mul_assoc]
  have hkw : k * w = w * k := mul_left_cancel (mul_right_cancel key)
  obtain ⟨n, hn⟩ := z_exists_zpow_of_comm_A5 hA5 eK d.hwK hk hw3 hkw
  have hk3 : k ^ 3 = 1 := by
    rw [hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3', one_zpow]
  have hum : u ^ Nat.card X = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard X hu)
  have hN := z_prod_pow_eq_one i hx3' hum hk3 hxu hxk huk
  have hcomm : Commute (x ^ i * u * k) l :=
    ((((show Commute x l from hxl).zpow_left i).mul_left (show Commute u l from hul)).mul_left
      (show Commute k l from hkl))
  have hsq : (x ^ i * u * k) ^ 2 * l ^ 2 = 1 := by
    rw [← hcomm.mul_pow]; exact ht2'
  have hmem : (x ^ i * u * k) ^ 2 ∈ L := by
    rw [eq_inv_of_mul_eq_one_left hsq]; exact L.inv_mem (L.pow_mem hl 2)
  have hodd : Odd (3 * Nat.card X) := Odd.mul (by decide) d.hXodd
  have ha : x ^ i * u * k ∈ L :=
    z_mem_of_pow_mem hN (Nat.coprime_two_left.2 hodd) hmem
  exact L.mul_mem ha hl

private theorem z_gen_βγ {z b₁ b₂ : G} (h1 : Commute z (b₁ * b₂))
    (h2 : Commute z (b₁ ^ 2 * b₂)) : z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z := by
  have e1 : b₁ = (b₁ ^ 2 * b₂) * (b₁ * b₂)⁻¹ := by group
  have c1 : Commute z b₁ := by rw [e1]; exact h2.mul_right h1.inv_right
  refine ⟨c1.eq, ?_⟩
  have e2 : b₂ = b₁⁻¹ * (b₁ * b₂) := by group
  have c2 : Commute z b₂ := by rw [e2]; exact c1.inv_right.mul_right h1
  exact c2.eq

private theorem z_t_comm_words {b₁ b₂ t : G} (h1 : t * b₁ = b₁ * t) (h2 : t * b₂ = b₂ * t) :
    t * (b₁ * b₂) = (b₁ * b₂) * t ∧ t * (b₁ ^ 2 * b₂) = (b₁ ^ 2 * b₂) * t := by
  have c1 : Commute t b₁ := h1
  have c2 : Commute t b₂ := h2
  exact ⟨(c1.mul_right c2).eq, (((c1.pow_right 2)).mul_right c2).eq⟩


private theorem z_main_aux (hTc : FF79KTransvComm) (hTz : FF79KTransvCenter)
    {b x z t : G} (hc : FF79CentL5 x b z)
    (hxo : x ^ 3 = 1) (hb : orderOf b = 3) (hz : orderOf z = 3)
    (hzb : z ∉ Subgroup.zpowers b) (hbz : b * z = z * b) (ht2 : orderOf t = 2)
    (htx : t * x = x * t) (htz : t * z = z * t) (htb : t * b * t⁻¹ = b⁻¹) :
    (∀ d : G, (∃ n : ℕ, d ^ (2 ^ n) = 1) → d * t = t * d → d * z = z * d → d ∈ Cen x →
      ∀ y ∈ Op 2 (Cen t) ⊓ Cen x, d * y * d⁻¹ * y⁻¹ ∈ Subgroup.zpowers t) ∧
    (∀ r₁ ∈ Op 2 (Cen t) ⊓ Cen x, ∀ r₂ ∈ Op 2 (Cen t) ⊓ Cen x, r₁ * r₂ ≠ r₂ * r₁ →
      ∀ r ∈ Op 2 (Cen t) ⊓ Cen x, (∀ w ∈ Op 2 (Cen t) ⊓ Cen x, r * w = w * r) →
      r ∈ Subgroup.zpowers t) := by
  obtain ⟨X, J', hXc, hJc, hXodd, ⟨e⟩, hXJ, hdec, hbJ, hzJ, h7⟩ := hc.exists_decomp
  have hxt : t ∈ Cen x := Subgroup.mem_centralizer_singleton_iff.mpr htx
  have htJ : t ∈ J' := by
    refine z_mem_J_of_two_power hxo hXc hJc hXodd hXJ (hdec t hxt) (n := 1) ?_
    simpa [ht2] using pow_orderOf_eq_one t
  have h2J : ∀ y ∈ Op 2 (Cen t) ⊓ Cen x, y ∈ J' := fun y hy => by
    obtain ⟨n, hn⟩ := z_op2_pow hy.1
    exact z_mem_J_of_two_power hxo hXc hJc hXodd hXJ (hdec y hy.2) hn
  set t' : J' := ⟨t, htJ⟩ with ht'
  set b' : J' := ⟨b, hbJ⟩ with hb'
  set z' : J' := ⟨z, hzJ⟩ with hz'
  let R : Subgroup G := Op 2 (Cen t) ⊓ Cen x
  let R' : Subgroup (GL (Fin 5) (ZMod 2)) := (R.subgroupOf J').map e.toMonoidHom
  have hR'mem : ∀ a : J', e a ∈ R' ↔ (a : G) ∈ R := by
    intro a
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  have hord : ∀ a : J', orderOf (e a) = orderOf (a : G) := fun a => by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
  have hcomm : ∀ a c : J', (a : G) * c = c * a → e a * e c = e c * e a := fun a c h => by
    rw [← map_mul, ← map_mul]; exact congrArg e (Subtype.ext h)
  have hcomm' : ∀ a c : J', e a * e c = e c * e a → (a : G) * c = c * a := fun a c h => by
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (e.injective h)
  have hsy : e t' * e b' * (e t')⁻¹ = (e b')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    exact congrArg e (Subtype.ext htb)
  have hzy : e z' ∉ Subgroup.zpowers (e b') := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← map_zpow] at hk
    have := congrArg Subtype.val (e.injective hk)
    exact hzb (Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using this⟩)
  have hR'p : IsPGroup 2 R' := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨n, hn⟩ := z_op2_pow (Subgroup.mem_subgroupOf.mp ha).1
    refine ⟨n, Subtype.ext ?_⟩
    have : a ^ 2 ^ n = 1 := Subtype.ext hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one, MonoidHom.coe_coe]
    rw [← map_pow, this, map_one]
  have hR'le : R' ≤ Subgroup.centralizer ({e t'} : Set (GL (Fin 5) (ZMod 2))) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
    have haR : (a : G) ∈ R := Subgroup.mem_subgroupOf.mp ha
    have : (a : G) ∈ Cen t := op2_le_cen t haR.1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm t' a (Subgroup.mem_centralizer_singleton_iff.mp this).symm).symm
  have hR'norm : ∀ g ∈ Subgroup.centralizer ({e t'} : Set (GL (Fin 5) (ZMod 2))), ∀ r ∈ R',
      g * r * g⁻¹ ∈ R' := by
    intro g hg r hr
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨g0, rfl⟩ := e.surjective g
    have haR : (a : G) ∈ R := Subgroup.mem_subgroupOf.mp ha
    have hg0 : (g0 : G) ∈ Cen t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm' g0 t' (Subgroup.mem_centralizer_singleton_iff.mp hg))
    have h1 : (g0 : G) * a * (g0 : G)⁻¹ ∈ R :=
      ⟨op2_conj_mem hg0 haR.1, by
        have hg0x : (g0 : G) ∈ Cen x := hJc g0.2
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg0x haR.2) (Subgroup.inv_mem _ hg0x)⟩
    have := (hR'mem (g0 * a * g0⁻¹)).mpr h1
    simpa using this
  have hcent : 7 ∣ Nat.card ↥(Subgroup.centralizer ({e b'} : Set (GL (Fin 5) (ZMod 2)))) := by
    rw [z_card_cent_transport e b hbJ]; exact h7
  refine ⟨?_, ?_⟩
  · rintro d ⟨n, hn⟩ hdt hdz hdx y hy
    have hdJ : d ∈ J' := z_mem_J_of_two_power hxo hXc hJc hXodd hXJ (hdec d hdx) hn
    set d' : J' := ⟨d, hdJ⟩ with hd'
    have hd'n : d' ^ 2 ^ n = 1 := Subtype.ext hn
    have key := hTc (e t') (e b') (e z') (by rw [hord]; exact ht2) (by rw [hord]; exact hb)
      hcent hsy (by rw [hord]; exact hz) (hcomm z' b' hbz.symm) hzy (hcomm t' z' htz)
      (e d') ⟨n, by rw [← map_pow, hd'n, map_one]⟩ (hcomm d' t' hdt) (hcomm d' z' hdz)
      R' hR'p hR'le hR'norm (e ⟨y, h2J y hy⟩) ((hR'mem _).mpr hy)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp key
    rw [← map_zpow, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hk
    have := congrArg Subtype.val (e.injective hk)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using this⟩
  · intro r₁ hr₁ r₂ hr₂ hne r hr hrc
    have key := hTz (e t') (e b') (e z') (by rw [hord]; exact ht2) (by rw [hord]; exact hb)
      hcent hsy (by rw [hord]; exact hz) (hcomm z' b' hbz.symm) hzy (hcomm t' z' htz)
      R' hR'p hR'le hR'norm (e ⟨r₁, h2J r₁ hr₁⟩) ((hR'mem _).mpr hr₁)
      (e ⟨r₂, h2J r₂ hr₂⟩) ((hR'mem _).mpr hr₂) (fun h => hne (hcomm' _ _ h))
      (e ⟨r, h2J r hr⟩) ((hR'mem _).mpr hr) (by
        intro w hw
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hw
        exact hcomm _ _ (hrc a (Subgroup.mem_subgroupOf.mp ha)))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp key
    rw [← map_zpow] at hk
    have := congrArg Subtype.val (e.injective hk)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using this⟩

private theorem z_pull_L3 (hL3 : FF79KCentL3NonAb) {L : Subgroup G}
    (e : L ≃* GL (Fin 3) (ZMod 2)) {t : G} (htL : t ∈ L) (ht : orderOf t = 2) :
    ∃ δ₁ ∈ L, ∃ δ₂ ∈ L, δ₁ * t = t * δ₁ ∧ δ₂ * t = t * δ₂ ∧ δ₁ ^ 4 = 1 ∧ δ₂ ^ 4 = 1 ∧
      δ₁ * δ₂ ≠ δ₂ * δ₁ := by
  have ho : orderOf (e ⟨t, htL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ht
  obtain ⟨d₁, d₂, h₁, h₂, h₁4, h₂4, hne⟩ := hL3 _ ho
  have comm : ∀ d : GL (Fin 3) (ZMod 2), d * e ⟨t, htL⟩ = e ⟨t, htL⟩ * d →
      ((e.symm d : L) : G) * t = t * (e.symm d : L) := fun d h => by
    have := congrArg e.symm h
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at this
    exact congrArg Subtype.val this
  have pow4 : ∀ d : GL (Fin 3) (ZMod 2), d ^ 4 = 1 → ((e.symm d : L) : G) ^ 4 = 1 := fun d h => by
    have := congrArg e.symm h
    rw [map_pow, map_one] at this
    exact congrArg Subtype.val this
  refine ⟨e.symm d₁, (e.symm d₁).2, e.symm d₂, (e.symm d₂).2, comm d₁ h₁, comm d₂ h₂,
    pow4 d₁ h₁4, pow4 d₂ h₂4, fun h => hne ?_⟩
  have h' : e.symm (d₁ * d₂) = e.symm (d₂ * d₁) := by
    rw [map_mul, map_mul]; exact Subtype.ext h
  exact e.symm.injective h'

private def zCommSub (t d : G) : Subgroup G where
  carrier := {x | x ∈ Cen t ∧ d * x * d⁻¹ * x⁻¹ ∈ Subgroup.zpowers t}
  mul_mem' := by
    rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
    refine ⟨(Cen t).mul_mem hxC hyC, ?_⟩
    have h : d * (x * y) * d⁻¹ * (x * y)⁻¹ =
        (d * x * d⁻¹ * x⁻¹) * (x * (d * y * d⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [h, conj_fix_zpowers hxC hy]
    exact Subgroup.mul_mem _ hx hy
  one_mem' := ⟨Subgroup.one_mem _, by simpa using Subgroup.one_mem _⟩
  inv_mem' := by
    rintro x ⟨hxC, hx⟩
    refine ⟨(Cen t).inv_mem hxC, ?_⟩
    have h : d * x⁻¹ * d⁻¹ * x⁻¹⁻¹ = x⁻¹ * (d * x * d⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [h, conj_fix_zpowers ((Cen t).inv_mem hxC) (Subgroup.inv_mem _ hx)]
    exact Subgroup.inv_mem _ hx

private def zCommY (t : G) : Subgroup G where
  carrier := {c | c ∈ Cen t ∧ ∀ x ∈ Op 2 (Cen t), c * x * c⁻¹ * x⁻¹ ∈ Subgroup.zpowers t}
  mul_mem' := by
    rintro c₁ c₂ ⟨hc₁, h₁⟩ ⟨hc₂, h₂⟩
    refine ⟨(Cen t).mul_mem hc₁ hc₂, fun x hx => ?_⟩
    have h : c₁ * c₂ * x * (c₁ * c₂)⁻¹ * x⁻¹ =
        (c₁ * (c₂ * x * c₂⁻¹ * x⁻¹) * c₁⁻¹) * (c₁ * x * c₁⁻¹ * x⁻¹) := by group
    rw [h, conj_fix_zpowers hc₁ (h₂ x hx)]
    exact Subgroup.mul_mem _ (h₂ x hx) (h₁ x hx)
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simpa using Subgroup.one_mem _⟩
  inv_mem' := by
    rintro c ⟨hc, h⟩
    refine ⟨(Cen t).inv_mem hc, fun x hx => ?_⟩
    have e : c⁻¹ * x * c⁻¹⁻¹ * x⁻¹ = c⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * c⁻¹⁻¹ := by group
    rw [e, conj_fix_zpowers ((Cen t).inv_mem hc) (Subgroup.inv_mem _ (h x hx))]
    exact Subgroup.inv_mem _ (h x hx)

private theorem z_mem_op2 [Finite G] (hchar : IsCharacteristicPType G 2) {t d : G}
    (ht : orderOf t = 2) (hdC : d ∈ Cen t)
    (hd : ∀ x ∈ Op 2 (Cen t), d * x * d⁻¹ * x⁻¹ ∈ Subgroup.zpowers t) : d ∈ Op 2 (Cen t) := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hpow : ∀ c ∈ zCommY t, ∃ k : ℕ, c ^ (2 ^ k) = 1 := by
    intro c hc
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine ⟨k, ?_⟩
    set c' := c ^ (2 ^ k) with hc'
    have hc'Y : c' ∈ zCommY t := (zCommY t).pow_mem hc _
    have hc'm : c' ^ m = 1 := by
      rw [hc', ← pow_mul, ← hkm]; exact pow_orderOf_eq_one c
    have hc'T : ∀ x ∈ Op 2 (Cen t), c' * x = x * c' := by
      intro x hx
      set a := c' * x * c'⁻¹ * x⁻¹ with ha
      have haZ : a ∈ Subgroup.zpowers t := hc'Y.2 x hx
      have ha2 : a ^ 2 = 1 := sq_eq_one_of_mem_zpowers ht2 haZ
      have hax : c' * x * c'⁻¹ = a * x := by rw [ha]; group
      have hn : ∀ n : ℕ, c' ^ n * x * (c' ^ n)⁻¹ = a ^ n * x := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have h : c' ^ (n + 1) * x * (c' ^ (n + 1))⁻¹ =
              (c' * (c' ^ n * x * (c' ^ n)⁻¹) * c'⁻¹) := by group
          have h2 : c' * (a ^ n * x) * c'⁻¹ = a ^ n * (a * x) := by
            rw [show c' * (a ^ n * x) * c'⁻¹ = (c' * a ^ n * c'⁻¹) * (c' * x * c'⁻¹) by group,
              conj_fix_zpowers hc'Y.1 (Subgroup.pow_mem _ haZ n), hax]
          rw [h, ih, h2, pow_succ]
          exact (mul_assoc _ _ _).symm
      have h1 : a ^ m = 1 := by
        have := hn m
        rw [hc'm, inv_one, one_mul, mul_one] at this
        exact (mul_eq_right.mp this.symm)
      obtain ⟨j, hj⟩ := hm
      have : a = 1 := by
        rw [hj, pow_succ, pow_mul, ha2, one_pow, one_mul] at h1; exact h1
      rw [this] at hax
      simpa [mul_inv_eq_iff_eq_mul] using hax
    have hc'T' : c' ∈ Op 2 (Cen t) := mem_op2_of_centralizes hchar ht hc'Y.1 hc'T
    obtain ⟨n, hn⟩ := z_op2_pow hc'T'
    have := pow_gcd_eq_one.mpr ⟨hn, hc'm⟩
    rwa [Nat.Coprime.gcd_eq_one ((Nat.coprime_two_left.2 hm).pow_left n), pow_one] at this
  have hP : IsPGroup 2 ↥((zCommY t).subgroupOf (Cen t)) := by
    intro g
    obtain ⟨k, hk⟩ := hpow g.1.1 g.2
    exact ⟨k, Subtype.ext (Subtype.ext hk)⟩
  have hN : ((zCommY t).subgroupOf (Cen t)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨-, ha⟩ := ha
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨(Cen t).mul_mem ((Cen t).mul_mem g.2 a.2) ((Cen t).inv_mem g.2), fun x hx => ?_⟩
    have hx' : (g : G)⁻¹ * x * (g : G) ∈ Op 2 (Cen t) := by
      simpa using op2_conj_mem ((Cen t).inv_mem g.2) hx
    have h : (g : G) * a * (g : G)⁻¹ * x * ((g : G) * a * (g : G)⁻¹)⁻¹ * x⁻¹ =
        (g : G) * ((a : G) * ((g : G)⁻¹ * x * g) * (a : G)⁻¹ * ((g : G)⁻¹ * x * g)⁻¹) *
          (g : G)⁻¹ := by group
    rw [h, conj_fix_zpowers g.2 (ha _ hx')]
    exact ha _ hx'
  have hle : (zCommY t).subgroupOf (Cen t) ≤ CFSG.pCore 2 ↥(Cen t) := by
    unfold CFSG.pCore
    exact le_sSup ⟨hN, hP⟩
  exact Subgroup.mem_map.mpr ⟨⟨d, hdC⟩, hle (Subgroup.mem_subgroupOf.mpr ⟨hdC, hd⟩), rfl⟩

theorem ff79_4_4Z_of (hstr : FF79_4_3Str) (hβ : FF79_4_4Beta) (hA5 : FF79KCentA5)
    (hL3 : FF79KCentL3NonAb) (hTc : FF79KTransvComm) (hTz : FF79KTransvCenter) :
    FF79_4_4Z := by
  intro G _ _ b J B b₁ b₂ h4 t ht y hy hyc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hb₁3, hb₂3, hcomm, hK1, hcardA, hA3⟩ := sec4_facts h4
  obtain ⟨-, -, -, hbb₁, hbb₂, -, hn₁, hn₂⟩ := z_sec4_facts h4
  have hS := hstr G b J B b₁ b₂ h4
  have hbo : orderOf b = 3 := h4.hyp.ord
  have hone : ∀ w : G, w ∉ Subgroup.zpowers b → w ≠ 1 := fun w hw h1 =>
    hw (h1 ▸ Subgroup.one_mem _)
  have hcb : t * b * t⁻¹ = b⁻¹ := ht.inv
  have hβ3 : (b₁ * b₂) ^ 3 = 1 := by
    rw [(show Commute b₁ b₂ from hcomm).mul_pow, hb₁3, hb₂3, one_mul]
  have hγ3 : (b₁ ^ 2 * b₂) ^ 3 = 1 := by
    rw [((show Commute b₁ b₂ from hcomm).pow_left 2).mul_pow, ← pow_mul, mul_comm 2 3, pow_mul,
      hb₁3, one_pow, hb₂3, one_mul]
  have hβo : orderOf (b₁ * b₂) = 3 := by
    refine orderOf_eq_prime hβ3 fun h => hK1 ?_
    rw [eq_inv_of_mul_eq_one_right h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b₁)
  have hγo : orderOf (b₁ ^ 2 * b₂) = 3 := by
    refine orderOf_eq_prime hγ3 fun h => hK1 ?_
    rw [eq_inv_of_mul_eq_one_right h]; exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ 2)
  obtain ⟨htβ, htγ⟩ := z_t_comm_words ht.comm₁ ht.comm₂
  obtain ⟨X, K, L, d⟩ := z_exists_dec hS.centβ
  have htL : t ∈ L := z_t_mem_L hA5 d hβo hγo ht.ord htβ htγ
  obtain ⟨eL⟩ := d.eL
  obtain ⟨δ₁, hδ₁L, δ₂, hδ₂L, hδ₁t, hδ₂t, hδ₁4, hδ₂4, hδne⟩ := z_pull_L3 hL3 eL htL ht.ord
  have hδ : ∀ δ ∈ L, δ * b₁ = b₁ * δ ∧ δ * b₂ = b₂ * δ := fun δ hδ =>
    z_gen_βγ (z_cen_comm (d.hLx hδ)).symm (d.hKL _ d.hwK δ hδ).symm
  have hb₁C : b₁ ∈ Cen t := Subgroup.mem_centralizer_singleton_iff.mpr ht.comm₁.symm
  have hb₂C : b₂ ∈ Cen t := Subgroup.mem_centralizer_singleton_iff.mpr ht.comm₂.symm
  have hAC : Subgroup.closure ({b₁, b₂} : Set G) ≤ Cen t := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h <;> rw [h] <;> assumption
  have hAn : Subgroup.closure ({b₁, b₂} : Set G) ≤ Subgroup.normalizer (Op 2 (Cen t) : Set G) :=
    hAC.trans (le_nor_of_conj_mem fun j hj s hs => op2_conj_mem hj hs)
  have hβ' := hβ G b J B b₁ b₂ h4 t ht
  have hP : ∀ x, (x = b₁ * b₂ ∨ x = b₁ ^ 2 * b₂) → ∀ z ∈ Op 2 (Cen t), z * x = x * z →
      z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z := fun x hx z hz hzx => by
    obtain ⟨h1, h2, -⟩ := hβ' x hx z
      (Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr hzx⟩)
    exact ⟨h1, h2⟩
  have hgen : ∀ W : Subgroup G, (∀ z ∈ Op 2 (Cen t),
      (z * b₁ = b₁ * z ∨ z * b₂ = b₂ * z) → z ∈ W) → Op 2 (Cen t) ≤ W := fun W hW =>
    gen_by_cent (op2_isPGroup t) hb₁3 hb₂3 hcomm hcardA hA3 hAn hP W hW
  have hone₁ := hone _ hn₂
  have hone₂ := hone _ hn₁
  have main₁ := z_main_aux hTc hTz hS.cent₁ hb₁3 hbo (orderOf_eq_prime hb₂3 hone₁) hn₂ hbb₂
    ht.ord ht.comm₁ ht.comm₂ hcb
  have main₂ := z_main_aux hTc hTz hS.cent₂ hb₂3 hbo (orderOf_eq_prime hb₁3 hone₂) hn₁ hbb₁
    ht.ord ht.comm₂ ht.comm₁ hcb
  have hcommT : ∀ δ : G, (∃ n : ℕ, δ ^ (2 ^ n) = 1) → δ * t = t * δ → δ * b₁ = b₁ * δ →
      δ * b₂ = b₂ * δ → ∀ x ∈ Op 2 (Cen t), δ * x * δ⁻¹ * x⁻¹ ∈ Subgroup.zpowers t := by
    intro δ hδ2 hδt hδ₁ hδ₂
    have hle := hgen (zCommSub t δ) fun z hz hzb => by
      refine ⟨op2_le_cen t hz, ?_⟩
      rcases hzb with h | h
      · exact main₁.1 δ hδ2 hδt hδ₂ (Subgroup.mem_centralizer_singleton_iff.mpr hδ₁) z
          ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr h⟩
      · exact main₂.1 δ hδ2 hδt hδ₁ (Subgroup.mem_centralizer_singleton_iff.mpr hδ₂) z
          ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr h⟩
    exact fun x hx => (hle hx).2
  have hδT : ∀ δ ∈ L, δ * t = t * δ → δ ^ 4 = 1 → δ ∈ Op 2 (Cen t) := by
    intro δ hδL hδt hδ4
    obtain ⟨hδ₁, hδ₂⟩ := hδ δ hδL
    exact z_mem_op2 h4.char2 ht.ord (Subgroup.mem_centralizer_singleton_iff.mpr hδt)
      (hcommT δ ⟨2, by simpa using hδ4⟩ hδt hδ₁ hδ₂)
  have hδ₁T := hδT δ₁ hδ₁L hδ₁t hδ₁4
  have hδ₂T := hδT δ₂ hδ₂L hδ₂t hδ₂4
  obtain ⟨hyb₁, -, -⟩ := hβ' (b₁ * b₂) (Or.inl rfl) y hy
  exact main₁.2 δ₁ ⟨hδ₁T, Subgroup.mem_centralizer_singleton_iff.mpr (hδ δ₁ hδ₁L).1⟩ δ₂
    ⟨hδ₂T, Subgroup.mem_centralizer_singleton_iff.mpr (hδ δ₂ hδ₂L).1⟩ hδne y
    ⟨hy.1, Subgroup.mem_centralizer_singleton_iff.mpr hyb₁⟩ fun w hw => hyc w hw.1

end CFSG.RankThree.PartTwo.Sec21.FF79
