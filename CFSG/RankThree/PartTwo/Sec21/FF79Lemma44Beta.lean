module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Str
public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts

import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

private theorem card_closure_pair_le {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : x * y = y * x) : Nat.card (Subgroup.closure ({x, y} : Set G)) ≤ 9 := by
  have hx' : x⁻¹ = x ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']; exact hx
  have hy' : y⁻¹ = y ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']; exact hy
  have hc : ∀ i j : ℕ, Commute (x ^ i) (y ^ j) := fun i j =>
    (Commute.pow_pow (show Commute x y from hxy) i j)
  let S : Subgroup G :=
    { carrier := {g | ∃ i j : ℕ, g = x ^ i * y ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        refine ⟨i + k, j + l, ?_⟩
        rw [pow_add, pow_add]
        have := hc k j
        calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by
              simp only [mul_assoc]
          _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [this.eq]
          _ = x ^ i * x ^ k * (y ^ j * y ^ l) := by simp only [mul_assoc]
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨2 * i, 2 * j, ?_⟩
        rw [mul_inv_rev, ← inv_pow, ← inv_pow, hx', hy', ← pow_mul, ← pow_mul]
        exact ((hc _ _).eq).symm }
  have hle : Subgroup.closure ({x, y} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  let f : Fin 3 × Fin 3 → G := fun p => x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ)
  have hsub : (S : Set G) ⊆ Set.range f := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [f]
    conv_rhs => rw [← Nat.mod_add_div i 3, ← Nat.mod_add_div j 3]
    rw [pow_add, pow_add, pow_mul, pow_mul, hx, hy]
    simp
  calc Nat.card (Subgroup.closure ({x, y} : Set G))
      ≤ Nat.card (Set.range f) :=
        Nat.card_mono (Set.toFinite _) (fun g hg => hsub (hle hg))
    _ ≤ Nat.card (Fin 3 × Fin 3) := Finite.card_range_le f
    _ = 9 := by simp

private theorem B_basic {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    b ∈ B ∧ (∀ g ∈ B, g ^ 3 = 1) ∧ (∀ u ∈ B, ∀ v ∈ B, u * v = v * u) := by
  have hel := h4.mono.1.1
  refine ⟨?_, fun g hg => elemPow_eq_one_of_isElementaryAbelian g hg, fun u hu v hv => ?_⟩
  · rw [h4.mono.2.1]; exact Subgroup.subset_closure (by simp)
  · exact congrArg Subtype.val (Std.Commutative.comm (op := fun a b : B => a * b) (⟨u, hu⟩ : B) ⟨v, hv⟩)

private theorem b₁_b₂_mem {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    b₁ ∈ B ∧ b₂ ∈ B := ⟨h4.hb₁.1, h4.hb₂.1⟩

private theorem not_le_closure_pair {b : G} {J B : Subgroup G} {b₁ b₂ : G}
    (h4 : FF79Sec4 b J B b₁ b₂) {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    ¬ B ≤ Subgroup.closure ({x, y} : Set G) := by
  intro h
  obtain ⟨-, hpow, hcomm⟩ := B_basic h4
  have h1 := card_closure_pair_le (hpow x hx) (hpow y hy) (hcomm x hx y hy)
  have h2 := Subgroup.card_le_of_le h
  have h3 := h4.mono.1.2
  omega

private theorem B_orders {b : G} {J B : Subgroup G} {b₁ b₂ : G}
    (h4 : FF79Sec4 b J B b₁ b₂) :
    orderOf b₁ = 3 ∧ orderOf b₂ = 3 ∧ orderOf (b₁ * b₂) = 3 ∧ orderOf (b₁ ^ 2 * b₂) = 3 ∧
      b₂ ∉ Subgroup.zpowers b₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hbB, hpow, hcomm⟩ := B_basic h4
  obtain ⟨hb₁B, hb₂B⟩ := b₁_b₂_mem h4
  have hBeq := h4.mono.2.1
  have hnot : b₂ ∉ Subgroup.zpowers b₁ := by
    intro hmem
    refine not_le_closure_pair h4 hbB hb₁B ?_
    rw [hBeq, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have : Subgroup.zpowers b₁ ≤ Subgroup.closure ({b, b₁} : Set G) := by
        rw [Subgroup.zpowers_le]; exact Subgroup.subset_closure (by simp)
      exact this hmem
  have hb₁1 : b₁ ≠ 1 := by
    intro h1
    refine not_le_closure_pair h4 hbB hb₂B ?_
    rw [hBeq, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · rw [h1]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
  have hb₂1 : b₂ ≠ 1 := by
    intro h1; apply hnot; rw [h1]; exact Subgroup.one_mem _
  refine ⟨orderOf_eq_prime (hpow _ hb₁B) hb₁1, orderOf_eq_prime (hpow _ hb₂B) hb₂1,
    orderOf_eq_prime (hpow _ (B.mul_mem hb₁B hb₂B)) ?_,
    orderOf_eq_prime (hpow _ (B.mul_mem (B.pow_mem hb₁B 2) hb₂B)) ?_, hnot⟩
  · intro h1; apply hnot
    rw [eq_inv_of_mul_eq_one_right h1]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  · intro h1; apply hnot
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ 2)

private theorem exists_zpow_of_comm_A5 (hA5 : FF79KCentA5) {K : Subgroup G}
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

private theorem sq_of_comm_L3 (hL3 : FF79KCentL3) {L : Subgroup G}
    (e : L ≃* GL (Fin 3) (ZMod 2)) {s y : G} (hs : s ∈ L) (hy : y ∈ L)
    (hso : orderOf s = 2) (hc : y * s = s * y) : y ^ 2 = 1 ∨ y ^ 2 = s := by
  have ho' : orderOf (e ⟨s, hs⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hso
  have hc' : e ⟨y, hy⟩ * e ⟨s, hs⟩ = e ⟨s, hs⟩ * e ⟨y, hy⟩ := by
    rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext hc
  rcases hL3 _ _ ho' hc' with h | h
  · left
    have : (⟨y, hy⟩ : L) ^ 2 = 1 := e.injective (by rw [map_pow, h, map_one])
    simpa using congrArg Subtype.val this
  · right
    have : (⟨y, hy⟩ : L) ^ 2 = ⟨s, hs⟩ := e.injective (by rw [map_pow, h])
    simpa using congrArg Subtype.val this

private theorem a5_center :
    ∀ g : alternatingGroup (Fin 5), (∀ h : alternatingGroup (Fin 5), h * g = g * h) → g = 1 := by
  decide +kernel

private structure A5L3Dec (x b w : G) (X K L : Subgroup G) : Prop where
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

private theorem exists_dec {x b w : G} (hs : FF79CentA5L3 x b w) :
    ∃ X K L, A5L3Dec x b w X K L := by
  obtain ⟨X, K, L, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hs.exists_decomp
  exact ⟨X, K, L, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

private theorem cen_comm {x g : G} (hg : g ∈ Cen x) : x * g = g * x :=
  Subgroup.mem_centralizer_iff.mp hg x rfl

private theorem mem_cen_of {x g : G} (h : x * g = g * x) : g ∈ Cen x := by
  rw [Subgroup.mem_centralizer_iff]
  intro h' hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact h

private theorem mem_of_pow_mem {a : G} {H : Subgroup G} {N m : ℕ} (hN : a ^ N = 1)
    (hcop : Nat.Coprime m N) (h : a ^ m ∈ H) : a ∈ H := by
  have hd : orderOf a ∣ N := orderOf_dvd_of_pow_eq_one hN
  obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime (hcop.coprime_dvd_right hd)
  rw [← hs]
  exact H.pow_mem h s

private theorem pow_eq_one_of_dvd {a : G} {n N : ℕ} (ha : a ^ n = 1) (h : n ∣ N) : a ^ N = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul, ha, one_pow]

private theorem zpow_pow_eq_one {a : G} {n N : ℕ} (i : ℤ) (ha : a ^ n = 1) (h : n ∣ N) :
    (a ^ i) ^ N = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_eq_one_of_dvd ha h,
    one_zpow]

private theorem prod_pow_eq_one {x u k : G} {m : ℕ} (i : ℤ) (hx : x ^ 3 = 1) (hu : u ^ m = 1)
    (hk : k ^ 3 = 1) (hxu : x * u = u * x) (hxk : x * k = k * x) (huk : u * k = k * u) :
    (x ^ i * u * k) ^ (3 * m) = 1 := by
  have h1 : Commute (x ^ i) u := (show Commute x u from hxu).zpow_left i
  have h2 : Commute (x ^ i) k := (show Commute x k from hxk).zpow_left i
  have h3 : Commute u k := huk
  rw [(h2.mul_left h3 : Commute (x ^ i * u) k).mul_pow, h1.mul_pow,
    zpow_pow_eq_one i hx (dvd_mul_right 3 m), one_mul,
    pow_eq_one_of_dvd hu (dvd_mul_left m 3), pow_eq_one_of_dvd hk (dvd_mul_right 3 m), mul_one]

private theorem t_mem_L (hA5 : FF79KCentA5) {x b w t : G} {X K L : Subgroup G}
    (d : A5L3Dec x b w X K L) (hx3 : orderOf x = 3) (hw3 : orderOf w = 3)
    (ht2 : orderOf t = 2) (htx : t * x = x * t) (htw : t * w = w * t) : t ∈ L := by
  obtain ⟨eK⟩ := d.eK
  have hx3' : x ^ 3 = 1 := by simpa [hx3] using pow_orderOf_eq_one x
  have hw3' : w ^ 3 = 1 := by simpa [hw3] using pow_orderOf_eq_one w
  have ht2' : t ^ 2 = 1 := by simpa [ht2] using pow_orderOf_eq_one t
  obtain ⟨i, u, hu, k, hk, l, hl, ht⟩ := d.hdec t (mem_cen_of htx.symm)
  have hxu : x * u = u * x := cen_comm (d.hXx hu)
  have hxk : x * k = k * x := cen_comm (d.hKx hk)
  have hxl : x * l = l * x := cen_comm (d.hLx hl)
  have huk := d.hXK u hu k hk
  have hul := d.hXL u hu l hl
  have hkl := d.hKL k hk l hl
  have hwx : x * w = w * x := cen_comm (d.hKx d.hwK)
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
  obtain ⟨n, hn⟩ := exists_zpow_of_comm_A5 hA5 eK d.hwK hk hw3 hkw
  have hk3 : k ^ 3 = 1 := by
    rw [hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3', one_zpow]
  have hum : u ^ Nat.card X = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard X hu)
  have hN := prod_pow_eq_one i hx3' hum hk3 hxu hxk huk
  have hcomm : Commute (x ^ i * u * k) l :=
    ((((show Commute x l from hxl).zpow_left i).mul_left (show Commute u l from hul)).mul_left
      (show Commute k l from hkl))
  have hsq : (x ^ i * u * k) ^ 2 * l ^ 2 = 1 := by
    rw [← hcomm.mul_pow]; exact ht2'
  have hmem : (x ^ i * u * k) ^ 2 ∈ L := by
    rw [eq_inv_of_mul_eq_one_left hsq]; exact L.inv_mem (L.pow_mem hl 2)
  have hodd : Odd (3 * Nat.card X) := Odd.mul (by decide) d.hXodd
  have ha : x ^ i * u * k ∈ L :=
    mem_of_pow_mem hN (Nat.coprime_two_left.2 hodd) hmem
  exact L.mul_mem ha hl

private theorem Op_isPGroup (H : Subgroup G) : IsPGroup 2 (Op 2 H) :=
  (CFSG.pCore_isPGroup (p := 2) (G := H)).map H.subtype

private theorem Op_le_cen {t : G} {y : G} (hy : y ∈ Op 2 (Cen t)) : t * y = y * t := by
  obtain ⟨y', -, rfl⟩ := Subgroup.mem_map.mp hy
  exact cen_comm y'.2

private theorem Op_conj_mem {p : ℕ} {H : Subgroup G} {g z : G} (hg : g ∈ H)
    (hz : z ∈ Op p H) : g * z * g⁻¹ ∈ Op p H := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (CFSG.pCore_normal (p := p) (G := H)).conj_mem z' hz' ⟨g, hg⟩

private theorem T_inf_K_trivial {T K : Subgroup G} (hT : IsPGroup 2 T)
    (hnorm : ∀ k ∈ K, ∀ z ∈ T, k * z * k⁻¹ ∈ T) (eK : K ≃* alternatingGroup (Fin 5))
    {w : G} (hw : w ∈ K) (hw3 : orderOf w = 3) : ∀ c ∈ T ⊓ K, c = 1 := by
  haveI : IsSimpleGroup K := eK.isSimpleGroup
  let N : Subgroup K := (T ⊓ K).subgroupOf K
  haveI : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hnorm g g.2 n hn.1, K.mul_mem (K.mul_mem g.2 n.2) (K.inv_mem g.2)⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · intro c hc
    have : (⟨c, hc.2⟩ : K) ∈ N := Subgroup.mem_subgroupOf.mpr hc
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  · exfalso
    have : (⟨w, hw⟩ : K) ∈ N := by rw [h]; exact Subgroup.mem_top _
    have hwT : w ∈ T := (Subgroup.mem_subgroupOf.mp this).1
    obtain ⟨n, hn⟩ := hT ⟨w, hwT⟩
    have h1 : w ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have h2 : 3 ∣ 2 ^ n := hw3 ▸ orderOf_dvd_of_pow_eq_one h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega

private theorem beta_aux (hA5 : FF79KCentA5) (hL3 : FF79KCentL3) {x b w t b₁ b₂ : G}
    (cs : FF79CentA5L3 x b w) (hx3 : orderOf x = 3) (hw3 : orderOf w = 3)
    (ht2 : orderOf t = 2) (htx : t * x = x * t) (htw : t * w = w * t)
    (hgen : ∀ z : G, z * x = x * z → z * w = w * z → z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z)
    {y : G} (hy : y ∈ Op 2 (Cen t) ⊓ Cen x) :
    y * b₁ = b₁ * y ∧ y * b₂ = b₂ * y ∧ y ^ 2 ∈ Subgroup.zpowers t := by
  obtain ⟨X, K, L, d⟩ := exists_dec cs
  obtain ⟨eK⟩ := d.eK
  obtain ⟨eL⟩ := d.eL
  have hx3' : x ^ 3 = 1 := by simpa [hx3] using pow_orderOf_eq_one x
  have htL : t ∈ L := t_mem_L hA5 d hx3 hw3 ht2 htx htw
  have hKcen : ∀ k' ∈ K, k' ∈ Cen t := fun k' hk' => mem_cen_of (d.hKL k' hk' t htL).symm
  obtain ⟨hyT, hyx⟩ := hy
  obtain ⟨i, u, hu, k, hk, l, hl, hyeq⟩ := d.hdec y hyx
  obtain ⟨a, ha_def⟩ : ∃ a : G, a = x ^ i * u := ⟨_, rfl⟩
  have hyeq' : y = a * k * l := by rw [hyeq, ha_def]
  have hxu : x * u = u * x := cen_comm (d.hXx hu)
  have hac : ∀ v ∈ K, a * v = v * a := by
    intro v hv
    rw [ha_def]
    have h1 : Commute (x ^ i) v := (show Commute x v from cen_comm (d.hKx hv)).zpow_left i
    exact (h1.mul_left (show Commute u v from d.hXK u hu v hv)).eq
  have hal : a * l = l * a := by
    rw [ha_def]
    have h1 : Commute (x ^ i) l := (show Commute x l from cen_comm (d.hLx hl)).zpow_left i
    exact (h1.mul_left (show Commute u l from d.hXL u hu l hl)).eq
  have ha1 : a ^ (3 * Nat.card X) = 1 := by
    have hum : u ^ Nat.card X = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard X hu)
    have := prod_pow_eq_one (k := 1) i hx3' hum (one_pow 3) hxu (by simp) (by simp)
    rw [mul_one] at this
    rwa [ha_def]
  have hodd : Odd (3 * Nat.card X) := Odd.mul (by decide) d.hXodd
  have hcomp : ∀ k' ∈ K, k' * y * k'⁻¹ * y⁻¹ = k' * k * k'⁻¹ * k⁻¹ := by
    intro k' hk'
    have h1 : k' * a = a * k' := (hac k' hk').symm
    have h2 : k'⁻¹ * l = l * k'⁻¹ := (show Commute k' l from d.hKL k' hk' l hl).inv_left.eq
    have hcK : k' * k * k'⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hk' hk) (K.inv_mem hk')) (K.inv_mem hk)
    have hm := hac _ hcK
    have e1 : k' * (a * k * l) * k'⁻¹ = a * (k' * k * k'⁻¹) * l := by
      calc k' * (a * k * l) * k'⁻¹ = (k' * a) * k * (l * k'⁻¹) := by simp only [mul_assoc]
        _ = (a * k') * k * (k'⁻¹ * l) := by rw [h1, h2]
        _ = a * (k' * k * k'⁻¹) * l := by simp only [mul_assoc]
    rw [hyeq', e1]
    calc a * (k' * k * k'⁻¹) * l * (a * k * l)⁻¹
        = a * (k' * k * k'⁻¹ * k⁻¹) * a⁻¹ := by group
      _ = k' * k * k'⁻¹ * k⁻¹ := by rw [hm]; simp
  have hkcomm : ∀ k' ∈ K, k' * k = k * k' := by
    intro k' hk'
    have hcT : k' * y * k'⁻¹ * y⁻¹ ∈ Op 2 (Cen t) :=
      (Op 2 (Cen t)).mul_mem (Op_conj_mem (hKcen k' hk') hyT) ((Op 2 (Cen t)).inv_mem hyT)
    rw [hcomp k' hk'] at hcT
    have hcK : k' * k * k'⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem hk' hk) (K.inv_mem hk')) (K.inv_mem hk)
    have := T_inf_K_trivial (Op_isPGroup (Cen t))
      (fun k'' hk'' z hz => Op_conj_mem (hKcen k'' hk'') hz) eK d.hwK hw3 _ ⟨hcT, hcK⟩
    rwa [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
  have hk1 : k = 1 := by
    have := a5_center (eK ⟨k, hk⟩) (fun h => by
      obtain ⟨h', rfl⟩ := eK.surjective h
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hkcomm h'.1 h'.2))
    have h2 : (⟨k, hk⟩ : K) = 1 := by simpa using this
    simpa using congrArg Subtype.val h2
  subst hk1
  rw [mul_one] at hyeq'
  obtain ⟨n, hn⟩ := Op_isPGroup (Cen t) ⟨y, hyT⟩
  have hyn : y ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hcomm : Commute a l := hal
  have hsq : a ^ (2 ^ n) * l ^ (2 ^ n) = 1 := by
    rw [← hcomm.mul_pow, ← hyeq']; exact hyn
  have hmem : a ^ (2 ^ n) ∈ L := by
    rw [eq_inv_of_mul_eq_one_left hsq]; exact L.inv_mem (L.pow_mem hl _)
  have haL : a ∈ L :=
    mem_of_pow_mem ha1 (Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd)) hmem
  have hyL : y ∈ L := by rw [hyeq']; exact L.mul_mem haL hl
  have hyw : y * w = w * y := (d.hKL w d.hwK y hyL).symm
  have hyx' : y * x = x * y := (cen_comm hyx).symm
  obtain ⟨hb₁, hb₂⟩ := hgen y hyx' hyw
  refine ⟨hb₁, hb₂, ?_⟩
  rcases sq_of_comm_L3 hL3 eL htL hyL ht2 (Op_le_cen hyT).symm with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h]; exact Subgroup.mem_zpowers t

private theorem gen_βγ {z b₁ b₂ : G} (h1 : Commute z (b₁ * b₂))
    (h2 : Commute z (b₁ ^ 2 * b₂)) : z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z := by
  have e1 : b₁ = (b₁ ^ 2 * b₂) * (b₁ * b₂)⁻¹ := by group
  have c1 : Commute z b₁ := by rw [e1]; exact h2.mul_right h1.inv_right
  refine ⟨c1.eq, ?_⟩
  have e2 : b₂ = b₁⁻¹ * (b₁ * b₂) := by group
  have c2 : Commute z b₂ := by rw [e2]; exact c1.inv_right.mul_right h1
  exact c2.eq

private theorem gen_γβ {z b₁ b₂ : G} (h1 : Commute z (b₁ ^ 2 * b₂))
    (h2 : Commute z (b₁ * b₂)) : z * b₁ = b₁ * z ∧ z * b₂ = b₂ * z :=
  gen_βγ h2 h1

private theorem t_comm_words {b₁ b₂ t : G} (h1 : t * b₁ = b₁ * t) (h2 : t * b₂ = b₂ * t) :
    t * (b₁ * b₂) = (b₁ * b₂) * t ∧ t * (b₁ ^ 2 * b₂) = (b₁ ^ 2 * b₂) * t := by
  have c1 : Commute t b₁ := h1
  have c2 : Commute t b₂ := h2
  exact ⟨(c1.mul_right c2).eq, (((c1.pow_right 2)).mul_right c2).eq⟩

theorem ff79_4_4Beta_of (hstr : FF79_4_3Str) (hA5 : FF79KCentA5) (hL3 : FF79KCentL3) :
    FF79_4_4Beta := by
  intro G _ _ b J B b₁ b₂ h4 t inv x hx y hy
  have hS := hstr G b J B b₁ b₂ h4
  obtain ⟨-, -, hβo, hγo, -⟩ := B_orders h4
  obtain ⟨htβ, htγ⟩ := t_comm_words inv.comm₁ inv.comm₂
  rcases hx with rfl | rfl
  · exact beta_aux hA5 hL3 hS.centβ hβo hγo inv.ord htβ htγ
      (fun z hzx hzw => gen_βγ (show Commute z _ from hzx) (show Commute z _ from hzw)) hy
  · exact beta_aux hA5 hL3 hS.centγ hγo hβo inv.ord htγ htβ
      (fun z hzx hzw => gen_γβ (show Commute z _ from hzx) (show Commute z _ from hzw)) hy

@[expose] def FF79_KleJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (J B : Subgroup G) (b₁ b₂ : G),
    FF79Sec4 b J B b₁ b₂ → ∀ K : Subgroup G, K ≤ Cen b →
      Nonempty (K ≃* alternatingGroup (Fin 5)) → K ≤ J

private theorem a5_order5 : ∃ g : alternatingGroup (Fin 5), orderOf g = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hs : Equiv.Perm.sign (finRotate 5) = 1 := by decide +kernel
  have h5 : (finRotate 5) ^ 5 = 1 := by decide +kernel
  have h1 : (finRotate 5 : Equiv.Perm (Fin 5)) ≠ 1 := by decide +kernel
  refine ⟨⟨finRotate 5, Equiv.Perm.mem_alternatingGroup.2 hs⟩, orderOf_eq_prime ?_ ?_⟩
  · exact Subtype.ext (by simpa using h5)
  · intro h
    exact h1 (by simpa using congrArg Subtype.val h)

private theorem conj_mem_J {b t : G} {J : Subgroup G} (hstd : FFStandardJ b J) {b₁ : G}
    (hb₁J : b₁ ∈ J) (hb₁o : orderOf b₁ = 3) (htt : t * t = 1) (htb : t * b * t⁻¹ = b⁻¹) :
    ∀ j ∈ J, t * j * t ∈ J := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [hti] at htb
  have hb2 : t * b⁻¹ * t = b := by
    calc t * b⁻¹ * t = t * (t * b * t) * t := by rw [htb]
      _ = (t * t) * b * (t * t) := by simp only [mul_assoc]
      _ = b := by rw [htt, one_mul, mul_one]
  have hCmem : ∀ c ∈ Cen b, t * c * t ∈ Cen b := by
    intro c hc
    have h : Commute c b⁻¹ := (show Commute b c from cen_comm hc).symm.inv_right
    have h2 := h.map (MulAut.conj t)
    simp only [MulAut.conj_apply, hti, hb2] at h2
    exact mem_cen_of h2.symm.eq
  have hconj : ∀ c d : G, t * (c * d) * t = (t * c * t) * (t * d * t) := by
    intro c d
    calc t * (c * d) * t = t * c * (t * t) * d * t := by rw [htt]; simp only [mul_one, mul_assoc]
      _ = (t * c * t) * (t * d * t) := by simp only [mul_assoc]
  have hinv : ∀ c : G, t * (t * c * t) * t = c := by
    intro c
    calc t * (t * c * t) * t = (t * t) * c * (t * t) := by simp only [mul_assoc]
      _ = c := by rw [htt, one_mul, mul_one]
  let φ : ↥(Cen b) ≃* ↥(Cen b) :=
    { toFun := fun c => ⟨t * c * t, hCmem c c.2⟩
      invFun := fun c => ⟨t * c * t, hCmem c c.2⟩
      left_inv := fun c => Subtype.ext (hinv c)
      right_inv := fun c => Subtype.ext (hinv c)
      map_mul' := fun c d => Subtype.ext (hconj c d) }
  have hcomp : CFSG.IsComponent (J.subgroupOf (Cen b)) := hstd.2.1
  have hcomp' := CFSG.LocalCores.isComponent_map_mulEquiv φ hcomp
  have hb₁C : b₁ ∈ Cen b := hstd.1 hb₁J
  have hmem : (⟨b₁, hb₁C⟩ : ↥(Cen b)) ∈ J.subgroupOf (Cen b) := hb₁J
  have hdvd : 3 ∣ Nat.card (J.subgroupOf (Cen b)) := by
    have := Subgroup.orderOf_dvd_natCard (J.subgroupOf (Cen b)) hmem
    rwa [Subgroup.orderOf_mk, hb₁o] at this
  have hdvd' : 3 ∣ Nat.card ((J.subgroupOf (Cen b)).map φ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective φ.injective]
  have heq := hstd.2.2 _ hcomp' hdvd'
  intro j hj
  have hjC : j ∈ Cen b := hstd.1 hj
  have hjK : (⟨j, hjC⟩ : ↥(Cen b)) ∈ J.subgroupOf (Cen b) := hj
  have : φ ⟨j, hjC⟩ ∈ (J.subgroupOf (Cen b)).map φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, hjK, rfl⟩
  rw [heq] at this
  exact this

theorem ff79_4_4J_of (hstr : FF79_4_3Str) (hA5 : FF79KCentA5) (hAut : FF79KAutL5)
    (hKJ : FF79_KleJ) : FF79_4_4J := by
  intro G _ _ b J B b₁ b₂ h4 t inv
  have hS := hstr G b J B b₁ b₂ h4
  obtain ⟨hb₁o, hb₂o, hβo, hγo, hnot⟩ := B_orders h4
  have ht2 := inv.ord
  have htt : t * t = 1 := by simpa [ht2, pow_two] using pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨htβ, htγ⟩ := t_comm_words inv.comm₁ inv.comm₂
  obtain ⟨X, K, L, d⟩ := exists_dec hS.centβ
  obtain ⟨eK⟩ := d.eK
  have htL := t_mem_L hA5 d hβo hγo ht2 htβ htγ
  have hKt : ∀ k ∈ K, t * k = k * t := fun k hk => (d.hKL k hk t htL).symm
  have hKb : K ≤ Cen b := fun k hk => mem_cen_of (d.hKL k hk b d.hbL).symm
  have hKJ' : K ≤ J := hKJ G b J B b₁ b₂ h4 K hKb ⟨eK⟩
  obtain ⟨g5, hg5⟩ := a5_order5
  have hρK : ((eK.symm g5 : K) : G) ∈ K := (eK.symm g5).2
  set ρ : G := ((eK.symm g5 : K) : G) with hρdef
  have hρo : orderOf ρ = 5 := by
    rw [hρdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg5]
  have hρJ : ρ ∈ J := hKJ' hρK
  have hρx : ρ * (b₁ * b₂) = (b₁ * b₂) * ρ := (cen_comm (d.hKx hρK)).symm
  have hρt : t * ρ * t = ρ := by
    rw [hKt ρ hρK, mul_assoc, htt, mul_one]
  have hb₁J : b₁ ∈ J := h4.hb₁.2
  have hb₂J : b₂ ∈ J := h4.hb₂.2
  have hJc := conj_mem_J h4.hyp.std hb₁J hb₁o htt inv.inv
  have hinv : ∀ c : G, t * (t * c * t) * t = c := by
    intro c
    calc t * (t * c * t) * t = (t * t) * c * (t * t) := by simp only [mul_assoc]
      _ = c := by rw [htt, one_mul, mul_one]
  have hconj : ∀ c d : G, t * (c * d) * t = (t * c * t) * (t * d * t) := by
    intro c d
    calc t * (c * d) * t = t * c * (t * t) * d * t := by rw [htt]; simp only [mul_one, mul_assoc]
      _ = (t * c * t) * (t * d * t) := by simp only [mul_assoc]
  let φJ : ↥J ≃* ↥J :=
    { toFun := fun j => ⟨t * j * t, hJc j j.2⟩
      invFun := fun j => ⟨t * j * t, hJc j j.2⟩
      left_inv := fun j => Subtype.ext (hinv j)
      right_inv := fun j => Subtype.ext (hinv j)
      map_mul' := fun c d => Subtype.ext (hconj c d) }
  obtain ⟨e⟩ := hS.equivJ
  let φ : MulAut (GL (Fin 5) (ZMod 2)) := (e.symm.trans φJ).trans e
  have hφ : ∀ j : ↥J, φ (e j) = e (φJ j) := fun j => by
    show e (φJ (e.symm (e j))) = e (φJ j)
    rw [e.symm_apply_apply]
  have hφφ : φ * φ = 1 := by
    ext y
    obtain ⟨j, rfl⟩ := e.surjective y
    rw [MulAut.mul_apply, hφ, hφ, MulAut.one_apply]
    have h : φJ (φJ j) = j := Subtype.ext (hinv j)
    rw [h]
  have hfix : ∀ (z : G) (hz : z ∈ J), t * z * t = z → φ (e ⟨z, hz⟩) = e ⟨z, hz⟩ := by
    intro z hz h
    rw [hφ]
    exact congrArg e (Subtype.ext h)
  have hfix' : ∀ z : G, t * z = z * t → t * z * t = z := fun z h => by
    rw [h, mul_assoc, htt, mul_one]
  have hcomm₁₂ : b₁ * b₂ = b₂ * b₁ := (B_basic h4).2.2 b₁ h4.hb₁.1 b₂ h4.hb₂.1
  have hφ1 : φ = 1 := by
    refine hAut φ hφφ (e ⟨b₁, hb₁J⟩) (e ⟨b₂, hb₂J⟩) (e ⟨ρ, hρJ⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hb₁o
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hb₂o
    · rw [← map_mul, ← map_mul]; exact congrArg e (Subtype.ext hcomm₁₂)
    · intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hnot
      have : (⟨b₁, hb₁J⟩ : ↥J) ^ n = ⟨b₂, hb₂J⟩ := e.injective (by rw [map_zpow]; exact hn)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val this⟩
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hρo
    · simp only [← map_mul]
      exact congrArg e (Subtype.ext (by simpa using hρx))
    · exact hfix _ hb₁J (hfix' _ inv.comm₁)
    · exact hfix _ hb₂J (hfix' _ inv.comm₂)
    · exact hfix _ hρJ hρt
  intro j hj
  have h1 : φ (e ⟨j, hj⟩) = e ⟨j, hj⟩ := by rw [hφ1, MulAut.one_apply]
  rw [hφ] at h1
  have h2 : t * j * t = j := congrArg Subtype.val (e.injective h1)
  apply mem_cen_of
  calc t * j = t * j * t * t := by rw [mul_assoc _ t t, htt, mul_one]
    _ = j * t := by rw [h2]

end CFSG.RankThree.PartTwo.Sec21.FF79
