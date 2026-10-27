module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Pick
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace Lem20Coprime

section Arith

theorem false_of_coprime_odd_dvd {N p a b : ℕ}
    (hN : ∀ r : ℕ, r.Prime → r ∣ N → r = 2 ∨ r = p) (ha : a ∣ N) (hb : b ∣ N) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hao : Odd a) (hbo : Odd b) (hab : Nat.Coprime a b) : False := by
  have hr : ∀ c : ℕ, c ∣ N → c ≠ 1 → Odd c → c.minFac = p := by
    intro c hc hc1 hco
    rcases hN _ (Nat.minFac_prime hc1) ((Nat.minFac_dvd c).trans hc) with h2 | hp
    · exfalso
      have h2c : 2 ∣ c := by
        rw [← h2]
        exact Nat.minFac_dvd c
      exact Nat.not_even_iff_odd.mpr hco (even_iff_two_dvd.mpr h2c)
    · exact hp
  have hpa : p ∣ a := by
    rw [← hr a ha ha1 hao]
    exact Nat.minFac_dvd a
  have hpb : p ∣ b := by
    rw [← hr b hb hb1 hbo]
    exact Nat.minFac_dvd b
  have hpp : p.Prime := by
    rw [← hr a ha ha1 hao]
    exact Nat.minFac_prime ha1
  have h1 := Nat.dvd_gcd hpa hpb
  rw [hab] at h1
  exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hx : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_succ]
  exact ⟨2 ^ k - 1, by omega⟩

theorem sq_sub_one_eq {x : ℕ} (hx : 1 ≤ x) : x ^ 2 - 1 = (x - 1) * (x + 1) := by
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le' hx
  have e : (y + 1) ^ 2 = y * (y + 1 + 1) + 1 := by ring
  rw [e, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem false_of_isPSL_two_two {X : Type} [Group X] {n p : ℕ} (h : IsPSL 2 2 n X)
    (hX : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → r = 2 ∨ r = p) : False := by
  have hn : 1 < n := by
    obtain ⟨⟨-, hf, -, hne, -⟩, -⟩ := h
    by_contra hn
    have h1 : n = 1 := by omega
    subst h1
    exact hne (by simp)
  have hodd : Odd (2 ^ n - 1) := odd_two_pow_sub_one (by omega)
  have hc := Vol2.Ch11.SecA.card_of_isPSL (by norm_num) h
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [hg, Nat.div_one, Finset.Icc_self, Finset.prod_singleton] at hc
  norm_num at hc
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hfac := sq_sub_one_eq (x := 2 ^ n) (by omega)
  refine false_of_coprime_odd_dvd hX (a := 2 ^ n - 1) (b := 2 ^ n + 1) ?_ ?_ (by omega)
    (by omega) hodd ?_ ?_
  · rw [hc, hfac]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  · rw [hc, hfac]
    exact Dvd.dvd.mul_left (dvd_mul_left _ _) _
  · exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  · have e : 2 ^ n + 1 = 2 + (2 ^ n - 1) := by omega
    rw [e, Nat.coprime_add_self_right]
    exact (Nat.coprime_two_left.mpr hodd).symm

theorem false_of_isSz {X : Type} [Group X] {n p : ℕ}
    (h : IsSz n X) (hX : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → r = 2 ∨ r = p) : False := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  subst hf
  have hc : Nat.card X =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  set q := 2 ^ (2 * a + 1) with hq
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqe : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd1 : Odd (q - 1) := by
    obtain ⟨r, hr⟩ := hqe
    exact ⟨r - 1, by omega⟩
  have hodd2 : Odd (q ^ 2 + 1) := (Nat.even_pow.mpr ⟨hqe, two_ne_zero⟩).add_one
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  refine false_of_coprime_odd_dvd hX (a := q - 1) (b := q ^ 2 + 1) ?_ ?_ (by omega) (by omega)
    hodd1 hodd2 ?_
  · rw [hc]
    exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
  · rw [hc]
    exact dvd_mul_left _ _
  · have e : q ^ 2 + 1 = 2 + (q + 1) * (q - 1) := by
      rw [mul_comm, ← sq_sub_one_eq (by omega)]
      omega
    rw [e, Nat.coprime_add_mul_right_right]
    exact (Nat.coprime_two_left.mpr hodd1).symm

end Arith

section Group

variable {G : Type} [Group G]

theorem mem_normalizer_conjugate_iff {V : Subgroup G} {g h : G} :
    g ∈ Subgroup.normalizer (CFSG.conjugate V h : Set G) ↔
      h * g * h⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
  simp only [Subgroup.mem_normalizer_iff, Lem21Post.mem_conjugate_iff]
  constructor
  · intro H w
    have h1 := H (h⁻¹ * w * h)
    have e1 : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
    have e2 : h * (g * (h⁻¹ * w * h) * g⁻¹) * h⁻¹ = h * g * h⁻¹ * w * (h * g * h⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  · intro H y
    have h1 := H (h * y * h⁻¹)
    have e2 : h * g * h⁻¹ * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ = h * (g * y * g⁻¹) * h⁻¹ := by
      group
    rw [e2] at h1
    exact h1

theorem eq_one_of_pow_four {h : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hhp : h ^ p = 1)
    (h4 : h ^ 4 = 1) : h = 1 := by
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hhp) (orderOf_dvd_of_pow_eq_one h4)
  have hc : Nat.gcd p 4 = 1 := by
    have := Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    simpa using this
  rw [hc] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem mem_of_sq_mem {K : Subgroup G} {h : G} {p : ℕ} (hpodd : Odd p) (hhp : h ^ p = 1)
    (h2 : h ^ 2 ∈ K) : h ∈ K := by
  obtain ⟨k, hk⟩ := hpodd
  have e : h = (h ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    calc h = h ^ (p + 1) := by rw [pow_succ, hhp, one_mul]
      _ = h ^ (2 * (k + 1)) := by rw [hk]; ring_nf
  rw [e]
  exact K.pow_mem h2 _

theorem inv_conj_pow (a b : G) (n : ℕ) : (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  have e : ∀ c : G, a⁻¹ * c * a = a⁻¹ * c * a⁻¹⁻¹ := fun c => by rw [inv_inv]
  rw [e, e, conj_pow]

variable [Finite G]

theorem exists_conj_mem_of_pi {H P T : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = p) (hPp : IsPGroup p ↥P)
    (hPH : P ≤ H) (hPi : ¬ p ∣ P.relIndex H) (hT2 : IsPGroup 2 ↥T) (hTH : T ≤ H)
    (hTi : ¬ 2 ∣ T.relIndex H) {x : G} (hxH : x ∈ H) (hxp : x ^ p = 1) :
    ∃ t ∈ T, t⁻¹ * x * t ∈ P := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' := P.subgroupOf H with hP'
  set T' := T.subgroupOf H with hT'
  have hP'p : IsPGroup p ↥P' := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hT'p : IsPGroup 2 ↥T' := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hidx2 : ∀ {r : ℕ}, r.Prime → r ∣ P'.index → r = 2 := by
    intro r hr hrd
    rcases hZ r hr (hrd.trans (Subgroup.index_dvd_card P')) with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ hrd) hPi
  have hidxpow := Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite hidx2
  set k := P'.index.primeFactorsList.length
  set TS : Sylow 2 ↥H := hT'p.toSylow hTi
  have hk : 2 ^ k ∣ Nat.card ↥T' := by
    have := TS.pow_dvd_card_of_pow_dvd_card (n := k) (by
      rw [← hidxpow]
      exact Subgroup.index_dvd_card P')
    exact this
  have hcop : Nat.Coprime (Nat.card ↥T') (Nat.card ↥P') := by
    obtain ⟨a, ha⟩ := hT'p.exists_card_eq
    obtain ⟨b, hb⟩ := hP'p.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hcard : Nat.card ↥T' * Nat.card ↥P' = Nat.card ↥H := by
    have h1 : Nat.card ↥P' * P'.index = Nat.card ↥H := Subgroup.card_mul_index P'
    have h2 : Nat.card ↥T' ∣ P'.index := by
      have h3 : Nat.card ↥T' ∣ Nat.card ↥P' * P'.index := by
        rw [h1]
        exact Subgroup.card_subgroup_dvd_card T'
      exact hcop.dvd_of_dvd_mul_left h3
    have h3 : P'.index ∣ Nat.card ↥T' := by
      rw [hidxpow]
      exact hk
    rw [Nat.dvd_antisymm h2 h3, mul_comm, h1]
  have hc : T'.IsComplement' P' := Subgroup.isComplement'_of_coprime hcard hcop
  set PS : Sylow p ↥H := hP'p.toSylow hPi
  set x' : ↥H := ⟨x, hxH⟩
  have hx'p : x' ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hzp : IsPGroup p ↥(Subgroup.zpowers x') := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx'p, one_zpow]
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H PS Q
  have hxQ : x' ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have hxP : g⁻¹ * x' * g ∈ P' := by
    have e : (MulAut.conj g)⁻¹ • x' = g⁻¹ * x' * g := by
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [← e]
    exact hxQ
  obtain ⟨⟨⟨t', ht'⟩, ⟨q', hq'⟩⟩, htq⟩ := hc.2 g
  simp only at htq
  have hmem : t'⁻¹ * x' * t' ∈ P' := by
    have e : t'⁻¹ * x' * t' = q' * (g⁻¹ * x' * g) * q'⁻¹ := by
      rw [← htq]
      group
    rw [e]
    exact P'.mul_mem (P'.mul_mem hq' hxP) (P'.inv_mem hq')
  refine ⟨(t' : G), Subgroup.mem_subgroupOf.mp ht', ?_⟩
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa using this

end Group

end Lem20Coprime

open Lem20Coprime Lem20Pick in
theorem coprimePick_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h325 : Stmt3_2_5) (h1216 : Stmt12_2_16) (h12218 : Stmt12_2_18)
    (hI62 : ASInputs.AS_I_6_2_twoCases) : CoprimePick := by
  intro G _ _ T L V H P p hyp hNE hHs hsolv hp hp2 hPp hPH hPi hHPT hΦ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hV2' := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => by
    simpa using congrArg Subtype.val (hV2' ⟨x, hx⟩)
  have hinv2 : ∀ {y : G}, y ^ 2 = 1 → y⁻¹ = y := fun hy =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hy])
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (hinv2 (hV2 _ (V.mul_mem hx hy))).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv2 (hV2 y hy), hinv2 (hV2 x hx)]
  have hcV : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVc a a.2 b b.2)⟩⟩
  have hVe : IsElemAbelian 2 V := ⟨hcV, hV2⟩
  have hTH : T ≤ H := hHs.1.1
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hZ : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = p := by
    obtain ⟨q, -, -, hZq⟩ :=
      (Lem7.minParabolic h331 hyp hHs).subgroupOf.exists_odd_prime_of_solvable hsolv
    have hP1 : P ≠ ⊥ := by
      intro h0
      apply hHs.2.1
      rw [hHPT, h0, bot_sup_eq]
      exact hTM
    have hpH : p ∣ Nat.card H := by
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := hPp.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact hP1 (Subgroup.eq_bot_of_card_eq P hk)
      have h1 : Nat.card P ∣ Nat.card H := Subgroup.card_dvd_of_le hPH
      rw [hk] at h1
      exact (dvd_pow_self p hk0).trans h1
    have hpq : p = q := (hZq p hp hpH).resolve_left hp2
    intro r hr hrH
    rw [hpq]
    exact hZq r hr hrH
  obtain ⟨v₀, hv₀V, hv₀O⟩ := IsConcreteLE.not_le_iff_exists.mp (h12218 G T L V hyp hNE H hHs)
  have hv₀H : v₀ ∈ H := hTH (hVT hv₀V)
  have hv₀1 : v₀ ≠ 1 := fun h0 => hv₀O (h0 ▸ Subgroup.one_mem _)
  obtain ⟨y, hyH, hy1, hyodd, hyinv⟩ :
      ∃ y ∈ H, y ≠ 1 ∧ Odd (orderOf y) ∧ v₀ * y * v₀⁻¹ = y⁻¹ := by
    set w : ↥H := ⟨v₀, hv₀H⟩
    have hw2 : w ^ 2 = 1 := Subtype.ext (by simpa using hV2 v₀ hv₀V)
    have hw1 : w ≠ 1 := fun h0 => hv₀1 (congrArg Subtype.val h0)
    have hcard : Nat.card (Subgroup.zpowers w) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hw2 hw1]
    have hnot : ¬ Subgroup.zpowers w ≤ CFSG.Open.pCore 2 ↥H := fun hle =>
      hv₀O ⟨w, hle (Subgroup.mem_zpowers w), rfl⟩
    obtain ⟨y, hy1, hyo, hyi⟩ := baer_suzuki_involution hcard hnot
    refine ⟨y, y.2, fun h0 => hy1 (Subtype.ext h0), by rwa [Subgroup.orderOf_coe], ?_⟩
    simpa using congrArg Subtype.val (hyi w (Subgroup.mem_zpowers w) hw1)
  have hpy : p ∣ orderOf y := by
    have hy1' : orderOf y ≠ 1 := fun h0 => hy1 (orderOf_eq_one_iff.mp h0)
    have hdvd : orderOf y ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hyH
    rcases hZ _ (Nat.minFac_prime hy1') ((Nat.minFac_dvd _).trans hdvd) with h2 | h2
    · exfalso
      have h2y : 2 ∣ orderOf y := by
        rw [← h2]
        exact Nat.minFac_dvd _
      exact Nat.not_even_iff_odd.mpr hyodd (even_iff_two_dvd.mpr h2y)
    · rw [← h2]
      exact Nat.minFac_dvd _
  set h₀ := y ^ (orderOf y / p) with hh₀
  have hoh₀ : orderOf h₀ = p := orderOf_pow_orderOf_div (orderOf_pos y).ne' hpy
  have hh₀H : h₀ ∈ H := H.pow_mem hyH _
  have hh₀p : h₀ ^ p = 1 := by
    rw [← hoh₀]
    exact pow_orderOf_eq_one h₀
  have hh₀inv : v₀ * h₀ * v₀⁻¹ = h₀⁻¹ := by rw [hh₀, ← conj_pow, hyinv, inv_pow]
  have hTi : ¬ 2 ∣ T.relIndex H := (isSylowTwoOf_of_isSylowTwo hyp.sylow hTH).2.2
  obtain ⟨t, htT, htP⟩ :=
    exists_conj_mem_of_pi hp hp2 hZ hPp hPH hPi hyp.sylow.1 hTH hTi hh₀H hh₀p
  set h := t⁻¹ * h₀ * t with hh
  set v := t⁻¹ * v₀ * t with hv
  have hvV : v ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem htT)) v₀).mp hv₀V
    simpa using this
  have hhH : h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem (hTH htT)) hh₀H) (hTH htT)
  have hhp : h ^ p = 1 := by rw [hh, inv_conj_pow, hh₀p, mul_one, inv_mul_cancel]
  have hh1 : h ≠ 1 := by
    intro h0
    have h0' : h₀ = 1 := by
      have e : h₀ = t * h * t⁻¹ := by rw [hh]; group
      rw [e, h0, mul_one, mul_inv_cancel]
    rw [h0', orderOf_one] at hoh₀
    exact hp.one_lt.ne hoh₀
  have hvh : v * h * v⁻¹ = h⁻¹ := by
    calc v * h * v⁻¹ = t⁻¹ * (v₀ * h₀ * v₀⁻¹) * t := by rw [hv, hh]; group
      _ = h⁻¹ := by rw [hh₀inv, hh]; group
  have hv2 : v ^ 2 = 1 := hV2 v hvV
  have hvinv : v⁻¹ = v := hinv2 hv2
  have hvh' : v * h⁻¹ * v = h := by
    calc v * h⁻¹ * v = v * h⁻¹ * v⁻¹ := by rw [hvinv]
      _ = (v * h * v⁻¹)⁻¹ := by group
      _ = h := by rw [hvh, inv_inv]
  have hhN : h ∉ Subgroup.normalizer (V : Set G) := by
    intro hN
    have h1 : h * v⁻¹ * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hN _).mp (V.inv_mem hvV)
    have h2 : v * (h * v⁻¹ * h⁻¹) ∈ V := V.mul_mem hvV h1
    have e : v * (h * v⁻¹ * h⁻¹) = h⁻¹ * h⁻¹ := by
      calc v * (h * v⁻¹ * h⁻¹) = (v * h * v⁻¹) * h⁻¹ := by group
        _ = h⁻¹ * h⁻¹ := by rw [hvh]
    rw [e] at h2
    have h3 := hV2 _ h2
    apply hh1
    refine eq_one_of_pow_four hp hp2 hhp ?_
    have h4 : (h ^ 4)⁻¹ = 1 := by
      rw [← h3]
      group
    simpa using h4
  have hhM : h ∉ Subgroup.normalizer (L : Set G) := by
    intro hhM'
    obtain ⟨-, ⟨hcomm, -⟩, -⟩ := h325 G T L V hyp.fsu hyp.conjClosure_eq.symm
    have hVT0 : conjClosure V T = V :=
      le_antisymm (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTV ht) l).1 hl)
        (le_conjClosure V T)
    rw [hVT0] at hcomm
    have hvVM : v ∈ conjClosure V (Subgroup.normalizer (L : Set G)) :=
      le_conjClosure V _ hvV
    have hv'VM : h⁻¹ * v * h ∈ conjClosure V (Subgroup.normalizer (L : Set G)) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure V _ (Subgroup.inv_mem _ hhM')) v).mp hvVM
      simpa using h1
    have hc : Commute v (h⁻¹ * v * h) := by
      have := congrArg Subtype.val (hcomm.is_comm.comm ⟨v, hvVM⟩ ⟨_, hv'VM⟩)
      exact this
    have e : v * (h⁻¹ * v * h) = h ^ 2 := by
      calc v * (h⁻¹ * v * h) = (v * h⁻¹ * v) * h := by group
        _ = h ^ 2 := by rw [hvh', pow_two]
    have hw2 : (h⁻¹ * v * h) ^ 2 = 1 := by rw [inv_conj_pow, hv2, mul_one, inv_mul_cancel]
    have h4 : h ^ 4 = 1 := by
      calc h ^ 4 = (v * (h⁻¹ * v * h)) ^ 2 := by rw [e, ← pow_mul]
        _ = v ^ 2 * (h⁻¹ * v * h) ^ 2 := hc.mul_pow 2
        _ = 1 := by rw [hv2, hw2, one_mul]
    exact hh1 (eq_one_of_pow_four hp hp2 hhp h4)
  have hvN : v ∉ Subgroup.normalizer (CFSG.conjugate V h : Set G) := by
    rw [mem_normalizer_conjugate_iff]
    intro hN
    have hv' : h * v = v * h⁻¹ := by
      have e1 : v⁻¹ * h * v = v * h * v⁻¹ := by rw [hvinv]
      calc h * v = v * (v⁻¹ * h * v) := by group
        _ = v * h⁻¹ := by rw [e1, hvh]
    have e : h * v * h⁻¹ = v * h⁻¹ ^ 2 := by
      rw [hv', mul_assoc, ← pow_two]
    rw [e] at hN
    have h2 : h⁻¹ ^ 2 ∈ Subgroup.normalizer (V : Set G) := by
      have := (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).inv_mem (Subgroup.le_normalizer hvV)) hN
      simpa using this
    have h3 : h⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      mem_of_sq_mem hpodd (by rw [inv_pow, hhp, inv_one]) h2
    exact hhN (by simpa using (Subgroup.normalizer (V : Set G)).inv_mem h3)
  set A := CFSG.conjugate V h with hAdef
  have hAmem : ∀ y : G, y ∈ A ↔ h * y * h⁻¹ ∈ V := fun y => Lem21Post.mem_conjugate_iff
  have hU0ne : ASInputs.tiU V A ≠ ⊥ := by
    have hZV := Lem7.omegaOneCenter_inf_ne_bot hyp.sylow.1 hVT hTV hyp.irrPlus.2.1 hV2
    obtain ⟨⟨z, hzZ, hzV⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZV
    have hz1 : z ≠ 1 := fun h0 => hz1' (Subtype.ext h0)
    have hzc : z ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
      ((Subgroup.closure_le _).mpr fun _ hz => hz.1) hzZ
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hyp.sylow
    have hOT : pCoreOf 2 H ≤ T := by
      rw [← hS]
      exact pCoreOf_two_le_sylow H S (by rw [hS]; exact hTH)
    have hzO : z ∈ pCoreOf 2 H := by
      refine charTwo_of_inH' hyp.qtke hyp.sylow hHs.1 (Subgroup.mem_inf.mpr ⟨hTH hzc.1, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_iff.mp hzc.2 x (hOT hx)
    have hzN : z ∈ Subgroup.normalizer (A : Set G) := by
      rw [hAdef, mem_normalizer_conjugate_iff]
      have h1 : h * z * h⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hhH) z).mp hzO
      exact hTV (hOT h1)
    intro h0
    apply hz1
    have : z ∈ ASInputs.tiU V A := ⟨hzV, hzN⟩
    rw [h0, Subgroup.mem_bot] at this
    exact this
  have hU0lt : ASInputs.tiU V A < V := by
    refine lt_of_le_of_ne inf_le_left fun h0 => hvN ?_
    have : v ∈ ASInputs.tiU V A := by rw [h0]; exact hvV
    exact this.2
  have hA2 : ∀ y ∈ A, y ^ 2 = 1 := fun y hy => by
    have := hV2 _ ((hAmem y).mp hy)
    rw [conj_pow] at this
    simpa using this
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h1 := hVc _ ((hAmem x).mp hx) _ ((hAmem y).mp hy)
    have h2 : h * (x * y) * h⁻¹ = h * (y * x) * h⁻¹ := by
      calc h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
        _ = (h * y * h⁻¹) * (h * x * h⁻¹) := h1
        _ = h * (y * x) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hAe : IsElemAbelian 2 A := ⟨⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩, hA2⟩
  have hcard : Nat.card V = Nat.card A :=
    (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).symm
  have hTI := h1216 G T L V hyp hNE
  have hTIV : IsTISetIn V ⊤ := by
    refine ⟨le_top, fun g _ hg => ?_⟩
    rcases hTI g with h1 | h1
    · exact absurd (Lem20Pick.mem_normalizer_of_conjugate_eq h1) hg
    · exact h1
  have hAV : A ≠ V := fun h1 => hvN (h1 ▸ Subgroup.le_normalizer hvV)
  have hVA : V ⊓ A = ⊥ := (hTI h).resolve_left hAV
  have hTIA : IsTISetIn A ⊤ := by
    refine ⟨le_top, fun g _ hg => ?_⟩
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rw [mem_conjSubgroup_iff] at hx2
    have hy1 : h * x * h⁻¹ ∈ V := (hAmem x).mp hx1
    have hy2 : h * (g * x * g⁻¹) * h⁻¹ ∈ V := (hAmem _).mp hx2
    have hk : ∀ y : G, (h * g * h⁻¹) * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ =
        h * (g * y * g⁻¹) * h⁻¹ := fun y => by group
    have hy2' : h * x * h⁻¹ ∈ CFSG.conjugate V (h * g * h⁻¹) := by
      rw [Lem21Post.mem_conjugate_iff, hk]
      exact hy2
    rcases hTI (h * g * h⁻¹) with h1 | h1
    · exfalso
      apply hg
      have hkN := Lem20Pick.mem_normalizer_of_conjugate_eq h1
      rw [Subgroup.mem_normalizer_iff] at hkN ⊢
      intro y
      rw [hAmem, hAmem, ← hk]
      exact hkN _
    · have : h * x * h⁻¹ ∈ V ⊓ CFSG.conjugate V (h * g * h⁻¹) := ⟨hy1, hy2'⟩
      rw [h1, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (by simpa using this)
  have hcross : ∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥ := by
    intro g hne
    have e : conjSubgroup A g = CFSG.conjugate V (h * g) := conjSubgroup_conjSubgroup V h g
    rw [e, inf_comm]
    exact (hTI (h * g)).resolve_left fun h1 => hne (e.trans h1).symm
  obtain ⟨⟨-, -, hXN, hYv⟩, hYn, hcases⟩ :=
    hI62 G V A hVe hAe hcard hTIV hTIA hcross hU0ne hU0lt
  set U₀ := ASInputs.tiU V A with hU₀
  set Y := ASInputs.tiY V A with hY
  set X := ASInputs.tiX V A with hX
  have hU₀V : U₀ ≤ V := inf_le_left
  have hVX : V ≤ X := le_sup_left
  have hvU₀ : v ∉ U₀ := fun h0 => hvN h0.2
  obtain ⟨hU₀Y, -⟩ := hYv v hvV hvU₀
  have hVY : ∀ y ∈ V, y ∈ Y → y ∈ U₀ := by
    intro y hyV hyY
    have : y ∈ Y ⊓ Subgroup.centralizer ({v} : Set G) :=
      ⟨hyY, Subgroup.mem_centralizer_singleton_iff.mpr (hVc y hyV v hvV)⟩
    rwa [← hU₀Y] at this
  have hAH : A ≤ H := fun y hy => by
    have h1 : h * y * h⁻¹ ∈ V := (hAmem y).mp hy
    have e : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hhH) (hTH (hVT h1))) hhH
  have hXH : X ≤ H := sup_le (hVT.trans hTH) hAH
  have hZX : ∀ r : ℕ, r.Prime → r ∣ Nat.card (↥X ⧸ Y.subgroupOf X) → r = 2 ∨ r = p :=
    fun r hr hrd => hZ r hr (hrd.trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hXH)))
  set f : ↥V →* ↥X ⧸ Y.subgroupOf X :=
    (QuotientGroup.mk' (Y.subgroupOf X)).comp (Subgroup.inclusion hVX) with hf
  have hker : f.ker = U₀.subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h1 => hVY x x.2 h1, fun h1 => Subgroup.mem_sup_left h1⟩
  have hidxf : U₀.relIndex V = Nat.card f.range := by
    show (U₀.subgroupOf V).index = _
    rw [← hker, Subgroup.index_ker]
  have hfp : IsPGroup 2 ↥f.range := by
    rintro ⟨_, x, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hV2' x, map_one]
  obtain ⟨j, hj⟩ := hfp.exists_card_eq
  have hrange : Nat.card f.range ∣ Nat.card (↥X ⧸ Y.subgroupOf X) :=
    Subgroup.card_subgroup_dvd_card _
  have hne1 : U₀.relIndex V ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact (lt_irrefl _ (lt_of_lt_of_le hU0lt h1))
  rcases hcases with ⟨m, hmodd, ⟨e⟩⟩ | ⟨n, hn⟩ | ⟨n, hn⟩
  ·
    have hXc : Nat.card (↥X ⧸ Y.subgroupOf X) = 2 * m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hj1 : j ≤ 1 := by
      by_contra hj2
      have h4 : 2 ^ 2 ∣ 2 * m := by
        have h5 := hrange
        rw [hj, hXc] at h5
        exact (pow_dvd_pow 2 (by omega)).trans h5
      have h6 : 2 ∣ m := by omega
      exact Nat.not_even_iff_odd.mpr hmodd (even_iff_two_dvd.mpr h6)
    refine ⟨h, v, htP, hhM, hhp, hvV, hvh, hvN, ?_⟩
    rw [hidxf, hj]
    interval_cases j
    · exact absurd (by rw [hidxf, hj]; rfl) hne1
    · rfl
  · exact (false_of_isPSL_two_two hn hZX).elim
  · exact (false_of_isSz hn hZX).elim

theorem lem12220Choice_of_coprime (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h325 : Stmt3_2_5) (h1216 : Stmt12_2_16) (h12218 : Stmt12_2_18)
    (hI62 : ASInputs.AS_I_6_2_twoCases) : Lem12220Choice :=
  lem12220Choice_of h1222 h1216 hI62 (coprimePick_of h331 h1222 h325 h1216 h12218 hI62)

theorem lem12220PickFull_of_coprime (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h325 : Stmt3_2_5) (h1216 : Stmt12_2_16) (h12218 : Stmt12_2_18)
    (hI62 : ASInputs.AS_I_6_2_twoCases) : Lem12220PickFull :=
  lem12220PickFull_of_pick h331 h1222 h1216 hI62
    (coprimePick_of h331 h1222 h325 h1216 h12218 hI62)

end CFSG.Quasithin.H13
