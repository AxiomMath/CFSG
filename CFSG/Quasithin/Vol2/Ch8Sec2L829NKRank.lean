module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4L2

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.H13.L829N
open scoped commutatorElement

section Rank

variable {G : Type} [Group G] [Finite G]

theorem nk_two_le_pRank_of_elemAb_sq {p : ℕ} [hp : Fact p.Prime] {H E : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian p E) (h9 : Nat.card E = p ^ 2) :
    2 ≤ CFSG.Open.pRank p H := by
  have hp1 : 1 < p := hp.out.one_lt
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEH, hE, ?_⟩
  · rintro k ⟨E', -, -, hE'⟩
    have h1 : p ^ k ≤ Nat.card G := by
      rw [← hE']
      exact Subgroup.card_le_card_group E'
    exact le_trans (Nat.lt_pow_self hp1).le h1
  · rw [h9]

end Rank

section Existence

theorem nk_exists_elemAb_sq_of_two_le_pRank {p : ℕ} [hp : Fact p.Prime] {X : Type} [Group X]
    [Finite X] (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hp1 : 1 < p := hp.out.one_lt
  unfold CFSG.Open.pRank at h
  have hbot : IsElemAbelian p (⊥ : Subgroup X) := by
    have h1 : ∀ a : (⊥ : Subgroup X), (a : X) = 1 := fun a => Subgroup.mem_bot.mp a.2
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · show (a : X) * (b : X) = (b : X) * (a : X)
      rw [h1 a, h1 b]
    · rw [Subgroup.mem_bot.mp hx, one_pow]
  have hne : {k : ℕ | ∃ E : Subgroup X, E ≤ ⊤ ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}.Nonempty :=
    ⟨0, ⊥, bot_le, hbot, by simp⟩
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup X, E ≤ ⊤ ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨E', -, -, hE'⟩
    have h1 : p ^ k ≤ Nat.card X := by
      rw [← hE']
      exact Subgroup.card_le_card_group E'
    exact le_trans (Nat.lt_pow_self hp1).le h1
  obtain ⟨E₀, -, hE₀, hcard₀⟩ := Nat.sSup_mem hne hbdd
  have hdvd : p ^ 2 ∣ Nat.card E₀ := by
    rw [hcard₀]
    exact pow_dvd_pow p h
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E₀) p (n := 2) hdvd
  refine ⟨S.map E₀.subtype, ?_, ?_⟩
  · exact isElemAbelian_mono_829 p (Subgroup.map_subtype_le S) hE₀
  · rw [Subgroup.card_map_of_injective E₀.subtype_injective, hS]

end Existence

section Commuting

theorem nk_eq_of_dvd_add_sub {p a c : ℕ} (ha : a < p) (hc : c < p) (h : p ∣ a + (p - c)) :
    a = c := by
  obtain ⟨k, hk⟩ := h
  rcases Nat.lt_trichotomy k 1 with h0 | h1 | h2
  · have hk0 : k = 0 := by omega
    rw [hk0, Nat.mul_zero] at hk
    omega
  · rw [h1, Nat.mul_one] at hk
    omega
  · have h2' : p * 2 ≤ p * k := Nat.mul_le_mul (le_refl p) (by omega)
    omega

theorem nk_exists_elemAb_sq_of_commuting {p : ℕ} [hp : Fact p.Prime] {Q : Type} [Group Q]
    [Finite Q] (x y : Q) (hx : orderOf x = p) (hy : orderOf y = p) (hxy : x * y = y * x)
    (hind : ∀ i j : ℕ, x ^ i * y ^ j = 1 → p ∣ i ∧ p ∣ j) :
    ∃ E : Subgroup Q, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hp1 : 1 < p := hp.out.one_lt
  have hxpow : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hypow : y ^ p = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hC : Commute x y := hxy
  have hCxy : ∀ i j : ℕ, Commute (x ^ i) (y ^ j) := fun i j => hC.pow_pow i j
  have hyx : ∀ j k : ℕ, y ^ j * x ^ k = x ^ k * y ^ j := fun j k => ((hC.symm).pow_pow j k).eq
  have hmul : ∀ a b a' b' : ℕ, x ^ a * y ^ b * (x ^ a' * y ^ b') = x ^ (a + a') * y ^ (b + b') := by
    intro a b a' b'
    calc x ^ a * y ^ b * (x ^ a' * y ^ b') = x ^ a * (y ^ b * x ^ a') * y ^ b' := by
          simp only [mul_assoc]
      _ = x ^ a * (x ^ a' * y ^ b) * y ^ b' := by rw [hyx b a']
      _ = x ^ (a + a') * y ^ (b + b') := by
          rw [pow_add, pow_add]
          simp only [mul_assoc]
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  let E : Subgroup Q :=
    { carrier := {g | ∃ i j : ℕ, g = x ^ i * y ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        exact ⟨i + k, j + l, hmul i j k l⟩
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨m * i, m * j, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [hmul i j (m * i) (m * j)]
        rw [show i + m * i = p * i by rw [hm]; ring, show j + m * j = p * j by rw [hm]; ring,
          pow_mul, pow_mul, hxpow, hypow, one_pow, one_pow, one_mul] }
  have hEmem : ∀ g : Q, g ∈ E ↔ ∃ i j : ℕ, g = x ^ i * y ^ j := fun g => Iff.rfl
  have hEc : IsMulCommutative ↥E := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨i, j, hij⟩ := (hEmem _).mp a.2
    obtain ⟨k, l, hkl⟩ := (hEmem _).mp b.2
    show (a : Q) * (b : Q) = (b : Q) * (a : Q)
    rw [hij, hkl]
    have h1 : Commute (x ^ i * y ^ j) (x ^ k) :=
      Commute.mul_left ((Commute.refl x).pow_pow i k) (hC.symm.pow_pow j k)
    have h2 : Commute (x ^ i * y ^ j) (y ^ l) :=
      Commute.mul_left (hCxy i l) ((Commute.refl y).pow_pow j l)
    exact (Commute.mul_right h1 h2).eq
  have hEexp : ∀ g ∈ E, g ^ p = 1 := by
    intro g hg
    obtain ⟨i, j, rfl⟩ := (hEmem _).mp hg
    have hxi : (x ^ i) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxpow, one_pow]
    have hyj : (y ^ j) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hypow, one_pow]
    rw [(hCxy i j).mul_pow, hxi, hyj, one_mul]
  have hxmod : ∀ i : ℕ, x ^ i = x ^ (i % p) := fun i => by
    conv_lhs => rw [← Nat.div_add_mod i p, pow_add, pow_mul, hxpow, one_pow, one_mul]
  have hymod : ∀ j : ℕ, y ^ j = y ^ (j % p) := fun j => by
    conv_lhs => rw [← Nat.div_add_mod j p, pow_add, pow_mul, hypow, one_pow, one_mul]
  have hkey : ∀ a b c d : ℕ, c ≤ p → d ≤ p → x ^ a * y ^ b = x ^ c * y ^ d →
      p ∣ a + (p - c) ∧ p ∣ b + (p - d) := by
    intro a b c d hc hd h
    apply hind
    have hxy3 : x ^ p * y ^ p = 1 := by rw [hxpow, hypow, one_mul]
    calc x ^ (a + (p - c)) * y ^ (b + (p - d))
        = x ^ a * y ^ b * (x ^ (p - c) * y ^ (p - d)) := (hmul a b (p - c) (p - d)).symm
      _ = x ^ c * y ^ d * (x ^ (p - c) * y ^ (p - d)) := by rw [h]
      _ = x ^ (c + (p - c)) * y ^ (d + (p - d)) := hmul c d (p - c) (p - d)
      _ = x ^ p * y ^ p := by rw [Nat.add_sub_cancel' hc, Nat.add_sub_cancel' hd]
      _ = 1 := hxy3
  let f : Fin p × Fin p → ↥E := fun ij =>
    ⟨x ^ (ij.1 : ℕ) * y ^ (ij.2 : ℕ), (hEmem _).mpr ⟨ij.1, ij.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      have h' : x ^ (a : ℕ) * y ^ (b : ℕ) = x ^ (c : ℕ) * y ^ (d : ℕ) := congrArg Subtype.val h
      obtain ⟨h1, h2⟩ := hkey _ _ _ _ (by omega) (by omega) h'
      have hac : (a : ℕ) = (c : ℕ) := nk_eq_of_dvd_add_sub a.2 c.2 h1
      have hbd : (b : ℕ) = (d : ℕ) := nk_eq_of_dvd_add_sub b.2 d.2 h2
      rw [Fin.ext_iff.mpr hac, Fin.ext_iff.mpr hbd]
    · rintro ⟨g, hg⟩
      obtain ⟨i, j, rfl⟩ := (hEmem _).mp hg
      refine ⟨(⟨i % p, Nat.mod_lt _ (by omega)⟩, ⟨j % p, Nat.mod_lt _ (by omega)⟩), ?_⟩
      apply Subtype.ext
      show x ^ (i % p) * y ^ (j % p) = x ^ i * y ^ j
      rw [← hxmod, ← hymod]
  refine ⟨E, ⟨hEc, hEexp⟩, ?_⟩
  have hcardE := Nat.card_eq_of_bijective f hf
  rw [Nat.card_prod] at hcardE
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcardE
  rw [sq]
  exact hcardE.symm

end Commuting

section TwoGroup

theorem nk_eq_one_of_mem_p_two {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X]
    {A B : Subgroup X} {n : ℕ} (hA : Nat.card A ∣ p ^ n) (hB : IsPGroup 2 B) {g : X}
    (hgA : g ∈ A) (hgB : g ∈ B) : g = 1 := by
  have h1 : orderOf g ∣ p ^ n := by
    have h := orderOf_dvd_natCard (⟨g, hgA⟩ : A)
    rw [← Subgroup.orderOf_coe] at h
    exact h.trans hA
  obtain ⟨k, hk⟩ := hB ⟨g, hgB⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
  have hcop : Nat.Coprime (p ^ n) (2 ^ k) := Nat.Coprime.pow _ _ hcop2
  have h3 : orderOf g ∣ Nat.gcd (p ^ n) (2 ^ k) := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem nk_exists_elemAb_sq_of_two_kernel {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {G : Type}
    [Group G] [Finite G] (P Y : Subgroup G) (hY : IsPGroup 2 Y) (hYP : Y ≤ P)
    (hcomm : ∀ g ∈ P, ∀ h ∈ P, g * h * g⁻¹ * h⁻¹ ∈ Y)
    (hcube : ∀ g ∈ P, g ^ p ∈ Y) (hcard : Nat.card P = p ^ 2 * Nat.card Y) :
    ∃ F : Subgroup G, F ≤ P ∧ IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) p (n := 2)
    ⟨Nat.card Y, hcard⟩
  set F : Subgroup G := S.map P.subtype with hFdef
  have hFP : F ≤ P := Subgroup.map_subtype_le S
  have hFcard : Nat.card F = p ^ 2 := by
    rw [hFdef, Subgroup.card_map_of_injective P.subtype_injective, hS]
  have hFY : ∀ g ∈ F, g ∈ Y → g = 1 := fun g hgF hgY =>
    nk_eq_one_of_mem_p_two hp2 (n := 2) (by simp [hFcard]) hY hgF hgY
  have hFc : ∀ g ∈ F, ∀ h ∈ F, g * h * g⁻¹ * h⁻¹ ∈ F := fun g hg h hh =>
    F.mul_mem (F.mul_mem (F.mul_mem hg hh) (F.inv_mem hg)) (F.inv_mem hh)
  refine ⟨F, hFP, ⟨?_, ?_⟩, hFcard⟩
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hc : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ = 1 :=
      hFY _ (hFc _ a.2 _ b.2) (hcomm _ (hFP a.2) _ (hFP b.2))
    have : (a : G) * b = b * a := by
      calc (a : G) * b = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * ((b : G) * (a : G)) := by group
        _ = (b : G) * (a : G) := by rw [hc, one_mul]
    simpa using this
  · intro x hx
    have h3 : x ^ p ∈ Y := hcube x (hFP hx)
    have h4 : x ^ p ∈ F := F.pow_mem hx p
    exact hFY _ h4 h3

end TwoGroup

section Cube

theorem nk_commute_central_pow {A : Type} [Group A] {z : A} (hz : ∀ a : A, a * z = z * a)
    (k : ℕ) (a : A) : a * z ^ k = z ^ k * a :=
  (Commute.pow_right (show Commute a z from hz a) k).eq

theorem nk_pow_mul_eq_of_central {A : Type} [Group A] {x y z : A} (hz : ∀ a : A, a * z = z * a)
    (hyx : y * x = z * (x * y)) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * z ^ (n.choose 2) := by
  have hzc : ∀ (k : ℕ) (a : A), a * z ^ k = z ^ k * a := fun k a =>
    nk_commute_central_pow hz k a
  have hzl : ∀ (k : ℕ) (a b : A), a * (z ^ k * b) = z ^ k * (a * b) := fun k a b => by
    rw [← mul_assoc, hzc k a, mul_assoc]
  have hyx_pow : ∀ j : ℕ, y ^ j * x = z ^ j * (x * y ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (j + 1) * x = y * (y ^ j * x) := by rw [pow_succ', mul_assoc]
        _ = y * (z ^ j * (x * y ^ j)) := by rw [ih]
        _ = z ^ j * (y * (x * y ^ j)) := by rw [← mul_assoc, hzc j y, mul_assoc]
        _ = z ^ j * ((y * x) * y ^ j) := by simp only [mul_assoc]
        _ = z ^ j * ((z * (x * y)) * y ^ j) := by rw [hyx]
        _ = z ^ (j + 1) * (x * y ^ (j + 1)) := by
          rw [pow_succ z j, pow_succ' y j]
          simp only [mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      have h := Nat.choose_succ_succ' n 1
      rw [Nat.choose_one_right] at h
      exact h
    rw [pow_succ (x * y) n, ih, hc]
    generalize n.choose 2 = C
    calc x ^ n * y ^ n * z ^ C * (x * y)
        = x ^ n * (y ^ n * (z ^ C * (x * y))) := by simp only [mul_assoc]
      _ = x ^ n * (z ^ C * (y ^ n * (x * y))) := by rw [hzl C (y ^ n) (x * y)]
      _ = z ^ C * (x ^ n * (y ^ n * (x * y))) := by rw [hzl C (x ^ n) (y ^ n * (x * y))]
      _ = z ^ C * (x ^ n * ((y ^ n * x) * y)) := by simp only [mul_assoc]
      _ = z ^ C * (x ^ n * ((z ^ n * (x * y ^ n)) * y)) := by rw [hyx_pow n]
      _ = z ^ C * (x ^ n * (z ^ n * (x * (y ^ n * y)))) := by simp only [mul_assoc]
      _ = z ^ C * (z ^ n * (x ^ n * (x * (y ^ n * y)))) := by
          rw [hzl n (x ^ n) (x * (y ^ n * y))]
      _ = z ^ (C + n) * (x ^ n * (x * (y ^ n * y))) := by
          rw [← mul_assoc (z ^ C) (z ^ n), ← pow_add]
      _ = z ^ (n + C) * (x ^ n * (x * (y ^ n * y))) := by rw [Nat.add_comm C n]
      _ = z ^ (n + C) * (x ^ (n + 1) * y ^ (n + 1)) := by
          rw [pow_succ x n, pow_succ y n]
          simp only [mul_assoc]
      _ = (x ^ (n + 1) * y ^ (n + 1)) * z ^ (n + C) := (hzc (n + C) _).symm

theorem nk_mul_pow_central {A : Type} [Group A] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x y z : A}
    (hz : ∀ a : A, a * z = z * a) (hzp : z ^ p = 1) (hyx : y * x = z * (x * y)) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have hp3 : 2 < p := by have := hp.two_le; omega
  have hdvd : p ∣ p.choose 2 := Nat.Prime.dvd_choose_self hp (by norm_num) hp3
  rw [nk_pow_mul_eq_of_central hz hyx p]
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, hzp, one_pow, mul_one]

theorem nk_exists_elemAb_sq_of_cube {A : Type} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (r : A) (hrp : orderOf r = p) (hrc : ∀ a : A, a * r = r * a)
    (B : Subgroup A) (hrB : r ∈ B) (hB : Nat.card B = p ^ 3)
    (hcube : ∀ b ∈ B, b ^ p ∈ Subgroup.zpowers r)
    (hcomm : ∀ b ∈ B, ∀ c ∈ B, b * c * b⁻¹ * c⁻¹ ∈ Subgroup.zpowers r) :
    ∃ F : Subgroup A, IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  have hp1 : 1 < p := hp.out.one_lt
  have hcard_z : Nat.card (Subgroup.zpowers r) = p := by rw [Nat.card_zpowers, hrp]
  have hzcen : ∀ n ∈ Subgroup.zpowers r, ∀ a : A, a * n = n * a := by
    intro n hn a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact Commute.zpow_right (show Commute a r from hrc a) k
  have hzcube : ∀ n ∈ Subgroup.zpowers r, n ^ p = 1 := by
    intro n hn
    have h1 : orderOf n ∣ orderOf r := orderOf_dvd_of_mem_zpowers hn
    rw [hrp] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hnorm : (Subgroup.zpowers r).Normal := CFSG.Quasithin.H13.normal_zpowers_of_central r hrc
  haveI := hnorm
  let φ : B →* A :=
    { toFun := fun b => (b : A) ^ p
      map_one' := by simp
      map_mul' := fun b c => by
        have hc := hcomm b.1 b.2 c.1 c.2
        have hyx : (c : A) * (b : A) = (b * c * b⁻¹ * c⁻¹ : A)⁻¹ * ((b : A) * (c : A)) :=
          CFSG.Quasithin.H13.comm_rel (b : A) (c : A)
        simp only [Subgroup.coe_mul]
        refine nk_mul_pow_central hp.out hp2 (z := (b * c * b⁻¹ * c⁻¹ : A)⁻¹) ?_ ?_ hyx
        · intro a
          exact (Commute.inv_right (show Commute a (b * c * b⁻¹ * c⁻¹ : A) from
            hzcen _ hc a)).eq
        · have h3 : (b * c * b⁻¹ * c⁻¹ : A) ^ p = 1 := hzcube _ hc
          rw [inv_pow, h3, inv_one] }
  have hφr : φ.range ≤ Subgroup.zpowers r := by
    rintro x ⟨b, rfl⟩
    exact hcube b.1 b.2
  have hker_range : Nat.card φ.ker * Nat.card φ.range = p ^ 3 := by
    rw [Subgroup.card_ker_mul_card_range, hB]
  have hrange_le : Nat.card φ.range ≤ p := by
    rw [← hcard_z]
    exact Subgroup.card_le_of_le hφr
  have hker_ge : p ^ 2 ≤ Nat.card φ.ker := by
    have h1 : Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * p :=
      Nat.mul_le_mul (le_refl _) hrange_le
    have h2 : p ^ 2 * p ≤ Nat.card φ.ker * p := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ = Nat.card φ.ker * Nat.card φ.range := hker_range.symm
        _ ≤ Nat.card φ.ker * p := h1
    exact Nat.le_of_mul_le_mul_right h2 (by omega)
  obtain ⟨w, hwB, hwcube, hwr⟩ : ∃ w : A, w ∈ B ∧ w ^ p = 1 ∧ w ∉ Subgroup.zpowers r := by
    by_contra hno
    push Not at hno
    let X : Subgroup A := φ.ker.map B.subtype
    have hXle : X ≤ Subgroup.zpowers r := by
      rintro x ⟨b, hb, rfl⟩
      have hb' : φ b = 1 := hb
      have : (b : A) ^ p = 1 := hb'
      exact hno b.1 b.2 this
    have hXcard : Nat.card X = Nat.card φ.ker := by
      rw [Subgroup.card_map_of_injective B.subtype_injective]
    have hle := Subgroup.card_le_of_le hXle
    rw [hcard_z, hXcard] at hle
    have hpp : p < p ^ 2 := by nlinarith
    exact absurd (hker_ge.trans hle) (not_le.mpr hpp)
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hwr (Subgroup.one_mem _)
  have hw3 : orderOf w = p := by
    have h1 : orderOf w ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hwcube
    rcases (Nat.dvd_prime hp.out).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  set P : Subgroup A := Subgroup.zpowers r with hPdef
  set Q : Subgroup A := Subgroup.zpowers w with hQdef
  haveI : P.Normal := hnorm
  have hPc : IsMulCommutative ↥P := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self r i j).eq
  have hQc : IsMulCommutative ↥Q := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self w i j).eq
  have hPQ : ∀ g ∈ P, ∀ q ∈ Q, g * q = q * g := fun g hg q _ => (hzcen g hg q).symm
  haveI hFc : IsMulCommutative ↥(P ⊔ Q) :=
    CFSG.Quasithin.H13.isMulCommutative_sup_of_commute hPc hQc hPQ
  have hPQint : ∀ x ∈ P, x ∈ Q → x = 1 := by
    intro x hxP hxQ
    by_contra hx1
    have hxo : orderOf x = p := by
      have h1 : orderOf x ∣ p := by
        rw [← hrp]
        exact orderOf_dvd_of_mem_zpowers hxP
      rcases (Nat.dvd_prime hp.out).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hPeq : Subgroup.zpowers x = P := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.mpr hxP
      · rw [hcard_z, Nat.card_zpowers, hxo]
    have hQeq : Subgroup.zpowers x = Q := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.mpr hxQ
      · have hQc' : Nat.card Q = p := by rw [hQdef, Nat.card_zpowers, hw3]
        rw [hQc', Nat.card_zpowers, hxo]
    have hwP : w ∈ P := by
      rw [← hPeq, hQeq]
      exact Subgroup.mem_zpowers w
    exact hwr hwP
  let e : (P × Q) → ↥(P ⊔ Q) := fun pq =>
    ⟨pq.1.1 * pq.2.1, Subgroup.mul_mem_sup pq.1.2 pq.2.2⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨⟨g, hg⟩, ⟨q, hq⟩⟩ ⟨⟨g', hg'⟩, ⟨q', hq'⟩⟩ h
      have h' : g * q = g' * q' := congrArg Subtype.val h
      have hx : g'⁻¹ * g = q' * q⁻¹ := by
        calc g'⁻¹ * g = g'⁻¹ * (g * q) * q⁻¹ := by group
          _ = g'⁻¹ * (g' * q') * q⁻¹ := by rw [h']
          _ = q' * q⁻¹ := by group
      have hPx : g'⁻¹ * g ∈ P := P.mul_mem (P.inv_mem hg') hg
      have hQx : q' * q⁻¹ ∈ Q := Q.mul_mem hq' (Q.inv_mem hq)
      have h1 : g'⁻¹ * g = 1 := hPQint _ hPx (by rw [hx]; exact hQx)
      have h2 : g = g' := (inv_mul_eq_one.mp h1).symm
      have h3 : q' * q⁻¹ = 1 := by rw [← hx, h1]
      have h4 : q = q' := (mul_inv_eq_one.mp h3).symm
      subst h2
      subst h4
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨g₀, hg₀, q₀, hq₀, hgq⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      exact ⟨(⟨g₀, hg₀⟩, ⟨q₀, hq₀⟩), Subtype.ext hgq⟩
  refine ⟨P ⊔ Q, ⟨hFc, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨g, hg, q, hq, hgq⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    have hcomm' : Commute g q := hPQ g hg q hq
    have hg3 : g ^ p = 1 := hzcube g hg
    have hq3 : q ^ p = 1 := by
      have h1 : orderOf q ∣ orderOf w := orderOf_dvd_of_mem_zpowers hq
      rw [hw3] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    rw [← hgq, hcomm'.mul_pow, hg3, hq3, one_mul]
  · rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_prod]
    have hQcard : Nat.card Q = p := by rw [hQdef, Nat.card_zpowers, hw3]
    rw [hcard_z, hQcard, sq]

end Cube

section Central

theorem nk_exists_elemAb_sq_of_central_kernel {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (V : Type) [Group V] [Finite V]
    (hV : IsElemAbelian p (⊤ : Subgroup V)) (hV9 : Nat.card V = p ^ 2) :
    ∀ (m : ℕ) (A : Type) [Group A] [Finite A] (f : A →* V), Nat.card A = m →
      Function.Surjective f → (∀ z ∈ f.ker, ∀ a : A, a * z = z * a) → IsPGroup p f.ker →
      ∃ F : Subgroup A, IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  have hp1 : 1 < p := hp.out.one_lt
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro A _ _ f hAm hsurj hcen hP
  by_cases hker : f.ker = ⊥
  ·
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
    let e : A ≃* V := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
    refine ⟨⊤, ⟨?_, ?_⟩, ?_⟩
    · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      apply hinj
      show f ((a : A) * (b : A)) = f ((b : A) * (a : A))
      rw [map_mul, map_mul]
      exact congrArg Subtype.val
        (isMulCommutative_iff.mp hV.1 ⟨f a, Subgroup.mem_top _⟩ ⟨f b, Subgroup.mem_top _⟩)
    · intro x _
      apply hinj
      rw [map_pow, map_one]
      exact hV.2 _ (Subgroup.mem_top _)
    · rw [Subgroup.card_top, Nat.card_congr e.toEquiv, hV9]
  ·
    obtain ⟨r, hrK, hrp⟩ : ∃ r ∈ f.ker, orderOf r = p := by
      have hcard1 : Nat.card f.ker ≠ 1 := fun h => hker ((Subgroup.eq_bot_iff_card _).mpr h)
      have hdvd : p ∣ Nat.card f.ker := by
        rcases IsPGroup.card_eq_or_dvd hP with h | h
        · exact absurd h hcard1
        · exact h
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
      refine ⟨x.1, x.2, ?_⟩
      rw [Subgroup.orderOf_coe, hx]
    have hrc : ∀ a : A, a * r = r * a := fun a => hcen r hrK a
    have hzN : Subgroup.zpowers r ≤ f.ker := Subgroup.zpowers_le.mpr hrK
    haveI := CFSG.Quasithin.H13.normal_zpowers_of_central r hrc
    let f' : A ⧸ Subgroup.zpowers r →* V := QuotientGroup.lift (Subgroup.zpowers r) f hzN
    have hf'mk : ∀ a : A, f' (a : A ⧸ Subgroup.zpowers r) = f a := fun a => rfl
    have hf'surj : Function.Surjective f' := by
      intro v
      obtain ⟨a, rfl⟩ := hsurj v
      exact ⟨(a : A ⧸ Subgroup.zpowers r), hf'mk a⟩
    have hcen' : ∀ z ∈ f'.ker, ∀ a : A ⧸ Subgroup.zpowers r, a * z = z * a := by
      intro z hz a
      obtain ⟨z₀, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
      have hz₀ : z₀ ∈ f.ker := by
        have h1 : f' (z₀ : A ⧸ Subgroup.zpowers r) = 1 := hz
        rw [hf'mk] at h1
        exact h1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcen z₀ hz₀ a₀]
    have hP' : IsPGroup p f'.ker := by
      intro y
      obtain ⟨z, hz⟩ := y
      obtain ⟨z₀, rfl⟩ := QuotientGroup.mk_surjective z
      have hz₀ : z₀ ∈ f.ker := by
        have h1 : f' (z₀ : A ⧸ Subgroup.zpowers r) = 1 := hz
        rw [hf'mk] at h1
        exact h1
      obtain ⟨k, hk⟩ := hP ⟨z₀, hz₀⟩
      refine ⟨k, Subtype.ext ?_⟩
      have hk' : z₀ ^ p ^ k = 1 := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← QuotientGroup.mk_pow, hk']
      rfl
    have hcardq : Nat.card A = Nat.card (A ⧸ Subgroup.zpowers r) * p := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers r),
        Nat.card_zpowers, hrp]
    have hqpos : 0 < Nat.card (A ⧸ Subgroup.zpowers r) := Nat.card_pos
    have hlt : Nat.card (A ⧸ Subgroup.zpowers r) < m := by nlinarith
    obtain ⟨F₁, hF₁, hF₁c⟩ :=
      ih _ hlt (A ⧸ Subgroup.zpowers r) f' rfl hf'surj hcen' hP'
    let B : Subgroup A := F₁.comap (QuotientGroup.mk' (Subgroup.zpowers r))
    have hB : Nat.card B = p ^ 3 := by
      rw [CFSG.Quasithin.H13.card_comap_mk', hF₁c, Nat.card_zpowers, hrp]
      ring
    have hrB : r ∈ B := by
      have h1 : (QuotientGroup.mk' (Subgroup.zpowers r)) r = 1 :=
        (QuotientGroup.eq_one_iff r).mpr (Subgroup.mem_zpowers r)
      exact Subgroup.mem_comap.mpr (by rw [h1]; exact F₁.one_mem)
    have hcube : ∀ b ∈ B, b ^ p ∈ Subgroup.zpowers r := by
      intro b hb
      have h1 : (QuotientGroup.mk' (Subgroup.zpowers r) b) ^ p = 1 :=
        hF₁.2 _ (Subgroup.mem_comap.mp hb)
      rw [← map_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hcomm : ∀ b ∈ B, ∀ c ∈ B, b * c * b⁻¹ * c⁻¹ ∈ Subgroup.zpowers r := by
      intro b hb c hc
      have hcomm' := isMulCommutative_iff.mp hF₁.1
        ⟨QuotientGroup.mk' (Subgroup.zpowers r) b, Subgroup.mem_comap.mp hb⟩
        ⟨QuotientGroup.mk' (Subgroup.zpowers r) c, Subgroup.mem_comap.mp hc⟩
      have hc' : QuotientGroup.mk' (Subgroup.zpowers r) b *
          QuotientGroup.mk' (Subgroup.zpowers r) c =
          QuotientGroup.mk' (Subgroup.zpowers r) c *
          QuotientGroup.mk' (Subgroup.zpowers r) b := congrArg Subtype.val hcomm'
      have h1 : QuotientGroup.mk' (Subgroup.zpowers r) (b * c * b⁻¹ * c⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hc']
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact nk_exists_elemAb_sq_of_cube hp2 r hrp hrc B hrB hB hcube hcomm

end Central

section QuotientMeet

theorem nk_isElemAbelian_top_of {p : ℕ} {V : Type} [Group V] (hc : ∀ a b : V, a * b = b * a)
    (hp : ∀ a : V, a ^ p = 1) : IsElemAbelian p (⊤ : Subgroup V) :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a.1 b.1)⟩⟩, fun z _ => hp z⟩

theorem nk_exists_elemAb_sq_of_quotient_meet {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X]
    (Y K' D : Subgroup X) [hYn : Y.Normal] (hD : IsPGroup 2 D)
    (hYK : ∀ y ∈ Y, ∀ k ∈ K', y * k * y⁻¹ * k⁻¹ ∈ D)
    (E : Subgroup (X ⧸ Y)) (hE : IsElemAbelian p E) (hE9 : Nat.card E = p ^ 2)
    (hEK : ∀ e ∈ E, ∃ k ∈ K', (k : X ⧸ Y) = e) :
    ∃ F : Subgroup X, F ≤ K' ∧ IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  have hp1 : 1 < p := hp.out.one_lt
  set P : Subgroup X := E.comap (QuotientGroup.mk' Y) ⊓ K' with hPdef
  set N : Subgroup X := Y ⊓ K' with hNdef
  have hPmem : ∀ x : X, x ∈ P ↔ ((x : X ⧸ Y) ∈ E ∧ x ∈ K') := fun x => Iff.rfl
  have hPK : P ≤ K' := inf_le_right
  have hNP : N ≤ P := by
    intro x hx
    obtain ⟨hxY, hxK⟩ := hx
    exact (hPmem x).mpr ⟨by rw [(QuotientGroup.eq_one_iff x).mpr hxY]; exact E.one_mem, hxK⟩
  have hNn : (N.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnY, hnK⟩ := hn
    exact ⟨hYn.conj_mem _ hnY g, K'.mul_mem (K'.mul_mem (hPK g.2) hnK) (K'.inv_mem (hPK g.2))⟩
  haveI := hNn
  let φ : ↥P →* X ⧸ Y := (QuotientGroup.mk' Y).comp P.subtype
  have hφr : φ.range = E := by
    ext e
    constructor
    · rintro ⟨g, rfl⟩
      exact ((hPmem g).mp g.2).1
    · intro he
      obtain ⟨k, hkK, hke⟩ := hEK e he
      have hkP : k ∈ P := (hPmem k).mpr ⟨by rw [hke]; exact he, hkK⟩
      exact ⟨⟨k, hkP⟩, hke⟩
  have hφk : φ.ker.map P.subtype = N := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : ((g : X) : X ⧸ Y) = 1 := hg
      exact ⟨(QuotientGroup.eq_one_iff _).mp hg', hPK g.2⟩
    · rintro ⟨hxY, hxK⟩
      have hxP : x ∈ P := hNP ⟨hxY, hxK⟩
      exact ⟨⟨x, hxP⟩, (QuotientGroup.eq_one_iff x).mpr hxY, rfl⟩
  have hkerc : Nat.card φ.ker = Nat.card N := by
    rw [← hφk, Subgroup.card_map_of_injective P.subtype_injective]
  have hPcard : Nat.card P = p ^ 2 * Nat.card N := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hkerc, hφr, hE9] at h
    linarith
  have hN₁card : Nat.card (N.subgroupOf P) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hN₁index : (N.subgroupOf P).index = p ^ 2 := by
    have h := Subgroup.card_mul_index (N.subgroupOf P)
    rw [hN₁card, hPcard] at h
    have hNpos : 0 < Nat.card N := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hNpos
    rw [h]
    ring
  have hPpos : Nat.card P ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm3, hPm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hPpos p (by omega)
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) p (n := a) ⟨m, hPm⟩
  have hSindex : S.index = m := by
    have h := Subgroup.card_mul_index S
    rw [hS, hPm] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos a) h
  have htop : S ⊔ (N.subgroupOf P) = ⊤ := by
    have h1 : (S ⊔ N.subgroupOf P).index ∣ S.index := Subgroup.index_dvd_of_le le_sup_left
    have h2 : (S ⊔ N.subgroupOf P).index ∣ (N.subgroupOf P).index :=
      Subgroup.index_dvd_of_le le_sup_right
    rw [hSindex] at h1
    rw [hN₁index] at h2
    have hcop : Nat.Coprime m (p ^ 2) :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm3).symm
    have h3 : (S ⊔ N.subgroupOf P).index = 1 := by
      have := Nat.dvd_gcd h1 h2
      rw [hcop.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    exact Subgroup.index_eq_one.mp h3
  set S' : Subgroup X := S.map P.subtype with hS'def
  have hS'P : S' ≤ P := Subgroup.map_subtype_le S
  have hS'K : S' ≤ K' := hS'P.trans hPK
  have hS'card : Nat.card S' = p ^ a := by
    rw [hS'def, Subgroup.card_map_of_injective P.subtype_injective, hS]
  have hmkS : ∀ x ∈ S', ((x : X) : X ⧸ Y) ∈ E := fun x hx => ((hPmem x).mp (hS'P hx)).1
  let fS : ↥S' →* ↥E :=
    { toFun := fun s => ⟨((s : X) : X ⧸ Y), hmkS s s.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp [QuotientGroup.mk_mul]) }
  have hfSsurj : Function.Surjective fS := by
    intro e
    obtain ⟨k, hkK, hke⟩ := hEK e.1 e.2
    have hkP : k ∈ P := (hPmem k).mpr ⟨by rw [hke]; exact e.2, hkK⟩
    obtain ⟨s, hs, n, hn, hsn⟩ := Subgroup.mem_sup_of_normal_right.mp
      (show (⟨k, hkP⟩ : ↥P) ∈ S ⊔ N.subgroupOf P by rw [htop]; exact Subgroup.mem_top _)
    have hsX : ((s : P) : X) ∈ S' := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
    refine ⟨⟨(s : P), hsX⟩, Subtype.ext ?_⟩
    show ((((s : P) : X)) : X ⧸ Y) = e.1
    have hnY : ((n : P) : X) ∈ Y := ((Subgroup.mem_subgroupOf).mp hn).1
    have hkn : ((s : P) : X) * ((n : P) : X) = k := by
      have := congrArg Subtype.val hsn
      simpa using this
    rw [← hke, ← hkn, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hnY, mul_one]
  have hcenS : ∀ z ∈ fS.ker, ∀ c : ↥S', c * z = z * c := by
    intro z hz c
    have hz1 : ((z : X) : X ⧸ Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    have hzY : (z : X) ∈ Y := (QuotientGroup.eq_one_iff _).mp hz1
    have hg := hYK (z : X) hzY (c : X) (hS'K c.2)
    have hgS : (z : X) * (c : X) * (z : X)⁻¹ * (c : X)⁻¹ ∈ S' :=
      S'.mul_mem (S'.mul_mem (S'.mul_mem z.2 c.2) (S'.inv_mem z.2)) (S'.inv_mem c.2)
    have hg1 : (z : X) * (c : X) * (z : X)⁻¹ * (c : X)⁻¹ = 1 :=
      nk_eq_one_of_mem_p_two hp2 (n := a) (dvd_of_eq hS'card) hD hgS hg
    apply Subtype.ext
    show (c : X) * (z : X) = (z : X) * (c : X)
    calc (c : X) * (z : X)
        = ((z : X) * (c : X) * (z : X)⁻¹ * (c : X)⁻¹)⁻¹ * ((z : X) * (c : X)) := by group
      _ = (z : X) * (c : X) := by rw [hg1, inv_one, one_mul]
  have hPker : IsPGroup p fS.ker := by
    apply IsPGroup.of_card_dvd_pow (n := a)
    rw [← hS'card]
    exact Subgroup.card_subgroup_dvd_card _
  have hVtop : IsElemAbelian p (⊤ : Subgroup ↥E) :=
    nk_isElemAbelian_top_of (fun u v => isMulCommutative_iff.mp hE.1 u v)
      (fun u => Subtype.ext (by simpa using hE.2 u.1 u.2))
  obtain ⟨F₀, hF₀, hF₀c⟩ := nk_exists_elemAb_sq_of_central_kernel hp2 ↥E hVtop hE9
    (Nat.card ↥S') ↥S' fS rfl hfSsurj hcenS hPker
  refine ⟨F₀.map S'.subtype, ?_, isElemAbelian_map p S'.subtype hF₀, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hS'K y.2
  · rw [Subgroup.card_map_of_injective S'.subtype_injective, hF₀c]

end QuotientMeet

section Lift

theorem nk_liftCase1 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : NKLiftCase1 p := by
  intro G _ _ H K M t hKc htH hJ hne hsimp hnab h3 hrank
  have hp1 : 1 < p := hp.out.one_lt
  have hJ2 : IsPGroup 2 ((kerIn M H).subgroupOf H) := by
    rw [hJ]
    exact isPGroup_pCoreOf_two H
  have hNX : kerIn M H ≤ H := by
    rw [hJ]
    exact Subgroup.map_subtype_le _
  have hJsolv : Group.IsSolvable ↥(kerIn M H) := by
    have hnil : Group.IsNilpotent ↥(pCoreOf 2 H) := by
      have hP2 : IsPGroup 2 ↥(pCoreOf 2 H) := by
        intro g
        obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp g.2
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨x, hx⟩
        refine ⟨k, Subtype.ext ?_⟩
        have hk' : x ^ 2 ^ k = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxg, ← map_pow, hk', map_one]
      exact hP2.isNilpotent
    rw [hJ]
    exact inferInstance
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hbij := cComp_quotient_bijOn_of_le hNX (by infer_instance) hJsolv
  have hKt : cjSub t K ∈ cComp H := conjSub_mem_cComp_of_mem hKc htH
  have hinj : E2.star M H (cjSub t K) ≠ E2.star M H K := fun h => hne (hbij.injOn hKt hKc h)
  set A : Subgroup (E2.StarQuot M H) := E2.star M H K with hAdef
  set tbar : E2.StarQuot M H := QuotientGroup.mk' ((kerIn M H).subgroupOf H) ⟨t, htH⟩ with htbar
  set c : E2.StarQuot M H →* E2.StarQuot M H := (MulAut.conj tbar).toMonoidHom with hcdef
  have hc_inj : Function.Injective c := (MulAut.conj tbar).injective
  have hA : A ∈ cComp (⊤ : Subgroup (E2.StarQuot M H)) := hbij.mapsTo hKc
  have hB : E2.star M H (cjSub t K) = A.map c := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyG : ((y : H) : G) ∈ cjSub t K := Subgroup.mem_subgroupOf.mp hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hyG
      have hkH : k ∈ H := hKH hk
      have hy_eq : y = (⟨t, htH⟩ : H) * ⟨k, hkH⟩ * (⟨t, htH⟩ : H)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hky]
        rfl
      refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' _ ⟨k, hkH⟩, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      · show tbar * QuotientGroup.mk' _ ⟨k, hkH⟩ * tbar⁻¹ = _
        rw [hy_eq, map_mul, map_mul, map_inv]
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨kH, hkH, rfl⟩ := Subgroup.mem_map.mp ha
      refine Subgroup.mem_map.mpr ⟨(⟨t, htH⟩ : H) * kH * (⟨t, htH⟩ : H)⁻¹, ?_, ?_⟩
      · apply Subgroup.mem_subgroupOf.mpr
        refine Subgroup.mem_map.mpr ⟨(kH : G), Subgroup.mem_subgroupOf.mp hkH, ?_⟩
        show t * (kH : G) * t⁻¹ = _
        simp [mul_assoc]
      · show QuotientGroup.mk' _ (⟨t, htH⟩ * kH * (⟨t, htH⟩ : H)⁻¹) = tbar * _ * tbar⁻¹
        rw [map_mul, map_mul, map_inv]
  have hBA : A ≠ A.map c := fun h => hinj (hB.trans h.symm)
  have hAsimp : IsSimpleGroup ↥A := hsimp
  have hAnc : ¬ IsMulCommutative ↥A := by
    intro hc
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (isMulCommutative_iff.mp hc a b)
  have hcen : Subgroup.center ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥A) with h | h
    · exact h
    · exfalso
      apply hAnc
      refine isMulCommutative_iff.mpr fun a b => ?_
      have ha : a ∈ Subgroup.center ↥A := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have eA : ↥A ≃* ↥(A.map c) := Subgroup.equivMapOfInjective A c hc_inj
  have hBsimp : IsSimpleGroup ↥(A.map c) := eA.isSimpleGroup_congr.mp hAsimp
  have hBnc : ¬ IsMulCommutative ↥(A.map c) := fun hc => hAnc (by
    refine isMulCommutative_iff.mpr fun a b => ?_
    apply eA.injective
    rw [map_mul, map_mul]
    exact isMulCommutative_iff.mp hc (eA a) (eA b))
  have hAq : CFSG.Open.IsQuasisimple ↥A := isQuasisimple_of_simple_nonabelian _ hAnc
  have hBq : CFSG.Open.IsQuasisimple ↥(A.map c) := isQuasisimple_of_simple_nonabelian _ hBnc
  have hBcC : A.map c ∈ cComp (⊤ : Subgroup (E2.StarQuot M H)) := by
    rw [← hB]
    exact hbij.mapsTo hKt
  have hAcomp : IsComponentOf A (⊤ : Subgroup (E2.StarQuot M H)) :=
    ⟨le_top, subnormal_of_mem_cComp hA, hAq⟩
  have hBcomp : IsComponentOf (A.map c) (⊤ : Subgroup (E2.StarQuot M H)) :=
    ⟨le_top, subnormal_of_mem_cComp hBcC, hBq⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ A.map c, a * b = b * a := by
    have h1 := CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hAcomp
      (subnormal_of_mem_cComp hBcC)
    have h2 := CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hBcomp
      (subnormal_of_mem_cComp hA)
    intro a ha b hb
    have key : ⁅A, A.map c⁆ = ⊥ → a * b = b * a := fun h => by
      have hab : ⁅a, b⁆ ∈ ⁅A, A.map c⁆ := Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
      exact hab
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd (le_antisymm h1 h2) hBA
      · exact key (by rw [Subgroup.commutator_comm]; exact h2)
    · exact key h1
  have hinter : ∀ g ∈ A, g ∈ A.map c → g = 1 := by
    intro g hgA hgB
    have hcenter : (⟨g, hgA⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro a'
      apply Subtype.ext
      exact hcomm a' a'.2 g hgB
    rw [hcen] at hcenter
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hcenter)
  have hpA : p ∣ Nat.card ↥A := h3
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) p hpA
  have hub_mem : (u : E2.StarQuot M H) ∈ A := u.2
  have hub_ord : orderOf (u : E2.StarQuot M H) = p := by
    rw [Subgroup.orderOf_coe, hu]
  have hyb_mem : c (u : E2.StarQuot M H) ∈ A.map c := Subgroup.mem_map_of_mem c hub_mem
  have hyb_ord : orderOf (c (u : E2.StarQuot M H)) = p := by
    rw [orderOf_injective c hc_inj, hub_ord]
  have hcomm' : (u : E2.StarQuot M H) * c (u : E2.StarQuot M H) =
      c (u : E2.StarQuot M H) * (u : E2.StarQuot M H) :=
    hcomm _ hub_mem _ hyb_mem
  have hind : ∀ i j : ℕ, (u : E2.StarQuot M H) ^ i * (c (u : E2.StarQuot M H)) ^ j = 1 →
      p ∣ i ∧ p ∣ j := by
    intro i j hij
    have hA_i : (u : E2.StarQuot M H) ^ i ∈ A := A.pow_mem hub_mem i
    have hB_j : (c (u : E2.StarQuot M H)) ^ j ∈ A.map c := (A.map c).pow_mem hyb_mem j
    have h1 : (u : E2.StarQuot M H) ^ i = 1 := by
      apply hinter _ hA_i
      have e : (u : E2.StarQuot M H) ^ i = ((c (u : E2.StarQuot M H)) ^ j)⁻¹ :=
        eq_inv_of_mul_eq_one_left hij
      rw [e]
      exact (A.map c).inv_mem hB_j
    have h2 : (c (u : E2.StarQuot M H)) ^ j = 1 := by
      apply hinter _ _ hB_j
      have e : (c (u : E2.StarQuot M H)) ^ j = ((u : E2.StarQuot M H) ^ i)⁻¹ :=
        eq_inv_of_mul_eq_one_right hij
      rw [e]
      exact A.inv_mem (A.pow_mem hub_mem i)
    constructor
    · have h := orderOf_dvd_of_pow_eq_one h1
      rwa [hub_ord] at h
    · have h := orderOf_dvd_of_pow_eq_one h2
      rwa [hyb_ord] at h
  obtain ⟨E₀, hE₀, hE₀9⟩ := nk_exists_elemAb_sq_of_commuting _ _ hub_ord hyb_ord hcomm' hind
  set Y : Subgroup H := (kerIn M H).subgroupOf H with hYdef
  set P : Subgroup H := E₀.comap (QuotientGroup.mk' Y) with hPdef
  have hYP : Y ≤ P := by
    intro y hy
    show QuotientGroup.mk' Y y ∈ E₀
    have h1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff (y : H)).mpr hy
    rw [h1]
    exact E₀.one_mem
  have hcomm_P : ∀ g ∈ P, ∀ q ∈ P, g * q * g⁻¹ * q⁻¹ ∈ Y := by
    intro g hg q hq
    have hgE : QuotientGroup.mk' Y g ∈ E₀ := hg
    have hqE : QuotientGroup.mk' Y q ∈ E₀ := hq
    have hc' : QuotientGroup.mk' Y g * QuotientGroup.mk' Y q =
        QuotientGroup.mk' Y q * QuotientGroup.mk' Y g :=
      congrArg Subtype.val (isMulCommutative_iff.mp hE₀.1 ⟨_, hgE⟩ ⟨_, hqE⟩)
    have h1 : QuotientGroup.mk' Y (g * q * g⁻¹ * q⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc']
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcube_P : ∀ g ∈ P, g ^ p ∈ Y := by
    intro g hg
    have hgE : QuotientGroup.mk' Y g ∈ E₀ := hg
    have h1 : QuotientGroup.mk' Y (g ^ p) = 1 := by
      rw [map_pow, hE₀.2 _ hgE]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcard_P : Nat.card P = p ^ 2 * Nat.card Y := by
    rw [hPdef, CFSG.Quasithin.H13.card_comap_mk' Y E₀, hE₀9]
  obtain ⟨F, -, hF, hF9⟩ :=
    nk_exists_elemAb_sq_of_two_kernel hp2 P Y hJ2 hYP hcomm_P hcube_P hcard_P
  have hFH : F.map H.subtype ≤ H := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hF' : IsElemAbelian p (F.map H.subtype) := isElemAbelian_map p H.subtype hF
  have hF'9 : Nat.card (F.map H.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hF9]
  have h2 := nk_two_le_pRank_of_elemAb_sq hFH hF' hF'9
  omega

theorem nk_liftCase2 {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : NKLiftCase2 p := by
  intro G _ _ H K M hKH hJ hrk hrank
  obtain ⟨E₀, hE₀, hE₀9⟩ := nk_exists_elemAb_sq_of_two_le_pRank hrk
  set Y : Subgroup H := (kerIn M H).subgroupOf H with hYdef
  set K' : Subgroup H := K.subgroupOf H with hK'def
  set D : Subgroup H := CFSG.pCore 2 H with hDdef
  have hD : IsPGroup 2 D := CFSG.pCore_isPGroup
  have hYK : ∀ y ∈ Y, ∀ k ∈ K', y * k * y⁻¹ * k⁻¹ ∈ D := by
    intro y hy k hk
    have hyJ : (y : G) ∈ kerIn M H := Subgroup.mem_subgroupOf.mp hy
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hmem := ((hJ (y : G)).mp hyJ).2 (k : G) (Subgroup.mem_sup_left hkK)
    have hmem' : ((y * k * y⁻¹ * k⁻¹ : H) : G) ∈ pCoreOf 2 H := by
      simpa using hmem
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hmem'
    have hxe : x = y * k * y⁻¹ * k⁻¹ := Subtype.ext hxg
    rw [← hxe]
    exact hx
  let E : Subgroup (E2.StarQuot M H) := E₀.map (E2.star M H K).subtype
  have hE : IsElemAbelian p E := isElemAbelian_map p _ hE₀
  have hE9 : Nat.card E = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (E2.star M H K).subtype_injective, hE₀9]
  have hEK : ∀ e ∈ E, ∃ k ∈ K', (k : E2.StarQuot M H) = e := by
    intro e he
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp he
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp x.2
    refine ⟨k, hk, ?_⟩
    rw [← hxe]
    exact hkx
  obtain ⟨F, -, hF, hF9⟩ :=
    nk_exists_elemAb_sq_of_quotient_meet hp2 Y K' D hD hYK E hE hE9 hEK
  have hFH : F.map H.subtype ≤ H := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hF' : IsElemAbelian p (F.map H.subtype) := isElemAbelian_map p H.subtype hF
  have hF'9 : Nat.card (F.map H.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hF9]
  have h2 := nk_two_le_pRank_of_elemAb_sq hFH hF' hF'9
  omega

end Lift

end CFSG.Quasithin.H13.L829NK
