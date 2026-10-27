module

public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C6Grp

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped Pointwise

section Cyc

variable {X : Type*} [Group X]

theorem pow_four_eq_one {τ : X} (h4 : orderOf τ = 4) : τ ^ 4 = 1 := by
  rw [← h4]
  exact pow_orderOf_eq_one τ

theorem sq_ne_one_of_orderOf_four {τ : X} (h4 : orderOf τ = 4) : τ * τ ≠ 1 := by
  intro h
  have h2 : τ ^ 2 = 1 := by rw [pow_two]; exact h
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h4] at this
  omega

theorem ne_one_of_orderOf_four {τ : X} (h4 : orderOf τ = 4) : τ ≠ 1 := by
  intro h
  rw [h, orderOf_one] at h4
  omega

theorem zpowers_cases {τ : X} (h4 : orderOf τ = 4) {y : X} (hy : y ∈ Subgroup.zpowers τ) :
    y = 1 ∨ y = τ ∨ y = τ * τ ∨ y = τ * τ * τ := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hm : τ ^ m = τ ^ (m % 4) := by
    have := zpow_mod_orderOf τ m
    rw [h4] at this
    exact_mod_cast this.symm
  rw [hm]
  have : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases this with h | h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; left; norm_num [zpow_ofNat, pow_two]
  · right; right; right; norm_num [zpow_ofNat, pow_succ]

theorem eq_sq_of_involution {τ : X} (h4 : orderOf τ = 4) {y : X} (hy : y ∈ Subgroup.zpowers τ)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) : y = τ * τ := by
  rcases zpowers_cases h4 hy with h | h | h | h
  · exact absurd h hy1
  · exfalso
    rw [h] at hy2
    exact sq_ne_one_of_orderOf_four h4 hy2
  · exact h
  · exfalso
    rw [h] at hy2
    have h6 : τ ^ 6 = 1 := by
      calc τ ^ 6 = τ * τ * τ * (τ * τ * τ) := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := hy2
    have := orderOf_dvd_of_pow_eq_one h6
    rw [h4] at this
    omega

theorem zpowers_cases_two {t : X} (ht2 : t * t = 1) {y : X} (hy : y ∈ Subgroup.zpowers t) :
    y = 1 ∨ y = t := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht2
  have hm : t ^ m = t ^ (m % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod m 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rw [hm]
  have : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases this with h | h <;> rw [h]
  · left; simp
  · right; simp

theorem zpowers_comm {τ a b : X} (ha : a ∈ Subgroup.zpowers τ) (hb : b ∈ Subgroup.zpowers τ) :
    a * b = b * a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow_self τ m n).eq

theorem exists_ne_one_of_card_ne {H : Subgroup X} (hH : Nat.card H ≠ 1) : ∃ u ∈ H, u ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply hH
  have : H = ⊥ := by
    rw [eq_bot_iff]
    exact fun w hw => hcon w hw
  rw [this, Subgroup.card_bot]

end Cyc

section Ctx

variable {V : Type} [CommGroup V]

structure FourCtx (A : Subgroup (MulAut V)) (τ t : MulAut V) : Prop where
  sq : ∀ v : V, v * v = 1
  card_V : Nat.card V = 16
  tau_mem : τ ∈ A
  tau_ord : orderOf τ = 4
  syl : IsSylowTwoOf (Subgroup.zpowers τ) A
  card_P : Nat.card (oTwoUpper A) = 9
  exp_P : ∀ x ∈ oTwoUpper A, x ^ 3 = 1
  comm_P : ∀ x ∈ oTwoUpper A, ∀ y ∈ oTwoUpper A, x * y = y * x
  t_mem : t ∈ A
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_inv : ∀ x ∈ oTwoUpper A, t * x * t⁻¹ = x⁻¹

theorem t_normalizes_of {P : Subgroup (MulAut V)} {t : MulAut V} (ht2 : t * t = 1)
    (hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) :
    Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set (MulAut V)) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  intro x
  constructor
  · intro hx
    rw [hinv x hx]
    exact P.inv_mem hx
  · intro hx
    have h1 := hinv _ hx
    have h2 : t * (t * x * t⁻¹) * t⁻¹ = x := by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
        _ = x := by rw [ht2, hti, ht2]; group
    rw [h2] at h1
    rw [h1]
    exact P.inv_mem hx

theorem tau_not_mem_of {P : Subgroup (MulAut V)} {τ t : MulAut V} (hτ4 : orderOf τ = 4)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (ht2 : t * t = 1) (hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) :
    τ ∉ P ⊔ Subgroup.zpowers t := by
  intro hτ
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left P (Subgroup.zpowers t)
    (t_normalizes_of ht2 hinv)
  have hτ' : τ ∈ ((P ⊔ Subgroup.zpowers t : Subgroup (MulAut V)) : Set (MulAut V)) := hτ
  rw [hset] at hτ'
  obtain ⟨p, hp, y, hy, hpy⟩ := hτ'
  have hpy' : p * y = τ := hpy
  rcases zpowers_cases_two ht2 hy with rfl | rfl
  · rw [mul_one] at hpy'
    have h3 : τ ^ 3 = 1 := by rw [← hpy']; exact hexp p hp
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hτ4] at this
    omega
  · apply sq_ne_one_of_orderOf_four hτ4
    rw [← hpy']
    have h1 := hinv p hp
    calc p * y * (p * y) = p * (y * p * y⁻¹) * (y * y) := by group
      _ = 1 := by rw [h1, ht2]; group

namespace FourCtx

variable {A : Subgroup (MulAut V)} {τ t : MulAut V}

theorem P_conj {a x : MulAut V} (ha : a ∈ A) (hx : x ∈ oTwoUpper A) :
    a * x * a⁻¹ ∈ oTwoUpper A :=
  conj_mem_oTwoUpper (Subgroup.le_normalizer ha) hx

variable [Finite V] (h : FourCtx A τ t)
include h

theorem A_eq : A = oTwoUpper A ⊔ Subgroup.zpowers τ := eq_oTwoUpper_sup_of_isSylowTwoOf h.syl

theorem mem_A {a : MulAut V} (ha : a ∈ A) :
    ∃ p ∈ oTwoUpper A, ∃ y ∈ Subgroup.zpowers τ, a = p * y := by
  have hle : Subgroup.zpowers τ ≤ Subgroup.normalizer (oTwoUpper A : Set (MulAut V)) :=
    (Subgroup.zpowers_le.mpr h.tau_mem).trans (le_normalizer_oTwoUpper A)
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left (oTwoUpper A) (Subgroup.zpowers τ) hle
  have ha' : a ∈ ((oTwoUpper A ⊔ Subgroup.zpowers τ : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [← h.A_eq]
    exact ha
  rw [hset] at ha'
  obtain ⟨p, hp, y, hy, rfl⟩ := ha'
  exact ⟨p, hp, y, hy, rfl⟩

omit [Finite V] in
theorem sq_ne_one : τ * τ ≠ 1 := sq_ne_one_of_orderOf_four h.tau_ord

theorem exists_conj : ∃ a ∈ A, t = a * (τ * τ) * a⁻¹ := by
  have hP : IsPGroup 2 (Subgroup.zpowers t) := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, pow_two, h.t_sq, one_zpow]
  obtain ⟨S', hS', hle⟩ := A4.exists_isSylowTwoOf_ge (Subgroup.zpowers_le.mpr h.t_mem) hP
  obtain ⟨a, haA, ha⟩ := A4.exists_conj_of_isSylowTwoOf h.syl hS'
  have h1 : a⁻¹ * t * a ∈ Subgroup.zpowers τ := (ha t).mp (hle (Subgroup.mem_zpowers t))
  have h2 : (a⁻¹ * t * a) * (a⁻¹ * t * a) = 1 := by
    calc (a⁻¹ * t * a) * (a⁻¹ * t * a) = a⁻¹ * (t * t) * a := by group
      _ = 1 := by rw [h.t_sq]; group
  have h3 : a⁻¹ * t * a ≠ 1 := by
    intro h4
    apply h.t_ne
    calc t = a * (a⁻¹ * t * a) * a⁻¹ := by group
      _ = 1 := by rw [h4]; group
  have h5 := eq_sq_of_involution h.tau_ord h1 h2 h3
  refine ⟨a, haA, ?_⟩
  calc t = a * (a⁻¹ * t * a) * a⁻¹ := by group
    _ = a * (τ * τ) * a⁻¹ := by rw [h5]

theorem s_inv {x : MulAut V} (hx : x ∈ oTwoUpper A) : (τ * τ) * x * (τ * τ)⁻¹ = x⁻¹ := by
  obtain ⟨a, haA, hta⟩ := h.exists_conj
  have hs : τ * τ = a⁻¹ * t * a := by rw [hta]; group
  have hx' : a * x * a⁻¹ ∈ oTwoUpper A := P_conj haA hx
  have h1 := h.t_inv _ hx'
  rw [hs]
  calc a⁻¹ * t * a * x * (a⁻¹ * t * a)⁻¹ = a⁻¹ * (t * (a * x * a⁻¹) * t⁻¹) * a := by group
    _ = a⁻¹ * (a * x * a⁻¹)⁻¹ * a := by rw [h1]
    _ = x⁻¹ := by group

omit [Finite V] h in
theorem comm_zpowers_s {y : MulAut V} (hy : y ∈ Subgroup.zpowers τ) : y * (τ * τ) = (τ * τ) * y := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : Commute (τ ^ m) τ := (Commute.refl τ).zpow_left m
  exact (hc.mul_right hc).eq

theorem exists_t_eq : ∃ q ∈ oTwoUpper A, t = q * (τ * τ) := by
  obtain ⟨a, haA, hta⟩ := h.exists_conj
  obtain ⟨p, hp, y, hy, rfl⟩ := h.mem_A haA
  have hc := comm_zpowers_s hy
  refine ⟨p * p, (oTwoUpper A).mul_mem hp hp, ?_⟩
  rw [hta]
  have e1 : p * y * (τ * τ) * (p * y)⁻¹ = p * (τ * τ) * p⁻¹ := by
    calc p * y * (τ * τ) * (p * y)⁻¹ = p * (y * (τ * τ) * y⁻¹) * p⁻¹ := by group
      _ = p * (τ * τ) * p⁻¹ := by rw [hc]; group
  rw [e1]
  have e2 : (τ * τ) * p⁻¹ * (τ * τ)⁻¹ = p := by
    rw [h.s_inv ((oTwoUpper A).inv_mem hp), inv_inv]
  calc p * (τ * τ) * p⁻¹ = p * ((τ * τ) * p⁻¹ * (τ * τ)⁻¹) * (τ * τ) := by group
    _ = p * p * (τ * τ) := by rw [e2]

theorem s_mem_A₀ : τ * τ ∈ oTwoUpper A ⊔ Subgroup.zpowers t := by
  obtain ⟨q, hq, hqt⟩ := h.exists_t_eq
  have : τ * τ = q⁻¹ * t := by rw [hqt]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((oTwoUpper A).inv_mem hq))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

omit [Finite V] in
theorem t_normalizes : Subgroup.zpowers t ≤ Subgroup.normalizer (oTwoUpper A : Set (MulAut V)) :=
  t_normalizes_of h.t_sq h.t_inv

omit [Finite V] in
theorem tau_not_mem : τ ∉ oTwoUpper A ⊔ Subgroup.zpowers t :=
  tau_not_mem_of h.tau_ord h.exp_P h.t_sq h.t_inv

theorem inf_A₀ :
    Subgroup.zpowers τ ⊓ (oTwoUpper A ⊔ Subgroup.zpowers t) = Subgroup.zpowers (τ * τ) := by
  apply le_antisymm
  · rintro x ⟨hx, hxA⟩
    rcases zpowers_cases h.tau_ord hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hxA h.tau_not_mem
    · exact Subgroup.mem_zpowers _
    · exfalso
      apply h.tau_not_mem
      have : τ = (τ * τ * τ) * (τ * τ)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ hxA (Subgroup.inv_mem _ h.s_mem_A₀)
  · intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨?_, ?_⟩
    · exact Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers τ) (Subgroup.mem_zpowers τ)) m
    · exact Subgroup.zpow_mem _ h.s_mem_A₀ m

end FourCtx

@[expose] def hOf (τ g : MulAut V) : MulAut V := τ * g * τ⁻¹

structure FourGen (A : Subgroup (MulAut V)) (τ g : MulAut V) : Prop where
  gP : g ∈ oTwoUpper A
  g1 : g ≠ 1
  g3 : g ^ 3 = 1
  tau_h : τ * hOf τ g * τ⁻¹ = g⁻¹
  card_U₁ : Nat.card (fixOf g) = 4
  card_U₂ : Nat.card (fixOf (hOf τ g)) = 4
  inf : fixOf g ⊓ fixOf (hOf τ g) = ⊥
  sup : fixOf g ⊔ fixOf (hOf τ g) = ⊤
  param : ∀ x ∈ oTwoUpper A, ∃ i j : ℕ, x = g ^ i * (hOf τ g) ^ j

theorem pow_apply_of_fix {g : MulAut V} {u : V} (hu : g u = u) (n : ℕ) : (g ^ n) u = u :=
  apply_eq_of_mem_zpowers hu (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) n)

theorem pow_mem_zpowers_of_mod {x : MulAut V} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {n : ℕ}
    (hn : n % 3 ≠ 0) : x ∈ Subgroup.zpowers (x ^ n) := by
  have hord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  apply A4.mem_zpowers_pow_of_coprime
  rw [hord]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three |>.mpr (by omega)).symm

theorem fixOf_pow_eq {x : MulAut V} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {n : ℕ} (hn : n % 3 ≠ 0) :
    fixOf (x ^ n) = fixOf x := by
  apply le_antisymm
  · exact fixOf_zpowers (pow_mem_zpowers_of_mod hx3 hx1 hn)
  · exact fixOf_zpowers (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) n)

theorem pow_eq_one_of_mod {x : MulAut V} (hx3 : x ^ 3 = 1) {n : ℕ} (hn : n % 3 = 0) :
    x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hn
  rw [pow_mul, hx3, one_pow]

theorem fixed_eq_one_of_pair {g h : MulAut V} (hgh : g * h = h * g) (hg3 : g ^ 3 = 1)
    (hh3 : h ^ 3 = 1) (hg1 : g ≠ 1) (hh1 : h ≠ 1) (hinf : fixOf g ⊓ fixOf h = ⊥)
    (hsup : fixOf g ⊔ fixOf h = ⊤) {i j : ℕ} (hi : i % 3 ≠ 0) (hj : j % 3 ≠ 0) {w : V}
    (hw : (g ^ i * h ^ j) w = w) : w = 1 := by
  have hcomm : g ^ i * h ^ j = h ^ j * g ^ i := (Commute.pow_pow (show Commute g h from hgh) i j).eq
  have hw' : w ∈ fixOf g ⊔ fixOf h := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw'
  have ha' : g a = a := ha
  have hb' : h b = b := hb
  have e1 : ∀ n : ℕ, (h ^ n) b = b := fun n => pow_apply_of_fix hb' n
  have e2 : ∀ n : ℕ, (g ^ n) a = a := fun n => pow_apply_of_fix ha' n
  have e3 : (g ^ i) ((h ^ j) a) = (h ^ j) a := by
    have : ((g ^ i) * (h ^ j)) a = ((h ^ j) * (g ^ i)) a := by rw [hcomm]
    calc (g ^ i) ((h ^ j) a) = ((g ^ i) * (h ^ j)) a := rfl
      _ = ((h ^ j) * (g ^ i)) a := this
      _ = (h ^ j) ((g ^ i) a) := rfl
      _ = (h ^ j) a := by rw [e2]
  have e4 : (h ^ j) ((g ^ i) b) = (g ^ i) b := by
    have : ((h ^ j) * (g ^ i)) b = ((g ^ i) * (h ^ j)) b := by rw [hcomm]
    calc (h ^ j) ((g ^ i) b) = ((h ^ j) * (g ^ i)) b := rfl
      _ = ((g ^ i) * (h ^ j)) b := this
      _ = (g ^ i) ((h ^ j) b) := rfl
      _ = (g ^ i) b := by rw [e1]
  have hmul : (g ^ i * h ^ j) (a * b) = (h ^ j) a * (g ^ i) b := by
    show (g ^ i) ((h ^ j) (a * b)) = _
    rw [map_mul, map_mul, e1, e3]
  rw [hmul] at hw
  have hA : (h ^ j) a ∈ fixOf g := by
    show g ((h ^ j) a) = (h ^ j) a
    have hc : g * h ^ j = h ^ j * g := (Commute.pow_right (show Commute g h from hgh) j).eq
    calc g ((h ^ j) a) = (g * h ^ j) a := rfl
      _ = (h ^ j * g) a := by rw [hc]
      _ = (h ^ j) (g a) := rfl
      _ = (h ^ j) a := by rw [ha']
  have hB : (g ^ i) b ∈ fixOf h := by
    show h ((g ^ i) b) = (g ^ i) b
    have hc : h * g ^ i = g ^ i * h := (Commute.pow_right (show Commute h g from hgh.symm) i).eq
    calc h ((g ^ i) b) = (h * g ^ i) b := rfl
      _ = (g ^ i * h) b := by rw [hc]
      _ = (g ^ i) (h b) := rfl
      _ = (g ^ i) b := by rw [hb']
  have key : (h ^ j) a / a = b / (g ^ i) b := by
    have : (h ^ j) a * (g ^ i) b = a * b := hw
    rw [div_eq_div_iff_mul_eq_mul, this, mul_comm]
  have hkey1 : (h ^ j) a / a ∈ fixOf g ⊓ fixOf h :=
    ⟨(fixOf g).div_mem hA ha, by rw [key]; exact (fixOf h).div_mem hb hB⟩
  rw [hinf, Subgroup.mem_bot, div_eq_one] at hkey1
  have hkey2 : b / (g ^ i) b = 1 := by
    rw [← key, div_eq_one]
    exact hkey1
  rw [div_eq_one] at hkey2
  have ha1 : a = 1 := by
    have h1 : h a = a := by
      have : a ∈ fixOf (h ^ j) := hkey1
      rw [fixOf_pow_eq hh3 hh1 hj] at this
      exact this
    have : a ∈ fixOf g ⊓ fixOf h := ⟨ha, h1⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have hb1 : b = 1 := by
    have h1 : g b = b := by
      have : b ∈ fixOf (g ^ i) := hkey2.symm
      rw [fixOf_pow_eq hg3 hg1 hi] at this
      exact this
    have : b ∈ fixOf g ⊓ fixOf h := ⟨h1, hb⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  rw [ha1, hb1, mul_one]

namespace FourCtx

variable {A : Subgroup (MulAut V)} {τ t : MulAut V} [Finite V] (h : FourCtx A τ t)
include h

theorem exists_gen : ∃ g : MulAut V, FourGen A τ g := by
  obtain ⟨g, hgP, h₀, hh₀P, hg1, hh1, hg4, hh4, hinf, hsup, hparam⟩ :=
    exists_pair h.card_P h.exp_P h.comm_P h.card_V h.sq
  have hg3 := h.exp_P g hgP
  have hh3 := h.exp_P h₀ hh₀P
  have hgh : g * h₀ = h₀ * g := h.comm_P g hgP h₀ hh₀P
  have hyP : τ * g * τ⁻¹ ∈ oTwoUpper A := P_conj h.tau_mem hgP
  have hy1 : τ * g * τ⁻¹ ≠ 1 := by
    intro h1
    apply hg1
    calc g = τ⁻¹ * (τ * g * τ⁻¹) * τ := by group
      _ = 1 := by rw [h1]; group
  have hy3 : (τ * g * τ⁻¹) ^ 3 = 1 := by rw [conj_pow, hg3]; group
  obtain ⟨i, j, hij⟩ := hparam _ hyP
  have hτy : τ * (τ * g * τ⁻¹) * τ⁻¹ = g⁻¹ := by
    calc τ * (τ * g * τ⁻¹) * τ⁻¹ = (τ * τ) * g * (τ * τ)⁻¹ := by group
      _ = g⁻¹ := h.s_inv hgP
  have hi0 : i % 3 = 0 := by
    by_contra hi
    by_cases hj : j % 3 = 0
    ·
      have hhj : h₀ ^ j = 1 := pow_eq_one_of_mod hh3 hj
      rw [hhj, mul_one] at hij
      have hord : orderOf g = 3 := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact orderOf_eq_prime hg3 hg1
      have hii : i * i % 3 = 1 := by
        have : i % 3 = 1 ∨ i % 3 = 2 := by omega
        rcases this with h' | h' <;> rw [Nat.mul_mod, h']
      have e1 : g⁻¹ = g ^ (i * i) := by
        calc g⁻¹ = τ * (τ * g * τ⁻¹) * τ⁻¹ := hτy.symm
          _ = τ * g ^ i * τ⁻¹ := by rw [hij]
          _ = (τ * g * τ⁻¹) ^ i := (conj_pow).symm
          _ = (g ^ i) ^ i := by rw [hij]
          _ = g ^ (i * i) := (pow_mul g i i).symm
      have e2 : g ^ (i * i) = g := by
        rw [← pow_mod_orderOf, hord, hii, pow_one]
      rw [e2] at e1
      apply hg1
      have h2 : g * g = 1 := by
        have := mul_inv_cancel g
        rwa [e1] at this
      calc g = g * (g * g) := by rw [h2, mul_one]
        _ = g ^ 3 := by rw [pow_succ, pow_succ, pow_one, mul_assoc]
        _ = 1 := hg3
    ·
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ fixOf g, u ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : fixOf g = ⊥ := by
          rw [eq_bot_iff]
          exact fun w hw => hcon w hw
        rw [this, Subgroup.card_bot] at hg4
        omega
      have hfix : (g ^ i * h₀ ^ j) (τ u) = τ u := by
        rw [← hij]
        show τ (g (τ⁻¹ (τ u))) = τ u
        have hgu : g u = u := hu
        simp [hgu]
      have := fixed_eq_one_of_pair hgh hg3 hh3 hg1 hh1 hinf hsup hi hj hfix
      apply hu1
      have h2 : τ u = τ 1 := by rw [this, map_one]
      exact τ.injective h2
  have hgi : g ^ i = 1 := pow_eq_one_of_mod hg3 hi0
  rw [hgi, one_mul] at hij
  have hj0 : j % 3 ≠ 0 := by
    intro hj
    apply hy1
    rw [hij, pow_eq_one_of_mod hh3 hj]
  have hfixy : fixOf (hOf τ g) = fixOf h₀ := by
    unfold hOf
    rw [hij]
    exact fixOf_pow_eq hh3 hh1 hj0
  have hh₀y : h₀ ∈ Subgroup.zpowers (τ * g * τ⁻¹) := by
    rw [hij]
    exact pow_mem_zpowers_of_mod hh3 hh1 hj0
  refine ⟨g, ⟨hgP, hg1, hg3, hτy, hg4, ?_, ?_, ?_, ?_⟩⟩
  · rw [hfixy]; exact hh4
  · rw [hfixy]; exact hinf
  · rw [hfixy]; exact hsup
  · intro x hx
    obtain ⟨a, b, rfl⟩ := hparam x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (Subgroup.pow_mem _ hh₀y b)
    obtain ⟨c, hc⟩ := exists_nat_pow_eq_zpow hy3 hy1 m
    exact ⟨a, c, by rw [hOf, ← hc, hm]⟩

end FourCtx

@[expose] def zOne (τ g : MulAut V) : Subgroup V := fixOf (τ * τ) ⊓ fixOf g

@[expose] def zTwo (τ g : MulAut V) : Subgroup V := fixOf (τ * τ) ⊓ fixOf (hOf τ g)

namespace FourGen

variable {A : Subgroup (MulAut V)} {τ t g : MulAut V}

theorem h_mem (h : FourCtx A τ t) (hg : FourGen A τ g) : hOf τ g ∈ oTwoUpper A :=
  FourCtx.P_conj h.tau_mem hg.gP

theorem h3 (h : FourCtx A τ t) (hg : FourGen A τ g) : hOf τ g ^ 3 = 1 :=
  h.exp_P _ (h_mem h hg)

theorem h1' (hg : FourGen A τ g) : hOf τ g ≠ 1 := by
  intro h1
  apply hg.g1
  unfold hOf at h1
  calc g = τ⁻¹ * (τ * g * τ⁻¹) * τ := by group
    _ = 1 := by rw [h1]; group

theorem gh_comm (h : FourCtx A τ t) (hg : FourGen A τ g) : g * hOf τ g = hOf τ g * g :=
  h.comm_P _ hg.gP _ (h_mem h hg)

theorem tau_U₁ {u : V} (hu : u ∈ fixOf g) : τ u ∈ fixOf (hOf τ g) := by
  have hgu : g u = u := hu
  show (τ * g * τ⁻¹) (τ u) = τ u
  show τ (g (τ⁻¹ (τ u))) = τ u
  simp [hgu]

theorem tau_U₂ (hg : FourGen A τ g) {u : V} (hu : u ∈ fixOf (hOf τ g)) : τ u ∈ fixOf g := by
  have hhu : (hOf τ g) u = u := hu
  have h1 : (τ * hOf τ g * τ⁻¹) (τ u) = τ u := by
    show τ ((hOf τ g) (τ⁻¹ (τ u))) = τ u
    simp [hhu]
  rw [hg.tau_h] at h1
  show g (τ u) = τ u
  calc g (τ u) = g (g⁻¹ (τ u)) := by rw [h1]
    _ = τ u := by simp

theorem tau3_U₁ (hg : FourGen A τ g) {u : V} (hu : u ∈ fixOf g) :
    (τ * τ * τ) u ∈ fixOf (hOf τ g) :=
  tau_U₁ (tau_U₂ hg (tau_U₁ hu))

theorem tau3_U₂ (hg : FourGen A τ g) {u : V} (hu : u ∈ fixOf (hOf τ g)) :
    (τ * τ * τ) u ∈ fixOf g :=
  tau_U₂ hg (tau_U₁ (tau_U₂ hg hu))

theorem s_U₁ (hg : FourGen A τ g) {u : V} (hu : u ∈ fixOf g) : (τ * τ) u ∈ fixOf g :=
  tau_U₂ hg (tau_U₁ hu)

theorem s_U₂ (hg : FourGen A τ g) {u : V} (hu : u ∈ fixOf (hOf τ g)) :
    (τ * τ) u ∈ fixOf (hOf τ g) :=
  tau_U₁ (tau_U₂ hg hu)

theorem decomp_unique (hg : FourGen A τ g) {a a' b b' : V} (ha : a ∈ fixOf g) (ha' : a' ∈ fixOf g)
    (hb : b ∈ fixOf (hOf τ g)) (hb' : b' ∈ fixOf (hOf τ g)) (hab : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have key : a / a' = b' / b := by
    rw [div_eq_div_iff_mul_eq_mul, hab, mul_comm]
  have h1 : a / a' ∈ fixOf g ⊓ fixOf (hOf τ g) :=
    ⟨(fixOf g).div_mem ha ha', by rw [key]; exact (fixOf (hOf τ g)).div_mem hb' hb⟩
  rw [hg.inf, Subgroup.mem_bot, div_eq_one] at h1
  refine ⟨h1, ?_⟩
  rw [h1] at hab
  exact mul_left_cancel hab

end FourGen

namespace FourCtx

variable {A : Subgroup (MulAut V)} {τ t : MulAut V}

theorem s_sq_apply (h : FourCtx A τ t) (u : V) : (τ * τ) ((τ * τ) u) = u := by
  have h4 : (τ * τ) * (τ * τ) = 1 := by
    have := pow_four_eq_one h.tau_ord
    calc (τ * τ) * (τ * τ) = τ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  exact congrArg (fun φ : MulAut V => φ u) h4

theorem s_mul_s (h : FourCtx A τ t) : (τ * τ) * (τ * τ) = 1 := by
  have := pow_four_eq_one h.tau_ord
  calc (τ * τ) * (τ * τ) = τ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := this

theorem tau_inv_eq (h : FourCtx A τ t) : τ⁻¹ = τ * τ * τ := by
  have h4 := pow_four_eq_one h.tau_ord
  have : τ * (τ * τ * τ) = 1 := by
    calc τ * (τ * τ * τ) = τ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h4
  exact inv_eq_of_mul_eq_one_right this

end FourCtx

namespace FourGen

variable {A : Subgroup (MulAut V)} {τ t g : MulAut V} [Finite V]

theorem exists_moved (h : FourCtx A τ t) (hg : FourGen A τ g) :
    ∃ a ∈ fixOf g, (τ * τ) a ≠ a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_ne (H := fixOf g) (by rw [hg.card_U₁]; norm_num)
  have hh3 := h3 h hg
  have hinv := h.s_inv (h_mem h hg)
  have hsu : (τ * τ) u = u := hcon u hu
  have hsiu : (τ * τ)⁻¹ u = u := by
    calc (τ * τ)⁻¹ u = (τ * τ)⁻¹ ((τ * τ) u) := by rw [hsu]
      _ = u := by simp
  have hhu : (hOf τ g) u ∈ fixOf g := by
    have := gh_comm h hg
    show g ((hOf τ g) u) = (hOf τ g) u
    calc g ((hOf τ g) u) = (g * hOf τ g) u := rfl
      _ = (hOf τ g * g) u := by rw [this]
      _ = (hOf τ g) (g u) := rfl
      _ = (hOf τ g) u := by rw [show g u = u from hu]
  have hshu : (τ * τ) ((hOf τ g) u) = (hOf τ g) u := hcon _ hhu
  have e1 : (hOf τ g)⁻¹ u = (hOf τ g) u := by
    calc (hOf τ g)⁻¹ u = ((τ * τ) * hOf τ g * (τ * τ)⁻¹) u := by rw [hinv]
      _ = (τ * τ) ((hOf τ g) ((τ * τ)⁻¹ u)) := rfl
      _ = (τ * τ) ((hOf τ g) u) := by rw [hsiu]
      _ = (hOf τ g) u := hshu
  have e2 : (hOf τ g) u = u := by
    have h4 : (hOf τ g) ((hOf τ g)⁻¹ u) = u := by simp
    rw [e1] at h4
    have h5 := apply_cube_c4 hh3 u
    rw [h4] at h5
    exact h5
  have : u ∈ fixOf g ⊓ fixOf (hOf τ g) := ⟨hu, e2⟩
  rw [hg.inf, Subgroup.mem_bot] at this
  exact hu1 this

theorem card_zOne (h : FourCtx A τ t) (hg : FourGen A τ g) : Nat.card (zOne τ g) = 2 := by
  obtain ⟨a, ha, hsa⟩ := exists_moved h hg
  have hFle : zOne τ g ≤ fixOf g := inf_le_right
  have hdvd : Nat.card (zOne τ g) ∣ 4 := by
    rw [← hg.card_U₁]
    exact Subgroup.card_dvd_of_le hFle
  have hsU := s_U₁ hg ha
  have hz : a * (τ * τ) a ∈ zOne τ g := by
    refine ⟨?_, (fixOf g).mul_mem ha hsU⟩
    show (τ * τ) (a * (τ * τ) a) = a * (τ * τ) a
    rw [map_mul, FourCtx.s_sq_apply h a, mul_comm]
  have hz1 : a * (τ * τ) a ≠ 1 := by
    intro h1
    apply hsa
    have : (τ * τ) a = a⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right (h.sq a)
  have hne1 : Nat.card (zOne τ g) ≠ 1 := by
    intro h1
    have : zOne τ g = ⊥ := Subgroup.card_eq_one.mp h1
    rw [this] at hz
    exact hz1 (Subgroup.mem_bot.mp hz)
  have hne4 : Nat.card (zOne τ g) ≠ 4 := by
    intro h4
    have heq : zOne τ g = fixOf g :=
      Subgroup.eq_of_le_of_card_ge hFle (by rw [h4, hg.card_U₁])
    have : a ∈ zOne τ g := by rw [heq]; exact ha
    exact hsa this.1
  have hle : Nat.card (zOne τ g) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card (zOne τ g) := Nat.card_pos
  interval_cases hc : Nat.card (zOne τ g) <;> simp_all

omit [Finite V] in
theorem zTwo_eq_map (h : FourCtx A τ t) (hg : FourGen A τ g) :
    zTwo τ g = (zOne τ g).map τ.toMonoidHom := by
  ext w
  constructor
  · intro hw
    have hw' : w ∈ fixOf (hOf τ g) := hw.2
    have hws : (τ * τ) w = w := hw.1
    refine ⟨(τ * τ * τ) w, ⟨?_, tau3_U₂ hg hw'⟩, ?_⟩
    · show (τ * τ) ((τ * τ * τ) w) = (τ * τ * τ) w
      have : (τ * τ) ((τ * τ * τ) w) = (τ * τ * τ) ((τ * τ) w) := rfl
      rw [this, hws]
    · show τ ((τ * τ * τ) w) = w
      have := FourCtx.s_sq_apply h w
      exact this
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, tau_U₁ hz.2⟩
    show (τ * τ) (τ z) = τ z
    have : (τ * τ) (τ z) = τ ((τ * τ) z) := rfl
    rw [this, show (τ * τ) z = z from hz.1]

theorem card_zTwo (h : FourCtx A τ t) (hg : FourGen A τ g) : Nat.card (zTwo τ g) = 2 := by
  rw [zTwo_eq_map h hg, Subgroup.card_map_of_injective τ.injective, card_zOne h hg]

omit [Finite V] in
theorem zOne_inf_zTwo (hg : FourGen A τ g) : zOne τ g ⊓ zTwo τ g = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ fixOf g ⊓ fixOf (hOf τ g) := ⟨hx.1.2, hx.2.2⟩
  rw [hg.inf] at this
  exact this

omit [Finite V] in
theorem fixOf_s_eq (hg : FourGen A τ g) :
    fixOf (τ * τ) = zOne τ g ⊔ zTwo τ g := by
  apply le_antisymm
  · intro w hw
    have hw' : w ∈ fixOf g ⊔ fixOf (hOf τ g) := by rw [hg.sup]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw'
    have hws : (τ * τ) (a * b) = a * b := hw
    rw [map_mul] at hws
    obtain ⟨h1, h2⟩ := decomp_unique hg (s_U₁ hg ha) ha (s_U₂ hg hb) hb hws
    exact Subgroup.mul_mem_sup ⟨h1, ha⟩ ⟨h2, hb⟩
  · exact sup_le inf_le_left inf_le_left


omit [Finite V] in
theorem apply_mem_fixOf_of_comm {x y : MulAut V} (hxy : x * y = y * x) {w : V}
    (hw : w ∈ fixOf y) : x w ∈ fixOf y := by
  have hw' : y w = w := hw
  show y (x w) = x w
  calc y (x w) = (y * x) w := rfl
    _ = (x * y) w := by rw [hxy]
    _ = x (y w) := rfl
    _ = x w := by rw [hw']

theorem exists_ne_one_zOne (h : FourCtx A τ t) (hg : FourGen A τ g) :
    ∃ z ∈ zOne τ g, z ≠ 1 :=
  exists_ne_one_of_card_ne (by rw [card_zOne h hg]; norm_num)

theorem exists_ne_one_zTwo (h : FourCtx A τ t) (hg : FourGen A τ g) :
    ∃ z ∈ zTwo τ g, z ≠ 1 :=
  exists_ne_one_of_card_ne (by rw [card_zTwo h hg]; norm_num)

omit [Finite V] in
theorem s_mem_zpowers (τ : MulAut V) : τ * τ ∈ Subgroup.zpowers τ :=
  Subgroup.mul_mem _ (Subgroup.mem_zpowers τ) (Subgroup.mem_zpowers τ)

omit [Finite V] in
theorem P_U₂ (h : FourCtx A τ t) (hg : FourGen A τ g) {x : MulAut V} (hx : x ∈ oTwoUpper A) {w : V}
    (hw : w ∈ fixOf (hOf τ g)) : x w ∈ fixOf (hOf τ g) :=
  apply_mem_fixOf_of_comm (h.comm_P x hx _ (h_mem h hg)) hw

omit [Finite V] in
theorem P_U₁ (h : FourCtx A τ t) (hg : FourGen A τ g) {x : MulAut V} (hx : x ∈ oTwoUpper A) {w : V}
    (hw : w ∈ fixOf g) : x w ∈ fixOf g :=
  apply_mem_fixOf_of_comm (h.comm_P x hx _ hg.gP) hw

theorem mem_Cbar (h : FourCtx A τ t) (hg : FourGen A τ g) {a : MulAut V} (ha : a ∈ A)
    (hfix : a ∈ fixingV (zOne τ g : Set V)) :
    ∃ i : ℕ, ∃ y ∈ Subgroup.zpowers (τ * τ), a = g ^ i * y := by
  obtain ⟨p, hp, y', hy', rfl⟩ := h.mem_A ha
  obtain ⟨i, j, rfl⟩ := hg.param p hp
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_zOne h hg
  have haz : (g ^ i * hOf τ g ^ j * y') z = z := hfix z hz
  have hzU₁ : z ∈ fixOf g := hz.2
  have hzs : (τ * τ) z = z := hz.1
  have hh3 := h3 h hg
  have hh1 := h1' hg
  have hswap : ∀ w : V, w ∈ fixOf (hOf τ g) → (g ^ i * hOf τ g ^ j) w ∈ fixOf (hOf τ g) := by
    intro w hw
    have e1 : (hOf τ g ^ j) w = w := pow_apply_of_fix hw j
    show (g ^ i) ((hOf τ g ^ j) w) ∈ _
    rw [e1]
    exact P_U₂ h hg ((oTwoUpper A).pow_mem hg.gP i) hw
  have hfixcase : ∀ y'' ∈ Subgroup.zpowers (τ * τ), y'' z = z →
      (g ^ i * hOf τ g ^ j * y'') z = z → ∃ i' : ℕ, ∃ y ∈ Subgroup.zpowers (τ * τ),
        g ^ i * hOf τ g ^ j * y'' = g ^ i' * y := by
    intro y'' hy'' hyz hz''
    have h1 : (g ^ i * hOf τ g ^ j) z = z := by
      have : (g ^ i * hOf τ g ^ j * y'') z = (g ^ i * hOf τ g ^ j) (y'' z) := rfl
      rw [this, hyz] at hz''
      exact hz''
    have hjz : j % 3 = 0 := by
      by_contra hj
      have hU : (hOf τ g ^ j) z ∈ fixOf g :=
        apply_mem_fixOf_of_comm (Commute.pow_left (show Commute (hOf τ g) g from
          (gh_comm h hg).symm) j).eq hzU₁
      have h2 : (g ^ i) ((hOf τ g ^ j) z) = (hOf τ g ^ j) z :=
        pow_apply_of_fix (show g ((hOf τ g ^ j) z) = (hOf τ g ^ j) z from hU) i
      have h3' : (hOf τ g ^ j) z = z := by
        have : (g ^ i * hOf τ g ^ j) z = (g ^ i) ((hOf τ g ^ j) z) := rfl
        rw [this, h2] at h1
        exact h1
      have h4 : z ∈ fixOf (hOf τ g ^ j) := h3'
      rw [fixOf_pow_eq hh3 hh1 hj] at h4
      have h5 : z ∈ fixOf g ⊓ fixOf (hOf τ g) := ⟨hzU₁, h4⟩
      rw [hg.inf, Subgroup.mem_bot] at h5
      exact hz1 h5
    refine ⟨i, y'', hy'', ?_⟩
    rw [pow_eq_one_of_mod hh3 hjz, mul_one]
  rcases zpowers_cases h.tau_ord hy' with h1 | h1 | h1 | h1
  ·
    exact hfixcase y' (by rw [h1]; exact Subgroup.one_mem _) (by rw [h1]; rfl) haz
  ·
    exfalso
    have hyz : y' z ∈ fixOf (hOf τ g) := by rw [h1]; exact tau_U₁ hzU₁
    have h2 := hswap _ hyz
    have e : (g ^ i * hOf τ g ^ j) (y' z) = z := haz
    rw [e] at h2
    have h5 : z ∈ fixOf g ⊓ fixOf (hOf τ g) := ⟨hzU₁, h2⟩
    rw [hg.inf, Subgroup.mem_bot] at h5
    exact hz1 h5
  ·
    exact hfixcase y' (by rw [h1]; exact Subgroup.mem_zpowers _) (by rw [h1]; exact hzs) haz
  ·
    exfalso
    have hyz : y' z ∈ fixOf (hOf τ g) := by rw [h1]; exact tau3_U₁ hg hzU₁
    have h2 := hswap _ hyz
    have e : (g ^ i * hOf τ g ^ j) (y' z) = z := haz
    rw [e] at h2
    have h5 : z ∈ fixOf g ⊓ fixOf (hOf τ g) := ⟨hzU₁, h2⟩
    rw [hg.inf, Subgroup.mem_bot] at h5
    exact hz1 h5

omit [Finite V] in
theorem zpowers_s_le (τ : MulAut V) : Subgroup.zpowers (τ * τ) ≤ Subgroup.zpowers τ :=
  Subgroup.zpowers_le.mpr (s_mem_zpowers τ)

omit [Finite V] in
theorem mem_Cbar_of (h : FourCtx A τ t) (hg : FourGen A τ g) (i : ℕ) {y : MulAut V}
    (hy : y ∈ Subgroup.zpowers (τ * τ)) : g ^ i * y ∈ sixCbar A (zOne τ g) := by
  refine ⟨A.mul_mem (A.pow_mem (oTwoUpper_le A hg.gP) i)
    ((Subgroup.zpowers_le.mpr h.tau_mem) (zpowers_s_le τ hy)), fun z hz => ?_⟩
  have hyz : y z = z := apply_eq_of_mem_zpowers (show (τ * τ) z = z from hz.1) hy
  show (g ^ i) (y z) = z
  rw [hyz]
  exact pow_apply_of_fix (show g z = z from hz.2) i

theorem Cbar_eq (h : FourCtx A τ t) (hg : FourGen A τ g) :
    sixCbar A (zOne τ g) = Subgroup.zpowers g ⊔ Subgroup.zpowers (τ * τ) := by
  apply le_antisymm
  · rintro a ⟨ha, hfix⟩
    obtain ⟨i, y, hy, rfl⟩ := mem_Cbar h hg ha hfix
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) i) hy
  · refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      simpa using mem_Cbar_of h hg 1 (Subgroup.one_mem _)
    · rw [Subgroup.zpowers_le]
      simpa using mem_Cbar_of h hg 0 (Subgroup.mem_zpowers _)

omit [Finite V] in
theorem g_mem_Cbar (h : FourCtx A τ t) (hg : FourGen A τ g) : g ∈ sixCbar A (zOne τ g) := by
  simpa using mem_Cbar_of h hg 1 (Subgroup.one_mem _)

omit [Finite V] in
theorem s_mem_Cbar (h : FourCtx A τ t) (hg : FourGen A τ g) :
    τ * τ ∈ sixCbar A (zOne τ g) := by
  simpa using mem_Cbar_of h hg 0 (Subgroup.mem_zpowers _)

omit [Finite V] in
theorem card_zpowers_s (h : FourCtx A τ t) : Nat.card (Subgroup.zpowers (τ * τ)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact FourCtx.s_mul_s h) h.sq_ne_one

theorem s_normalizes (h : FourCtx A τ t) (hg : FourGen A τ g) :
    Subgroup.zpowers (τ * τ) ≤ Subgroup.normalizer (Subgroup.zpowers g : Set (MulAut V)) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  have hsg := h.s_inv hg.gP
  have hss := FourCtx.s_mul_s h
  have hsi : (τ * τ)⁻¹ = τ * τ := inv_eq_of_mul_eq_one_right hss
  have key : ∀ m : ℤ, (τ * τ) * g ^ m * (τ * τ)⁻¹ = (g⁻¹) ^ m := by
    intro m
    rw [← hsg, conj_zpow]
  intro x
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [key]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)) m
  · intro hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hx' : x = (τ * τ) * (τ * τ) * x * ((τ * τ)⁻¹ * (τ * τ)⁻¹) := by
      rw [hss, hsi, hss]; group
    have : x = (τ * τ) * ((τ * τ) * x * (τ * τ)⁻¹) * (τ * τ)⁻¹ := by
      calc x = (τ * τ) * (τ * τ) * x * ((τ * τ)⁻¹ * (τ * τ)⁻¹) := hx'
        _ = (τ * τ) * ((τ * τ) * x * (τ * τ)⁻¹) * (τ * τ)⁻¹ := by group
    rw [this, ← hm, key]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)) m

theorem card_Cbar (h : FourCtx A τ t) (hg : FourGen A τ g) :
    Nat.card (sixCbar A (zOne τ g)) = 6 := by
  have hbot : Subgroup.zpowers (τ * τ) ⊓ Subgroup.zpowers g = ⊥ := by
    set K := Subgroup.zpowers (τ * τ) ⊓ Subgroup.zpowers g with hK
    have hd2 : Nat.card K ∣ 2 := by
      rw [← card_zpowers_s h]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hd3 : Nat.card K ∣ 3 := by
      rw [← card_pow_gen hg.g3 hg.g1]
      exact Subgroup.card_dvd_of_le inf_le_right
    have : Nat.card K = 1 := by
      have := Nat.dvd_gcd hd2 hd3
      simpa using this
    exact Subgroup.card_eq_one.mp this
  have hrel := B6.relIndex_inf_eq_relIndex_sup (s_normalizes h hg)
  rw [hbot, Subgroup.relIndex_bot_left, card_pow_gen hg.g3 hg.g1] at hrel
  have hcard := Subgroup.relIndex_mul_card (Subgroup.zpowers (τ * τ))
    (Subgroup.zpowers (τ * τ) ⊔ Subgroup.zpowers g)
  rw [inf_of_le_left le_sup_left, ← hrel, card_zpowers_s h] at hcard
  rw [Cbar_eq h hg, sup_comm]
  omega

theorem T0_eq (h : FourCtx A τ t) (hg : FourGen A τ g) :
    Subgroup.zpowers τ ⊓ fixingV (zOne τ g : Set V) = Subgroup.zpowers (τ * τ) := by
  apply le_antisymm
  · rintro x ⟨hx, hfix⟩
    obtain ⟨z, hz, hz1⟩ := exists_ne_one_zOne h hg
    have hzU₁ : z ∈ fixOf g := hz.2
    have hxz : x z = z := hfix z hz
    have hbad : ∀ w : V, w ∈ fixOf (hOf τ g) → x z = w → False := by
      intro w hw hxw
      have h5 : z ∈ fixOf g ⊓ fixOf (hOf τ g) := ⟨hzU₁, by rw [← hxz, hxw]; exact hw⟩
      rw [hg.inf, Subgroup.mem_bot] at h5
      exact hz1 h5
    rcases zpowers_cases h.tau_ord hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact (hbad _ (tau_U₁ hzU₁) rfl).elim
    · exact Subgroup.mem_zpowers _
    · exact (hbad _ (tau3_U₁ hg hzU₁) rfl).elim
  · intro x hx
    refine ⟨zpowers_s_le τ hx, fun z hz => ?_⟩
    exact apply_eq_of_mem_zpowers (show (τ * τ) z = z from hz.1) hx

theorem card_T0 (h : FourCtx A τ t) (hg : FourGen A τ g) :
    Nat.card (Subgroup.zpowers τ ⊓ fixingV (zOne τ g : Set V) : Subgroup (MulAut V)) = 2 := by
  rw [T0_eq h hg, card_zpowers_s h]

omit [Finite V] in
theorem index_T0 (h : FourCtx A τ t) :
    (Subgroup.zpowers (τ * τ)).relIndex (Subgroup.zpowers τ) = 2 := by
  have hcard := Subgroup.relIndex_mul_card (Subgroup.zpowers (τ * τ)) (Subgroup.zpowers τ)
  rw [inf_of_le_left (zpowers_s_le τ), card_zpowers_s h, Nat.card_zpowers, h.tau_ord] at hcard
  omega

theorem odd_mem_Cbar (h : FourCtx A τ t) (hg : FourGen A τ g) {x : MulAut V}
    (hx : x ∈ sixCbar A (zOne τ g)) (hxo : Odd (orderOf x)) : x ∈ Subgroup.zpowers g := by
  obtain ⟨hxA, hfix⟩ := hx
  obtain ⟨i, y, hy, rfl⟩ := mem_Cbar h hg hxA hfix
  have hss := FourCtx.s_mul_s h
  have hsi : (τ * τ)⁻¹ = τ * τ := inv_eq_of_mul_eq_one_right hss
  rcases zpowers_cases_two hss hy with rfl | rfl
  · rw [mul_one] at hxo ⊢
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) i
  · have hsg := h.s_inv hg.gP
    have hconj : (τ * τ) * g ^ i * (τ * τ)⁻¹ = (g ^ i)⁻¹ := by
      rw [← inv_pow, ← hsg, conj_pow]
    have key : ∀ a s : MulAut V, (a * s) * (a * s) = a * (s * a * s⁻¹) * (s * s) := by
      intro a s
      group
    have hx2 : (g ^ i * (τ * τ)) * (g ^ i * (τ * τ)) = 1 := by
      calc (g ^ i * (τ * τ)) * (g ^ i * (τ * τ))
          = g ^ i * ((τ * τ) * g ^ i * (τ * τ)⁻¹) * ((τ * τ) * (τ * τ)) := key _ _
        _ = 1 := by rw [hconj, hss]; group
    have hd : orderOf (g ^ i * (τ * τ)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · rw [orderOf_eq_one_iff.mp h1]
      exact Subgroup.one_mem _
    · rw [h2] at hxo
      exact absurd hxo (by decide)

theorem oTwoUpper_Cbar (h : FourCtx A τ t) (hg : FourGen A τ g) :
    oTwoUpper (sixCbar A (zOne τ g)) = Subgroup.zpowers g := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr fun x hx => odd_mem_Cbar h hg hx.1 hx.2
  · rw [Subgroup.zpowers_le]
    refine mem_oTwoUpper_of_odd (g_mem_Cbar h hg) ?_
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [orderOf_eq_prime hg.g3 hg.g1]
    decide

theorem Cbar_sup_T (h : FourCtx A τ t) (hg : FourGen A τ g) :
    sixCbar A (zOne τ g) ⊔ Subgroup.zpowers τ = A := by
  apply le_antisymm
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr h.tau_mem)
  · intro a ha
    obtain ⟨p, hp, y, hy, rfl⟩ := h.mem_A ha
    obtain ⟨i, j, rfl⟩ := hg.param p hp
    have hτ : τ ∈ sixCbar A (zOne τ g) ⊔ Subgroup.zpowers τ :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
    have hgC : g ∈ sixCbar A (zOne τ g) ⊔ Subgroup.zpowers τ :=
      Subgroup.mem_sup_left (g_mem_Cbar h hg)
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hgC i) ?_)
      (Subgroup.mem_sup_right hy)
    unfold hOf
    rw [conj_pow]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hτ (Subgroup.pow_mem _ hgC j))
      (Subgroup.inv_mem _ hτ)

omit [Finite V] in
theorem fixV_zpowers_s (hg : FourGen A τ g) :
    fixV (Subgroup.zpowers (τ * τ)) = zOne τ g ⊔ zTwo τ g := by
  rw [← fixOf_s_eq hg]
  ext v
  constructor
  · intro hv
    exact hv _ (Subgroup.mem_zpowers _)
  · intro hv x hx
    exact apply_eq_of_mem_zpowers hv hx

omit [Finite V] in
theorem tau_zTwo (hg : FourGen A τ g) {z : V} (hz : z ∈ zTwo τ g) : τ z ∈ zOne τ g := by
  refine ⟨?_, tau_U₂ hg hz.2⟩
  show (τ * τ) (τ z) = τ z
  have : (τ * τ) (τ z) = τ ((τ * τ) z) := rfl
  rw [this, show (τ * τ) z = z from hz.1]

omit [Finite V] in
theorem diag_fix {z : V} (hz : z ∈ zTwo τ g) :
    τ z * z ∈ fixV (Subgroup.zpowers τ) := by
  intro x hx
  refine apply_eq_of_mem_zpowers (show τ (τ z * z) = τ z * z from ?_) hx
  rw [map_mul]
  have h1 : τ (τ z) = z := show (τ * τ) z = z from hz.1
  rw [h1, mul_comm]

omit [Finite V] in
theorem fixV_tau_le (hg : FourGen A τ g) {w : V} (hw : w ∈ fixV (Subgroup.zpowers τ)) :
    w ∈ zOne τ g ⊔ zTwo τ g := by
  rw [← fixV_zpowers_s hg]
  intro x hx
  exact hw x (zpowers_s_le τ hx)

omit [Finite V] in
theorem swap_mem (h : FourCtx A τ t) (hg : FourGen A τ g) {a : MulAut V}
    (ha : a ∈ Subgroup.zpowers τ) (hna : a ∉ Subgroup.zpowers (τ * τ)) {w : V}
    (hw : w ∈ fixOf (hOf τ g)) : a w ∈ fixOf g := by
  rcases zpowers_cases h.tau_ord ha with rfl | rfl | rfl | rfl
  · exact absurd (Subgroup.one_mem _) hna
  · exact tau_U₂ hg hw
  · exact absurd (Subgroup.mem_zpowers _) hna
  · exact tau3_U₂ hg hw

theorem zpowers_s_inf_fixingV (h : FourCtx A τ t) (hg : FourGen A τ g) :
    Subgroup.zpowers (τ * τ) ⊓ fixingV (fixOf g : Set V) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hfix⟩
  obtain ⟨a, ha, hsa⟩ := exists_moved h hg
  rcases zpowers_cases_two (FourCtx.s_mul_s h) hx with rfl | rfl
  · exact Subgroup.one_mem _
  · exact absurd (hfix a ha) hsa

omit [Finite V] in
theorem zpowers_g_U₂ (h : FourCtx A τ t) (hg : FourGen A τ g) {a : MulAut V}
    (ha : a ∈ Subgroup.zpowers g) {w : V} (hw : w ∈ fixOf (hOf τ g)) : a w ∈ fixOf (hOf τ g) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact apply_mem_fixOf_of_comm ((show Commute g (hOf τ g) from gh_comm h hg).zpow_left m).eq hw

omit [Finite V] in
theorem g_fpf_U₂ (hg : FourGen A τ g) {w : V} (hw : w ∈ fixOf (hOf τ g)) (hgw : g w = w) :
    w = 1 := by
  have : w ∈ fixOf g ⊓ fixOf (hOf τ g) := ⟨hgw, hw⟩
  rw [hg.inf, Subgroup.mem_bot] at this
  exact this

end FourGen

end Ctx
