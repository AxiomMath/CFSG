module

public import CFSG.RankThree.PartOne.K1214.Arith
public import CFSG.RankThree.PartOne.SP4GA.Pointwise
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartOne.SP4GA

open CFSG.RankThree.PartOne.K1214 (exists_pow_mul)

theorem lte_aux {p e s k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : 1 ≤ s) (hk : 2 ≤ k)
    (h1 : p ^ e ∣ k ^ (p ^ s) - 1) (h2 : ¬ p ^ e ∣ k ^ (p ^ (s - 1)) - 1) :
    p ∣ k - 1 ∧ padicValNat p (k - 1) + s = e := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : Odd p := hp.odd_of_ne_two hp2
  have hps : p ^ s ≠ 0 := (pow_pos hp.pos s).ne'
  have hps' : p ^ (s - 1) ≠ 0 := (pow_pos hp.pos _).ne'
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; exact absurd (by simp) h2
    · exact h
  have hpk : p ∣ k - 1 := by
    have hdvd : p ∣ k ^ (p ^ s) - 1 := (dvd_pow_self p (by omega)).trans h1
    have hk1 : 1 ≤ k ^ (p ^ s) := Nat.one_le_pow _ _ (by omega)
    have hz : ((k ^ (p ^ s) : ℕ) : ZMod p) = 1 := by
      have := (Nat.modEq_iff_dvd' hk1).2 hdvd
      have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).2 this.symm
      simpa using h3
    have hz2 : ((k : ℕ) : ZMod p) ^ (p ^ s) = 1 := by simpa using hz
    rw [ZMod.pow_card_pow] at hz2
    have : (k : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using hz2
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).1 this
    exact (Nat.modEq_iff_dvd' (by omega)).1 h4.symm
  have hpk' : ¬ p ∣ k := by
    intro hdvd
    have h5 : p ∣ 1 := by
      have : p ∣ k - (k - 1) := Nat.dvd_sub hdvd hpk
      have e1 : k - (k - 1) = 1 := by omega
      rwa [e1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h5)
  have hlt : 1 < k := by omega
  have hv1 := padicValNat.pow_sub_pow (p := p) hp1 (x := k) (y := 1) hlt (by simpa using hpk) hpk'
    (n := p ^ s) hps
  have hv2 := padicValNat.pow_sub_pow (p := p) hp1 (x := k) (y := 1) hlt (by simpa using hpk) hpk'
    (n := p ^ (s - 1)) hps'
  simp only [one_pow, padicValNat.prime_pow] at hv1 hv2
  have hne1 : k ^ (p ^ s) - 1 ≠ 0 := by
    have : 1 < k ^ (p ^ s) := Nat.one_lt_pow hps hlt
    omega
  have hne2 : k ^ (p ^ (s - 1)) - 1 ≠ 0 := by
    have : 1 < k ^ (p ^ (s - 1)) := Nat.one_lt_pow hps' hlt
    omega
  have hle : e ≤ padicValNat p (k ^ (p ^ s) - 1) := (padicValNat_dvd_iff_le hne1).1 h1
  have hlt2 : padicValNat p (k ^ (p ^ (s - 1)) - 1) < e := by
    by_contra hcon
    exact h2 ((padicValNat_dvd_iff_le hne2).2 (not_lt.1 hcon))
  refine ⟨hpk, ?_⟩
  omega

variable {G : Type*} [Group G]

theorem centralizer_cyclic_eq {p e s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : 1 ≤ s) (he : 1 ≤ e)
    {x u : G} (hx : orderOf x = p ^ e)
    (hu : ∀ r ∈ Subgroup.zpowers x, u * r * u⁻¹ ∈ Subgroup.zpowers x)
    (h1 : u ^ (p ^ s) * x * (u ^ (p ^ s))⁻¹ = x)
    (h2 : u ^ (p ^ (s - 1)) * x * (u ^ (p ^ (s - 1)))⁻¹ ≠ x) :
    s ≤ e ∧ Subgroup.zpowers x ⊓ Subgroup.centralizer {u} = Subgroup.zpowers (x ^ (p ^ s)) := by
  classical
  have hp0 : 0 < p := hp.pos
  have hord : 0 < orderOf x := by rw [hx]; exact pow_pos hp0 e
  obtain ⟨kz, hkz⟩ := Subgroup.mem_zpowers_iff.1 (hu x (Subgroup.mem_zpowers x))
  set kn : ℕ := (kz % (orderOf x : ℤ)).toNat with hkn
  have hkn' : ((kn : ℕ) : ℤ) = kz % (orderOf x : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hord.ne'))
  have hk : u * x * u⁻¹ = x ^ kn := by
    rw [← hkz, ← zpow_natCast, hkn', zpow_mod_orderOf]
  have hconj : ∀ N : ℕ, u ^ N * x * (u ^ N)⁻¹ = x ^ (kn ^ N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      calc u ^ (N + 1) * x * (u ^ (N + 1))⁻¹ = u * (u ^ N * x * (u ^ N)⁻¹) * u⁻¹ := by
            rw [pow_succ']; group
        _ = u * x ^ (kn ^ N) * u⁻¹ := by rw [ih]
        _ = (u * x * u⁻¹) ^ (kn ^ N) := by rw [conj_pow]
        _ = (x ^ kn) ^ (kn ^ N) := by rw [hk]
        _ = x ^ (kn ^ (N + 1)) := by rw [← pow_mul, ← pow_succ']
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    have : p ^ e = p ^ 0 := by rw [← hx]; simp
    have := Nat.pow_right_injective hp.two_le this
    omega
  have hkn0 : kn ≠ 0 := by
    intro h
    rw [h, pow_zero] at hk
    apply hx1
    calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
      _ = 1 := by rw [hk]; group
  have hkn1 : kn ≠ 1 := by
    intro h
    apply h2
    rw [hconj, h, one_pow, pow_one]
  have hkn2 : 2 ≤ kn := by omega
  have hmod : ∀ N : ℕ, u ^ N * x * (u ^ N)⁻¹ = x ↔ p ^ e ∣ kn ^ N - 1 := by
    intro N
    rw [hconj N]
    have h1' : 1 ≤ kn ^ N := Nat.one_le_pow _ _ (by omega)
    constructor
    · intro h
      have h3 : x ^ (kn ^ N) = x ^ 1 := by rw [h, pow_one]
      have h4 := (pow_eq_pow_iff_modEq.1 h3)
      rw [hx] at h4
      exact (Nat.modEq_iff_dvd' h1').1 h4.symm
    · intro h
      have h4 : 1 ≡ kn ^ N [MOD p ^ e] := (Nat.modEq_iff_dvd' h1').2 h
      have h3 : x ^ (kn ^ N) = x ^ 1 := pow_eq_pow_iff_modEq.2 (by rw [hx]; exact h4.symm)
      rw [h3, pow_one]
  have hdiv1 : p ^ e ∣ kn ^ (p ^ s) - 1 := (hmod _).1 h1
  have hdiv2 : ¬ p ^ e ∣ kn ^ (p ^ (s - 1)) - 1 := fun h => h2 ((hmod _).2 h)
  obtain ⟨hpk, hv⟩ := lte_aux hp hp2 hs hkn2 hdiv1 hdiv2
  have hse : s ≤ e := by omega
  obtain ⟨m, hm, hpm⟩ := exists_pow_mul hp (show kn - 1 ≠ 0 by omega)
  set v := padicValNat p (kn - 1) with hvdef
  have hev : e = v + s := by omega
  refine ⟨hse, ?_⟩
  have hcop : Nat.Coprime (p ^ s) m := Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hcopZ : IsCoprime ((p ^ s : ℕ) : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hkn1z : ((kn : ℕ) : ℤ) - 1 = ((p ^ v * m : ℕ) : ℤ) := by
    rw [← hm]; push_cast [Nat.cast_sub (show 1 ≤ kn by omega)]; ring
  have key : ∀ i : ℤ, x ^ i ∈ Subgroup.centralizer {u} ↔ ((p ^ s : ℕ) : ℤ) ∣ i := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : x ^ i * u = u * x ^ i ↔ u * x ^ i * u⁻¹ = x ^ i := by
      rw [mul_inv_eq_iff_eq_mul, eq_comm]
    rw [e1, ← conj_zpow, hk, ← zpow_natCast, ← zpow_mul, zpow_eq_zpow_iff_modEq, hx,
      Int.modEq_iff_dvd]
    have e2 : i - (kn : ℤ) * i = -(((p ^ v * m : ℕ) : ℤ) * i) := by rw [← hkn1z]; ring
    rw [e2, dvd_neg]
    have e3 : (((p ^ e : ℕ)) : ℤ) = ((p ^ v : ℕ) : ℤ) * ((p ^ s : ℕ) : ℤ) := by
      rw [hev, pow_add]; push_cast; ring
    have e4 : ((p ^ v * m : ℕ) : ℤ) * i = ((p ^ v : ℕ) : ℤ) * ((m : ℤ) * i) := by push_cast; ring
    have hpv : ((p ^ v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (pow_pos hp0 v).ne'
    rw [e3, e4, mul_dvd_mul_iff_left hpv]
    constructor
    · intro h
      exact hcopZ.dvd_of_dvd_mul_left h
    · intro h
      exact h.mul_left _
  ext r
  constructor
  · rintro ⟨hr, hc⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    obtain ⟨j, hj⟩ := (key i).1 hc
    refine Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩
    rw [hj, ← zpow_natCast, ← zpow_mul]
  · intro hr
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have h3 : (x ^ (p ^ s)) ^ j = x ^ (((p ^ s : ℕ) : ℤ) * j) := by
      rw [← zpow_natCast, ← zpow_mul]
    rw [h3]
    exact ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _, (key _).2 ⟨j, rfl⟩⟩

theorem exists_mul_zpow_of_sup {P Q : Subgroup G} {f : G} (hQn : ∀ u ∈ P, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q)
    (hf : f ∈ P) (hPf : P = Q ⊔ Subgroup.zpowers f) : ∀ g ∈ P, ∃ j : ℤ, g * (f ^ j)⁻¹ ∈ Q := by
  intro g hg
  rw [hPf, Subgroup.sup_eq_closure] at hg
  refine Subgroup.closure_induction (p := fun g _ => ∃ j : ℤ, g * (f ^ j)⁻¹ ∈ Q) ?_ ?_ ?_ ?_ hg
  · rintro g (hgQ | hgf)
    · exact ⟨0, by simpa using hgQ⟩
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgf
      exact ⟨j, by simp [Q.one_mem]⟩
  · exact ⟨0, by simp [Q.one_mem]⟩
  · rintro g₁ g₂ - - ⟨j₁, h₁⟩ ⟨j₂, h₂⟩
    refine ⟨j₁ + j₂, ?_⟩
    have hconj : f ^ j₁ * (g₂ * (f ^ j₂)⁻¹) * (f ^ j₁)⁻¹ ∈ Q := hQn _ (P.zpow_mem hf j₁) _ h₂
    have := Q.mul_mem h₁ hconj
    convert this using 1
    rw [zpow_add]; group
  · rintro g - ⟨j, h⟩
    refine ⟨-j, ?_⟩
    have h' := hQn _ (P.zpow_mem hf (-j)) _ (Q.inv_mem h)
    convert h' using 1
    rw [zpow_neg, inv_inv]; group

theorem exists_zpow_mul_of_sup {a b g : G} (hab : a * b = b * a)
    (hg : g ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) : ∃ i j : ℤ, g = a ^ i * b ^ j := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with hg | hg
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact ⟨i, 0, by simp⟩
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact ⟨0, j, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨i₁, j₁, rfl⟩ := h₁
    obtain ⟨i₂, j₂, rfl⟩ := h₂
    exact ⟨i₁ + i₂, j₁ + j₂, comb_mul hab _ _ _ _⟩
  | inv g _ h =>
    obtain ⟨i, j, rfl⟩ := h
    exact ⟨-i, -j, comb_inv hab i j⟩

theorem card_sup_zpowers {a b : G} [Finite G] (hab : a * b = b * a)
    (hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) =
      orderOf a * orderOf b := by
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_zpow (show Commute a b from hab) i j)).eq
  have hcomm' : ∀ (m : ↥(Subgroup.zpowers a)) (n : ↥(Subgroup.zpowers b)),
      Commute ((Subgroup.zpowers a).subtype m) ((Subgroup.zpowers b).subtype n) :=
    fun m n => hcomm m.1 m.2 n.1 n.2
  let φ := MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype hcomm'
  have hinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨(Subgroup.zpowers a).subtype_injective, (Subgroup.zpowers b).subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hdisj
  have hrange : φ.range = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_zpowers a, ← Nat.card_zpowers b, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem mem_zpowers_of_pow_eq_one {C : Type*} [Group C] [Finite C] [IsCyclic C] {p : ℕ}
    (hp : p.Prime) {a b : C} (ha : orderOf a = p) (hb : b ^ p = 1) : b ∈ Subgroup.zpowers a := by
  classical
  have := Fintype.ofFinite C
  have hle := IsCyclic.card_pow_eq_one_le (α := C) hp.pos
  have hsub : (Finset.univ.filter (fun b : C => b ∈ Subgroup.zpowers a)) ⊆
      Finset.univ.filter (fun b : C => b ^ p = 1) := by
    intro b hb'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb' ⊢
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha, pow_orderOf_eq_one,
      one_zpow]
  have hcard : (Finset.univ.filter (fun b : C => b ∈ Subgroup.zpowers a)).card = p := by
    rw [← ha, ← Nat.card_zpowers, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have hb' : b ∈ Finset.univ.filter (fun b : C => b ^ p = 1) := by simp [hb]
  rw [← heq] at hb'
  simpa using hb'

theorem commute_of_pow_commute {p : ℕ} (hp : p.Prime) {c x : G} (hcp : c ^ p = 1) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) (h : Commute (c ^ k) x) : Commute c x := by
  have hcop : IsCoprime (p : ℤ) k :=
    (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.2 hk
  obtain ⟨u, a, hua⟩ := hcop
  have hc : c = (c ^ k) ^ a := by
    calc c = c ^ (k * a + (p : ℤ) * u) := by
          have e : k * a + (p : ℤ) * u = 1 := by linarith [hua]
          rw [e, zpow_one]
      _ = (c ^ k) ^ a := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, hcp, one_zpow, mul_one]
  rw [hc]
  exact h.zpow_left a

theorem orderOf_pow_p_pow {p e s : ℕ} (hp : p.Prime) (hse : s ≤ e) {x : G}
    (hx : orderOf x = p ^ e) : orderOf (x ^ (p ^ s)) = p ^ (e - s) := by
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (by rw [hx]; exact pow_dvd_pow p hse), hx,
    Nat.pow_div hse hp.pos]

theorem mem_sup_centralizers {x y m g : G} (hyx : y * x = x * y)
    (hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    (hmx : ∀ r ∈ Subgroup.zpowers x, m * r * m⁻¹ ∈ Subgroup.zpowers x)
    (hmy : ∀ z ∈ Subgroup.zpowers y, m * z * m⁻¹ ∈ Subgroup.zpowers y)
    (hg : g ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers x) (hgm : g * m = m * g) :
    g ∈ (Subgroup.zpowers y ⊓ Subgroup.centralizer {m}) ⊔
      (Subgroup.zpowers x ⊓ Subgroup.centralizer {m}) := by
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_sup hyx hg
  have hyi : y ^ i ∈ Subgroup.zpowers y := Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) i
  have hxj : x ^ j ∈ Subgroup.zpowers x := Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) j
  have hy1 := hmy (y ^ i) hyi
  have hx1 := hmx (x ^ j) hxj
  have hconj : m * (y ^ i * x ^ j) * m⁻¹ = y ^ i * x ^ j := by
    rw [mul_inv_eq_iff_eq_mul]; exact hgm.symm
  have hconj' : (m * y ^ i * m⁻¹) * (m * x ^ j * m⁻¹) = y ^ i * x ^ j := by
    rw [← hconj]; group
  have h3 : (y ^ i)⁻¹ * (m * y ^ i * m⁻¹) = x ^ j * (m * x ^ j * m⁻¹)⁻¹ := by
    calc (y ^ i)⁻¹ * (m * y ^ i * m⁻¹)
        = (y ^ i)⁻¹ * ((m * y ^ i * m⁻¹) * (m * x ^ j * m⁻¹)) * (m * x ^ j * m⁻¹)⁻¹ := by group
      _ = x ^ j * (m * x ^ j * m⁻¹)⁻¹ := by rw [hconj']; group
  have h4 : (y ^ i)⁻¹ * (m * y ^ i * m⁻¹) ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers y :=
    ⟨h3 ▸ Subgroup.mul_mem _ hxj (Subgroup.inv_mem _ hx1),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyi) hy1⟩
  rw [hdisj, Subgroup.mem_bot] at h4
  have h5 : m * y ^ i * m⁻¹ = y ^ i := by
    have := congrArg (y ^ i * ·) h4
    simpa using this
  have h6 : m * x ^ j * m⁻¹ = x ^ j := by
    have h3' : x ^ j * (m * x ^ j * m⁻¹)⁻¹ = 1 := by rw [← h3]; exact h4
    exact (mul_inv_eq_one.1 h3').symm
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hyi, ?_⟩))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hxj, ?_⟩))
  · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h5).symm
  · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h6).symm

theorem eq_of_abelian_card_le [Finite G] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    {P Q M : Subgroup G} {x y c f : G} (hPp : IsPGroup p P)
    (hQn : ∀ u ∈ P, ∀ q ∈ Q, u * q * u⁻¹ ∈ Q)
    (hf : f ∈ P) (hPf : P = Q ⊔ Subgroup.zpowers f)
    (hQ : Q = Subgroup.zpowers y ⊔ Subgroup.zpowers x) (hxy : x * y = y * x)
    (hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    (hxo : orderOf x = p ^ e) (hyo : orderOf y = p ^ e)
    (hxn : ∀ u ∈ P, ∀ r ∈ Subgroup.zpowers x, u * r * u⁻¹ ∈ Subgroup.zpowers x)
    (hyn : ∀ u ∈ P, ∀ z ∈ Subgroup.zpowers y, u * z * u⁻¹ ∈ Subgroup.zpowers y)
    (hcP : c ∈ P) (hcQ : c ∉ Q) (hcp : c ^ p = 1)
    (hcx : c * x ≠ x * c) (hcy : c * y ≠ y * c)
    (hMP : M ≤ P) (hMab : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (hcard : Nat.card Q ≤ Nat.card M) : M = Q := by
  classical
  have hp0 : 0 < p := hp.pos
  have : Fact p.Prime := ⟨hp⟩
  have hyx : y * x = x * y := hxy.symm
  have hdisj' : Subgroup.zpowers y ⊓ Subgroup.zpowers x = ⊥ := by rw [inf_comm]; exact hdisj
  have hcardQ : Nat.card Q = p ^ (2 * e) := by
    rw [hQ, card_sup_zpowers hyx hdisj', hxo, hyo, ← pow_add]; congr 1; ring
  set N : Subgroup ↥P := Q.subgroupOf P with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    have := hQn (g : G) g.2 (n : G) hn
    simpa using this⟩
  let π : ↥P →* ↥P ⧸ N := QuotientGroup.mk' N
  have hcyc : IsCyclic (↥P ⧸ N) := by
    refine ⟨⟨π ⟨f, hf⟩, fun a => ?_⟩⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨j, hj⟩ := exists_mul_zpow_of_sup hQn hf hPf g g.2
    refine ⟨j, ?_⟩
    show π ⟨f, hf⟩ ^ j = (g : ↥P ⧸ N)
    rw [← map_zpow]
    show QuotientGroup.mk (⟨f, hf⟩ ^ j : ↥P) = (g : ↥P ⧸ N)
    apply QuotientGroup.eq.2
    rw [hN, Subgroup.mem_subgroupOf]
    have h1 := hQn (f ^ (-j)) (P.zpow_mem hf _) _ hj
    have h2 : f ^ (-j) * (g * (f ^ j)⁻¹) * (f ^ (-j))⁻¹ = (f ^ j)⁻¹ * g := by
      rw [zpow_neg, inv_inv]; group
    rw [h2] at h1
    simpa using h1
  have hpg : IsPGroup p (↥P ⧸ N) := hPp.to_quotient N
  have hc1 : π ⟨c, hcP⟩ ≠ 1 := by
    intro h
    apply hcQ
    have : (⟨c, hcP⟩ : ↥P) ∈ N := (QuotientGroup.eq_one_iff _).1 h
    exact Subgroup.mem_subgroupOf.1 this
  have hcp' : π ⟨c, hcP⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨c, hcP⟩ : ↥P) ^ p = 1 := Subtype.ext (by simpa using hcp)
    rw [this, map_one]
  set M₀ : Subgroup ↥P := M.subgroupOf P with hM₀
  let φ : ↥M₀ →* ↥P ⧸ N := π.comp M₀.subtype
  set T : Subgroup (↥P ⧸ N) := φ.range with hT
  have : IsCyclic ↥T := Subgroup.isCyclic T
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥T)
  obtain ⟨m₀, hm₀⟩ := t.2
  have hTpg : IsPGroup p ↥T := hpg.of_injective T.subtype T.subtype_injective
  obtain ⟨s, hs⟩ := (IsPGroup.iff_card.1 hTpg)
  have hord : orderOf (π (m₀ : ↥P)) = p ^ s := by
    have h1 : orderOf t = Nat.card ↥T := orderOf_eq_card_of_forall_mem_zpowers ht
    rw [hs] at h1
    rw [← h1, ← Subgroup.orderOf_coe t, ← hm₀]
    rfl
  have hQx : ∀ q ∈ Q, q * x = x * q := by
    intro q hq
    have hq' : q ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers x := by rwa [hQ] at hq
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_sup hyx hq'
    exact (Commute.mul_left (Commute.zpow_left (show Commute y x from hyx) i)
      ((Commute.refl x).zpow_left j)).eq
  have hmP : ((m₀ : ↥P) : G) ∈ P := (m₀ : ↥P).2
  have hmM : ((m₀ : ↥P) : G) ∈ M := Subgroup.mem_subgroupOf.1 m₀.2
  rcases Nat.eq_zero_or_pos s with hs0 | hs1
  ·
    have hT1 : T = ⊥ := by
      rw [← Subgroup.card_eq_one, hs, hs0, pow_zero]
    have hMQ : M ≤ Q := by
      intro a ha
      have h1 : φ ⟨⟨a, hMP ha⟩, Subgroup.mem_subgroupOf.2 ha⟩ ∈ T := ⟨_, rfl⟩
      rw [hT1, Subgroup.mem_bot] at h1
      exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
    exact Subgroup.eq_of_le_of_card_ge hMQ hcard
  · exfalso
    have hQy : ∀ q ∈ Q, q * y = y * q := by
      intro q hq
      have hq' : q ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers x := by rwa [hQ] at hq
      obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_sup hyx hq'
      exact (Commute.mul_left ((Commute.refl y).zpow_left i)
        (Commute.zpow_left (show Commute x y from hxy) j)).eq
    set mP : ↥P := (m₀ : ↥P) with hmPdef
    set m : G := (mP : G) with hmdef
    have hs1' : s - 1 + 1 = s := Nat.sub_add_cancel hs1
    have hcord : orderOf (π ⟨c, hcP⟩) = p := orderOf_eq_prime hcp' hc1
    have hb1 : (π mP ^ (p ^ (s - 1))) ^ p = 1 := by
      rw [← pow_mul, ← pow_succ, hs1', ← hord]
      exact pow_orderOf_eq_one _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_pow_eq_one hp hcord hb1)
    have hpk : ¬ (p : ℤ) ∣ k := by
      intro hdvd
      have h1 : π ⟨c, hcP⟩ ^ k = 1 := by
        obtain ⟨l, rfl⟩ := hdvd
        rw [zpow_mul, zpow_natCast, hcp', one_zpow]
      rw [h1] at hk
      have h2 : orderOf (π mP) ∣ p ^ (s - 1) := orderOf_dvd_of_pow_eq_one hk.symm
      rw [hord] at h2
      have h3 := Nat.le_of_dvd (pow_pos hp0 _) h2
      have h4 : p ^ (s - 1) < p ^ s := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega
    have hq1 : (c ^ k)⁻¹ * m ^ (p ^ (s - 1)) ∈ Q := by
      have h1 : ((⟨c, hcP⟩ : ↥P) ^ k)⁻¹ * mP ^ (p ^ (s - 1)) ∈ N := by
        apply QuotientGroup.eq.1
        show π ((⟨c, hcP⟩ : ↥P) ^ k) = π (mP ^ (p ^ (s - 1)))
        rw [map_zpow, map_pow]
        exact hk
      simpa using Subgroup.mem_subgroupOf.1 h1
    have hmQ : m ^ (p ^ s) ∈ Q := by
      have h1 : π mP ^ (p ^ s) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
      have h2 : mP ^ (p ^ s) ∈ N := (QuotientGroup.eq_one_iff _).1 ((map_pow π mP (p ^ s)).trans h1)
      simpa using Subgroup.mem_subgroupOf.1 h2
    have hconj : ∀ z : G, (∀ q ∈ Q, q * z = z * q) → (c * z ≠ z * c) →
        m ^ (p ^ (s - 1)) * z * (m ^ (p ^ (s - 1)))⁻¹ ≠ z := by
      intro z hQz hcz h
      obtain ⟨q₁, hq₁, hq₁'⟩ : ∃ q₁ ∈ Q, m ^ (p ^ (s - 1)) = c ^ k * q₁ :=
        ⟨(c ^ k)⁻¹ * m ^ (p ^ (s - 1)), hq1, by group⟩
      rw [hq₁'] at h
      have h' : c ^ k * z * (c ^ k)⁻¹ = z := by
        have h1 : q₁ * z * q₁⁻¹ = z := by rw [mul_inv_eq_iff_eq_mul]; exact hQz q₁ hq₁
        calc c ^ k * z * (c ^ k)⁻¹ = c ^ k * (q₁ * z * q₁⁻¹) * (c ^ k)⁻¹ := by rw [h1]
          _ = c ^ k * q₁ * z * (c ^ k * q₁)⁻¹ := by group
          _ = z := h
      have hcomm : Commute (c ^ k) z := by
        rw [mul_inv_eq_iff_eq_mul] at h'
        exact h'
      exact hcz (commute_of_pow_commute hp hcp hpk hcomm).eq
    have hmz : ∀ z : G, (∀ q ∈ Q, q * z = z * q) → m ^ (p ^ s) * z * (m ^ (p ^ s))⁻¹ = z := by
      intro z hQz
      rw [mul_inv_eq_iff_eq_mul]
      exact hQz _ hmQ
    obtain ⟨hse, hCx⟩ := centralizer_cyclic_eq hp hp2 hs1 he hxo (hxn m hmP) (hmz x hQx)
      (hconj x hQx hcx)
    obtain ⟨-, hCy⟩ := centralizer_cyclic_eq hp hp2 hs1 he hyo (hyn m hmP) (hmz y hQy)
      (hconj y hQy hcy)
    set S : Subgroup G := Subgroup.zpowers (y ^ (p ^ s)) ⊔ Subgroup.zpowers (x ^ (p ^ s)) with hS
    have hSdisj : Subgroup.zpowers (y ^ (p ^ s)) ⊓ Subgroup.zpowers (x ^ (p ^ s)) = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have h1 : g ∈ Subgroup.zpowers y :=
        (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers y) _)) hg.1
      have h2 : g ∈ Subgroup.zpowers x :=
        (Subgroup.zpowers_le.2 (pow_mem (Subgroup.mem_zpowers x) _)) hg.2
      exact hdisj.le ⟨h2, h1⟩
    have hScard : Nat.card S = p ^ (e - s) * p ^ (e - s) := by
      rw [hS, card_sup_zpowers (Commute.pow_pow (show Commute y x from hyx) _ _).eq hSdisj,
        orderOf_pow_p_pow hp hse hyo, orderOf_pow_p_pow hp hse hxo]
    have hmem : ∀ a : ↥φ.ker, (((a : ↥M₀) : ↥P) : G) ∈ S := by
      intro a
      have hgN : ((a : ↥M₀) : ↥P) ∈ N := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 a.2)
      have hgQ : (((a : ↥M₀) : ↥P) : G) ∈ Q := Subgroup.mem_subgroupOf.1 hgN
      have hgM : (((a : ↥M₀) : ↥P) : G) ∈ M := Subgroup.mem_subgroupOf.1 (a : ↥M₀).2
      have hgm : (((a : ↥M₀) : ↥P) : G) * m = m * (((a : ↥M₀) : ↥P) : G) := hMab _ hgM m hmM
      have := mem_sup_centralizers hyx hdisj (hxn m hmP) (hyn m hmP) (by rwa [hQ] at hgQ) hgm
      rwa [hCx, hCy] at this
    have hker : Nat.card ↥φ.ker ≤ Nat.card S := by
      refine Nat.card_le_card_of_injective (fun a => ⟨(((a : ↥M₀) : ↥P) : G), hmem a⟩) ?_
      intro a b hab
      have h1 := congrArg Subtype.val hab
      simp only at h1
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    have hMcard : Nat.card ↥M₀ = Nat.card ↥φ.ker * p ^ s := by
      rw [← Subgroup.card_ker_mul_card_range φ, ← hs]
    have hMM : Nat.card ↥M₀ = Nat.card ↥M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMP).toEquiv
    have hlt : Nat.card ↥M < Nat.card ↥Q := by
      rw [← hMM, hMcard, hcardQ]
      calc Nat.card ↥φ.ker * p ^ s ≤ (p ^ (e - s) * p ^ (e - s)) * p ^ s :=
            Nat.mul_le_mul_right _ (hker.trans_eq hScard)
        _ = p ^ ((e - s) + (e - s) + s) := by rw [← pow_add, ← pow_add]
        _ < p ^ (2 * e) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd hcard (not_le.2 hlt)

end CFSG.RankThree.PartOne.SP4GA
