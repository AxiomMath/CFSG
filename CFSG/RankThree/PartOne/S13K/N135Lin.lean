module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.S13K.N135

variable {V : Type} [CommGroup V]

theorem pow_apply_eq (x : MulAut V) (n : ℕ) (v : V) (h : x v = v) : (x ^ n) v = v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h]; exact ih

theorem apply_eq_of_sq {x : MulAut V} (hx : Odd (orderOf x)) {v : V} (h : (x * x) v = v) :
    x v = v := by
  obtain ⟨k, hk⟩ := hx
  have h0 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have e1 : (x * x) ^ (k + 1) = x := by
    rw [← sq, ← pow_mul]
    calc x ^ (2 * (k + 1)) = x ^ (2 * k + 1) * x := by
          rw [← pow_succ]; exact congrArg (fun n => x ^ n) (by omega : 2 * (k + 1) = 2 * k + 1 + 1)
      _ = x := by rw [h0, one_mul]
  conv_lhs => rw [← e1]
  exact pow_apply_eq (x * x) (k + 1) v h

@[expose] def jHom (x : MulAut V) : V →* V :=
  MonoidHom.mk' (fun e => x e * (x⁻¹ e)⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

theorem jHom_apply (x : MulAut V) (e : V) : jHom x e = x e * (x⁻¹ e)⁻¹ := rfl

theorem jHom_eq_one_iff {x : MulAut V} (hx : Odd (orderOf x)) (f : V) : jHom x f = 1 ↔ x f = f := by
  rw [jHom_apply]
  constructor
  · intro h
    have h1 : x f = x⁻¹ f := mul_inv_eq_one.1 h
    have h2 : (x * x) f = f := by
      rw [MulAut.mul_apply, h1, MulAut.apply_inv_self]
    exact apply_eq_of_sq hx h2
  · intro h
    have h1 : x⁻¹ f = f := by
      have h2 : x⁻¹ (x f) = f := MulAut.inv_apply_self V x f
      rwa [h] at h2
    rw [h, h1]
    exact mul_inv_cancel f

theorem eq_one_of_jj {p : ℕ} (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1) {x : MulAut V}
    (hodd : Odd (orderOf x)) (hxp : ¬ p ∣ orderOf x) (h : ∀ e : V, x (jHom x e) = jHom x e) :
    x = 1 := by
  have ha : ∀ e : V, (x * x) e * e⁻¹ = jHom x e := by
    intro e
    have h1 := h e
    rw [jHom_apply, map_mul, map_inv, MulAut.apply_inv_self] at h1
    rw [jHom_apply]
    exact h1
  have hya : ∀ e : V, (x * x) ((x * x) e * e⁻¹) = (x * x) e * e⁻¹ := by
    intro e
    rw [ha e, MulAut.mul_apply, h e, h e]
  have hpow : ∀ (n : ℕ) (e : V), ((x * x) ^ n) e = e * ((x * x) e * e⁻¹) ^ n := by
    intro n e
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hya e, pow_succ]
      have : e * ((x * x) e * e⁻¹) = (x * x) e := by
        rw [mul_comm ((x * x) e) e⁻¹, mul_inv_cancel_left]
      calc (x * x) e * ((x * x) e * e⁻¹) ^ n
          = (e * ((x * x) e * e⁻¹)) * ((x * x) e * e⁻¹) ^ n := by rw [this]
        _ = e * (((x * x) e * e⁻¹) ^ n * ((x * x) e * e⁻¹)) := by rw [mul_assoc, mul_comm (((x * x) e * e⁻¹) ^ n)]
  have h1 : (x * x) ^ orderOf x = 1 := by
    rw [← sq, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hcop : Nat.Coprime (orderOf x) p := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hxp
  have hm : ∀ e : V, (x * x) e = e := by
    intro e
    have h2 := hpow (orderOf x) e
    rw [h1] at h2
    have h3 : ((x * x) e * e⁻¹) ^ orderOf x = 1 := by
      have h4 : e * ((x * x) e * e⁻¹) ^ orderOf x = e * 1 := by
        rw [mul_one]; exact h2.symm
      exact mul_left_cancel h4
    have h5 := pow_gcd_eq_one.2 ⟨h3, hexp _⟩
    rw [hcop, pow_one] at h5
    exact mul_inv_eq_one.1 h5
  have hy1 : x * x = 1 := MulEquiv.ext hm
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy1)
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h2 | h2
  · exact orderOf_eq_one_iff.1 h2
  · exfalso
    rw [h2] at hodd
    exact absurd hodd (by decide)

@[expose] def vMinus (u : MulAut V) : Subgroup V where
  carrier := {e | u e = e⁻¹}
  mul_mem' := by
    intro a b ha hb
    have ha' : u a = a⁻¹ := ha
    have hb' : u b = b⁻¹ := hb
    show u (a * b) = (a * b)⁻¹
    rw [map_mul, ha', hb', mul_inv]
  one_mem' := by
    show u 1 = (1 : V)⁻¹
    rw [map_one, inv_one]
  inv_mem' := by
    intro a ha
    have ha' : u a = a⁻¹ := ha
    show u a⁻¹ = (a⁻¹)⁻¹
    rw [map_inv, ha']

theorem exists_decomp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    {u : MulAut V} (hu2 : u * u = 1) (e : V) :
    ∃ s t : V, u s = s ∧ u t = t⁻¹ ∧ e = s * t := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have huu : ∀ v : V, u (u v) = v := fun v => by
    have := congrArg (fun m : MulAut V => m v) hu2
    simpa [MulAut.mul_apply] using this
  set a : V := e * u e with ha
  set b : V := e * (u e)⁻¹ with hb
  have hab : a * b = e ^ 2 := by
    rw [ha, hb, sq, mul_mul_mul_comm, mul_inv_cancel, mul_one]
  have he : e = (a * b) ^ (k + 1) := by
    rw [hab, ← pow_mul]
    have h0 : e ^ (2 * k + 1) = 1 := by rw [← hk]; exact hexp e
    calc e = e ^ (2 * k + 1) * e := by rw [h0, one_mul]
      _ = e ^ (2 * (k + 1)) := by
          rw [← pow_succ]; exact congrArg (fun n => e ^ n) (by omega : 2 * k + 1 + 1 = 2 * (k + 1))
  have hua : u a = a := by
    rw [ha, map_mul, huu, mul_comm]
  have hub : u b = b⁻¹ := by
    rw [hb, map_mul, map_inv, huu, mul_inv, inv_inv, mul_comm]
  refine ⟨a ^ (k + 1), b ^ (k + 1), ?_, ?_, ?_⟩
  · rw [map_pow, hua]
  · rw [map_pow, hub, inv_pow]
  · rw [← mul_pow]; exact he

theorem card_vMinus [Finite V] {p : ℕ} [hpp : Fact p.Prime] (hp2 : p ≠ 2)
    (hexp : ∀ v : V, v ^ p = 1) (hcard : Nat.card V = p ^ 4) {u : MulAut V} (hu2 : u * u = 1)
    {c : V} (hc1 : c ≠ 1) (hfix : ∀ e, u e = e ↔ e ∈ Subgroup.zpowers c) :
    Nat.card (vMinus u) = p ^ 3 := by
  have hp := hpp.out
  have hcord : orderOf c = p := orderOf_eq_prime (hexp c) hc1
  have hcardc : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hcord]
  have hinter : ∀ e : V, u e = e → e ∈ vMinus u → e = 1 := by
    intro e h1 h2
    have h3 : u e = e⁻¹ := h2
    rw [h1] at h3
    have h4 : e ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.2 h3
    have h5 := pow_gcd_eq_one.2 ⟨h4, hexp e⟩
    have hcop : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    rwa [hcop, pow_one] at h5
  let f : Subgroup.zpowers c × vMinus u → V := fun q => (q.1 : V) * (q.2 : V)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩⟩ ⟨⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩⟩ h
      have h0 : a₁ * b₁ = a₂ * b₂ := h
      have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
        calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
          _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h0]
          _ = b₂ * b₁⁻¹ := by group
      have hu1 : u a₁ = a₁ := (hfix a₁).2 ha₁
      have hu2' : u a₂ = a₂ := (hfix a₂).2 ha₂
      have hw1 : u (a₂⁻¹ * a₁) = a₂⁻¹ * a₁ := by rw [map_mul, map_inv, hu1, hu2']
      have hw2 : a₂⁻¹ * a₁ ∈ vMinus u := by
        rw [h1]; exact (vMinus u).mul_mem hb₂ ((vMinus u).inv_mem hb₁)
      have hw3 : a₂⁻¹ * a₁ = 1 := hinter _ hw1 hw2
      have hA : a₁ = a₂ := (inv_mul_eq_one.1 hw3).symm
      have hB : b₁ = b₂ := by
        rw [hw3] at h1
        exact (mul_inv_eq_one.1 h1.symm).symm
      subst hA; subst hB
      rfl
    · intro e
      obtain ⟨s, t, hs, ht, rfl⟩ := exists_decomp hp hp2 hexp hu2 e
      exact ⟨⟨⟨s, (hfix s).1 hs⟩, ⟨t, ht⟩⟩, rfl⟩
  have h1 : Nat.card (Subgroup.zpowers c × vMinus u) = Nat.card V :=
    Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, hcardc, hcard] at h1
  have hp0 : 0 < p := hp.pos
  have : p * Nat.card (vMinus u) = p * p ^ 3 := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hp0 this

theorem vMinus_eq [Finite V] {p : ℕ} [hpp : Fact p.Prime] (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    (hcard : Nat.card V = p ^ 4) {u : MulAut V} (hu2 : u * u = 1) {c : V} (hc1 : c ≠ 1)
    (hfix : ∀ e, u e = e ↔ e ∈ Subgroup.zpowers c) {Λ : Subgroup (MulAut V)}
    (hucomm : ∀ g ∈ Λ, g * u = u * g) {B₀ : Subgroup V}
    (hB₀ : ∀ S : Subgroup V, (∀ g ∈ Λ, ∀ s ∈ S, g s ∈ S) → S ≠ ⊥ → S ≠ ⊤ →
      S = Subgroup.zpowers c ∨ S = B₀) : vMinus u = B₀ := by
  have hp := hpp.out
  have hcord : orderOf c = p := orderOf_eq_prime (hexp c) hc1
  have hcardc : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hcord]
  have hcardm : Nat.card (vMinus u) = p ^ 3 := card_vMinus hp2 hexp hcard hu2 hc1 hfix
  have hVm_inv : ∀ g ∈ Λ, ∀ s ∈ vMinus u, g s ∈ vMinus u := by
    intro g hg s hs
    have hs' : u s = s⁻¹ := hs
    show u (g s) = (g s)⁻¹
    have h1 : u (g s) = g (u s) := by
      have := congrArg (fun m : MulAut V => m s) (hucomm g hg)
      simpa [MulAut.mul_apply] using this.symm
    rw [h1, hs', map_inv]
  have hp3 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp34 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp2le : 2 ≤ p := hp.two_le
  have hVm_ne_bot : vMinus u ≠ ⊥ := by
    intro h
    have h1 : Nat.card (vMinus u) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hcardm] at h1
    omega
  have hVm_ne_top : vMinus u ≠ ⊤ := by
    intro h
    have h1 : Nat.card (vMinus u) = Nat.card V := by rw [h]; exact Subgroup.card_top
    rw [hcardm, hcard] at h1
    omega
  rcases hB₀ _ hVm_inv hVm_ne_bot hVm_ne_top with h | h
  · exfalso
    have h1 : Nat.card (vMinus u) = p := by rw [h]; exact hcardc
    rw [hcardm] at h1
    omega
  · exact h

theorem c_not_mem_vMinus {p : ℕ} [hpp : Fact p.Prime] (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    {u : MulAut V} {c : V} (hc1 : c ≠ 1) (hfix : ∀ e, u e = e ↔ e ∈ Subgroup.zpowers c) :
    c ∉ vMinus u := by
  intro h
  have h1 : u c = c := (hfix c).2 (Subgroup.mem_zpowers c)
  have h2 : u c = c⁻¹ := h
  rw [h1] at h2
  have h4 : c ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.2 h2
  have h5 := pow_gcd_eq_one.2 ⟨h4, hexp c⟩
  have hcop : Nat.gcd 2 p = 1 := (Nat.coprime_primes Nat.prime_two hpp.out).2 (Ne.symm hp2)
  rw [hcop, pow_one] at h5
  exact hc1 h5

theorem core [Finite V] {p : ℕ} [hpp : Fact p.Prime] (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    (hcard : Nat.card V = p ^ 4) {u : MulAut V} (hu2 : u * u = 1) {c : V} (hc1 : c ≠ 1)
    (hfix : ∀ e, u e = e ↔ e ∈ Subgroup.zpowers c) {Λ : Subgroup (MulAut V)}
    (hucomm : ∀ g ∈ Λ, g * u = u * g)
    (hfour : ∃ B₀ : Subgroup V, ∀ S : Subgroup V, (∀ g ∈ Λ, ∀ s ∈ S, g s ∈ S) → S ≠ ⊥ → S ≠ ⊤ →
      S = Subgroup.zpowers c ∨ S = B₀)
    {x : MulAut V} (hx1 : x ≠ 1) (hxodd : Odd (orderOf x)) (hxp : ¬ p ∣ orderOf x)
    (hux : u * x * u⁻¹ = x⁻¹)
    (hcomm : ∀ g ∈ Λ, (g * x * g⁻¹) * x = x * (g * x * g⁻¹)) : False := by
  have hp := hpp.out
  obtain ⟨B₀, hB₀⟩ := hfour
  have hcord : orderOf c = p := orderOf_eq_prime (hexp c) hc1
  have hcardc : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hcord]
  have hcardm : Nat.card (vMinus u) = p ^ 3 := card_vMinus hp2 hexp hcard hu2 hc1 hfix
  have huu : ∀ v : V, u (u v) = v := fun v => by
    have := congrArg (fun m : MulAut V => m v) hu2
    simpa [MulAut.mul_apply] using this
  have hux0 : u * x = x⁻¹ * u := by
    calc u * x = (u * x * u⁻¹) * u := by group
      _ = x⁻¹ * u := by rw [hux]
  have hux1 : ∀ e : V, u (x e) = x⁻¹ (u e) := fun e =>
    congrArg (fun m : MulAut V => m e) hux0
  have hux2 : ∀ e : V, u (x⁻¹ e) = x (u e) := by
    intro e
    have h1 := hux1 (x⁻¹ e)
    rw [MulAut.apply_inv_self] at h1
    have h2 := congrArg x h1
    rw [MulAut.apply_inv_self] at h2
    exact h2.symm
  have hJu : ∀ e : V, u (jHom x e) = (jHom x (u e))⁻¹ := by
    intro e
    rw [jHom_apply, jHom_apply, map_mul, map_inv, hux1, hux2, mul_inv, inv_inv]
    exact mul_comm _ _
  have hJm : ∀ e ∈ vMinus u, jHom x e ∈ Subgroup.zpowers c := by
    intro e he
    have he' : u e = e⁻¹ := he
    exact (hfix _).1 (by rw [hJu, he', map_inv, inv_inv])
  have hJp : ∀ e ∈ Subgroup.zpowers c, jHom x e ∈ vMinus u := by
    intro e he
    have hue : u e = e := (hfix e).2 he
    show u (jHom x e) = (jHom x e)⁻¹
    rw [hJu, hue]
  let P : Subgroup V := MonoidHom.eqLocus (x : V →* V) (MonoidHom.id V)
  have hP : ∀ e, e ∈ P ↔ x e = e := fun e => Iff.rfl
  have hc_notin : c ∉ P := by
    intro hc
    have hxc : x c = c := (hP c).1 hc
    apply hx1
    apply eq_one_of_jj hp hexp hxodd hxp
    intro e
    obtain ⟨s, t, hs, ht, rfl⟩ := exists_decomp hp hp2 hexp hu2 e
    have hs' : s ∈ Subgroup.zpowers c := (hfix s).1 hs
    have hJs : jHom x s = 1 := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs'
      rw [map_zpow, (jHom_eq_one_iff hxodd c).2 hxc, one_zpow]
    have hJt : jHom x t ∈ Subgroup.zpowers c := hJm t ht
    rw [map_mul, hJs, one_mul]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hJt
    rw [← hn, map_zpow, hxc]
  have hP_u : ∀ e ∈ P, u e ∈ P := by
    intro e he
    have hxe : x e = e := (hP e).1 he
    refine (hP _).2 ?_
    have h1 := hux1 e
    rw [hxe] at h1
    have h2 := congrArg x h1
    rw [MulAut.apply_inv_self] at h2
    exact h2
  have hP_sub : ∀ e ∈ P, e ∈ vMinus u := by
    intro e he
    have h1 : e * u e ∈ P := P.mul_mem he (hP_u e he)
    have h2 : u (e * u e) = e * u e := by rw [map_mul, huu, mul_comm]
    have h3 : e * u e ∈ Subgroup.zpowers c := (hfix _).1 h2
    have h4 : e * u e = 1 := by
      by_contra hne
      have hord : orderOf (e * u e) = p := orderOf_eq_prime (hexp _) hne
      have hle : Subgroup.zpowers (e * u e) ≤ Subgroup.zpowers c := (Subgroup.zpowers_le).2 h3
      have heq : Subgroup.zpowers (e * u e) = Subgroup.zpowers c := by
        apply Subgroup.eq_of_le_of_card_ge hle
        rw [Nat.card_zpowers, Nat.card_zpowers, hord, hcord]
      have hcm : c ∈ Subgroup.zpowers (e * u e) := by rw [heq]; exact Subgroup.mem_zpowers c
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hcm
      apply hc_notin
      rw [← hn]
      exact P.zpow_mem h1 n
    show u e = e⁻¹
    exact eq_inv_of_mul_eq_one_right h4
  have hP_inv : ∀ g ∈ Λ, ∀ e ∈ P, g e ∈ P := by
    intro g hg e he
    set x' : MulAut V := g⁻¹ * x * g with hx'
    have hgi : g⁻¹ ∈ Λ := Λ.inv_mem hg
    have hcomm' : x' * x = x * x' := by
      have := hcomm g⁻¹ hgi
      rwa [inv_inv] at this
    have hodd' : Odd (orderOf x') := by
      have h0 : orderOf x' = orderOf x := by
        have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
        simpa [MulAut.conj_apply, hx'] using this
      rw [h0]; exact hxodd
    have hug : u * g = g * u := (hucomm g hg).symm
    have hugi : u * g⁻¹ = g⁻¹ * u := (hucomm g⁻¹ hgi).symm
    have hux' : u * x' = x'⁻¹ * u := by
      calc u * x' = (u * g⁻¹) * x * g := by rw [hx']; group
        _ = g⁻¹ * (u * x) * g := by rw [hugi]; group
        _ = g⁻¹ * (x⁻¹ * u) * g := by rw [hux0]
        _ = g⁻¹ * x⁻¹ * (u * g) := by group
        _ = g⁻¹ * x⁻¹ * (g * u) := by rw [hug]
        _ = x'⁻¹ * u := by rw [hx']; group
    have hxe : x e = e := (hP e).1 he
    have h1 : x (x' e) = x' e := by
      have := congrArg (fun m : MulAut V => m e) hcomm'
      simp only [MulAut.mul_apply] at this
      rw [hxe] at this
      exact this.symm
    have h2 : u e = e⁻¹ := hP_sub e he
    have h3 : u (x' e) = (x' e)⁻¹ := hP_sub (x' e) ((hP _).2 h1)
    have h4 : u (x' e) = (x'⁻¹ e)⁻¹ := by
      have := congrArg (fun m : MulAut V => m e) hux'
      simp only [MulAut.mul_apply] at this
      rw [this, h2, map_inv]
    have h5 : x'⁻¹ e = x' e := inv_inj.1 (h4.symm.trans h3)
    have h6 : (x' * x') e = e := by
      rw [MulAut.mul_apply, ← h5, MulAut.apply_inv_self]
    have h7 : x' e = e := apply_eq_of_sq hodd' h6
    have h8 : g * x' = x * g := by rw [hx']; group
    have h9 : x (g e) = g (x' e) := (congrArg (fun m : MulAut V => m e) h8).symm
    refine (hP _).2 ?_
    rw [h9, h7]
  have hVmB : vMinus u = B₀ := vMinus_eq hp2 hexp hcard hu2 hc1 hfix hucomm hB₀
  have hp3 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp2le : 2 ≤ p := hp.two_le
  have hP_ne_top : P ≠ ⊤ := by
    intro h
    apply hx1
    refine MulEquiv.ext fun e => ?_
    have : e ∈ P := by rw [h]; trivial
    exact (hP e).1 this
  have hP_ne_bot : P ≠ ⊥ := by
    intro h
    let f : vMinus u → Subgroup.zpowers c := fun e => ⟨jHom x e, hJm e e.2⟩
    have hnotinj : ¬ Function.Injective f := by
      intro hinj
      have h1 := Nat.card_le_card_of_injective f hinj
      rw [hcardm, hcardc] at h1
      omega
    simp only [Function.Injective, not_forall] at hnotinj
    obtain ⟨a, b, hab, hne⟩ := hnotinj
    have hJ : jHom x ((a : V) * (b : V)⁻¹) = 1 := by
      have h1 : jHom x (a : V) = jHom x (b : V) := congrArg Subtype.val hab
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hxe : x ((a : V) * (b : V)⁻¹) = (a : V) * (b : V)⁻¹ := (jHom_eq_one_iff hxodd _).1 hJ
    have hmem : (a : V) * (b : V)⁻¹ ∈ P := (hP _).2 hxe
    rw [h, Subgroup.mem_bot] at hmem
    exact hne (Subtype.ext (mul_inv_eq_one.1 hmem))
  rcases hB₀ P hP_inv hP_ne_bot hP_ne_top with h | h
  · exact hc_notin (by rw [h]; exact Subgroup.mem_zpowers c)
  · have hVP : ∀ e ∈ vMinus u, x e = e := by
      intro e he
      have : e ∈ P := by rw [h, ← hVmB]; exact he
      exact (hP e).1 this
    apply hx1
    apply eq_one_of_jj hp hexp hxodd hxp
    intro e
    obtain ⟨s, t, hs, ht, rfl⟩ := exists_decomp hp hp2 hexp hu2 e
    have hJt : jHom x t = 1 := (jHom_eq_one_iff hxodd t).2 (hVP t ht)
    have hJs : jHom x s ∈ vMinus u := hJp s ((hfix s).1 hs)
    rw [map_mul, hJt, mul_one]
    exact hVP _ hJs

theorem claimA [Finite V] {p : ℕ} [hpp : Fact p.Prime] (hp2 : p ≠ 2) (hexp : ∀ v : V, v ^ p = 1)
    (hcard : Nat.card V = p ^ 4) {u : MulAut V} (hu2 : u * u = 1) {c : V} (hc1 : c ≠ 1)
    (hfix : ∀ e, u e = e ↔ e ∈ Subgroup.zpowers c) {Λ : Subgroup (MulAut V)} (huΛ : u ∈ Λ)
    (hucomm : ∀ g ∈ Λ, g * u = u * g)
    (hfour : ∃ B₀ : Subgroup V, ∀ S : Subgroup V, (∀ g ∈ Λ, ∀ s ∈ S, g s ∈ S) → S ≠ ⊥ → S ≠ ⊤ →
      S = Subgroup.zpowers c ∨ S = B₀)
    {Z : Subgroup (MulAut V)} (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hZΛ : ∀ g ∈ Λ, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) (hZodd : ∀ z ∈ Z, Odd (orderOf z))
    (hZp : ∀ z ∈ Z, ¬ p ∣ orderOf z) : ∀ z ∈ Z, z * u = u * z := by
  intro z hz
  by_contra hne
  set y : MulAut V := u * z * u⁻¹ with hy
  set x : MulAut V := z * y⁻¹ with hx
  have hyZ : y ∈ Z := hZΛ u huΛ z hz
  have hxZ : x ∈ Z := Z.mul_mem hz (Z.inv_mem hyZ)
  have hx1 : x ≠ 1 := by
    intro h
    apply hne
    have h1 : z = y := mul_inv_eq_one.1 h
    calc z * u = y * u := by rw [← h1]
      _ = u * z := by rw [hy]; group
  have h1 : u * y * u⁻¹ = z := by
    have : u * y * u⁻¹ = (u * u) * z * (u * u)⁻¹ := by rw [hy]; group
    rw [this, hu2]; group
  have hux : u * x * u⁻¹ = x⁻¹ := by
    have h2 : u * x * u⁻¹ = (u * z * u⁻¹) * (u * y * u⁻¹)⁻¹ := by rw [hx]; group
    rw [h2, h1, ← hy, hx]; group
  exact core hp2 hexp hcard hu2 hc1 hfix hucomm hfour hx1 (hZodd x hxZ) (hZp x hxZ) hux
    (fun g hg => hZc _ (hZΛ g hg x hxZ) x hxZ)

end CFSG.RankThree.PartOne.S13K.N135
