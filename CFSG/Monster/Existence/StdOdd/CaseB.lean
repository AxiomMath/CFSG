module

public import CFSG.Monster.Existence.StdOdd.CaseA
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm

public section

namespace CFSG.Monster.Existence.StdOdd

open Subgroup

variable {G : Type*} [Group G]

section Fixed

variable [Finite G]

theorem exists_fixed_card {F : Subgroup G} [F.Normal] (hFc : centralizer (F : Set G) ≤ F)
    {a : ℕ} (haF : Nat.card F = 3 ^ a) {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) {g : G}
    (hg : orderOf g = p) :
    ∃ c : ℕ, c < a ∧ Nat.card ↥(F ⊓ centralizer ({g} : Set G)) = 3 ^ c ∧
      3 ^ a ≡ 3 ^ c [MOD p] := by
  have hmod := card_modEq_zpowers hg (mem_normalizer_of_normal (F := F) g)
  have hdvd : Nat.card ↥(F ⊓ centralizer ({g} : Set G)) ∣ 3 ^ a :=
    (Subgroup.card_dvd_of_le inf_le_left).trans (dvd_of_eq haF)
  obtain ⟨c, hc, hceq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  refine ⟨c, ?_, hceq, by rwa [haF, hceq] at hmod⟩
  rcases Nat.lt_or_ge c a with h | h
  · exact h
  · exfalso
    have hca : c = a := le_antisymm hc h
    have heq : F ⊓ centralizer ({g} : Set G) = F :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hceq, haF, hca])
    have hgF : g ∈ centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : x ∈ F ⊓ centralizer ({g} : Set G) := by rw [heq]; exact hx
      exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx').2) g rfl).symm
    have hgF' : g ∈ F := hFc hgF
    have h1 : orderOf g ∣ 3 ^ a := (Subgroup.orderOf_dvd_natCard F hgF').trans (dvd_of_eq haF)
    rw [hg] at h1
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow h1))

end Fixed

section Arith

private theorem arith5 : ∀ a < 10, ∀ c < a, c ≤ 2 → 3 ^ a ≡ 3 ^ c [MOD 5] →
    a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9 := by
  intro a ha c hc hc2 h
  interval_cases a <;> interval_cases c <;> simp_all [Nat.ModEq]

private theorem arith7 : ∀ a < 10, ∀ c < a, c ≤ 2 → 3 ^ a ≡ 3 ^ c [MOD 7] →
    a = 6 ∨ a = 7 ∨ a = 8 := by decide

private theorem arith11 : ∀ a < 10, ∀ c < a, c ≤ 1 → 3 ^ a ≡ 3 ^ c [MOD 11] →
    a = 5 ∨ a = 6 := by decide

private theorem arith13 : ∀ a < 10, ∀ c < a, c = 0 → 3 ^ a ≡ 3 ^ c [MOD 13] →
    a = 3 ∨ a = 6 ∨ a = 9 := by decide

private theorem arith17 : ∀ a < 10, ∀ c < a, c ≤ 1 → ¬ 3 ^ a ≡ 3 ^ c [MOD 17] := by decide

private theorem arith19 : ∀ a < 10, ∀ c < a, c ≤ 1 → ¬ 3 ^ a ≡ 3 ^ c [MOD 19] := by decide

private theorem sep5 : ∀ c < 3, ∀ e ≤ c, 3 ^ c ≡ 3 ^ e [MOD 5] → c = e := by decide

private theorem sep7 : ∀ c < 3, ∀ e ≤ c, 3 ^ c ≡ 3 ^ e [MOD 7] → c = e := by decide

private theorem sq5 : ∀ a < 10, ∀ c < a, c ≤ 2 → ¬ 3 ^ a ≡ 3 ^ c [MOD 5 ^ 2] := by decide

private theorem sq7 : ∀ a < 10, ∀ c < a, c ≤ 2 → ¬ 3 ^ a ≡ 3 ^ c [MOD 7 ^ 2] := by decide

private theorem arith35 : ∀ a < 10, ∀ e < a, e ≤ 2 → 3 ^ a ≡ 3 ^ e [MOD 5] → 3 ^ a ≡ 3 ^ e [MOD 7] →
    False := by decide

theorem le_of_pow_dvd_mul {c e m : ℕ} (hm : ¬ 3 ∣ m) (h : 3 ^ c ∣ 3 ^ e * m) : c ≤ e := by
  have hcop : Nat.Coprime (3 ^ c) m :=
    Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right h)

end Arith

section Subgroups

variable [Finite G]

omit [Finite G] in
theorem exists_card_pow_of_le {F K : Subgroup G} {a : ℕ} (haF : Nat.card F = 3 ^ a)
    (hKF : K ≤ F) : ∃ c : ℕ, c ≤ a ∧ Nat.card K = 3 ^ c := by
  obtain ⟨c, hc, h⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    ((Subgroup.card_dvd_of_le hKF).trans (dvd_of_eq haF))
  exact ⟨c, hc, h⟩

theorem inf_centralizer_eq_of_commute {F : Subgroup G} [F.Normal] {a : ℕ}
    (haF : Nat.card F = 3 ^ a) {p : ℕ} [Fact p.Prime] {cm : ℕ}
    (hcm : ∀ x : G, orderOf x = p →
      ∀ c, 3 ^ c ∣ Nat.card (centralizer ({x} : Set G)) → c ≤ cm)
    (hsep : ∀ e c, e ≤ c → c ≤ cm → 3 ^ c ≡ 3 ^ e [MOD p] → c = e)
    {z₀ z : G} (h₀ : orderOf z₀ = p) (h₁ : orderOf z = p) (hc : z₀ * z = z * z₀) :
    F ⊓ centralizer ({z₀} : Set G) = F ⊓ centralizer ({z} : Set G) := by
  set F₀ : Subgroup G := F ⊓ centralizer ({z₀} : Set G) with hF₀
  set F₁ : Subgroup G := F ⊓ centralizer ({z} : Set G) with hF₁
  have hn₀ : z ∈ normalizer (F₀ : Set G) :=
    mem_normalizer_inf (mem_normalizer_of_normal z) (mem_normalizer_centralizer_of_commute hc.symm)
  have hn₁ : z₀ ∈ normalizer (F₁ : Set G) :=
    mem_normalizer_inf (mem_normalizer_of_normal z₀) (mem_normalizer_centralizer_of_commute hc)
  have hm₀ := card_modEq_zpowers h₁ hn₀
  have hm₁ := card_modEq_zpowers h₀ hn₁
  have hE : F₁ ⊓ centralizer ({z₀} : Set G) = F₀ ⊓ centralizer ({z} : Set G) :=
    inf_right_comm _ _ _
  rw [hE] at hm₁
  set E : Subgroup G := F₀ ⊓ centralizer ({z} : Set G) with hEdef
  have hEF₀ : E ≤ F₀ := inf_le_left
  have hEF₁ : E ≤ F₁ := hE ▸ inf_le_left
  have hF₀F : F₀ ≤ F := inf_le_left
  have hF₁F : F₁ ≤ F := inf_le_left
  obtain ⟨c₀, -, hc₀⟩ := exists_card_pow_of_le haF hF₀F
  obtain ⟨c₁, -, hc₁⟩ := exists_card_pow_of_le haF hF₁F
  obtain ⟨e, -, he⟩ := exists_card_pow_of_le haF (hEF₀.trans hF₀F)
  have hec₀ : e ≤ c₀ := by
    have := Subgroup.card_dvd_of_le hEF₀
    rw [he, hc₀] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hec₁ : e ≤ c₁ := by
    have := Subgroup.card_dvd_of_le hEF₁
    rw [he, hc₁] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hcm₀ : c₀ ≤ cm := hcm z₀ h₀ c₀ (hc₀ ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hcm₁ : c₁ ≤ cm := hcm z h₁ c₁ (hc₁ ▸ Subgroup.card_dvd_of_le inf_le_right)
  rw [hc₀, he] at hm₀
  rw [hc₁, he] at hm₁
  have e₀ : c₀ = e := hsep e c₀ hec₀ hcm₀ hm₀
  have e₁ : c₁ = e := hsep e c₁ hec₁ hcm₁ hm₁
  have hEq : E = F₀ := Subgroup.eq_of_le_of_card_ge hEF₀ (by rw [he, hc₀, e₀])
  have hle : F₀ ≤ F₁ := hEq ▸ hEF₁
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc₀, hc₁, e₀, e₁])

end Subgroups

section Square

variable [Finite G]

theorem no_subgroup_card_sq {F : Subgroup G} [F.Normal]
    (hFc : centralizer (F : Set G) ≤ F) {a : ℕ} (haF : Nat.card F = 3 ^ a) {p : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) {cm : ℕ}
    (hcm : ∀ x : G, orderOf x = p →
      ∀ c, 3 ^ c ∣ Nat.card (centralizer ({x} : Set G)) → c ≤ cm)
    (hsep : ∀ e c, e ≤ c → c ≤ cm → 3 ^ c ≡ 3 ^ e [MOD p] → c = e)
    (harith : ∀ c, c ≤ cm → c < a → ¬ 3 ^ a ≡ 3 ^ c [MOD p ^ 2])
    (P : Subgroup G) (hP : Nat.card P = p ^ 2) : False := by
  have hpp := (Fact.out : p.Prime)
  have hcomm : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP
  have hPc : ∀ u v : G, u ∈ P → v ∈ P → Commute u v := fun u v hu hv =>
    congrArg Subtype.val (hcomm.is_comm.comm (⟨u, hu⟩ : P) ⟨v, hv⟩)
  obtain ⟨z₀', hz₀'⟩ := exists_prime_orderOf_dvd_card' (G := P) p
    (by rw [hP]; exact dvd_pow_self p two_ne_zero)
  have hz₀o : orderOf (z₀' : G) = p := by rw [Subgroup.orderOf_coe]; exact hz₀'
  have hz₀P : (z₀' : G) ∈ P := z₀'.2
  have hPF : P ≤ normalizer (F : Set G) := fun g _ => mem_normalizer_of_normal g
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer P F hPF
  let Sset : Set F := {x | (x : G) ∈ centralizer ({(z₀' : G)} : Set G)}
  have hS : ∀ k : P, ∀ x ∈ Sset, k • x ∈ Sset := by
    intro k x hx
    have hk : Commute (z₀' : G) k := hPc _ _ hz₀P k.2
    have hxc : Commute (z₀' : G) x := (Subgroup.mem_centralizer_iff.1 hx) _ rfl
    show ((k • x : F) : G) ∈ centralizer ({(z₀' : G)} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact ((hk.mul_right hxc).mul_right hk.inv_right).eq
  have hfree : ∀ x ∉ Sset, ∀ k : P, k • x = x → k = 1 := by
    intro x hx k hkx
    by_contra hk1
    have hkx' : Commute (k : G) x := by
      have h1 : (k : G) * x * (k : G)⁻¹ = x := congrArg Subtype.val hkx
      exact (mul_inv_eq_iff_eq_mul.1 h1 : (k : G) * x = x * k)
    have hk1' : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
    have hdvd : orderOf (k : G) ∣ p ^ 2 := by
      rw [← hP, Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard k
    have hne : orderOf (k : G) ≠ 1 := fun h => hk1' (orderOf_eq_one_iff.1 h)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hpp).1 (hq.dvd_of_dvd_pow (hqd.trans hdvd))
    subst hqp
    have : Fact q.Prime := ⟨hq⟩
    have hcard : q ∣ Nat.card (zpowers (k : G)) := by rw [Nat.card_zpowers]; exact hqd
    obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := zpowers (k : G)) q hcard
    have hz'o : orderOf (z' : G) = q := by rw [Subgroup.orderOf_coe]; exact hz'
    have hz'P : (z' : G) ∈ P := (Subgroup.zpowers_le.2 k.2) z'.2
    have hz'x : Commute (z' : G) x := by
      have hle : zpowers (k : G) ≤ centralizer ({(x : G)} : Set G) := by
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hkx'.eq.symm
      exact (Subgroup.mem_centralizer_iff.1 (hle z'.2) _ rfl).symm
    have hcomm' : (z₀' : G) * (z' : G) = (z' : G) * (z₀' : G) := (hPc _ _ hz₀P hz'P).eq
    have heq := inf_centralizer_eq_of_commute haF hcm hsep hz₀o hz'o hcomm'
    apply hx
    have hxz' : (x : G) ∈ F ⊓ centralizer ({(z' : G)} : Set G) :=
      Subgroup.mem_inf.2 ⟨x.2, by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hz'x.eq⟩
    rw [← heq] at hxz'
    exact (Subgroup.mem_inf.1 hxz').2
  have hmod := card_modEq_of_free_outside (K := P) (X := F) Sset hS hfree
  have hSc : Nat.card Sset = Nat.card ↥(F ⊓ centralizer ({(z₀' : G)} : Set G)) :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨(y : G), (Subgroup.mem_inf.1 y.2).1⟩, (Subgroup.mem_inf.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  obtain ⟨c, hca, hcard, -⟩ := exists_fixed_card hFc haF hp3 hz₀o
  have hcmc : c ≤ cm := hcm _ hz₀o c (hcard ▸ Subgroup.card_dvd_of_le inf_le_right)
  rw [hSc, hcard, hP, haF] at hmod
  exact harith c hcmc hca hmod

end Square

section Context

structure CaseBCtx (G : Type*) [Group G] (F : Subgroup G) (a : ℕ) : Prop where
  normal : F.Normal
  card : Nat.card F = 3 ^ a
  le_nine : a ≤ 9
  cent : centralizer (F : Set G) ≤ F
  odd : Odd (Nat.card G)
  dvd : Nat.card G ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19
  facts : CentralizerFacts G

variable {F : Subgroup G} {a : ℕ}

theorem CaseBCtx.c5 (ctx : CaseBCtx G F a) : ∀ x : G, orderOf x = 5 →
    ∀ c, 3 ^ c ∣ Nat.card (centralizer ({x} : Set G)) → c ≤ 2 := fun x hx c hc =>
  le_of_pow_dvd_mul (m := 5 ^ 2 * 7) (by norm_num)
    (hc.trans (by simpa only [mul_assoc] using ctx.facts.c5_odd ctx.odd hx))

theorem CaseBCtx.c7 (ctx : CaseBCtx G F a) : ∀ x : G, orderOf x = 7 →
    ∀ c, 3 ^ c ∣ Nat.card (centralizer ({x} : Set G)) → c ≤ 2 := fun x hx c hc =>
  le_of_pow_dvd_mul (m := 5 * 7 ^ 2) (by norm_num)
    (hc.trans (by simpa only [mul_assoc] using ctx.facts.c7_odd ctx.odd hx))

theorem CaseBCtx.c11 (ctx : CaseBCtx G F a) : ∀ x : G, orderOf x = 11 →
    ∀ c, 3 ^ c ∣ Nat.card (centralizer ({x} : Set G)) → c ≤ 1 := fun x hx c hc =>
  le_of_pow_dvd_mul (m := 11) (by norm_num)
    (hc.trans (by simpa only [pow_one] using ctx.facts.c11_odd ctx.odd hx))

theorem CaseBCtx.c13 (ctx : CaseBCtx G F a) : ∀ x : G, orderOf x = 13 →
    ∀ c, 3 ^ c ∣ Nat.card (centralizer ({x} : Set G)) → c ≤ 0 := fun x hx c hc =>
  le_of_pow_dvd_mul (e := 0) (m := 13) (by norm_num)
    (hc.trans (by rw [ctx.facts.c13 x hx]; simp))

theorem CaseBCtx.c17 (ctx : CaseBCtx G F a) : ∀ x : G, orderOf x = 17 →
    ∀ c, 3 ^ c ∣ Nat.card (centralizer ({x} : Set G)) → c ≤ 1 := fun x hx c hc =>
  le_of_pow_dvd_mul (m := 17) (by norm_num)
    (hc.trans (by simpa only [pow_one] using ctx.facts.c17 x hx))

theorem CaseBCtx.c19 (ctx : CaseBCtx G F a) : ∀ x : G, orderOf x = 19 →
    ∀ c, 3 ^ c ∣ Nat.card (centralizer ({x} : Set G)) → c ≤ 1 := fun x hx c hc =>
  le_of_pow_dvd_mul (m := 19) (by norm_num)
    (hc.trans (by simpa only [pow_one] using ctx.facts.c19 x hx))

variable [Finite G]

theorem CaseBCtx.exists_fixed_card (ctx : CaseBCtx G F a) {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {g : G} (hg : orderOf g = p) :
    ∃ c : ℕ, c < a ∧ Nat.card ↥(F ⊓ centralizer ({g} : Set G)) = 3 ^ c ∧
      3 ^ a ≡ 3 ^ c [MOD p] :=
  haveI := ctx.normal
  _root_.CFSG.Monster.Existence.StdOdd.exists_fixed_card ctx.cent ctx.card hp3 hg

theorem CaseBCtx.feasible5 (ctx : CaseBCtx G F a) {g : G} (hg : orderOf g = 5) :
    a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hca, hc, hmod⟩ := ctx.exists_fixed_card (p := 5) (by norm_num) hg
  have hc2 : c ≤ 2 := ctx.c5 g hg c (hc ▸ Subgroup.card_dvd_of_le inf_le_right)
  exact arith5 a (by have := ctx.le_nine; omega) c hca hc2 hmod

theorem CaseBCtx.feasible7 (ctx : CaseBCtx G F a) {g : G} (hg : orderOf g = 7) :
    a = 6 ∨ a = 7 ∨ a = 8 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨c, hca, hc, hmod⟩ := ctx.exists_fixed_card (p := 7) (by norm_num) hg
  have hc2 : c ≤ 2 := ctx.c7 g hg c (hc ▸ Subgroup.card_dvd_of_le inf_le_right)
  exact arith7 a (by have := ctx.le_nine; omega) c hca hc2 hmod

theorem CaseBCtx.feasible11 (ctx : CaseBCtx G F a) {g : G} (hg : orderOf g = 11) :
    a = 5 ∨ a = 6 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨c, hca, hc, hmod⟩ := ctx.exists_fixed_card (p := 11) (by norm_num) hg
  have hc2 : c ≤ 1 := ctx.c11 g hg c (hc ▸ Subgroup.card_dvd_of_le inf_le_right)
  exact arith11 a (by have := ctx.le_nine; omega) c hca hc2 hmod

theorem CaseBCtx.feasible13 (ctx : CaseBCtx G F a) {g : G} (hg : orderOf g = 13) :
    a = 3 ∨ a = 6 ∨ a = 9 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨c, hca, hc, hmod⟩ := ctx.exists_fixed_card (p := 13) (by norm_num) hg
  have hc2 : c = 0 := Nat.le_zero.1 (ctx.c13 g hg c (hc ▸ Subgroup.card_dvd_of_le inf_le_right))
  exact arith13 a (by have := ctx.le_nine; omega) c hca hc2 hmod

theorem CaseBCtx.not_order17 (ctx : CaseBCtx G F a) {g : G} (hg : orderOf g = 17) : False := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨c, hca, hc, hmod⟩ := ctx.exists_fixed_card (p := 17) (by norm_num) hg
  have hc2 : c ≤ 1 := ctx.c17 g hg c (hc ▸ Subgroup.card_dvd_of_le inf_le_right)
  exact arith17 a (by have := ctx.le_nine; omega) c hca hc2 hmod

theorem CaseBCtx.not_order19 (ctx : CaseBCtx G F a) {g : G} (hg : orderOf g = 19) : False := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨c, hca, hc, hmod⟩ := ctx.exists_fixed_card (p := 19) (by norm_num) hg
  have hc2 : c ≤ 1 := ctx.c19 g hg c (hc ▸ Subgroup.card_dvd_of_le inf_le_right)
  exact arith19 a (by have := ctx.le_nine; omega) c hca hc2 hmod

theorem CaseBCtx.not_dvd_sq5 (ctx : CaseBCtx G F a) : ¬ 5 ^ 2 ∣ Nat.card G := by
  intro h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) 5 (n := 2) h
  have := ctx.normal
  exact no_subgroup_card_sq (F := F) ctx.cent ctx.card (p := 5) (by norm_num) (cm := 2) ctx.c5
    (fun e c he hc hmod => by
      have := sep5 c (by omega) e he hmod
      exact this)
    (fun c hc hca => sq5 a (by have := ctx.le_nine; omega) c hca hc) P hP

theorem CaseBCtx.not_dvd_sq7 (ctx : CaseBCtx G F a) : ¬ 7 ^ 2 ∣ Nat.card G := by
  intro h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) 7 (n := 2) h
  have := ctx.normal
  exact no_subgroup_card_sq (F := F) ctx.cent ctx.card (p := 7) (by norm_num) (cm := 2) ctx.c7
    (fun e c he hc hmod => by
      have := sep7 c (by omega) e he hmod
      exact this)
    (fun c hc hca => sq7 a (by have := ctx.le_nine; omega) c hca hc) P hP

end Context

section Commuting

variable {F : Subgroup G} {a : ℕ} [Finite G]

omit [Finite G] in
theorem orderOf_dvd_card_centralizer {g₁ g₂ : G} (hc : g₁ * g₂ = g₂ * g₁) :
    orderOf g₂ ∣ Nat.card (centralizer ({g₁} : Set G)) := by
  refine Subgroup.orderOf_dvd_natCard _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact hc

theorem CaseBCtx.not_commute_five_seven (ctx : CaseBCtx G F a) {g₅ g₇ : G} (h5 : orderOf g₅ = 5)
    (h7 : orderOf g₇ = 7) (hc : g₅ * g₇ = g₇ * g₅) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := ctx.normal
  obtain ⟨c₅, hc₅a, hc₅, hm₅⟩ := ctx.exists_fixed_card (p := 5) (by norm_num) h5
  obtain ⟨c₇, hc₇a, hc₇, hm₇⟩ := ctx.exists_fixed_card (p := 7) (by norm_num) h7
  have hc₅2 : c₅ ≤ 2 := ctx.c5 g₅ h5 c₅ (hc₅ ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hc₇2 : c₇ ≤ 2 := ctx.c7 g₇ h7 c₇ (hc₇ ▸ Subgroup.card_dvd_of_le inf_le_right)
  set F₅ : Subgroup G := F ⊓ centralizer ({g₅} : Set G) with hF₅
  set F₇ : Subgroup G := F ⊓ centralizer ({g₇} : Set G) with hF₇
  have hn₅ : g₇ ∈ normalizer (F₅ : Set G) :=
    mem_normalizer_inf (mem_normalizer_of_normal g₇) (mem_normalizer_centralizer_of_commute hc.symm)
  have hn₇ : g₅ ∈ normalizer (F₇ : Set G) :=
    mem_normalizer_inf (mem_normalizer_of_normal g₅) (mem_normalizer_centralizer_of_commute hc)
  have hm1 := card_modEq_zpowers h7 hn₅
  have hm2 := card_modEq_zpowers h5 hn₇
  have hE : F₇ ⊓ centralizer ({g₅} : Set G) = F₅ ⊓ centralizer ({g₇} : Set G) :=
    inf_right_comm _ _ _
  rw [hE] at hm2
  set E : Subgroup G := F₅ ⊓ centralizer ({g₇} : Set G) with hEdef
  have hEF₅ : E ≤ F₅ := inf_le_left
  have hEF₇ : E ≤ F₇ := hE ▸ inf_le_left
  obtain ⟨e, -, he⟩ := exists_card_pow_of_le ctx.card (hEF₅.trans (inf_le_left : F₅ ≤ F))
  have he₅ : e ≤ c₅ := by
    have := Subgroup.card_dvd_of_le hEF₅
    rw [he, hc₅] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have he₇ : e ≤ c₇ := by
    have := Subgroup.card_dvd_of_le hEF₇
    rw [he, hc₇] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  rw [hc₅, he] at hm1
  rw [hc₇, he] at hm2
  have e5 : c₅ = e := sep7 c₅ (by omega) e he₅ hm1
  have e7 : c₇ = e := sep5 c₇ (by omega) e he₇ hm2
  have hm₅' : 3 ^ a ≡ 3 ^ e [MOD 5] := by
    rw [← e5]
    exact hm₅
  have hm₇' : 3 ^ a ≡ 3 ^ e [MOD 7] := by
    rw [← e7]
    exact hm₇
  exact arith35 a (by have := ctx.le_nine; omega) e (by omega) (by omega) hm₅' hm₇'

theorem CaseBCtx.not_commute (ctx : CaseBCtx G F a) {r s : ℕ}
    (hr : r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 13) (hs : s = 5 ∨ s = 7 ∨ s = 11 ∨ s = 13) (hrs : r ≠ s)
    {g₁ g₂ : G} (h₁ : orderOf g₁ = r) (h₂ : orderOf g₂ = s) (hc : g₁ * g₂ = g₂ * g₁) : False := by
  have d12 : orderOf g₂ ∣ Nat.card (centralizer ({g₁} : Set G)) := orderOf_dvd_card_centralizer hc
  have d21 : orderOf g₁ ∣ Nat.card (centralizer ({g₂} : Set G)) :=
    orderOf_dvd_card_centralizer hc.symm
  rw [h₂] at d12
  rw [h₁] at d21
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hrs
    | skip
  · exact ctx.not_commute_five_seven h₁ h₂ hc
  · have := d21.trans (ctx.facts.c11_odd ctx.odd h₂)
    revert this
    decide
  · have := d21.trans (dvd_of_eq (ctx.facts.c13 g₂ h₂))
    revert this
    decide
  · exact ctx.not_commute_five_seven h₂ h₁ hc.symm
  · have := d21.trans (ctx.facts.c11_odd ctx.odd h₂)
    revert this
    decide
  · have := d21.trans (dvd_of_eq (ctx.facts.c13 g₂ h₂))
    revert this
    decide
  · have := d12.trans (ctx.facts.c11_odd ctx.odd h₁)
    revert this
    decide
  · have := d12.trans (ctx.facts.c11_odd ctx.odd h₁)
    revert this
    decide
  · have := d21.trans (dvd_of_eq (ctx.facts.c13 g₂ h₂))
    revert this
    decide
  · have := d12.trans (dvd_of_eq (ctx.facts.c13 g₁ h₁))
    revert this
    decide
  · have := d12.trans (dvd_of_eq (ctx.facts.c13 g₁ h₁))
    revert this
    decide
  · have := d12.trans (dvd_of_eq (ctx.facts.c13 g₁ h₁))
    revert this
    decide

end Commuting

section Quotient

variable [Finite G] {F : Subgroup G} {a : ℕ}

open CFSG

omit [Finite G] in
theorem pCore_three_quotient [F.Normal] (ctx : CaseBCtx G F a)
    (hmax : ∀ K : Subgroup G, K.Normal → IsPGroup 3 K → K ≤ F) : pCore 3 (G ⧸ F) = ⊥ := by
  have hF3 : IsPGroup 3 F := IsPGroup.of_card ctx.card
  set K : Subgroup G := (pCore 3 (G ⧸ F)).comap (QuotientGroup.mk' F) with hK
  have hKn : K.Normal := Subgroup.Normal.comap pCore_normal _
  have hK3 : IsPGroup 3 K := by
    intro x
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := G ⧸ F)) ⟨QuotientGroup.mk' F x.1, x.2⟩
    have h1 : (x.1) ^ (3 ^ n) ∈ F := by
      rw [← QuotientGroup.eq_one_iff]
      have := congrArg Subtype.val hn
      simpa using this
    obtain ⟨m, hm⟩ := hF3 ⟨x.1 ^ (3 ^ n), h1⟩
    refine ⟨n + m, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hm
    simpa [pow_add, pow_mul] using this
  have hKF : K ≤ F := hmax K hKn hK3
  refine eq_bot_iff.2 fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : g ∈ K := hq
  have := hKF hg
  simpa using (QuotientGroup.eq_one_iff g).2 this

end Quotient

section Structure

variable [Finite G] {F : Subgroup G} {a : ℕ}

open CFSG

omit [Finite G] in
theorem prime_dvd_card_pCore {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (h : pCore p H ≠ ⊥) : p ∣ Nat.card (pCore p H) := by
  obtain ⟨j, hj⟩ := (pCore_isPGroup (p := p) (G := H)).exists_card_eq
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact h (Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero]))
  rw [hj]
  exact dvd_pow_self p hj0

omit [Finite G] in
theorem card_quotient_dvd (F : Subgroup G) : Nat.card (G ⧸ F) ∣ Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup F]
  exact dvd_mul_right _ _

theorem CaseBCtx.pCore_prime_cases [F.Normal] (ctx : CaseBCtx G F a)
    (hmax : ∀ K : Subgroup G, K.Normal → IsPGroup 3 K → K ≤ F) {s : ℕ} [Fact s.Prime]
    (hs : pCore s (G ⧸ F) ≠ ⊥) : s = 5 ∨ s = 7 ∨ s = 11 ∨ s = 13 := by
  have hsQ : s ∣ Nat.card (G ⧸ F) :=
    (prime_dvd_card_pCore hs).trans (Subgroup.card_subgroup_dvd_card _)
  have hsG : s ∣ Nat.card G := hsQ.trans (card_quotient_dvd F)
  have h3 : s ≠ 3 := by
    rintro rfl
    exact hs (pCore_three_quotient ctx hmax)
  rcases prime_dvd_cases (Fact.out) (hsG.trans ctx.dvd) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h3
  · simp
  · simp
  · simp
  · simp
  · exfalso
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 17 hsG
    exact ctx.not_order17 hg
  · exfalso
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 19 hsG
    exact ctx.not_order19 hg

theorem caseB_prime_structure [F.Normal] (ctx : CaseBCtx G F a) (hsolv : Group.IsSolvable G)
    (hmax : ∀ K : Subgroup G, K.Normal → IsPGroup 3 K → K ≤ F) {r : ℕ} [hrp : Fact r.Prime]
    (hr : r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 13) (hR : pCore r (G ⧸ F) ≠ ⊥) :
    ∃ k : ℕ, Odd k ∧ k ∣ r - 1 ∧ Nat.card G = 3 ^ a * (r * k) := by
  have hF3 : IsPGroup 3 F := IsPGroup.of_card ctx.card
  have hQsolv : Group.IsSolvable (G ⧸ F) := inferInstance
  have hno : ∀ s : ℕ, s.Prime → s ≠ r → pCore s (G ⧸ F) = ⊥ := by
    intro s hs hsr
    by_contra hsQ
    have : Fact s.Prime := ⟨hs⟩
    have hs' := ctx.pCore_prime_cases hmax hsQ
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := pCore r (G ⧸ F)) r
      (prime_dvd_card_pCore hR)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := pCore s (G ⧸ F)) s
      (prime_dvd_card_pCore hsQ)
    have hxo : orderOf (x : G ⧸ F) = r := by rw [Subgroup.orderOf_coe]; exact hx
    have hyo : orderOf (y : G ⧸ F) = s := by rw [Subgroup.orderOf_coe]; exact hy
    have hcomm : Commute (x : G ⧸ F) (y : G ⧸ F) :=
      Subgroup.commute_of_normal_of_disjoint _ _ pCore_normal pCore_normal
        (IsPGroup.disjoint_of_ne r s (Ne.symm hsr) _ _ pCore_isPGroup pCore_isPGroup)
        _ _ x.2 y.2
    have hcop : Nat.Coprime r s :=
      (Nat.coprime_primes (Fact.out) hs).2 (Ne.symm hsr)
    have hxy : orderOf ((x : G ⧸ F) * (y : G ⧸ F)) = r * s := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hxo, hyo]; exact hcop), hxo, hyo]
    obtain ⟨g, hg⟩ := exists_orderOf_eq_of_quotient F hF3 hxy
    have h₁ : orderOf (g ^ s) = r := by
      rw [orderOf_pow_of_dvd hs.ne_zero (hg ▸ dvd_mul_left s r), hg]
      exact Nat.mul_div_cancel r hs.pos
    have h₂ : orderOf (g ^ r) = s := by
      rw [orderOf_pow_of_dvd (Fact.out : r.Prime).ne_zero (hg ▸ dvd_mul_right r s), hg]
      exact Nat.mul_div_cancel_left s (Fact.out : r.Prime).pos
    exact ctx.not_commute hr hs' (Ne.symm hsr) h₁ h₂ ((Commute.refl g).pow_pow s r).eq
  have hfit : fittingSubgroup (G ⧸ F) = pCore r (G ⧸ F) := by
    apply le_antisymm
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun q => ?_
      by_cases hq : q.1.1 = r
      · rw [hq]
      · rw [hno q.1.1 (Nat.prime_of_mem_primeFactors q.1.2) hq]
        exact bot_le
    · exact pCore_le_fitting (G ⧸ F) r
  have hcent : centralizer (pCore r (G ⧸ F) : Set (G ⧸ F)) ≤ pCore r (G ⧸ F) := by
    rw [← hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hQsolv
  obtain ⟨j, hj⟩ := (pCore_isPGroup (p := r) (G := G ⧸ F)).exists_card_eq
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hR (Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero]))
  have hQG : Nat.card (G ⧸ F) ∣ Nat.card G := card_quotient_dvd F
  have hj1 : j = 1 := by
    by_contra hne
    have hj2 : 2 ≤ j := by omega
    have hdvd : r ^ 2 ∣ Nat.card G :=
      ((pow_dvd_pow r hj2).trans (hj ▸ Subgroup.card_subgroup_dvd_card _)).trans hQG
    rcases hr with rfl | rfl | rfl | rfl
    · exact ctx.not_dvd_sq5 hdvd
    · exact ctx.not_dvd_sq7 hdvd
    · have := hdvd.trans ctx.dvd
      revert this
      decide
    · have := hdvd.trans ctx.dvd
      revert this
      decide
  subst hj1
  rw [pow_one] at hj
  have hcyc : IsCyclic (pCore r (G ⧸ F)) := isCyclic_of_prime_card hj
  obtain ⟨k, hk, hkt⟩ := exists_card_eq_mul_dvd_totient (pCore r (G ⧸ F)) ⊤
    (by rw [Subgroup.normalizer_eq_top])
  have hcab : IsMulCommutative (pCore r (G ⧸ F)) := inferInstance
  have hCeq : centralizer (pCore r (G ⧸ F) : Set (G ⧸ F)) = pCore r (G ⧸ F) :=
    le_antisymm hcent (Subgroup.le_centralizer_iff_isMulCommutative.2 hcab)
  rw [top_inf_eq, hCeq, Subgroup.card_top, hj] at hk
  rw [hj, Nat.totient_prime (Fact.out)] at hkt
  have hGQ : Nat.card G = Nat.card (G ⧸ F) * Nat.card F :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup F
  refine ⟨k, ?_, hkt, ?_⟩
  · have hkQ : k ∣ Nat.card (G ⧸ F) := hk ▸ dvd_mul_left k r
    exact ctx.odd.of_dvd_nat (hkQ.trans hQG)
  · rw [hGQ, hk, ctx.card, mul_comm]

end Structure

section Shape

@[expose] def CaseBShape (n a : ℕ) : Prop :=
  n = 3 ^ a ∨
  (n = 3 ^ a * 5 ∧ (a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9)) ∨
  (∃ k, (k = 1 ∨ k = 3) ∧ n = 3 ^ a * 7 * k ∧ (a = 6 ∨ a = 7 ∨ a = 8)) ∨
  (∃ k, (k = 1 ∨ k = 5) ∧ n = 3 ^ a * 11 * k ∧ (a = 5 ∨ a = 6)) ∨
  (∃ k, (k = 1 ∨ k = 3) ∧ n = 3 ^ a * 13 * k ∧ (a = 3 ∨ a = 6 ∨ a = 9))

variable [Finite G] {F : Subgroup G} {a : ℕ}

open CFSG

theorem caseB_shape [F.Normal] (ctx : CaseBCtx G F a) (hsolv : Group.IsSolvable G)
    (hmax : ∀ K : Subgroup G, K.Normal → IsPGroup 3 K → K ≤ F) :
    CaseBShape (Nat.card G) a := by
  by_cases hFtop : F = ⊤
  · left
    rw [← ctx.card, ← Subgroup.card_top (G := G), hFtop]
  right
  have hQsolv : Group.IsSolvable (G ⧸ F) := inferInstance
  have hfit : fittingSubgroup (G ⧸ F) ≠ ⊥ := fun h =>
    hFtop (QuotientGroup.subsingleton_iff.1
      (Nat.card_eq_one_iff_unique.1
        ((fitting_eq_bot_iff_card_eq_one_of_solvable (G ⧸ F)).1 h)).1)
  rw [fitting_eq_sup_pCore] at hfit
  obtain ⟨q, hq⟩ : ∃ q : (Nat.card (G ⧸ F)).primeFactors.attach, pCore q.1.1 (G ⧸ F) ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hfit (iSup_eq_bot.2 h)
  obtain ⟨r, hrp, hRne⟩ : ∃ r : ℕ, r.Prime ∧ pCore r (G ⧸ F) ≠ ⊥ :=
    ⟨q.1.1, Nat.prime_of_mem_primeFactors q.1.2, hq⟩
  have : Fact r.Prime := ⟨hrp⟩
  have hr := ctx.pCore_prime_cases hmax hRne
  obtain ⟨k, hkodd, hkd, hG⟩ := caseB_prime_structure ctx hsolv hmax hr hRne
  have hdvd : r ∣ Nat.card G := by
    rw [hG]
    exact ⟨3 ^ a * k, by ring⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) r hdvd
  rcases hr with rfl | rfl | rfl | rfl
  · have hk1 : k = 1 := by
      have hb : ∀ d ∈ Nat.divisors 4, Odd d → d = 1 := by decide
      exact hb k (Nat.mem_divisors.2 ⟨hkd, by norm_num⟩) hkodd
    subst hk1
    exact Or.inl ⟨by rw [hG], ctx.feasible5 hg⟩
  · have hb : ∀ d ∈ Nat.divisors 6, Odd d → d = 1 ∨ d = 3 := by decide
    exact Or.inr (Or.inl ⟨k, hb k (Nat.mem_divisors.2 ⟨hkd, by norm_num⟩) hkodd,
      by rw [hG, mul_assoc], ctx.feasible7 hg⟩)
  · have hb : ∀ d ∈ Nat.divisors 10, Odd d → d = 1 ∨ d = 5 := by decide
    exact Or.inr (Or.inr (Or.inl ⟨k, hb k (Nat.mem_divisors.2 ⟨hkd, by norm_num⟩) hkodd,
      by rw [hG, mul_assoc], ctx.feasible11 hg⟩))
  · have hb : ∀ d ∈ Nat.divisors 12, Odd d → d = 1 ∨ d = 3 := by decide
    exact Or.inr (Or.inr (Or.inr ⟨k, hb k (Nat.mem_divisors.2 ⟨hkd, by norm_num⟩) hkodd,
      by rw [hG, mul_assoc], ctx.feasible13 hg⟩))

end Shape

section Setup

variable [Finite G]

open CFSG

theorem caseB_ctx (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (hdvd : Nat.card G ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19) (hC : CentralizerFacts G)
    (hnot : ∀ r : ℕ, r.Prime → r ≠ 3 → pCore r G = ⊥) :
    ∃ a, CaseBCtx G (pCore 3 G) a ∧
      ∀ K : Subgroup G, K.Normal → IsPGroup 3 K → K ≤ pCore 3 G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, haF⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have hfit : fittingSubgroup G = pCore 3 G := by
    apply le_antisymm
    · rw [fitting_eq_sup_pCore]
      refine iSup_le fun q => ?_
      by_cases hq : q.1.1 = 3
      · rw [hq]
      · rw [hnot q.1.1 (Nat.prime_of_mem_primeFactors q.1.2) hq]
        exact bot_le
    · exact pCore_le_fitting G 3
  refine ⟨a, ⟨pCore_normal, haF, ?_, ?_, hodd, hdvd, hC⟩, fun K hK h3 => le_sSup ⟨hK, h3⟩⟩
  · have h1 : 3 ^ a ∣ 3 ^ 9 * (5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19) := by
      have := (haF ▸ Subgroup.card_subgroup_dvd_card (pCore 3 G)).trans hdvd
      simpa only [mul_assoc] using this
    exact le_of_pow_dvd_mul (m := 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19) (by norm_num) h1
  · rw [← hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv

end Setup

section E4

open scoped commutatorElement

private theorem pow3_mod11 (k : ℕ) : 3 ^ k ≡ 3 ^ (k % 5) [MOD 11] := by
  conv_lhs => rw [← Nat.div_add_mod k 5, pow_add, pow_mul]
  have h5 : 3 ^ 5 ≡ 1 [MOD 11] := by decide
  calc (3 ^ 5) ^ (k / 5) * 3 ^ (k % 5) ≡ 1 ^ (k / 5) * 3 ^ (k % 5) [MOD 11] :=
        (h5.pow _).mul_right _
    _ = 3 ^ (k % 5) := by rw [one_pow, one_mul]

private theorem mod5_eq_of_modEq {k e : ℕ} (he : e ≤ 1) (h : 3 ^ k ≡ 3 ^ e [MOD 11]) :
    k % 5 = e := by
  have h1 : 3 ^ (k % 5) ≡ 3 ^ e [MOD 11] := (pow3_mod11 k).symm.trans h
  have hk : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize k % 5 = j at h1 hk ⊢
  interval_cases e <;> interval_cases j <;> simp_all [Nat.ModEq]

@[expose] def powKer (A : Subgroup G) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (n : ℕ) :
    Subgroup G where
  carrier := {x | x ∈ A ∧ x ^ n = 1}
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    refine ⟨A.mul_mem hx hy, ?_⟩
    rw [Commute.mul_pow (show Commute x y from hA x hx y hy), hx1, hy1, mul_one]
  one_mem' := ⟨A.one_mem, one_pow n⟩
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    exact ⟨A.inv_mem hx, by rw [inv_pow, hx1, inv_one]⟩

theorem mem_powKer {A : Subgroup G} {hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {n : ℕ} {x : G} :
    x ∈ powKer A hA n ↔ x ∈ A ∧ x ^ n = 1 := Iff.rfl

theorem powKer_le (A : Subgroup G) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (n : ℕ) :
    powKer A hA n ≤ A := fun _ hx => hx.1

theorem mem_normalizer_powKer {A : Subgroup G} {hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {n : ℕ}
    {g : G} (hg : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer ((powKer A hA n : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_powKer, mem_powKer, (Subgroup.mem_normalizer_iff.1 hg) x]
  have : (g * x * g⁻¹) ^ n = g * x ^ n * g⁻¹ := conj_pow
  rw [this]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; group⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := congrArg (fun y => g⁻¹ * y * g) h2
    simpa [mul_assoc] using this

section E4Group

variable [Finite G] {F : Subgroup G} {a : ℕ}

theorem fact_one {g : G} (hg : orderOf g = 11) {c : ℕ} (F : Subgroup G)
    (hc : Nat.card ↥(F ⊓ centralizer ({g} : Set G)) = 3 ^ c) (hc1 : c ≤ 1)
    {K : Subgroup G} (hKF : K ≤ F) (hgK : g ∈ normalizer (K : Set G)) {k : ℕ}
    (hK : Nat.card K = 3 ^ k) : k % 5 ≤ c := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hmod := card_modEq_zpowers hg hgK
  obtain ⟨e, -, he⟩ := exists_card_pow_of_le hK (inf_le_left : K ⊓ centralizer ({g} : Set G) ≤ K)
  have hec : e ≤ c := by
    have := Subgroup.card_dvd_of_le (inf_le_inf hKF (le_refl (centralizer ({g} : Set G))))
    rw [he, hc] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  rw [hK, he] at hmod
  have := mod5_eq_of_modEq (by omega : e ≤ 1) hmod
  omega

theorem CaseBCtx.e4_abelian (ctx : CaseBCtx G F a) (hT : ThreeLocalFacts G) (ha : a = 5 ∨ a = 6)
    {g : G} (hg : orderOf g = 11) {c : ℕ}
    (hc : Nat.card ↥(F ⊓ centralizer ({g} : Set G)) = 3 ^ c) (hc1 : c ≤ 1)
    (hca : a % 5 = c) (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) : False := by
  have hgF : g ∈ normalizer (F : Set G) := by
    have := ctx.normal
    exact mem_normalizer_of_normal g
  set X : Subgroup G := powKer F hcomm 3 with hXdef
  set Y : Subgroup G := powKer F hcomm 9 with hYdef
  have hX : g ∈ normalizer (X : Set G) := mem_normalizer_powKer hgF
  have hY : g ∈ normalizer (Y : Set G) := mem_normalizer_powKer hgF
  have hXF : X ≤ F := powKer_le F hcomm 3
  have hYF : Y ≤ F := powKer_le F hcomm 9
  obtain ⟨w, hwa, hXw⟩ := exists_card_pow_of_le ctx.card hXF
  have hw5 : w % 5 ≤ c := fact_one hg F hc hc1 hXF hX hXw
  have h3F : 3 ∣ Nat.card F := by
    rw [ctx.card]
    exact dvd_pow_self 3 (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := F) 3 h3F
  have hyo : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyX : (y : G) ∈ X := ⟨y.2, by rw [← hyo]; exact pow_orderOf_eq_one _⟩
  have hw1 : 1 ≤ w := by
    by_contra h0
    have h0' : w = 0 := by omega
    have hbot : X = ⊥ := Subgroup.eq_bot_of_card_eq X (by rw [hXw, h0', pow_zero])
    have : (y : G) = 1 := by
      have := hyX
      rw [hbot] at this
      simpa using this
    rw [this, orderOf_one] at hyo
    omega
  have helem : ∀ K : Subgroup G, K ≤ F → (∀ x ∈ K, x ^ 3 = 1) → g ∈ normalizer (K : Set G) →
      ∀ k, Nat.card K = 3 ^ k → k = 5 → False := by
    intro K hKF hK3 hgK k hKk hk5
    refine hT.elem11 K hK3 (fun x hx y hy => hcomm x (hKF hx) y (hKF hy)) (by rw [hKk, hk5])
      g hgK hg
  rcases ha with rfl | rfl
  ·
    have hc0 : c = 0 := by omega
    have hw : w = 5 := by omega
    subst hw
    exact helem X hXF (fun x hx => hx.2) hX 5 hXw rfl
  ·
    have hc1' : c = 1 := by omega
    have hw' : w = 1 ∨ w = 5 ∨ w = 6 := by omega
    rcases hw' with rfl | rfl | rfl
    ·
      have hXY : X ≤ Y := fun x hx =>
        ⟨hx.1, by rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hx.2, one_pow]⟩
      obtain ⟨v, hvle, hYv⟩ := exists_card_pow_of_le ctx.card hYF
      have hv5 : v % 5 ≤ c := fact_one hg F hc hc1 hYF hY hYv
      have hv1 : 1 ≤ v := by
        have := Subgroup.card_dvd_of_le hXY
        rw [hXw, hYv] at this
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
      let ψ : Y →* X :=
        { toFun := fun x => ⟨(x : G) ^ 3, F.pow_mem (hYF x.2) 3, by
            rw [← pow_mul]
            exact x.2.2⟩
          map_one' := Subtype.ext (one_pow 3)
          map_mul' := fun x y => Subtype.ext
            ((Commute.mul_pow (hcomm _ (hYF x.2) _ (hYF y.2))) 3) }
      have hkr : Nat.card ψ.ker ≤ Nat.card X := by
        have hle : ψ.ker.map Y.subtype ≤ X := by
          rintro _ ⟨k, hk, rfl⟩
          refine ⟨hYF k.2, ?_⟩
          have h1 : ((ψ k : X) : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
          exact h1
        calc Nat.card ψ.ker = Nat.card (ψ.ker.map Y.subtype) :=
              (Subgroup.card_map_of_injective Y.subtype_injective).symm
          _ ≤ Nat.card X := Subgroup.card_le_of_le hle
      have hrg : Nat.card ψ.range ≤ Nat.card X := Subgroup.card_le_card_group ψ.range
      have hY9 : Nat.card Y ≤ Nat.card X * Nat.card X := by
        rw [← Subgroup.card_ker_mul_card_range ψ]
        exact Nat.mul_le_mul hkr hrg
      rw [hYv, hXw, ← pow_add] at hY9
      have hv2 : v ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hY9
      have hv1' : v = 1 := by omega
      have hYX : X = Y := Subgroup.eq_of_le_of_card_ge hXY (by rw [hYv, hXw, hv1'])
      have hall : ∀ n : ℕ, ∀ x ∈ F, x ^ (3 ^ (n + 1)) = 1 → x ^ 3 = 1 := by
        intro n
        induction n with
        | zero =>
          intro x _ h
          simpa using h
        | succ n ih =>
          intro x hx h
          have h1 : (x ^ 3) ^ (3 ^ (n + 1)) = 1 := by
            rw [← pow_mul, ← pow_succ']
            exact h
          have h2 := ih (x ^ 3) (F.pow_mem hx 3) h1
          have hx9 : x ∈ Y := ⟨hx, by rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul]; exact h2⟩
          rw [← hYX] at hx9
          exact hx9.2
      have hFX : F ≤ X := fun x hx => by
        refine ⟨hx, hall 5 x hx ?_⟩
        have := congrArg Subtype.val (pow_card_eq_one' (G := F) (x := ⟨x, hx⟩))
        rw [ctx.card] at this
        simpa using this
      have hXeq : X = F := le_antisymm hXF hFX
      rw [hXeq, ctx.card] at hXw
      have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hXw
      omega
    · exact helem X hXF (fun x hx => hx.2) hX 5 hXw rfl
    ·
      have hXeq : X = F := Subgroup.eq_of_le_of_card_ge hXF (by rw [hXw, ctx.card])
      have := hT.rank3 F (fun x hx => by rw [← hXeq] at hx; exact hx.2)
        (fun x hx y hy => hcomm x hx y hy)
      rw [ctx.card] at this
      norm_num at this

omit [Finite G] in
theorem mem_normalizer_map_characteristic {g : G} (hg : g ∈ normalizer (F : Set G))
    (K : Subgroup F) [K.Characteristic] :
    g ∈ normalizer ((K.map F.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hF := Subgroup.mem_normalizer_iff.1 hg x
  let φ : MulAut F := F.normalizerMonoidHom ⟨g, hg⟩
  have hφ : ∀ y : F, ((φ y : F) : G) = g * y * g⁻¹ := fun y => rfl
  have hK : ∀ y : F, φ y ∈ K ↔ y ∈ K := by
    intro y
    have h1 := Subgroup.Characteristic.fixed ‹K.Characteristic› φ
    have h2 : y ∈ K.comap φ.toMonoidHom ↔ y ∈ K := by rw [h1]
    rw [Subgroup.mem_comap] at h2
    exact h2
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨φ k, (hK k).2 hk, hφ k⟩
  · rintro ⟨k', hk', hx⟩
    have hxF : x ∈ F := hF.2 (hx ▸ k'.2)
    refine ⟨⟨x, hxF⟩, ?_, rfl⟩
    have : φ ⟨x, hxF⟩ = k' := Subtype.ext (by rw [hφ]; exact hx.symm)
    have h3 : φ ⟨x, hxF⟩ ∈ K := by
      rw [this]
      exact hk'
    exact (hK _).1 h3

theorem eq_inf_centralizer_of_card_three {g : G} (hg : orderOf g = 11) {F K : Subgroup G}
    (hc : Nat.card ↥(F ⊓ centralizer ({g} : Set G)) = 3) (hKF : K ≤ F)
    (hgK : g ∈ normalizer (K : Set G)) (hK : Nat.card K = 3) :
    K = F ⊓ centralizer ({g} : Set G) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hmod := card_modEq_zpowers hg hgK
  have hdvd : Nat.card ↥(K ⊓ centralizer ({g} : Set G)) ∣ 3 :=
    hK ▸ Subgroup.card_dvd_of_le inf_le_left
  rw [hK] at hmod
  have h3 : Nat.card ↥(K ⊓ centralizer ({g} : Set G)) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · rw [h] at hmod
      exact absurd hmod (by decide)
    · exact h
  have hKC : K ⊓ centralizer ({g} : Set G) = K :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hK])
  have hle : K ≤ F ⊓ centralizer ({g} : Set G) :=
    le_inf hKF (by rw [← hKC]; exact inf_le_right)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hK])

theorem card_eq_pow_one_add_two_mul_of_pow_mem {D : Type*} [Group D] [Finite D] {r : ℕ}
    [Fact r.Prime] (hD : ∀ x : D, x ^ r ∈ commutator D) (hZ : center D = commutator D)
    (hc : Nat.card (center D) = r) : ∃ a : ℕ, Nat.card D = r ^ (1 + 2 * a) := by
  obtain ⟨ε⟩ := OddSolvableUnitary.nonempty_center_mulEquiv hc
  have hkill : ∀ v : Additive (Abelianization D), r • v = 0 := by
    intro v
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
    induction u using QuotientGroup.induction_on with
    | H x =>
      change r • Additive.ofMul (Abelianization.of x) = 0
      rw [← ofMul_pow, ← map_pow]
      have : Abelianization.of (x ^ r) = 1 := by
        rw [← MonoidHom.mem_ker, Abelianization.ker_of]
        exact hD x
      rw [this]
      rfl
  have := AddCommGroup.zmodModule hkill
  obtain ⟨B, hBa, hBn, -⟩ := OddSolvableUnitary.exists_commForm hZ ε
  have : Finite (Additive (Abelianization D)) :=
    Finite.of_surjective (fun x : D => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod r) (Additive (Abelianization D)) := Module.Finite.of_finite
  obtain ⟨a, ha⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod r) hBa hBn
  refine ⟨a, ?_⟩
  have h1 : Nat.card (Abelianization D) = r ^ (2 * a) := by
    change Nat.card (Additive (Abelianization D)) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod, ha, two_mul]
  rw [OddSolvableUnitary.card_eq_card_abelianization_mul hZ hc, h1, pow_add, pow_one, mul_comm]

theorem CaseBCtx.e4_nonabelian (ctx : CaseBCtx G F a) (ha : a = 5 ∨ a = 6)
    {g : G} (hg : orderOf g = 11) {c : ℕ}
    (hc : Nat.card ↥(F ⊓ centralizer ({g} : Set G)) = 3 ^ c) (hc1 : c ≤ 1) (hca : a % 5 = c)
    (hnc : ¬ ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) : False := by
  have hnormal := ctx.normal
  have hgF : g ∈ normalizer (F : Set G) := mem_normalizer_of_normal g
  have hF3 : IsPGroup 3 F := IsPGroup.of_card ctx.card
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 F) := ⟨hF3⟩
  have hnc' : ¬ IsMulCommutative F := fun h =>
    hnc (fun x hx y hy => congrArg Subtype.val (h.is_comm.comm (⟨x, hx⟩ : F) ⟨y, hy⟩))
  have hFnt : Nontrivial F := by
    rw [← Finite.one_lt_card_iff_nontrivial, ctx.card]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hZG := mem_normalizer_map_characteristic hgF (Subgroup.center F)
  have hZle : (Subgroup.center F).map F.subtype ≤ F := Subgroup.map_subtype_le _
  obtain ⟨z, hza, hZ⟩ := exists_card_pow_of_le ctx.card hZle
  rw [card_map_subtype_eq] at hZ
  have hz5 : z % 5 ≤ c := by
    refine fact_one hg F hc hc1 hZle hZG ?_
    rw [card_map_subtype_eq]
    exact hZ
  have hz1 : 1 ≤ z := by
    have : Nontrivial (Subgroup.center F) := IsPGroup.center_nontrivial hF3
    have h2 : 1 < Nat.card (Subgroup.center F) := Finite.one_lt_card_iff_nontrivial.2 this
    rw [hZ] at h2
    by_contra h0
    have : z = 0 := by omega
    rw [this] at h2
    norm_num at h2
  have hzne : z ≠ a := by
    intro hza'
    apply hnc'
    have htop : Subgroup.center F = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hZ, hza', ctx.card])
    refine ⟨⟨fun x y => ?_⟩⟩
    have : y ∈ Subgroup.center F := by rw [htop]; exact Subgroup.mem_top y
    exact Subgroup.mem_center_iff.1 this x
  have ha6 : a = 6 := by
    rcases ha with rfl | rfl
    · exfalso
      omega
    · rfl
  subst ha6
  have hc6 : c = 1 := by omega
  subst hc6
  have hz_one : z = 1 := by
    by_contra hz1'
    have hz5' : z = 5 := by omega
    have hq : Nat.card (F ⧸ Subgroup.center F) = 3 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center F)
      rw [ctx.card, hZ, hz5'] at h
      omega
    have : IsCyclic (F ⧸ Subgroup.center F) := isCyclic_of_prime_card hq
    exact hnc' (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center F)) (by simp))
  subst hz_one
  have hΦne : frattini F ≠ ⊤ := fun htop =>
    bot_ne_top (frattini_nongenerating (K := (⊥ : Subgroup F)) (by rw [htop]; exact sup_top_eq _))
  have hΦG := mem_normalizer_map_characteristic hgF (frattini F)
  have hΦle : (frattini F).map F.subtype ≤ F := Subgroup.map_subtype_le _
  obtain ⟨φ, hφa, hΦ⟩ := exists_card_pow_of_le ctx.card hΦle
  rw [card_map_subtype_eq] at hΦ
  have hφ5 : φ % 5 ≤ 1 := by
    refine fact_one hg F hc hc1 hΦle hΦG ?_
    rw [card_map_subtype_eq]
    exact hΦ
  have hφne : φ ≠ 6 := by
    intro h6
    exact hΦne (Subgroup.eq_top_of_card_eq _ (by rw [hΦ, h6, ctx.card]))
  have hφ1 : φ = 1 := by
    have : φ = 0 ∨ φ = 1 ∨ φ = 5 := by omega
    rcases this with h0 | h1 | h5
    · exfalso
      have hbot : frattini F = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hΦ, h0, pow_zero])
      exact hnc' ((frattini_eq_bot_iff_isElementaryAbelian (p := 3)).1 hbot).toIsMulCommutative
    · exact h1
    · exfalso
      obtain ⟨x, hx⟩ : ∃ x : F, x ∉ frattini F := by
        by_contra hall
        push Not at hall
        exact hΦne (eq_top_iff.2 fun y _ => hall y)
      have hT : zpowers x ⊔ frattini F = ⊤ := by
        set T := zpowers x ⊔ frattini F with hTdef
        have hΦT : frattini F ≤ T := le_sup_right
        have hxT : x ∈ T := (le_sup_left : zpowers x ≤ T) (Subgroup.mem_zpowers x)
        obtain ⟨t, ht6, hTt⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
          ((Subgroup.card_subgroup_dvd_card T).trans (dvd_of_eq ctx.card))
        have h5t : 5 ≤ t := by
          have := Subgroup.card_dvd_of_le hΦT
          rw [hΦ, h5, hTt] at this
          exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
        by_cases ht : t = 5
        · exfalso
          have hΦeq : frattini F = T :=
            Subgroup.eq_of_le_of_card_ge hΦT (by rw [hΦ, hTt, h5, ht])
          exact hx (hΦeq ▸ hxT)
        · have ht6' : t = 6 := by omega
          exact Subgroup.eq_top_of_card_eq T (by rw [hTt, ht6', ctx.card])
      have hcyc : IsCyclic F := isCyclic_iff_exists_zpowers_eq_top.2 ⟨x, frattini_nongenerating hT⟩
      exact hnc' hcyc.isMulCommutative
  subst hφ1
  have hF'le : _root_.commutator F ≤ frattini F :=
    CFSG.commutator_le_frattini_of_isPGroup (R := F) (p := 3)
  have hF'ne : _root_.commutator F ≠ ⊥ := by
    intro hbot
    apply hnc'
    refine ⟨⟨fun x y => ?_⟩⟩
    have h1 : ⁅x, y⁆ ∈ _root_.commutator F := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hbot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 (by simpa using h1)
  have hF'Φ : _root_.commutator F = frattini F := by
    have hdvd : Nat.card (_root_.commutator F) ∣ 3 := by
      have := Subgroup.card_dvd_of_le hF'le
      rwa [hΦ, pow_one] at this
    have hne1 : Nat.card (_root_.commutator F) ≠ 1 := fun h =>
      hF'ne (Subgroup.eq_bot_of_card_eq _ h)
    have h3 : Nat.card (_root_.commutator F) = 3 :=
      ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left hne1
    exact Subgroup.eq_of_le_of_card_ge hF'le (by rw [h3, hΦ, pow_one])
  have hc3 : Nat.card ↥(F ⊓ centralizer ({g} : Set G)) = 3 := by rw [hc, pow_one]
  have hZΦ : Subgroup.center F = frattini F := by
    have e1 := eq_inf_centralizer_of_card_three hg hc3 hZle hZG
      (by rw [card_map_subtype_eq, hZ, pow_one])
    have e2 := eq_inf_centralizer_of_card_three hg hc3 hΦle hΦG
      (by rw [card_map_subtype_eq, hΦ, pow_one])
    exact Subgroup.map_injective F.subtype_injective (e1.trans e2.symm)
  obtain ⟨a', ha'⟩ := card_eq_pow_one_add_two_mul_of_pow_mem (D := F) (r := 3)
    (fun x => hF'Φ ▸ CFSG.pth_power_mem_frattini_of_isPGroup (p := 3) x)
    (hZΦ.trans hF'Φ.symm) (by rw [hZ, pow_one])
  rw [ctx.card] at ha'
  have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) ha'
  omega

theorem CaseBCtx.e4_false (ctx : CaseBCtx G F a) (hT : ThreeLocalFacts G) (ha : a = 5 ∨ a = 6)
    {g : G} (hg : orderOf g = 11) : False := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hn := ctx.normal
  obtain ⟨c, hca, hc, hmod⟩ := ctx.exists_fixed_card (p := 11) (by norm_num) hg
  have hc1 : c ≤ 1 := ctx.c11 g hg c (hc ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hac : a % 5 = c := mod5_eq_of_modEq hc1 hmod
  by_cases hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  · exact ctx.e4_abelian hT ha hg hc hc1 hac hcomm
  · exact ctx.e4_nonabelian ha hg hc hc1 hac hcomm

end E4Group

end E4

end CFSG.Monster.Existence.StdOdd
