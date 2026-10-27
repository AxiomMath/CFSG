module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec16.KS1619SecProof

open Finset

section Algebra

variable {M : Type*} [Ring M]

def xp (x : M) (i : ZMod 13) : M := x ^ i.val

theorem xp_add {x : M} (hx : x ^ 13 = 1) (i j : ZMod 13) :
    xp x (i + j) = xp x i * xp x j := by
  unfold xp
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ hx]

theorem xp_zero (x : M) : xp x 0 = 1 := by simp [xp]

theorem xp_one (x : M) : xp x 1 = x := by
  unfold xp
  rw [show (1 : ZMod 13).val = 1 from rfl, pow_one]

theorem mul_pow_eq {c x : M} {r : ℕ} (hcx : c * x = x ^ r * c) (n : ℕ) :
    c * x ^ n = x ^ (r * n) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, hcx, ← mul_assoc, ← pow_add,
      show r * n + r = r * (n + 1) by ring]

theorem mul_xp {c x : M} (hx : x ^ 13 = 1) (hcx : c * x = x ^ 3 * c) (k : ZMod 13) :
    c * xp x k = xp x (3 * k) * c := by
  unfold xp
  rw [mul_pow_eq hcx, ZMod.val_mul, ← pow_eq_pow_mod _ hx]
  rfl

theorem sq_mul_xp {c x : M} (hx : x ^ 13 = 1) (hcx : c * x = x ^ 3 * c) (k : ZMod 13) :
    c ^ 2 * xp x k = xp x (9 * k) * c ^ 2 := by
  rw [sq, mul_assoc, mul_xp hx hcx, ← mul_assoc, mul_xp hx hcx, mul_assoc, ← mul_assoc 3]
  rfl

def mulEquiv13 (a b : ZMod 13) (h : a * b = 1) : ZMod 13 ≃ ZMod 13 where
  toFun k := a * k
  invFun k := b * k
  left_inv k := by
    change b * (a * k) = k
    rw [← mul_assoc, mul_comm b a, h, one_mul]
  right_inv k := by
    change a * (b * k) = k
    rw [← mul_assoc, h, one_mul]

theorem sum_xp_mul (x : M) (a b : ZMod 13) (h : a * b = 1) :
    ∑ k : ZMod 13, xp x (a * k) = ∑ k : ZMod 13, xp x k :=
  Fintype.sum_equiv (mulEquiv13 a b h) _ _ fun _ => rfl

end Algebra

section GroupAlgebra

variable {M : Type*} [Ring M] [Algebra (ZMod 2) M]

def rz (x : M) (f : ZMod 13 → ZMod 2) : M := ∑ k, f k • xp x k

def cv (f g : ZMod 13 → ZMod 2) : ZMod 13 → ZMod 2 := fun k => ∑ i, f i * g (k - i)

def dl (j : ZMod 13) : ZMod 13 → ZMod 2 := fun k => if k = j then 1 else 0

def e13 : ZMod 13 → ZMod 2 := fun _ => 1

def u0 : ZMod 13 → ZMod 2 := fun k => if k = 0 ∨ k = 1 ∨ k = 3 ∨ k = 9 then 1 else 0

theorem rz_mul {x : M} (hx : x ^ 13 = 1) (f g : ZMod 13 → ZMod 2) :
    rz x f * rz x g = rz x (cv f g) := by
  unfold rz cv
  rw [Finset.sum_mul_sum]
  simp_rw [smul_mul_smul_comm, ← xp_add hx, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun j => by simp)

theorem rz_add (x : M) (f g : ZMod 13 → ZMod 2) : rz x f + rz x g = rz x (f + g) := by
  unfold rz
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.add_apply, add_smul]

theorem rz_dl (x : M) (j : ZMod 13) : rz x (dl j) = xp x j := by
  unfold rz dl
  simp [ite_smul]

theorem rz_zero (x : M) : rz x 0 = 0 := by
  simp [rz]

theorem rz_e13 (x : M) : rz x e13 = ∑ k : ZMod 13, xp x k := by
  simp [rz, e13]

theorem mul_rz {c x : M} (hx : x ^ 13 = 1) (hcx : c * x = x ^ 3 * c) (f : ZMod 13 → ZMod 2) :
    c * rz x f = rz x (fun m => f (9 * m)) * c := by
  unfold rz
  rw [Finset.mul_sum, Finset.sum_mul]
  have h : ∀ k, c * (f k • xp x k) = f k • xp x (3 * k) * c := fun k => by
    rw [mul_smul_comm, mul_xp hx hcx, smul_mul_assoc]
  simp_rw [h]
  refine Fintype.sum_equiv (mulEquiv13 3 9 (by decide)) _ _ fun k => ?_
  have h93 : 9 * (3 * k) = k := by
    rw [← mul_assoc]
    exact (by decide : ∀ k : ZMod 13, (9 * 3 : ZMod 13) * k = k) k
  change f k • xp x (3 * k) * c = f (9 * (3 * k)) • xp x (3 * k) * c
  rw [h93]

theorem thirteen_eq_one : (13 : M) = 1 := by
  have h := map_ofNat (algebraMap (ZMod 2) M) 13
  rw [← h, show (13 : ZMod 2) = 1 from rfl, map_one]

theorem sum_xp_trace {c x : M} (hx : x ^ 13 = 1) (hcx : c * x = x ^ 3 * c) :
    ∑ k : ZMod 13, xp x k * (1 + c + c ^ 2) * xp x (-k) =
      1 + rz x e13 * c + rz x e13 * c ^ 2 := by
  have h1 : ∀ k : ZMod 13, xp x k * (1 + c + c ^ 2) * xp x (-k) =
      1 + xp x (11 * k) * c + xp x (5 * k) * c ^ 2 := by
    intro k
    rw [mul_add, mul_add, add_mul, add_mul, mul_one, mul_assoc (xp x k) c, mul_xp hx hcx,
      mul_assoc (xp x k) (c ^ 2), sq_mul_xp hx hcx, ← mul_assoc, ← mul_assoc, ← xp_add hx,
      ← xp_add hx, ← xp_add hx, add_neg_cancel, xp_zero,
      (by decide : ∀ k : ZMod 13, k + 3 * -k = 11 * k) k,
      (by decide : ∀ k : ZMod 13, k + 9 * -k = 5 * k) k]
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    sum_xp_mul x 11 6 (by decide), sum_xp_mul x 5 8 (by decide), ← rz_e13,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_ofNat,
    thirteen_eq_one]

end GroupAlgebra

theorem cv_dl_one_e13 : cv (dl 1) e13 = e13 := by decide

theorem cv_e13_e13 : cv e13 e13 = e13 := by decide

theorem cv_e13_dl : ∀ j : ZMod 13, cv e13 (dl j) = e13 := by decide

theorem u0_nine_mul : ∀ m : ZMod 13, u0 (9 * m) = u0 m := by decide

theorem cv_e13_u0 : cv e13 u0 = 0 := by decide

theorem phi5_u0 : dl 0 + u0 + cv u0 u0 + cv (cv u0 u0) u0 + cv (cv (cv u0 u0) u0) u0 = e13 := by
  decide

theorem four_le_of_two_pow_modEq {d : ℕ} (h2 : 2 ≤ 2 ^ d) (h5 : 2 ^ d ≡ 1 [MOD 5]) : 4 ≤ d := by
  by_contra hlt
  push Not at hlt
  interval_cases d <;> simp_all [Nat.ModEq]

theorem card_modEq_one_of_perm {W : Type*} [Finite W] (σ : Equiv.Perm W) (hσ : σ ^ 5 = 1)
    (w₀ : W) (hfix : ∀ y, σ y = y ↔ y = w₀) : Nat.card W ≡ 1 [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp : IsPGroup 5 (Subgroup.zpowers σ) := by
    have hdvd : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one hσ
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hmod := hp.card_modEq_card_fixedPoints W
  have hfix1 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) W) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨w₀, fun g => ?_⟩, fun y => ?_⟩
    · obtain ⟨g, hg⟩ := g
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      change (σ ^ n) w₀ = w₀
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self ((hfix w₀).mpr rfl) n
    · obtain ⟨y, hy⟩ := y
      have h1 : σ y = y := hy ⟨σ, Subgroup.mem_zpowers σ⟩
      exact Subtype.ext ((hfix y).mp h1)
  rwa [hfix1] at hmod

section Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem five_nsmul (v : V) : (5 : ℕ) • v = v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), show ((5 : ℕ) : ZMod 2) = 1 from rfl, one_smul]

theorem exists_fixed_ker_ne_zero {x c : Module.End (ZMod 2) V} (hx : x ^ 13 = 1)
    (hc : c ^ 3 = 1) (hcx : c * x = x ^ 3 * c) (hx1 : x ≠ 1) :
    ∃ w : V, w ≠ 0 ∧ rz x e13 w = 0 ∧ c w = w := by
  obtain ⟨N, hN⟩ : ∃ N, N = rz x e13 := ⟨_, rfl⟩
  rw [← hN]
  have hxN : x * N = N := by
    calc x * N = rz x (dl 1) * rz x e13 := by rw [rz_dl, xp_one, hN]
      _ = N := by rw [rz_mul hx, cv_dl_one_e13, hN]
  have hNN : N * N = N := by rw [hN, rz_mul hx, cv_e13_e13]
  have hNxp : ∀ j : ZMod 13, N * xp x j = N := by
    intro j
    rw [hN, ← rz_dl, rz_mul hx, cv_e13_dl]
  have hcN : c * N = N * c := by
    rw [hN, mul_rz hx hcx]
    rfl
  have hc2N : c ^ 2 * N = N * c ^ 2 := by
    rw [sq, mul_assoc, hcN, ← mul_assoc, hcN, mul_assoc]
  have hP : (1 : Module.End (ZMod 2) V) - N ≠ 0 := by
    intro h
    have h1 : N = 1 := (sub_eq_zero.mp h).symm
    apply hx1
    rw [← mul_one x, ← h1, hxN, h1]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, ((1 : Module.End (ZMod 2) V) - N) v₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hP (LinearMap.ext hall)
  obtain ⟨v, hv⟩ : ∃ v, v = ((1 : Module.End (ZMod 2) V) - N) v₀ := ⟨_, rfl⟩
  rw [← hv] at hv₀
  have hNv : N v = 0 := by
    rw [hv, ← Module.End.mul_apply, mul_sub, mul_one, hNN, sub_self, LinearMap.zero_apply]
  have htr := congrArg (fun f : Module.End (ZMod 2) V => f v) (sum_xp_trace hx hcx)
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, ← hN] at htr
  have hNcv : N (c v) = 0 := by
    rw [← Module.End.mul_apply, ← hcN, Module.End.mul_apply, hNv, map_zero]
  have hNc2v : N ((c ^ 2) v) = 0 := by
    rw [← Module.End.mul_apply, ← hc2N, Module.End.mul_apply, hNv, map_zero]
  rw [hNcv, hNc2v, add_zero, add_zero, LinearMap.sum_apply] at htr
  obtain ⟨T, hT⟩ : ∃ T : Module.End (ZMod 2) V, T = 1 + c + c ^ 2 := ⟨_, rfl⟩
  rw [← hT] at htr
  obtain ⟨k, -, hk⟩ : ∃ k ∈ (Finset.univ : Finset (ZMod 13)), T (xp x (-k) v) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hv₀
    rw [← htr]
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [Module.End.mul_apply]
    rw [hall k hk, map_zero]
  have hcT : c * T = T := by
    rw [hT, mul_add, mul_add, mul_one, ← pow_two, ← pow_succ', hc]
    abel
  have hNT : N * T = T * N := by
    rw [hT, mul_add, mul_add, add_mul, add_mul, mul_one, one_mul, ← hcN, hc2N]
  refine ⟨T (xp x (-k) v), hk, ?_, ?_⟩
  · rw [← Module.End.mul_apply, ← Module.End.mul_apply, hNT, mul_assoc, hNxp,
      Module.End.mul_apply, hNv, map_zero]
  · rw [← Module.End.mul_apply, hcT]

theorem sixteen_le_card_fixed [Finite V] {x c : Module.End (ZMod 2) V} (hx : x ^ 13 = 1)
    (hc : c ^ 3 = 1) (hcx : c * x = x ^ 3 * c) (hx1 : x ≠ 1) :
    16 ≤ Nat.card {v : V // c v = v} := by
  classical
  obtain ⟨w, hw0, hNw, hcw⟩ := exists_fixed_ker_ne_zero hx hc hcx hx1
  obtain ⟨N, hN⟩ : ∃ N, N = rz x e13 := ⟨_, rfl⟩
  rw [← hN] at hNw
  obtain ⟨W, hW⟩ : ∃ W : Submodule (ZMod 2) V, W = LinearMap.ker N ⊓ LinearMap.ker (c - 1) :=
    ⟨_, rfl⟩
  have memW : ∀ y : V, y ∈ W ↔ N y = 0 ∧ c y = y := by
    intro y
    rw [hW, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
  have hwW : w ∈ W := (memW w).mpr ⟨hNw, hcw⟩
  obtain ⟨u, hu⟩ : ∃ u, u = rz x u0 := ⟨_, rfl⟩
  have hcu : c * u = u * c := by
    rw [hu, mul_rz hx hcx]
    congr 2
    funext m
    exact u0_nine_mul m
  have hNu : N * u = 0 := by
    rw [hN, hu, rz_mul hx, cv_e13_u0, rz_zero]
  have hgeom : ∑ i ∈ Finset.range 5, u ^ i = N := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    have h2 : u ^ 2 = rz x (cv u0 u0) := by rw [sq, hu, rz_mul hx]
    have h3 : u ^ 3 = rz x (cv (cv u0 u0) u0) := by rw [pow_succ, h2, hu, rz_mul hx]
    have h4 : u ^ 4 = rz x (cv (cv (cv u0 u0) u0) u0) := by rw [pow_succ, h3, hu, rz_mul hx]
    rw [h2, h3, h4, ← xp_zero x, ← rz_dl, hu, rz_add, rz_add, rz_add, rz_add, phi5_u0, hN]
  have hu5 : ∀ y ∈ W, (u ^ 5) y = y := by
    intro y hy
    have h := congrArg (fun f : Module.End (ZMod 2) V => f y) (mul_geom_sum u 5)
    simp only [hgeom, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply,
      ((memW y).mp hy).1, map_zero] at h
    exact (sub_eq_zero.mp h.symm)
  have hufix : ∀ y ∈ W, u y = y → y = 0 := by
    intro y hy huy
    have hpow : ∀ i : ℕ, (u ^ i) y = y := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ, Module.End.mul_apply, huy, ih]
    have h := congrArg (fun f : Module.End (ZMod 2) V => f y) hgeom
    simp only [LinearMap.sum_apply, hpow, Finset.sum_const, Finset.card_range,
      five_nsmul] at h
    rw [h]
    exact ((memW y).mp hy).1
  have huW : ∀ y ∈ W, u y ∈ W := by
    intro y hy
    obtain ⟨hNy, hcy⟩ := (memW y).mp hy
    refine (memW _).mpr ⟨?_, ?_⟩
    · rw [← Module.End.mul_apply, hNu, LinearMap.zero_apply]
    · rw [← Module.End.mul_apply, hcu, Module.End.mul_apply, hcy]
  have huW' : ∀ (i : ℕ), ∀ y ∈ W, (u ^ i) y ∈ W := by
    intro i
    induction i with
    | zero => intro y hy; exact hy
    | succ i ih => intro y hy; rw [pow_succ, Module.End.mul_apply]; exact ih _ (huW y hy)
  have hleft : ∀ y : W, (u ^ 4) (u y) = y := fun y => by
    rw [← Module.End.mul_apply, ← pow_succ, hu5 y y.2]
  have hright : ∀ y : W, u ((u ^ 4) y) = y := fun y => by
    rw [← Module.End.mul_apply, ← pow_succ', hu5 y y.2]
  let σ : Equiv.Perm W :=
    { toFun := fun y => ⟨u y, huW y y.2⟩
      invFun := fun y => ⟨(u ^ 4) y, huW' 4 y y.2⟩
      left_inv := fun y => Subtype.ext (hleft y)
      right_inv := fun y => Subtype.ext (hright y) }
  have hσ : ∀ y : W, ((σ y : W) : V) = u y := fun y => rfl
  have hσpow : ∀ (i : ℕ) (y : W), ((σ ^ i) y : V) = (u ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Module.End.mul_apply, ← ih, hσ]
  have hσ5 : σ ^ 5 = 1 := by
    ext y
    rw [hσpow, hu5 y y.2]
    rfl
  have hfixσ : ∀ y : W, σ y = y ↔ y = 0 := by
    intro y
    constructor
    · intro h
      exact Subtype.ext (hufix y y.2 (by rw [← hσ, h]))
    · rintro rfl
      exact Subtype.ext (by rw [hσ]; exact map_zero u)
  have hmod := card_modEq_one_of_perm σ hσ5 0 hfixσ
  have hcardW := FiniteField.pow_finrank_eq_natCard 2 W
  have hW2 : 2 ≤ Nat.card W := by
    have : Nontrivial W := ⟨⟨⟨w, hwW⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  rw [← hcardW] at hmod hW2
  have hd4 := four_le_of_two_pow_modEq hW2 hmod
  have h16 : 16 ≤ Nat.card W := by
    rw [← hcardW]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ Module.finrank (ZMod 2) W := Nat.pow_le_pow_right (by norm_num) hd4
  refine h16.trans (Nat.card_le_card_of_injective (fun y => ⟨y, ((memW y).mp y.2).2⟩) ?_)
  intro y z hyz
  have h := congrArg Subtype.val hyz
  exact Subtype.ext h

theorem sixteen_le_card_fixed' [Finite V] {x c : Module.End (ZMod 2) V} (hx : x ^ 13 = 1)
    (hc : c ^ 3 = 1) (hcx : c * x = x ^ 3 * c ∨ c * x = x ^ 9 * c) (hx1 : x ≠ 1) :
    16 ≤ Nat.card {v : V // c v = v} := by
  rcases hcx with h | h
  · exact sixteen_le_card_fixed hx hc h hx1
  · have h2 : c ^ 2 * x = x ^ 3 * c ^ 2 := by
      calc c ^ 2 * x = (c * x ^ 9) * c := by rw [sq, mul_assoc, h, mul_assoc]
        _ = x ^ 81 * (c * c) := by rw [mul_pow_eq h, mul_assoc]
        _ = x ^ 3 * c ^ 2 := by rw [pow_eq_pow_mod 81 hx, sq]
    have hc2 : (c ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hc, one_pow]
    refine (sixteen_le_card_fixed hx hc2 h2 hx1).trans
      (Nat.card_le_card_of_injective (fun v => ⟨v.1, ?_⟩) ?_)
    · have hv : (c ^ 2) v.1 = v.1 := v.2
      calc c v.1 = c ((c ^ 2) v.1) := by rw [hv]
        _ = (c ^ 3) v.1 := by rw [pow_succ' c 2]; rfl
        _ = v.1 := by rw [hc]; rfl
    · intro v w hvw
      have h' := congrArg Subtype.val hvw
      exact Subtype.ext h'

end Module

end CFSG.RankThree.PartTwo.Sec16.KS1619SecProof
