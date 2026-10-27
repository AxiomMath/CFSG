module

public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import CFSG.RankThree.PartOne.LIT.McMitchell

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private theorem tffr_pow_eq_one_add_nsmul {A : Type*} [Ring A] [Algebra (ZMod p) A]
    (N : A) (hN : N ^ 2 = 0) (k : ℕ) : (1 + N) ^ k = 1 + k • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) k N,
        ← Nat.cast_smul_eq_nsmul (ZMod p) (k + 1) N]
    rw [Nat.cast_add, Nat.cast_one]
    have hexp : (1 + (k : ZMod p) • N) * (1 + N) =
        1 + (k : ZMod p) • N + N + (k : ZMod p) • (N * N) := by
      simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc]
      abel
    rw [hexp, show N * N = 0 from by simpa only [pow_two] using hN, smul_zero, add_zero]
    rw [add_smul, one_smul]
    abel

theorem pow_eq_one_of_sub_one_sq_eq_zero {g : V ≃ₗ[ZMod p] V}
    (hg : ((g : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) : g ^ p = 1 := by
  let N : V →ₗ[ZMod p] V := (g : V →ₗ[ZMod p] V) - 1
  have hN : N ^ 2 = 0 := hg
  have hg' : (g : V →ₗ[ZMod p] V) = 1 + N := by
    change (g : V →ₗ[ZMod p] V) = 1 + ((g : V →ₗ[ZMod p] V) - 1)
    abel
  have hp : (g : V →ₗ[ZMod p] V) ^ p = 1 := by
    rw [hg', tffr_pow_eq_one_add_nsmul (p := p) N hN p]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p N, ZMod.natCast_self]
    simp
  apply LinearEquiv.ext
  intro v
  have h := congrArg (fun f : V →ₗ[ZMod p] V => f v) hp
  rw [Module.End.pow_apply] at h
  rwa [LinearEquiv.coe_pow]

private theorem tffr_natCard_linearEquiv_dvd_of_finrank_le_two {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] [Module.Finite (ZMod p) W] (hW : Module.finrank (ZMod p) W ≤ 2) :
    Nat.card (W ≃ₗ[ZMod p] W) ∣ p * (p - 1) ^ 2 * (p + 1) := by
  set r : ℕ := Module.finrank (ZMod p) W with hr
  have hr2 : r ≤ 2 := hW
  let e : W ≃ₗ[ZMod p] (Fin r → ZMod p) :=
    (Module.finBasisOfFinrankEq (ZMod p) W (n := r) hr.symm).equivFun
  have hcard : Nat.card (W ≃ₗ[ZMod p] W) = Nat.card (GL (Fin r) (ZMod p)) :=
    Nat.card_congr (CFSG.RankThree.PartOne.LIT.autGL e).toEquiv
  rw [hcard, Matrix.card_GL_field, ZMod.card]
  interval_cases r
  · simp
  · simp only [Fin.prod_univ_one, pow_one, pow_zero, Fin.val_zero]
    refine ⟨p * (p - 1) * (p + 1), by ring⟩
  · simp only [Fin.prod_univ_two, pow_one, pow_zero, Fin.val_zero, Fin.val_one]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h1 : 1 ≤ p ^ 2 := by nlinarith
    have h2 : p ≤ p ^ 2 := by nlinarith
    have hp1 : 1 ≤ p := by omega
    have heq : (p ^ 2 - 1) * (p ^ 2 - p) = p * (p - 1) ^ 2 * (p + 1) := by
      apply Nat.cast_injective (R := ℤ)
      push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub hp1]
      ring
    refine ⟨1, by rw [mul_one]; exact heq.symm⟩

private theorem tffr_x_mul_y_sub_one (x y : V ≃ₗ[ZMod p] V) :
    (x : V →ₗ[ZMod p] V) * ((y : V →ₗ[ZMod p] V) - 1) =
      ((y : V →ₗ[ZMod p] V) - 1) + ((x : V →ₗ[ZMod p] V) - 1) *
        ((y : V →ₗ[ZMod p] V) - 1) := by
  noncomm_ring

private theorem tffr_g_sub_one_mem {x y : V ≃ₗ[ZMod p] V} (_hx : IsRefl p x) (v : V) :
    (x * y) v - v ∈ LinearMap.range ((x : V →ₗ[ZMod p] V) - 1) ⊔
      LinearMap.range ((y : V →ₗ[ZMod p] V) - 1) := by
  have hxy : (x * y) v - v = x (y v - v) + (x v - v) := by
    rw [LinearEquiv.mul_apply, map_sub]
    abel
  rw [hxy]
  have h := congrArg (fun f : V →ₗ[ZMod p] V => f v) (tffr_x_mul_y_sub_one x y)
  rw [Module.End.mul_apply] at h
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    Module.End.mul_apply] at h
  rw [show x (y v - v) = (y : V →ₗ[ZMod p] V) v - v +
    ((x : V →ₗ[ZMod p] V) - 1) (y v - v) from h]
  rw [add_assoc, sup_comm]
  exact Submodule.add_mem_sup (S := LinearMap.range ((y : V →ₗ[ZMod p] V) - 1))
    (T := LinearMap.range ((x : V →ₗ[ZMod p] V) - 1)) ⟨v, rfl⟩
    (Submodule.add_mem (p := LinearMap.range ((x : V →ₗ[ZMod p] V) - 1))
      ⟨y v - v, rfl⟩ ⟨v, rfl⟩)

private theorem tffr_restrict_pow_apply {g : V ≃ₗ[ZMod p] V} {W : Submodule (ZMod p) V}
    (hgW : W.map (g : V →ₗ[ZMod p] V) ≤ W)
    (gW : W ≃ₗ[ZMod p] W) (hgW_apply : ∀ w : W, (gW w : V) = g (w : V))
    (n : ℕ) : ∀ w : W, (g ^ n) (w : V) = ((gW ^ n) w : V) := by
  induction n with
  | zero => intro w; simp
  | succ n ih =>
    intro w
    rw [pow_succ, pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    let w' : W := ⟨g (w : V), hgW ⟨w, w.2, rfl⟩⟩
    have hw' : w' = gW w := Subtype.ext (hgW_apply w).symm
    rw [ih w', hw']

private theorem tffr_pow_sub_one_mem {g : V ≃ₗ[ZMod p] V} {W : Submodule (ZMod p) V}
    (hg_sub : ∀ v : V, g v - v ∈ W) (n : ℕ) : ∀ v : V, (g ^ n) v - v ∈ W := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [pow_succ, LinearEquiv.mul_apply]
    have h : (g ^ n) (g v) - v = ((g ^ n) (g v) - g v) + (g v - v) := by abel
    rw [h]
    exact Submodule.add_mem (p := W) (ih (g v)) (hg_sub v)

private theorem tffr_exists_pow_sub_one_sq_eq_zero [Module.Finite (ZMod p) V]
    {g : V ≃ₗ[ZMod p] V} {W : Submodule (ZMod p) V}
    (hg_sub : ∀ v : V, g v - v ∈ W) (hgW : W.map (g : V →ₗ[ZMod p] V) ≤ W)
    (hWfin : Module.finrank (ZMod p) W ≤ 2) :
    ∃ k : ℕ, k ∣ p * (p - 1) ^ 2 * (p + 1) ∧
      (((g ^ k : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 := by
  have hWmap : W.map (g : V →ₗ[ZMod p] V) = W := by
    apply Submodule.eq_of_le_of_finrank_le hgW
    rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
      (g : V →ₗ[ZMod p] V) g.injective W)]
  let gW : W ≃ₗ[ZMod p] W :=
    (Submodule.equivMapOfInjective (g : V →ₗ[ZMod p] V) g.injective W).trans
      (LinearEquiv.ofEq (p := W.map (g : V →ₗ[ZMod p] V)) (q := W) hWmap)
  let k : ℕ := Nat.card (W ≃ₗ[ZMod p] W)
  have hgW_apply : ∀ w : W, (gW w : V) = g (w : V) := by intro w; rfl
  have hgW_pow : gW ^ k = 1 := pow_card_eq_one'
  have hg_pow_eq : ∀ w : W, (g ^ k) (w : V) = (w : V) := by
    intro w
    rw [tffr_restrict_pow_apply hgW gW hgW_apply k w, hgW_pow]
    rfl
  have hgk_sq : (((g ^ k : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 := by
    apply LinearMap.ext
    intro v
    have h1 : (g ^ k) v - v ∈ W := tffr_pow_sub_one_mem hg_sub k v
    have h2 : (g ^ k) ((g ^ k) v - v) = (g ^ k) v - v :=
      hg_pow_eq ⟨(g ^ k) v - v, h1⟩
    rw [pow_two, Module.End.mul_apply]
    change (g ^ k) ((g ^ k) v - v) - ((g ^ k) v - v) = 0
    rw [h2, sub_self]
  exact ⟨k, tffr_natCard_linearEquiv_dvd_of_finrank_le_two hWfin, hgk_sq⟩

theorem orderOf_mul_dvd_of_isRefl [Module.Finite (ZMod p) V] {x y : V ≃ₗ[ZMod p] V}
    (hx : IsRefl p x) (hy : IsRefl p y) :
    orderOf (x * y) ∣ p ^ 2 * (p - 1) ^ 2 * (p + 1) := by
  let g : V ≃ₗ[ZMod p] V := x * y
  let Vx : Submodule (ZMod p) V := LinearMap.range ((x : V →ₗ[ZMod p] V) - 1)
  let Vy : Submodule (ZMod p) V := LinearMap.range ((y : V →ₗ[ZMod p] V) - 1)
  let W : Submodule (ZMod p) V := Vx ⊔ Vy
  have hWfin : Module.finrank (ZMod p) W ≤ 2 := by
    have h1 : Module.finrank (ZMod p) Vx = 1 := hx.2
    have h2 : Module.finrank (ZMod p) Vy = 1 := hy.2
    have hle := Submodule.finrank_add_le_finrank_add_finrank Vx Vy
    rw [h1, h2] at hle
    rw [show W = Vx ⊔ Vy from rfl]
    simpa using hle
  have hg_sub : ∀ v : V, g v - v ∈ W := fun v => tffr_g_sub_one_mem hx v
  have hgW : W.map (g : V →ₗ[ZMod p] V) ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    have h := hg_sub (w : V)
    have hsum : g (w : V) = (w : V) + (g (w : V) - (w : V)) := by abel
    change g (w : V) ∈ W
    rw [hsum]
    exact Submodule.add_mem (p := W) hw h
  obtain ⟨k, hk, hgk_sq⟩ := tffr_exists_pow_sub_one_sq_eq_zero hg_sub hgW hWfin
  have hgk_pow_p : (g ^ k) ^ p = 1 := pow_eq_one_of_sub_one_sq_eq_zero hgk_sq
  have hg_pow : g ^ (k * p) = 1 := by rw [pow_mul, hgk_pow_p]
  have hdvd : orderOf g ∣ k * p := orderOf_dvd_of_pow_eq_one hg_pow
  have hfinal : (p * (p - 1) ^ 2 * (p + 1)) * p = p ^ 2 * (p - 1) ^ 2 * (p + 1) := by ring
  have hk' : k * p ∣ p ^ 2 * (p - 1) ^ 2 * (p + 1) := by
    rw [← hfinal]
    exact Nat.mul_dvd_mul_right hk p
  exact dvd_trans hdvd hk'

theorem five_dvd_of_orderOf_mul_eq_five [Module.Finite (ZMod p) V] {x y : V ≃ₗ[ZMod p] V}
    (hx : IsRefl p x) (hy : IsRefl p y) (h5 : orderOf (x * y) = 5) :
    p = 5 ∨ 5 ∣ p - 1 ∨ 5 ∣ p + 1 := by
  have hdvd : 5 ∣ p ^ 2 * (p - 1) ^ 2 * (p + 1) := by
    rw [← h5]
    exact orderOf_mul_dvd_of_isRefl hx hy
  have h5prime : Nat.Prime 5 := by norm_num
  rcases h5prime.dvd_mul.mp hdvd with h12 | h3
  · rcases h5prime.dvd_mul.mp h12 with hp2 | hp1sq
    · left
      have hp : 5 ∣ p := h5prime.dvd_of_dvd_pow hp2
      exact ((Nat.prime_dvd_prime_iff_eq h5prime (Fact.out : p.Prime)).mp hp).symm
    · right; left
      exact h5prime.dvd_of_dvd_pow hp1sq
  · right; right
    exact h3

theorem card_center_dvd_of_absIrred [Module.Finite (ZMod p) V] {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hA : AbsIrred p J) : Nat.card (Subgroup.center J) ∣ p - 1 :=
  card_center_dvd_sub_one hA

end CFSG.StandardType.ZS.TableFacts

end
