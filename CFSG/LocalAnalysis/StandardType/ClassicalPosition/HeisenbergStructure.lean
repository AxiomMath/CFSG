module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.LinearAlgebra.OddSolvableUnitary.ExtraspecialModule
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

private theorem heisStr_pow_eigenspace {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {x : Module.End F V} {μ : F} {v : V} (hv : x v = μ • v) (n : ℕ) :
    (x ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [pow_succ, Module.End.mul_apply]
    rw [hv, map_smul, ih, smul_smul, ← pow_succ']

private theorem heisStr_y_injective {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {p : ℕ} [Fact p.Prime] (y : Module.End F V) (hy : y ^ p = 1) :
    Function.Injective y := by
  intro a b hab
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hleft : y ^ (p - 1) * y = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hp1, hy]
  have h2 : (y ^ (p - 1) * y) a = (y ^ (p - 1) * y) b := by
    rw [Module.End.mul_apply, Module.End.mul_apply, hab]
  rwa [hleft, Module.End.one_apply, Module.End.one_apply] at h2

private theorem heisStr_mul_pow_comm {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {g y : Module.End F V} (h : g * y = y * g) (n : ℕ) : g * y ^ n = y ^ n * g := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc g * y ^ (n + 1) = g * (y * y ^ n) := by rw [pow_succ']
      _ = (g * y) * y ^ n := by rw [mul_assoc]
      _ = (y * g) * y ^ n := by rw [h]
      _ = y * (g * y ^ n) := by rw [mul_assoc]
      _ = y * (y ^ n * g) := by rw [ih]
      _ = (y * y ^ n) * g := by rw [mul_assoc]
      _ = y ^ (n + 1) * g := by rw [pow_succ']

theorem eigenspace_structure {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {p : ℕ} [Fact p.Prime]
    (x y : Module.End F V) (hx : x ^ p = 1) (hy : y ^ p = 1) {ζ : F} (hζ : ζ ≠ 1)
    (hζp : ζ ^ p = 1) (hxy : x * y = ζ • (y * x)) :
    Module.finrank F V = p * Module.finrank F (Module.End.eigenspace x 1) ∧
      ∀ g : Module.End F V, g * x = x * g → g * y = y * g → ∀ c : F,
        (∀ w ∈ Module.End.eigenspace x 1, g w = c • w) → ∀ v, g v = c • v := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hprim : IsPrimitiveRoot ζ p := by
    have h : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
    rwa [orderOf_eq_prime hζp hζ] at h
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hy_inj : Function.Injective y := heisStr_y_injective y hy
  have hfin : Module.finrank F V = p * Module.finrank F (Module.End.eigenspace x 1) := by
    have hζ0 : ζ ≠ 0 := hprim.ne_zero (Fact.out : p.Prime).ne_zero
    have hcb : y * x = ζ⁻¹ • (x * y) := by
      have h' : ζ⁻¹ • (x * y) = y * x := by
        rw [hxy, smul_smul, inv_mul_cancel₀ hζ0, one_smul]
      exact h'.symm
    have h := CFSG.OddSolvableUnitary.finrank_eq_mul_finrank_eigenspace_one
      (F := F) (W := V) (r := p) (ζ := ζ⁻¹) (b := x) (c := y)
      hp_pos hprim.inv hx hy_inj hcb
    simpa using h
  refine ⟨hfin, ?_⟩
  let En : ℕ → Submodule F V := fun j => Module.End.eigenspace x (ζ ^ j)
  have hper : ∀ j m : ℕ, En (j + p * m) = En j := by
    intro j m
    change Module.End.eigenspace x (ζ ^ (j + p * m)) =
      Module.End.eigenspace x (ζ ^ j)
    rw [pow_add, pow_mul, hζp, one_pow, mul_one]
  have hxy_apply : ∀ v : V, x (y v) = ζ • y (x v) := by
    intro v
    have h := congrArg (fun f : Module.End F V => f v) hxy
    simpa [Module.End.mul_apply, LinearMap.smul_apply] using h
  have hmap : ∀ j : ℕ, ∀ v ∈ En j, y v ∈ En (j + 1) := by
    intro j v hv
    change v ∈ Module.End.eigenspace x (ζ ^ j) at hv
    change y v ∈ Module.End.eigenspace x (ζ ^ (j + 1))
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hxy_apply v, hv, map_smul, smul_smul, ← pow_succ']
  have hshift : ∀ k j : ℕ, ∀ v ∈ En j, (y ^ k) v ∈ En (j + k) := by
    intro k
    induction k with
    | zero =>
      intro j v hv
      simpa using hv
    | succ k ih =>
      intro j v hv
      have h1 : (y ^ k) v ∈ En (j + k) := ih j v hv
      have h2 : y ((y ^ k) v) ∈ En ((j + k) + 1) := hmap (j + k) _ h1
      have h3 : (y ^ (k + 1)) v = y ((y ^ k) v) := by
        rw [pow_succ', Module.End.mul_apply]
      rw [h3]
      simpa only [Nat.add_assoc] using h2
  have hmul : ∀ i : ℕ, i + (p - 1) * i = p * i := by
    intro i
    calc i + (p - 1) * i = 1 * i + (p - 1) * i := by rw [one_mul]
      _ = (1 + (p - 1)) * i := by rw [← Nat.add_mul]
      _ = p * i := by rw [Nat.add_comm 1 (p - 1), Nat.sub_add_cancel hp1]
  have hsup : (⨆ i : Fin p, En i) = ⊤ := by
    have hdiag : (⨆ μ : F, Module.End.eigenspace x μ) = ⊤ :=
      CFSG.RankThree.PartOne.iSup_eigenspace_eq_top_of_pow_eq_one hprim hx
    apply le_antisymm le_top
    rw [← hdiag]
    apply iSup_le
    intro μ v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    by_cases hμ : μ ^ p = 1
    · obtain ⟨i, hi, hζi⟩ := hprim.eq_pow_of_pow_eq_one hμ
      refine Submodule.mem_iSup_of_mem ⟨i, hi⟩ ?_
      change v ∈ Module.End.eigenspace x (ζ ^ i)
      rw [Module.End.mem_eigenspace_iff, hζi]
      exact hv
    · have hpow := heisStr_pow_eigenspace hv p
      have hxp : v = μ ^ p • v := by
        have h := hpow
        rw [hx] at h
        simpa using h
      have hzero : (1 - μ ^ p) • v = 0 := by
        rw [sub_smul, one_smul]
        exact sub_eq_zero.mpr hxp
      have hcoef : (1 : F) - μ ^ p ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h => hμ h.symm
      have hv0 : v = 0 := by
        have h := congrArg (fun w : V => (1 - μ ^ p)⁻¹ • w) hzero
        simpa [smul_smul, inv_mul_cancel₀ hcoef] using h
      rw [hv0]
      exact Submodule.zero_mem _
  intro g hgx hgy c hg0 v
  have hvmem : v ∈ ⨆ i : Fin p, En i := hsup ▸ Submodule.mem_top
  refine Submodule.iSup_induction (motive := fun w => g w = c • w)
    (fun i : Fin p => En i) hvmem ?_ ?_ ?_
  · intro i w hw
    have hw0 : (y ^ ((p - 1) * (i : ℕ))) w ∈ En 0 := by
      have h1 := hshift ((p - 1) * (i : ℕ)) (i : ℕ) w hw
      have hEq : En ((i : ℕ) + (p - 1) * (i : ℕ)) = En 0 := by
        rw [hmul (i : ℕ)]
        have h := hper 0 (i : ℕ)
        simpa using h
      rwa [hEq] at h1
    have hpre : (y ^ (i : ℕ)) ((y ^ ((p - 1) * (i : ℕ))) w) = w := by
      calc (y ^ (i : ℕ)) ((y ^ ((p - 1) * (i : ℕ))) w)
          = (y ^ ((i : ℕ) + (p - 1) * (i : ℕ))) w := by
            rw [← Module.End.mul_apply, ← pow_add]
        _ = (y ^ (p * (i : ℕ))) w := by rw [hmul]
        _ = ((y ^ p) ^ (i : ℕ)) w := by rw [pow_mul]
        _ = w := by rw [hy, one_pow, Module.End.one_apply]
    have hgw0 : g ((y ^ ((p - 1) * (i : ℕ))) w) =
        c • ((y ^ ((p - 1) * (i : ℕ))) w) :=
      hg0 _ (by simpa [En] using hw0)
    have hcommi : g * y ^ (i : ℕ) = y ^ (i : ℕ) * g :=
      heisStr_mul_pow_comm hgy (i : ℕ)
    calc g w = g ((y ^ (i : ℕ)) ((y ^ ((p - 1) * (i : ℕ))) w)) := by rw [hpre]
      _ = (g * y ^ (i : ℕ)) ((y ^ ((p - 1) * (i : ℕ))) w) := by
            rw [Module.End.mul_apply]
      _ = (y ^ (i : ℕ) * g) ((y ^ ((p - 1) * (i : ℕ))) w) := by rw [hcommi]
      _ = (y ^ (i : ℕ)) (g ((y ^ ((p - 1) * (i : ℕ))) w)) := by
            rw [Module.End.mul_apply]
      _ = (y ^ (i : ℕ)) (c • ((y ^ ((p - 1) * (i : ℕ))) w)) := by rw [hgw0]
      _ = c • ((y ^ (i : ℕ)) ((y ^ ((p - 1) * (i : ℕ))) w)) := by rw [map_smul]
      _ = c • w := by rw [hpre]
  · simp
  · intro a b ha hb
    rw [map_add, ha, hb, smul_add]

end CFSG.StandardType.ClassicalPosition.HeisRank
