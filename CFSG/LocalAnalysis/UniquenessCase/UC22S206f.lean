module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem uc22s206f_mul_pow {R : Type*} [Monoid R] {X Y : R} (hXY : X * Y = Y ^ 2 * X) (k : ℕ) :
    X * Y ^ k = Y ^ (2 * k) * X := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, hXY, ← mul_assoc, ← pow_add, mul_add_one]

theorem uc22s206f_cube {R : Type*} [Ring R] (Y : R) :
    Y ^ 3 = 1 + Y * (1 + (Y + Y ^ 2 + Y ^ 4)) + Y ^ 2 * (Y + Y ^ 2 + Y ^ 4) -
      ∑ i ∈ Finset.range 7, Y ^ i := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  noncomm_ring

theorem uc22s206f_average {R : Type*} [Ring R] {X Y : R} (hY7 : Y ^ 7 = 1)
    (hXY : X * Y = Y ^ 2 * X) :
    ∑ i ∈ Finset.range 7, Y ^ (7 - i) * (1 + X + X ^ 2) * Y ^ i =
      7 + (∑ i ∈ Finset.range 7, Y ^ i) * X + (∑ i ∈ Finset.range 7, Y ^ i) * X ^ 2 := by
  have hY : ∀ n : ℕ, Y ^ (n + 7) = Y ^ n := fun n => by rw [pow_add, hY7, mul_one]
  have h2 : ∀ k : ℕ, X ^ 2 * Y ^ k = Y ^ (4 * k) * X ^ 2 := by
    intro k
    calc X ^ 2 * Y ^ k = X * (X * Y ^ k) := by rw [sq, mul_assoc]
      _ = X * Y ^ (2 * k) * X := by rw [uc22s206f_mul_pow hXY k, mul_assoc]
      _ = Y ^ (4 * k) * X ^ 2 := by
        rw [uc22s206f_mul_pow hXY (2 * k), mul_assoc, ← sq, show 2 * (2 * k) = 4 * k by ring]
  have hterm : ∀ i ∈ Finset.range 7, Y ^ (7 - i) * (1 + X + X ^ 2) * Y ^ i =
      1 + Y ^ i * X + Y ^ (3 * i) * X ^ 2 := by
    intro i hi
    have hi7 : i ≤ 7 := (Finset.mem_range.mp hi).le
    calc Y ^ (7 - i) * (1 + X + X ^ 2) * Y ^ i =
        Y ^ (7 - i) * Y ^ i + Y ^ (7 - i) * (X * Y ^ i) + Y ^ (7 - i) * (X ^ 2 * Y ^ i) := by
          noncomm_ring
      _ = Y ^ (7 - i + i) + Y ^ (7 - i + 2 * i) * X + Y ^ (7 - i + 4 * i) * X ^ 2 := by
          rw [uc22s206f_mul_pow hXY i, h2 i]
          simp only [← mul_assoc, ← pow_add]
      _ = 1 + Y ^ i * X + Y ^ (3 * i) * X ^ 2 := by
          rw [show 7 - i + i = 0 + 7 by omega, show 7 - i + 2 * i = i + 7 by omega,
            show 7 - i + 4 * i = 3 * i + 7 by omega, hY, hY, hY, pow_zero]
  have h3 : ∑ i ∈ Finset.range 7, Y ^ (3 * i) = ∑ i ∈ Finset.range 7, Y ^ i := by
    have h9 : Y ^ 9 = Y ^ 2 := hY 2
    have h12 : Y ^ 12 = Y ^ 5 := hY 5
    have h15 : Y ^ 15 = Y ^ 1 := (hY 8).trans (hY 1)
    have h18 : Y ^ 18 = Y ^ 4 := (hY 11).trans (hY 4)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, h9, h12, h15, h18]
    abel
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, ← Finset.sum_mul, ← Finset.sum_mul, h3, nsmul_one,
    Nat.cast_ofNat]

section Linear

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem uc22s206f_descent [FiniteDimensional F V] {X Y : Module.End F V} (hX3 : X ^ 3 = 1)
    (hY7 : Y ^ 7 = 1) (hXY : X * Y = Y ^ 2 * X) (h7 : (7 : F) ≠ 0) :
    Module.finrank F (LinearMap.range (Y - 1)) ≤
      3 * Module.finrank F (LinearMap.ker (X - 1)) := by
  set U := LinearMap.range (Y - 1)
  set W := U ⊓ LinearMap.ker (X - 1)
  set S := W ⊔ W.map Y ⊔ W.map (Y ^ 2)
  have hinv : ∀ A B : Module.End F V, A * (Y - 1) = (Y - 1) * B → ∀ u ∈ U, A u ∈ U := by
    rintro A B hAB _ ⟨v, rfl⟩
    exact ⟨B v, (LinearMap.congr_fun hAB v).symm⟩
  have hYU : ∀ u ∈ U, Y u ∈ U := hinv Y Y (by noncomm_ring)
  have hXU : ∀ u ∈ U, X u ∈ U := hinv X ((Y + 1) * X) (by
    rw [mul_sub, mul_one, hXY]
    noncomm_ring)
  have hYkU : ∀ k : ℕ, ∀ u ∈ U, (Y ^ k) u ∈ U := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [pow_succ', Module.End.mul_apply]
      exact hYU _ (ih u hu)
  have hNU : ∀ u ∈ U, (∑ i ∈ Finset.range 7, Y ^ i) u = 0 := by
    rintro _ ⟨v, rfl⟩
    show ((∑ i ∈ Finset.range 7, Y ^ i) * (Y - 1)) v = 0
    rw [geom_sum_mul, hY7, sub_self, LinearMap.zero_apply]
  have hWX : ∀ w ∈ W, X w = w := by
    intro w hw
    have h := (Submodule.mem_inf.mp hw).2
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  have hWU : ∀ w ∈ W, w ∈ U := fun w hw => (Submodule.mem_inf.mp hw).1
  have hmemW : ∀ w ∈ U, X w = w → w ∈ W := by
    intro w hwU hwX
    refine Submodule.mem_inf.mpr ⟨hwU, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hwX, sub_self]
  have hXT : X * (1 + X + X ^ 2) = 1 + X + X ^ 2 := by
    have h : X * (1 + X + X ^ 2) = X ^ 3 + X + X ^ 2 := by noncomm_ring
    rw [h, hX3]
  have hT : ∀ u ∈ U, (1 + X + X ^ 2 : Module.End F V) u ∈ W := by
    intro u hu
    refine hmemW _ ?_ ?_
    · rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, sq,
        Module.End.mul_apply]
      exact U.add_mem (U.add_mem hu (hXU u hu)) (hXU _ (hXU u hu))
    · show (X * (1 + X + X ^ 2) : Module.End F V) u = _
      rw [hXT]
  have hXη : X * (Y + Y ^ 2 + Y ^ 4) = (Y + Y ^ 2 + Y ^ 4) * X := by
    have h8 : Y ^ (2 * 4) = Y := by
      rw [show 2 * 4 = 1 + 7 from rfl, pow_add, hY7, mul_one, pow_one]
    rw [mul_add, mul_add, hXY, uc22s206f_mul_pow hXY 2, uc22s206f_mul_pow hXY 4, h8,
      show 2 * 2 = 4 from rfl]
    noncomm_ring
  have hηW : ∀ w ∈ W, (Y + Y ^ 2 + Y ^ 4) w ∈ W := by
    intro w hw
    refine hmemW _ ?_ ?_
    · rw [LinearMap.add_apply, LinearMap.add_apply]
      exact U.add_mem (U.add_mem (hYU _ (hWU w hw)) (hYkU 2 _ (hWU w hw)))
        (hYkU 4 _ (hWU w hw))
    · show (X * (Y + Y ^ 2 + Y ^ 4)) w = _
      rw [hXη, Module.End.mul_apply, hWX w hw]
  have hWS : ∀ w ∈ W, w ∈ S := fun w hw => Submodule.mem_sup_left (Submodule.mem_sup_left hw)
  have hYWS : ∀ w ∈ W, Y w ∈ S := fun w hw =>
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem hw))
  have hY2WS : ∀ w ∈ W, (Y ^ 2) w ∈ S := fun w hw =>
    Submodule.mem_sup_right (Submodule.mem_map_of_mem hw)
  have hY3WS : ∀ w ∈ W, (Y ^ 3) w ∈ S := by
    intro w hw
    rw [uc22s206f_cube Y, LinearMap.sub_apply, hNU w (hWU w hw), sub_zero, LinearMap.add_apply,
      LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
    refine S.add_mem (S.add_mem (hWS w hw) (hYWS _ ?_)) (hY2WS _ (hηW w hw))
    rw [LinearMap.add_apply, Module.End.one_apply]
    exact W.add_mem hw (hηW w hw)
  have hSY : ∀ s ∈ S, Y s ∈ S := by
    have hle : S ≤ S.comap Y := by
      refine sup_le (sup_le (fun w hw => hYWS w hw) ?_) ?_
      · rintro _ ⟨w, hw, rfl⟩
        show Y (Y w) ∈ S
        rw [← Module.End.mul_apply, ← sq]
        exact hY2WS w hw
      · rintro _ ⟨w, hw, rfl⟩
        show Y ((Y ^ 2) w) ∈ S
        rw [← Module.End.mul_apply, ← pow_succ']
        exact hY3WS w hw
    exact fun s hs => hle hs
  have hSYk : ∀ k : ℕ, ∀ s ∈ S, (Y ^ k) s ∈ S := by
    intro k
    induction k with
    | zero => intro s hs; simpa using hs
    | succ k ih =>
      intro s hs
      rw [pow_succ', Module.End.mul_apply]
      exact hSY _ (ih s hs)
  have hUS : U ≤ S := by
    intro u hu
    have hX2u : (X ^ 2) u ∈ U := by
      rw [sq, Module.End.mul_apply]
      exact hXU _ (hXU u hu)
    have hsum : (∑ i ∈ Finset.range 7, Y ^ (7 - i) * (1 + X + X ^ 2) * Y ^ i :
        Module.End F V) u ∈ S := by
      rw [LinearMap.sum_apply]
      refine S.sum_mem fun i _ => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply]
      exact hSYk _ _ (hWS _ (hT _ (hYkU i u hu)))
    rw [uc22s206f_average hY7 hXY, LinearMap.add_apply, LinearMap.add_apply,
      Module.End.mul_apply, Module.End.mul_apply, hNU _ (hXU u hu), hNU _ hX2u, add_zero,
      add_zero, Module.End.ofNat_apply, ← ofNat_smul_eq_nsmul F] at hsum
    exact (S.smul_mem_iff h7).mp hsum
  have hWk : Module.finrank F W ≤ Module.finrank F (LinearMap.ker (X - 1)) :=
    Submodule.finrank_mono inf_le_right
  have h1 : Module.finrank F S ≤
      Module.finrank F ↥(W ⊔ W.map Y) + Module.finrank F ↥(W.map (Y ^ 2)) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  have h2 : Module.finrank F ↥(W ⊔ W.map Y) ≤
      Module.finrank F W + Module.finrank F ↥(W.map Y) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  have h3 := Submodule.finrank_map_le Y W
  have h4 := Submodule.finrank_map_le (Y ^ 2) W
  have hU : Module.finrank F U ≤ Module.finrank F S := Submodule.finrank_mono hUS
  omega

theorem uc22s206f_rep [FiniteDimensional F V] {Γ : Type*} [Group Γ] (P : Γ →* Module.End F V)
    {a b : Γ} (ha : a ^ 3 = 1) (hb : b ^ 7 = 1) (hab : a * b * a⁻¹ = b ^ 2) (h7 : (7 : F) ≠ 0) :
    Module.finrank F (LinearMap.range (P b - 1)) ≤
      3 * Module.finrank F (LinearMap.ker (P a - 1)) := by
  refine uc22s206f_descent (by rw [← map_pow, ha, map_one]) (by rw [← map_pow, hb, map_one]) ?_
    h7
  rw [← map_mul, ← map_pow, ← map_mul, ← hab, inv_mul_cancel_right]

end Linear

theorem uc22s206f_one_lt_GL {d p : ℕ} [Fact p.Prime] (hp7 : p ≠ 7) {g h : GL (Fin d) (ZMod p)}
    (hh3 : h ^ 3 = 1) (hg7 : g ^ 7 = 1) (hhg : h * g * h⁻¹ = g ^ 2)
    (h6 : 6 ≤ Module.finrank (ZMod p) (LinearMap.range
      ((Matrix.mulVecLin (g : Matrix (Fin d) (Fin d) (ZMod p)) :
        Module.End (ZMod p) (Fin d → ZMod p)) - 1))) :
    1 < Module.finrank (ZMod p) (LinearMap.ker
      ((Matrix.mulVecLin (h : Matrix (Fin d) (Fin d) (ZMod p)) :
        Module.End (ZMod p) (Fin d → ZMod p)) - 1)) := by
  have h7 : (7 : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((7 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_ofNat]; exact h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact hp7 ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide)).mp h0')
  have key := uc22s206f_rep (F := ZMod p) (V := Fin d → ZMod p)
    ((Units.coeHom (Module.End (ZMod p) (Fin d → ZMod p))).comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom) hh3 hg7 hhg h7
  have hPg : ((Units.coeHom (Module.End (ZMod p) (Fin d → ZMod p))).comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom) g =
        Matrix.mulVecLin (g : Matrix (Fin d) (Fin d) (ZMod p)) :=
    Matrix.GeneralLinearGroup.coe_toLin g
  have hPh : ((Units.coeHom (Module.End (ZMod p) (Fin d → ZMod p))).comp
      Matrix.GeneralLinearGroup.toLin.toMonoidHom) h =
        Matrix.mulVecLin (h : Matrix (Fin d) (Fin d) (ZMod p)) :=
    Matrix.GeneralLinearGroup.coe_toLin h
  rw [hPg, hPh] at key
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
