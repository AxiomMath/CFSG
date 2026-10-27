module

public import Mathlib.LinearAlgebra.Semisimple

public section

namespace CFSG.Quasithin.SimsG45

open Polynomial

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

namespace OddAux

theorem bilin_symm [CharP F 2] (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (x y : V) :
    B y x = B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  have h' : B y x = -B x y := by linear_combination h
  rw [h']
  exact CharTwo.neg_eq (B x y)

theorem isSemisimple_transv_mul [CharP F 2] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) {u w : V} {c d : F} (hc : c ≠ 0) (hd : d ≠ 0)
    {a b : Module.End F V}
    (ha : ∀ v, a v = v + (c * B v u) • u) (hb : ∀ v, b v = v + (d * B v w) • w)
    (huw : B u w ≠ 0) : Module.End.IsSemisimple (a * b) := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨e, he⟩ : ∃ e, e = B u w := ⟨_, rfl⟩
  have he0 : e ≠ 0 := he ▸ huw
  have hwu : B w u = e := by rw [bilin_symm B halt u w, he]
  obtain ⟨t, ht⟩ : ∃ t, t = c * d * e ^ 2 := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := by
    rw [ht]
    exact mul_ne_zero (mul_ne_zero hc hd) (pow_ne_zero 2 he0)
  have hau : a u = u := by rw [ha u, halt u, mul_zero, zero_smul, add_zero]
  have haw : a w = w + (c * e) • u := by rw [ha w, hwu]
  have hbu : b u = u + (d * e) • w := by rw [hb u, he]
  have hbw : b w = w := by rw [hb w, halt w, mul_zero, zero_smul, add_zero]
  have hGu : (a * b) u = (1 + t) • u + (d * e) • w := by
    rw [Module.End.mul_apply, hbu, map_add, map_smul, hau, haw, ht]
    module
  have hGw : (a * b) w = w + (c * e) • u := by
    rw [Module.End.mul_apply, hbw, haw]
  have hgv : ∀ v, (a * b) v - v = (c * B (b v) u) • u + (d * B v w) • w := by
    intro v
    rw [Module.End.mul_apply, ha (b v)]
    linear_combination (norm := module) hb v
  obtain ⟨s, hs⟩ : ∃ s : F, s = 2 + t := ⟨_, rfl⟩
  have hQu : (a * b) ((a * b) u) - s • (a * b) u + u = 0 := by
    simp only [hGu, hGw, map_add, map_smul]
    rw [hs, ht]
    module
  have hQw : (a * b) ((a * b) w) - s • (a * b) w + w = 0 := by
    simp only [hGu, hGw, map_add, map_smul]
    rw [hs, ht]
    module
  have hC2 : (C (2 : F) : F[X]) = 0 := by rw [h2, map_zero]
  have h2X : (2 : F[X]) = 0 := by rw [← map_ofNat C 2, h2, map_zero]
  have hCt : C t⁻¹ * C t = 1 := by rw [← C_mul, inv_mul_cancel₀ ht0, C_1]
  have hCs : (C s : F[X]) = 2 + C t := by rw [hs, map_add, map_ofNat]
  obtain ⟨Q, hQ⟩ : ∃ Q : F[X], Q = X ^ 2 - C s * X + 1 := ⟨_, rfl⟩
  have hdQ : derivative Q = -C t := by
    rw [hQ, hCs]
    simp
    linear_combination (X - 1) * h2X
  have hQsep : Q.Separable := by
    rw [separable_def', hdQ]
    exact ⟨0, -C t⁻¹, by linear_combination hCt⟩
  have hX1 : (X - 1 : F[X]).Separable := by
    have := separable_X_sub_C (R := F) (x := 1)
    rwa [map_one] at this
  have hcop : IsCoprime Q (X - 1) := by
    refine ⟨-C t⁻¹, C t⁻¹ * (X + 1 - (2 + C t)), ?_⟩
    rw [hQ, hCs]
    linear_combination hCt
  have hsq : Squarefree (Q * (X - 1)) := (hQsep.mul hX1 hcop).squarefree
  have hQop : ∀ x, aeval (a * b) Q x = (a * b) ((a * b) x) - s • (a * b) x + x := by
    intro x
    simp [hQ, sq]
  have hQu' : aeval (a * b) Q u = 0 := by
    rw [hQop]
    exact hQu
  have hQw' : aeval (a * b) Q w = 0 := by
    rw [hQop]
    exact hQw
  have hp : aeval (a * b) (Q * (X - 1)) = 0 := by
    ext v
    have h1 : aeval (a * b) (X - 1 : F[X]) v = (a * b) v - v := by simp
    rw [map_mul, Module.End.mul_apply, h1, hgv v, map_add, map_smul, map_smul, hQu', hQw']
    simp
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hp

theorem odd_orderOf_of_isSemisimple [CharP F 2] [FiniteDimensional F V] [Finite (V ≃ₗ[F] V)]
    (g : V ≃ₗ[F] V) (hg : Module.End.IsSemisimple (g : Module.End F V)) : Odd (orderOf g) := by
  classical
  by_contra hodd
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have heven : 2 ∣ orderOf g := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have hord : orderOf (g ^ (orderOf g / 2)) = 2 := orderOf_pow_orderOf_div hpos heven
  obtain ⟨h, hh⟩ : ∃ h : V ≃ₗ[F] V, h = g ^ (orderOf g / 2) := ⟨_, rfl⟩
  rw [← hh] at hord
  have hsq : h * h = 1 := by
    have := pow_orderOf_eq_one h
    rwa [hord, pow_two] at this
  have hne : h ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hHpow : (h : Module.End F V) = (g : Module.End F V) ^ (orderOf g / 2) := by
    rw [hh]
    exact map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom g _
  have hHss : Module.End.IsSemisimple (h : Module.End F V) := by
    rw [hHpow]
    exact hg.pow _
  have hH1ss : Module.End.IsSemisimple ((h : Module.End F V) - 1) := by
    have := (Module.End.isSemisimple_sub_algebraMap_iff (μ := (1 : F))).mpr hHss
    simpa using this
  have h2v : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul F x, CharTwo.two_eq_zero (R := F), zero_smul]
  have hv : ∀ v, h (h v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hsq]
    rfl
  have hnil : IsNilpotent ((h : Module.End F V) - 1) := by
    refine ⟨2, ?_⟩
    ext v
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, map_sub,
      Module.End.one_apply, LinearMap.zero_apply, LinearEquiv.coe_coe, hv]
    linear_combination (norm := module) (h2v v) - (h2v (h v))
  have hzero := Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hH1ss
  apply hne
  ext v
  have := LinearMap.congr_fun hzero v
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply,
    LinearEquiv.coe_coe] at this
  exact sub_eq_zero.mp this

end OddAux

theorem odd_orderOf_transv_mul [Finite F] [CharP F 2] (B : LinearMap.BilinForm F V)
    (hfin : Module.finrank F V = 4) (halt : ∀ x, B x x = 0)
    {u w : V} {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) {a b : V ≃ₗ[F] V}
    (ha : ∀ v, a v = v + (c * B v u) • u) (hb : ∀ v, b v = v + (d * B v w) • w)
    (huw : B u w ≠ 0) : Odd (orderOf (a * b)) := by
  haveI : Module.Finite F V := Module.finite_of_finrank_pos (by omega)
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V)) DFunLike.coe_injective
  refine OddAux.odd_orderOf_of_isSemisimple (a * b) ?_
  exact OddAux.isSemisimple_transv_mul B halt hc hd (a := (a : Module.End F V))
    (b := (b : Module.End F V)) ha hb huw

end CFSG.Quasithin.SimsG45
