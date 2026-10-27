module

public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem eq_zero_of_neg_eq_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {v : V}
    (h : -v = v) : v = 0 := by
  have h2 : (2 : ZMod 3) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel v
  calc v = ((2 : ZMod 3) * 2) • v := by rw [show ((2 : ZMod 3) * 2) = 1 from rfl, one_smul]
    _ = (2 : ZMod 3) • ((2 : ZMod 3) • v) := mul_smul _ _ _
    _ = 0 := by rw [h2, smul_zero]

theorem fix_of_pow_prime {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [DecidableEq V]
    (f : V →ₗ[ZMod 3] V) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : ∀ v, f^[p] v = v)
    (S : Finset V) (hS : ∀ v ∈ S, f v ∈ S) (hneg : ∀ v ∈ S, -v ∈ S) (hcard : S.card ≤ 9)
    (h0 : (0 : V) ∈ S) {v : V} (hv : v ∈ S) : f v = v := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have ha := hf a
    have hb := hf b
    rw [hq, Function.iterate_succ_apply] at ha hb
    rw [← ha, ← hb, hab]
  set N := S.filter (fun x => f x ≠ x) with hN
  have hNf : ∀ x ∈ N, f x ∈ N := by
    intro x hx
    rw [hN, Finset.mem_filter] at hx ⊢
    exact ⟨hS x hx.1, fun h => hx.2 (hinj h)⟩
  let F : Function.End ↥N := fun y => ⟨f y, hNf y y.2⟩
  have hFpow : ∀ (j : ℕ) (x : ↥N), (((F ^ j) x : ↥N) : V) = f^[j] x := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ', Function.iterate_succ_apply', ← ih]
      rfl
  have hFp : F ^ p ^ 1 = 1 := by
    funext x
    rw [pow_one]
    exact Subtype.ext ((hFpow p x).trans (hf x))
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥N) hFp
  have hfix0 : Fintype.card ↥(Function.fixedPoints F) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    have h := x.2
    have h' : f (x.1 : V) = x.1 := congrArg Subtype.val h
    have hx : (x.1 : V) ∈ S.filter (fun x => f x ≠ x) := x.1.2
    rw [Finset.mem_filter] at hx
    exact hx.2 h'
  rw [hfix0, Fintype.card_coe] at hmod
  have hNmod : p ∣ N.card := Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hmod)
  have hNneg : ∀ x ∈ N, -x ∈ N := by
    intro x hx
    rw [hN, Finset.mem_filter] at hx ⊢
    refine ⟨hneg x hx.1, fun h => hx.2 ?_⟩
    rw [map_neg] at h
    exact neg_injective h
  let Ng : Function.End ↥N := fun y => ⟨-y, hNneg y y.2⟩
  have hNg : Ng ^ 2 ^ 1 = 1 := by
    funext x
    rw [pow_one, pow_two]
    exact Subtype.ext (neg_neg _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod2 := Equiv.Perm.card_fixedPoints_modEq (α := ↥N) hNg
  have hfix2 : Fintype.card ↥(Function.fixedPoints Ng) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    have h := x.2
    have h' : -(x.1 : V) = x.1 := congrArg Subtype.val h
    have h0x : (x.1 : V) = 0 := eq_zero_of_neg_eq_self h'
    have hx : (x.1 : V) ∈ S.filter (fun x => f x ≠ x) := x.1.2
    rw [Finset.mem_filter, h0x, map_zero] at hx
    exact hx.2 rfl
  rw [hfix2, Fintype.card_coe] at hmod2
  have hN2 : 2 ∣ N.card := Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hmod2)
  have hNle : N.card ≤ 8 := by
    have h0N : (0 : V) ∉ N := by simp [hN]
    have hsub : N ⊆ S.erase 0 := fun x hx => by
      rw [Finset.mem_erase]
      exact ⟨fun h => h0N (h ▸ hx), (Finset.mem_filter.mp hx).1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem h0] at this
    omega
  have hN0 : N.card = 0 := by
    have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    have h2p : p * 2 ∣ N.card := hcop.mul_dvd_of_dvd_of_dvd hNmod hN2
    exact Nat.eq_zero_of_dvd_of_lt h2p (by omega)
  by_contra hne
  have hvN : v ∈ N := by rw [hN, Finset.mem_filter]; exact ⟨hv, hne⟩
  rw [Finset.card_eq_zero] at hN0
  rw [hN0] at hvN
  exact absurd hvN (Finset.notMem_empty v)

theorem mulVec_fix_of_commute {k : ℕ} {m σ : GL (Fin k) (ZMod 3)} {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hm : m ^ p = 1) (hcomm : σ * m = m * σ) {e w : Fin k → ZMod 3}
    (he : (σ : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ e = e)
    (hfix : ∀ v, (σ : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v = v → ∃ c d : ZMod 3,
      v = c • e + d • w) :
    (m : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ e = e := by
  set S : Finset (Fin k → ZMod 3) :=
    ((Finset.univ : Finset (ZMod 3 × ZMod 3)).image fun cd => cd.1 • e + cd.2 • w).filter
      fun v => Matrix.mulVec σ.val v = v with hSdef
  have hmemS : ∀ v, v ∈ S ↔ σ.val *ᵥ v = v := by
    intro v
    rw [hSdef, Finset.mem_filter, Finset.mem_image]
    constructor
    · exact fun h => h.2
    · intro h
      obtain ⟨c, d, rfl⟩ := hfix v h
      exact ⟨⟨(c, d), Finset.mem_univ _, rfl⟩, h⟩
  have hσm : ∀ v, σ.val *ᵥ (m.val *ᵥ v) =
      m.val *ᵥ (σ.val *ᵥ v) := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hcomm]
  have hcard : S.card ≤ 9 := by
    refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card]
  let f : (Fin k → ZMod 3) →ₗ[ZMod 3] (Fin k → ZMod 3) :=
    Matrix.toLin' m.val
  have hfpow : ∀ j : ℕ, ∀ v, f^[j] v = (m ^ j).val *ᵥ v := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec]
      rfl
  refine fix_of_pow_prime f hp hp5 (fun v => by rw [hfpow, hm]; simp) S ?_ ?_ hcard ?_
    ((hmemS e).mpr he)
  · intro v hv
    rw [hmemS] at hv ⊢
    show σ.val *ᵥ (m.val *ᵥ v) = m.val *ᵥ v
    rw [hσm, hv]
  · intro v hv
    rw [hmemS] at hv ⊢
    rw [Matrix.mulVec_neg, hv]
  · rw [hmemS, Matrix.mulVec_zero]

theorem inv_of_centralizer_trivial {Γ : Type} [Group Γ] {X M : Subgroup Γ}
    (hMn : ∀ g ∈ X, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hMc : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    {σ : Γ} (hσ : σ ∈ X) (hσ2 : σ * σ = 1) (hC : ∀ m ∈ M, σ * m = m * σ → m = 1)
    {m : Γ} (hm : m ∈ M) : σ * m * σ⁻¹ = m⁻¹ := by
  set c := σ * m * σ⁻¹ with hc
  have hcm : σ * c * σ⁻¹ = m := by
    rw [hc, show σ * (σ * m * σ⁻¹) * σ⁻¹ = (σ * σ) * m * (σ * σ)⁻¹ by group, hσ2]
    group
  have hcM : c ∈ M := hMn σ hσ m hm
  have hyM : m * c ∈ M := M.mul_mem hm hcM
  have hcomm : σ * (m * c) = m * c * σ := by
    have h1 : σ * (m * c) * σ⁻¹ = c * m := by
      rw [show σ * (m * c) * σ⁻¹ = (σ * m * σ⁻¹) * (σ * c * σ⁻¹) by group, hcm]
    have h2 : c * m = m * c := hMc c hcM m hm
    calc σ * (m * c) = σ * (m * c) * σ⁻¹ * σ := by group
      _ = m * c * σ := by rw [h1, h2]
  exact eq_inv_of_mul_eq_one_right (hC _ hyM hcomm)

end CFSG.StandardType.FrameRoute.FS81

end
