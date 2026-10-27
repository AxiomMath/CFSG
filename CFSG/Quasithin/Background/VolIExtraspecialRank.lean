module

public import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule

public section

namespace CFSG.Quasithin.VolI

open Polynomial Module CFSG.LinearAlgebra
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q] {V : Type*} [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem prime_dvd_finrank_centralImage (hp2 : p ≠ 2) {ρ : Representation (ZMod 2) Q V}
    {x y z : Q} (hzc : ∀ g : Q, Commute g z) (hexp : ∀ g : Q, g ^ p = 1)
    (hyx : y⁻¹ * x * y = x * z) : p ∣ finrank (ZMod 2) (centralImage ρ z) := by
  classical
  set d : ℕ → ℕ := fun j => finrank (ZMod 2) (cosetFixed ρ z x j) with hd
  have hEW : ∀ j, cosetFixed ρ z x j ≤ centralImage ρ z := fun j => inf_le_left
  have hstep : ∀ j, d j ≤ d (j + 1) := by
    intro j
    let f : cosetFixed ρ z x j →ₗ[ZMod 2] cosetFixed ρ z x (j + 1) :=
      (ρ y⁻¹).restrict fun w hw => mem_cosetFixed_succ hzc hyx hw
    have hinj : Function.Injective f := by
      intro a b hab
      have h1 := congrArg (fun w : cosetFixed ρ z x (j + 1) => ρ y (w : V)) hab
      simp only [f, LinearMap.restrict_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply] at h1
      exact Subtype.ext h1
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have hmono : ∀ i j, i ≤ j → d i ≤ d j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact ih.trans (hstep j)
  have hper : d p = d 0 := by
    simp only [hd]
    rw [← cosetFixed_add_self hexp 0, zero_add]
  have hconst : ∀ j, j ≤ p → d j = d 0 := fun j hj =>
    le_antisymm ((hmono j p hj).trans hper.le) (hmono 0 j (Nat.zero_le j))
  have hle : ∑ j : Fin p, d j ≤ finrank (ZMod 2) (centralImage ρ z) := by
    have h := sum_finrank_inf_cosetFixed_le (x := x) (ρ := ρ) hp2 hzc hexp
      (S := centralImage ρ z)
    have heq : ∀ j : ℕ, centralImage ρ z ⊓ cosetFixed ρ z x j = cosetFixed ρ z x j :=
      fun j => inf_of_le_right (hEW j)
    have h' : ∑ j : Fin p, finrank (ZMod 2) ↥(centralImage ρ z ⊓ cosetFixed ρ z x j) =
        ∑ j : Fin p, d j :=
      Finset.sum_congr rfl fun j _ => (LinearEquiv.ofEq _ _ (heq j)).finrank_eq
    rw [h'] at h
    exact h
  have hge : finrank (ZMod 2) (centralImage ρ z) ≤ ∑ j : Fin p, d j := by
    let Ψ : (∀ j : Fin p, cosetFixed ρ z x j) →ₗ[ZMod 2] V :=
      ∑ j : Fin p, (cosetFixed ρ z x j).subtype.comp (LinearMap.proj j)
    have hΨ : ∀ s, Ψ s = ∑ j : Fin p, ((s j : cosetFixed ρ z x j) : V) := fun s => by
      simp [Ψ, LinearMap.sum_apply]
    have hW : centralImage ρ z ≤ LinearMap.range Ψ := by
      intro w hw
      refine ⟨fun j => ⟨cosetAverage p ρ z x j w, cosetAverage_mem_cosetFixed hzc hexp j hw⟩, ?_⟩
      rw [hΨ]
      simp only
      rw [Fin.sum_univ_eq_sum_range (fun j => cosetAverage p ρ z x j w) p]
      exact sum_cosetAverage_apply hp2 hzc hexp hw
    calc finrank (ZMod 2) (centralImage ρ z) ≤ finrank (ZMod 2) (LinearMap.range Ψ) :=
          Submodule.finrank_mono hW
      _ ≤ finrank (ZMod 2) (∀ j : Fin p, cosetFixed ρ z x j) := LinearMap.finrank_range_le Ψ
      _ = ∑ j : Fin p, d j := Module.finrank_pi_fintype (ZMod 2)
  have hsum : ∑ j : Fin p, d j = p * d 0 := by
    rw [Finset.sum_congr rfl fun (j : Fin p) _ => hconst j j.2.le, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact ⟨d 0, by omega⟩

theorem sub_one_dvd_finrank_centralImage (hp2 : p ≠ 2) (hord : orderOf (2 : ZMod p) = p - 1)
    {ρ : Representation (ZMod 2) Q V} {z : Q} (hTp : ρ z ^ p = 1) :
    p - 1 ∣ finrank (ZMod 2) (centralImage ρ z) := by
  rcases subsingleton_or_nontrivial (centralImage ρ z) with hW | hW
  · rw [finrank_zero_of_subsingleton]
    exact dvd_zero _
  have hΦ := irreducible_cyclotomic_two hp2 hord
  have hKzero := aeval_centralImageOp_cyclotomic hp2 hTp
  have hK : IsField (centralImageAlgebra ρ z) :=
    isField_adjoin_singleton_of_aeval_eq_zero hΦ _ hKzero
  have hKdim : finrank (ZMod 2) (centralImageAlgebra ρ z) = p - 1 := by
    rw [centralImageAlgebra, finrank_adjoin_singleton_of_aeval_eq_zero hΦ
      (cyclotomic.monic p (ZMod 2)) _ hKzero, natDegree_cyclotomic_two]
  let _ : Field (centralImageAlgebra ρ z) := hK.toField
  have h := Module.finrank_mul_finrank (ZMod 2) (centralImageAlgebra ρ z) (centralImage ρ z)
  rw [hKdim] at h
  exact ⟨_, h.symm⟩

theorem dvd_finrank_centralImage (hp2 : p ≠ 2) (hord : orderOf (2 : ZMod p) = p - 1)
    {ρ : Representation (ZMod 2) Q V} {x y z : Q} (hzc : ∀ g : Q, Commute g z)
    (hexp : ∀ g : Q, g ^ p = 1) (hyx : y⁻¹ * x * y = x * z) :
    p * (p - 1) ∣ finrank (ZMod 2) (centralImage ρ z) := by
  have hTp : ρ z ^ p = 1 := by rw [← map_pow, hexp, map_one]
  have hcop : Nat.Coprime p (p - 1) := by
    have h2 := hp.out.two_le
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  exact hcop.mul_dvd_of_dvd_of_dvd (prime_dvd_finrank_centralImage hp2 hzc hexp hyx)
    (sub_one_dvd_finrank_centralImage hp2 hord hTp)

theorem inv_mul_mul_eq_mul_commutator {x y : Q} (hzc : ∀ g : Q, Commute g ⁅x, y⁆) :
    y⁻¹ * x * y = x * ⁅x, y⁆ := by
  have hzy : y⁻¹ * ⁅x, y⁆ * y = ⁅x, y⁆ := by
    rw [mul_assoc, ← (hzc y).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  calc y⁻¹ * x * y = y⁻¹ * (x * y * x⁻¹ * y⁻¹) * y * x := by group
    _ = ⁅x, y⁆ * x := by rw [← commutatorElement_def, hzy]
    _ = x * ⁅x, y⁆ := ((hzc x).eq).symm

theorem six_dvd_finrank_centralImage {ρ : Representation (ZMod 2) Q V} {x y : Q}
    (hzc : ∀ g : Q, Commute g ⁅x, y⁆) (hexp : ∀ g : Q, g ^ 3 = 1) :
    6 ∣ finrank (ZMod 2) (centralImage ρ ⁅x, y⁆) := by
  have hord : orderOf (2 : ZMod 3) = 3 - 1 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact dvd_finrank_centralImage (p := 3) (by norm_num) hord hzc hexp
    (inv_mul_mul_eq_mul_commutator hzc)

end CFSG.Quasithin.VolI
