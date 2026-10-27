module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.IsPerfect
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic

public section

namespace CFSG.LocalAnalysis

open CFSG.QuasithinUnique.Setup.X7

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {R : Type*} [Group R] [Finite R]

theorem eq_one_of_commute_of_fixes_invariants (hR : IsPGroup p R)
    (σ : Representation (ZMod p) R V) {g : Module.End (ZMod p) V} {m : ℕ}
    (hm : Nat.Coprime m p) (hgm : g ^ m = 1) (hgσ : ∀ r, Commute g (σ r))
    (hgfix : ∀ v ∈ σ.invariants, g v = v) : g = 1 := by
  set N := g - 1 with hN
  have hW : ∀ r, ∀ w ∈ LinearMap.range N, σ r w ∈ LinearMap.range N := by
    rintro r _ ⟨v, rfl⟩
    refine ⟨σ r v, ?_⟩
    rw [hN, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub, ← Module.End.mul_apply, (hgσ r).eq, Module.End.mul_apply]
  set S : Module.End (ZMod p) V := ∑ i ∈ Finset.range m, g ^ i with hS
  have hSN : S * N = 0 := by
    have h := Commute.geom_sum₂_mul (Commute.one_right g) m
    rw [one_pow, hgm, sub_self] at h
    simpa [hS, hN] using h
  by_contra hg1
  have hne : LinearMap.range N ≠ ⊥ := by
    intro h
    apply hg1
    rw [LinearMap.range_eq_bot, hN, sub_eq_zero] at h
    exact h
  obtain ⟨w, ⟨v, rfl⟩, hw0, hwfix⟩ :=
    exists_fixed_mem_of_pGroup (ZMod p) hp.out hR σ _ hW hne
  have hgw : g (N v) = N v := hgfix _ ((σ.mem_invariants _).mpr hwfix)
  have hpow : ∀ i : ℕ, (g ^ i) (N v) = N v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, Module.End.mul_apply, hgw, ih]
  have hSw : S (N v) = (m : ZMod p) • N v := by
    rw [hS, LinearMap.sum_apply]
    simp only [hpow, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have h0 : (m : ZMod p) • N v = 0 := by
    rw [← hSw, ← Module.End.mul_apply, hSN, LinearMap.zero_apply]
  have hm0 : (m : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hdvd
    exact hp.out.one_lt.ne' (hm.symm.eq_one_of_dvd hdvd)
  exact hw0 ((smul_eq_zero.mp h0).resolve_left hm0)

theorem perfect_action_detected_on_p_fixed_points {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (hR : IsPGroup p R) (ρ : Representation (ZMod p) X V)
    (σ : Representation (ZMod p) R V) (hρσ : ∀ x r, Commute (ρ x) (σ r)) :
    (∀ x, ρ x = 1) ↔ ∀ x, ∀ v ∈ σ.invariants, ρ x v = v := by
  constructor
  · intro h x v _
    rw [h x, Module.End.one_apply]
  intro hfix
  have hpow : ∀ x : X, ∃ a : ℕ, ρ (x ^ p ^ a) = 1 := by
    intro x
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p
      hp.out.one_lt.ne'
    refine ⟨a, eq_one_of_commute_of_fixes_invariants hR σ
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hm))) ?_
      (fun r => hρσ _ r) (hfix _)⟩
    rw [← map_pow, ← pow_mul, ← hxm, pow_orderOf_eq_one, map_one]
  set f := ρ.asGroupHom
  have hpg : IsPGroup p f.range := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨a, ha⟩ := hpow x
    refine ⟨a, Subtype.ext (Units.ext ?_)⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one,
      Representation.asGroupHom_apply, ← map_pow, ha]
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isNilpotent f.range hpg.isNilpotent
  intro x
  have h1 : (⟨f x, x, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : f.range => ((u : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V)) h1
  simpa [f, Representation.asGroupHom_apply] using h2

end CFSG.LocalAnalysis
