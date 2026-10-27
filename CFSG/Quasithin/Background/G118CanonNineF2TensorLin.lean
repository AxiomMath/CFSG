module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2Tensor

open scoped LinearAlgebra.Projectivization

section Basic

variable {F U : Type*} [Field F] [AddCommGroup U] [Module F U]

theorem eq_zero_or_one_of_card_two (hF : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
    exact (huniq a ha).trans (huniq 1 one_ne_zero).symm

theorem eq_one_of_fixed_of_cube (hF : Nat.card F = 2) (h2 : (2 : F) = 0)
    (hk : Module.finrank F U = 2) (g : U ≃ₗ[F] U) (hg3 : g * g * g = 1) {u : U} (hu : u ≠ 0)
    (hgu : g u = u) : g = 1 := by
  have hF' := eq_zero_or_one_of_card_two hF
  obtain ⟨v, hv⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (by omega : 1 < Module.finrank F U) hu
  have hv' := LinearIndependent.pair_iff.1 hv
  let b : Module.Basis (Fin 2) F U :=
    basisOfLinearIndependentOfCardEqFinrank hv (by simp [hk])
  have hb0 : b 0 = u := by simp [b]
  have hb1 : b 1 = v := by simp [b]
  have hsum := b.sum_repr (g v)
  rw [Fin.sum_univ_two, hb0, hb1] at hsum
  set α : F := b.repr (g v) 0 with hα
  set β : F := b.repr (g v) 1 with hβ
  have hβ1 : β = 1 := by
    rcases hF' β with h0 | h1
    · exfalso
      rw [h0, zero_smul, add_zero] at hsum
      have hgv : g v = g (α • u) := by rw [map_smul, hgu, hsum]
      have hvu : v = α • u := g.injective hgv
      have := (hv' α (-1) (by rw [neg_smul, one_smul, ← hvu, add_neg_cancel])).2
      exact one_ne_zero (neg_eq_zero.1 this)
    · exact h1
  rw [hβ1, one_smul] at hsum
  have hggv : g (g v) = v := by
    rw [← hsum, map_add, map_smul, hgu, ← hsum, ← add_assoc, ← add_smul, ← two_mul, h2, zero_mul,
      zero_smul, zero_add]
  have hgg : g * g = 1 := by
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    fin_cases i
    · show g (g (b 0)) = b 0
      rw [hb0, hgu, hgu]
    · show g (g (b 1)) = b 1
      rw [hb1, hggv]
  rw [hgg, one_mul] at hg3
  exact hg3

theorem exists_fixed_of_sq [Nontrivial U] (h2 : (2 : F) = 0) (g : U ≃ₗ[F] U) (hg2 : g * g = 1) :
    ∃ u : U, u ≠ 0 ∧ g u = u := by
  have hgg : ∀ x : U, g (g x) = x := fun x => by
    have h := congrArg (fun k : U ≃ₗ[F] U => k x) hg2
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] using h
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : U)
  by_cases h : g u₀ + u₀ = 0
  · refine ⟨u₀, hu₀, ?_⟩
    have h1 : g u₀ = -u₀ := eq_neg_of_add_eq_zero_left h
    have h3 : u₀ + u₀ = 0 := by rw [← two_smul F u₀, h2, zero_smul]
    rw [h1]
    exact neg_eq_of_add_eq_zero_left h3
  · refine ⟨g u₀ + u₀, h, ?_⟩
    rw [map_add, hgg, add_comm]

theorem fixed_vec_of_smul_eq (hF : Nat.card F = 2) (g : U ≃ₗ[F] U) (P : ℙ F U) (h : g • P = P) :
    ∃ u : U, u ≠ 0 ∧ g u = u := by
  induction P using Projectivization.ind with
  | _ u hu =>
    rw [Projectivization.smul_mk] at h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ hu).1 h
    refine ⟨u, hu, ?_⟩
    rcases eq_zero_or_one_of_card_two hF a with h0 | h1
    · exfalso
      rw [h0, zero_smul] at ha
      apply hu
      have : g u = 0 := ha.symm
      exact g.injective (by rw [this, map_zero])
    · rw [h1, one_smul] at ha
      exact ha.symm

theorem smul_eq_of_fixed_vec (g : U ≃ₗ[F] U) {u : U} (hu : u ≠ 0) (hgu : g u = u) :
    g • Projectivization.mk F u hu = Projectivization.mk F u hu := by
  rw [Projectivization.smul_mk]
  exact (Projectivization.mk_eq_mk_iff' F _ _ _ hu).2 ⟨1, by rw [one_smul]; exact hgu.symm⟩

end Basic

end F2Tensor

end Canon

end G11

end CFSG.Quasithin
