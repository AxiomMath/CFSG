module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCLinearDegree

public section

namespace CFSG.StandardType.RCKC1

theorem rckIIp_sq_eq_one_of_pow_eq_one_GL {F ι : Type} [Field F] [CharP F 2] [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι = 2) {g : GL ι F} {a : ℕ} (hg : g ^ (2 ^ a) = 1) :
    g ^ 2 = 1 := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let M : Matrix ι ι F := (g : Matrix ι ι F)
  have hM : M ^ (2 ^ a) = 1 := by
    have := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hg
    simpa [M] using this
  have hnil : IsNilpotent (M - 1) := by
    refine ⟨2 ^ a, ?_⟩
    rw [sub_pow_char_pow_of_commute 2 a (Commute.one_right M), hM, one_pow, sub_self]
  have hzero : (M - 1) ^ 2 = 0 := by
    have h :=
      CFSG.ComponentClassification.UnbalancedGS.LinearDegree.pow_card_eq_zero_of_isNilpotent hnil
    rwa [hι] at h
  have hsq : (M - 1) ^ 2 = M ^ 2 - 1 := by
    have h := sub_pow_char_of_commute (p := 2) (Commute.one_right M)
    simpa using h
  have hM2 : M ^ 2 = 1 := by
    rw [hsq] at hzero
    exact sub_eq_zero.mp hzero
  apply Units.ext
  show (g : Matrix ι ι F) ^ 2 = 1
  simpa [M] using hM2

theorem rckIIp_card_range_of_alt_eight {X : Type} [Group X] {G : Type} [Group G] (π : G →* X)
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    Nat.card ↥π.range = 20160 * Nat.card (Subgroup.center ↥π.range) := by
  obtain ⟨eA⟩ := hA8
  have hA8card : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
    rw [Nat.card_perm, Nat.card_fin] at h
    have h8 : (8 : ℕ).factorial = 40320 := by decide
    omega
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥π.range)
  rw [Nat.card_congr eA.toEquiv, hA8card] at h
  exact h

theorem rckIIp_false_of_alt_eight_of_sq_eq_one {G X : Type} [Group G] [Finite G] [Group X]
    (h2 : ∀ (g : G) (a : ℕ), g ^ (2 ^ a) = 1 → g ^ 2 = 1) (π : G →* X)
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    False := by
  classical
  obtain ⟨eA⟩ := hA8
  let τ : alternatingGroup (Fin 8) :=
    ⟨c[0, 1, 2, 3] * Equiv.swap 4 5, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel⟩
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    revert h'
    decide +kernel
  have hτ4 : τ ^ 4 = 1 := Subtype.ext (by decide +kernel)
  have hτord : orderOf τ = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := τ)
      (by simpa using hτ2) (by simpa using hτ4)
    simpa using h
  let ψ : G →* alternatingGroup (Fin 8) :=
    eA.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥π.range)).comp π.rangeRestrict)
  have hψsurj : Function.Surjective ψ :=
    eA.surjective.comp ((QuotientGroup.mk'_surjective _).comp π.rangeRestrict_surjective)
  obtain ⟨g, hg⟩ := hψsurj τ
  obtain ⟨a, b, hb, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hgb : (g ^ b) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, mul_comm b (2 ^ a), ← hord, pow_orderOf_eq_one]
  have hgb2 : (g ^ b) ^ 2 = 1 := h2 (g ^ b) a hgb
  have hψgb : ψ (g ^ b) = τ ^ b := by rw [map_pow, hg]
  have htau : τ ^ (2 * b) = 1 := by
    have h := congrArg ψ hgb2
    rw [map_pow, hψgb, map_one, ← pow_mul, mul_comm b 2] at h
    exact h
  have hdvd : 4 ∣ 2 * b := by
    rw [← hτord]
    exact orderOf_dvd_of_pow_eq_one htau
  obtain ⟨c, rfl⟩ := hb
  obtain ⟨d, hd⟩ := hdvd
  omega

theorem rckIIp_false_of_alt_eight_of_GL_two {G X F ι : Type} [Group G] [Finite G] [Group X]
    [Field F] [CharP F 2] [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 2)
    (j : G →* GL ι F) (hj : Function.Injective j) (π : G →* X)
    (hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8))) :
    False := by
  refine rckIIp_false_of_alt_eight_of_sq_eq_one (h2 := ?_) π hA8
  intro g a hg
  have hpow : (j g) ^ (2 ^ a) = 1 := by
    rw [← map_pow, hg, map_one]
  have hsq : (j g) ^ 2 = 1 := rckIIp_sq_eq_one_of_pow_eq_one_GL hι hpow
  exact hj (by rw [map_pow, map_one]; exact hsq)

end CFSG.StandardType.RCKC1
