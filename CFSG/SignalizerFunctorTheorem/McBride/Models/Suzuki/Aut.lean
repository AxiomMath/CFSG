module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LieType.Suzuki.SuzukiOuterCyclic
import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut
import CFSG.SignalizerFunctorTheorem.McBride.Models.Transport
import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge

public section

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.SignalizerFunctorTheorem.NearModels
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.SzModel

variable {n : ℕ}

theorem outer_isCyclic_card_dvd (hn : 1 ≤ n) :
    IsCyclic (Outer (Sz n)) ∧ Nat.card (Outer (Sz n)) ∣ 2 * n + 1 := by
  obtain ⟨E⟩ := Suzuki.nonempty_mulEquiv_sz_suzukiGroup n
  have hK : Nat.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) :=
    GaloisField.card 2 (2 * n + 1) (by omega)
  obtain ⟨h1, h2⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd hn hK
  refine ⟨((CFSG.ComponentClassification.OuterAutomorphisms.equivalence E).isCyclic).mpr h1, ?_⟩
  rwa [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence E).toEquiv]
    at h2

theorem exists_conj_of_coprime_orderOf
    (hn : 1 ≤ n) (g : MulAut (Sz n))
    (hg : Nat.Coprime (2 * n + 1) (orderOf g)) : ∃ x : Sz n, g = MulAut.conj x := by
  let π : MulAut (Sz n) →* Outer (Sz n) := QuotientGroup.mk' (inner (Sz n))
  have h1 : orderOf (π g) ∣ orderOf g := orderOf_map_dvd π g
  have h2 : orderOf (π g) ∣ 2 * n + 1 :=
    (orderOf_dvd_natCard _).trans (outer_isCyclic_card_dvd hn).2
  have h := Nat.dvd_gcd h2 h1
  rw [hg.gcd_eq_one] at h
  have h3 : π g = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  obtain ⟨x, hx⟩ := h3
  exact ⟨x, hx.symm⟩

theorem perfect_le_inner
    (hn : 1 ≤ n) (P : Subgroup (MulAut (Sz n))) (hP : Group.IsPerfect P) :
    P ≤ (MulAut.conj : Sz n →* MulAut (Sz n)).range := by
  have hcyc := (outer_isCyclic_card_dvd hn).1
  let π : MulAut (Sz n) →* Outer (Sz n) := QuotientGroup.mk' (inner (Sz n))
  have hcomm : ∀ a b : MulAut (Sz n), ⁅a, b⁆ ∈ inner (Sz n) := by
    intro a b
    rw [← QuotientGroup.eq_one_iff (N := inner (Sz n)), ← QuotientGroup.mk'_apply,
      map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (IsCyclic.commGroup (α := Outer (Sz n))).mul_comm _ _
  have hle : ⁅P, P⁆ ≤ inner (Sz n) := Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
  rwa [Subgroup.commutator_eq_self] at hle

theorem exists_aut
    (hp : (2 * n + 1).Prime) : ∃ f : MulAut (Sz n), orderOf f = 2 * n + 1 := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact Nat.not_prime_one hp)
  obtain ⟨E⟩ := Suzuki.nonempty_mulEquiv_sz_suzukiGroup n
  have hK : Nat.card (GaloisField 2 (2 * n + 1)) = 2 ^ (2 * n + 1) :=
    GaloisField.card 2 (2 * n + 1) (by omega)
  obtain ⟨σ, -, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK
  have hφ : orderOf (Suzuki.szFieldAut n (GaloisField 2 (2 * n + 1)) σ) = 2 * n + 1 := by
    rw [orderOf_injective _ Suzuki.szFieldAut_injective σ, hord]
  exact ⟨MulAut.congr E.symm (Suzuki.szFieldAut n _ σ), by rw [orderOf_congr, hφ]⟩

end CFSG.SignalizerFunctorTheorem.McBride.SzModel
