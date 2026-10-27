module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.Quasithin.A10

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

theorem perm6_cent : ∀ σ : Equiv.Perm (Fin 6),
    σ * (Equiv.swap 0 1 * Equiv.swap 1 2) = (Equiv.swap 0 1 * Equiv.swap 1 2) * σ →
    σ * (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) =
      (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) * σ → σ = 1 := by
  decide +kernel

theorem three_cycle_mem : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 6) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 6) ≠ 2 by decide)]
  decide

theorem five_cycle_mem :
    (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) ∈
      alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (show (0 : Fin 6) ≠ 1 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 6) ≠ 2 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 6) ≠ 3 by decide),
    Equiv.Perm.sign_swap (show (3 : Fin 6) ≠ 4 by decide)]
  decide

@[expose] noncomputable def swapAut : MulAut (alternatingGroup (Fin 6)) :=
  MulAut.conjNormal (Equiv.swap (0 : Fin 6) 1)

theorem swapAut_apply (x : alternatingGroup (Fin 6)) :
    ((swapAut x : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
      Equiv.swap 0 1 * (x : Equiv.Perm (Fin 6)) * (Equiv.swap 0 1)⁻¹ :=
  MulAut.conjNormal_apply _ _

theorem swapAut_sq : swapAut ^ 2 = 1 := by
  unfold swapAut
  rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]

theorem swapAut_not_inner : swapAut ∉ inner (alternatingGroup (Fin 6)) := by
  rintro ⟨a, ha⟩
  have key : ∀ x : alternatingGroup (Fin 6),
      (a : Equiv.Perm (Fin 6)) * (x : Equiv.Perm (Fin 6)) * (a : Equiv.Perm (Fin 6))⁻¹ =
        Equiv.swap 0 1 * (x : Equiv.Perm (Fin 6)) * (Equiv.swap 0 1)⁻¹ := by
    intro x
    have h := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) =>
      ((φ x : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) ha
    simp only [swapAut_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hcomm : ∀ x : alternatingGroup (Fin 6),
      ((Equiv.swap 0 1)⁻¹ * (a : Equiv.Perm (Fin 6))) * (x : Equiv.Perm (Fin 6)) =
        (x : Equiv.Perm (Fin 6)) * ((Equiv.swap 0 1)⁻¹ * (a : Equiv.Perm (Fin 6))) := by
    intro x
    have h := key x
    calc ((Equiv.swap 0 1)⁻¹ * (a : Equiv.Perm (Fin 6))) * (x : Equiv.Perm (Fin 6))
        = (Equiv.swap 0 1)⁻¹ * ((a : Equiv.Perm (Fin 6)) * (x : Equiv.Perm (Fin 6)) *
            (a : Equiv.Perm (Fin 6))⁻¹) * (a : Equiv.Perm (Fin 6)) := by group
      _ = (Equiv.swap 0 1)⁻¹ * (Equiv.swap 0 1 * (x : Equiv.Perm (Fin 6)) *
            (Equiv.swap 0 1)⁻¹) * (a : Equiv.Perm (Fin 6)) := by rw [h]
      _ = (x : Equiv.Perm (Fin 6)) * ((Equiv.swap 0 1)⁻¹ * (a : Equiv.Perm (Fin 6))) := by group
  have h1 := perm6_cent ((Equiv.swap 0 1)⁻¹ * (a : Equiv.Perm (Fin 6)))
    (hcomm ⟨_, three_cycle_mem⟩) (hcomm ⟨_, five_cycle_mem⟩)
  have h2 : (a : Equiv.Perm (Fin 6)) = Equiv.swap 0 1 := by
    have : Equiv.swap (0 : Fin 6) 1 * ((Equiv.swap 0 1)⁻¹ * (a : Equiv.Perm (Fin 6))) =
        Equiv.swap 0 1 * 1 := by rw [h1]
    simpa using this
  have h3 : (Equiv.swap (0 : Fin 6) 1) ∈ alternatingGroup (Fin 6) := h2 ▸ a.2
  rw [Equiv.Perm.mem_alternatingGroup,
    Equiv.Perm.sign_swap (show (0 : Fin 6) ≠ 1 by decide)] at h3
  exact absurd h3 (by decide)

theorem two_dvd_card_outer_alternating_six :
    2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
  let b : Outer (alternatingGroup (Fin 6)) := QuotientGroup.mk swapAut
  have hb1 : b ≠ 1 := fun h => swapAut_not_inner ((QuotientGroup.eq_one_iff _).1 h)
  have hb2 : b ^ 2 = 1 := by
    show (QuotientGroup.mk swapAut : Outer (alternatingGroup (Fin 6))) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, swapAut_sq]
    rfl
  have hord : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  rw [← hord]
  exact orderOf_dvd_natCard b

theorem finite_outer {X : Type*} [Group X] [Finite X] : Finite (Outer X) := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun σ : MulAut X => (σ : X → X)) (fun σ τ hστ => MulEquiv.ext
      (fun x => congrFun hστ x))
  exact Quotient.finite _

theorem three_not_dvd_card_outer {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Finite (Outer X) := finite_outer
  have hle := outer_card_le_four_of_equiv e
  have h2 : 2 ∣ Nat.card (Outer X) := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact two_dvd_card_outer_alternating_six
  intro h3
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  have h6 : 6 ∣ Nat.card (Outer X) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have := Nat.le_of_dvd hpos h6
  omega

theorem mem_inner_of_pow_three {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6))
    {γ : MulAut X} (hγ : γ ^ 3 = 1) : γ ∈ inner X := by
  have hOut := three_not_dvd_card_outer e
  let b : Outer X := QuotientGroup.mk γ
  have hb3 : b ^ 3 = 1 := by
    show (QuotientGroup.mk γ : Outer X) ^ 3 = 1
    rw [← QuotientGroup.mk_pow, hγ]
    rfl
  have hd : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
  have hd' : orderOf b ∣ Nat.card (Outer X) := orderOf_dvd_natCard b
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
  · exact (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
  · exact absurd (h3 ▸ hd') hOut

end CFSG.Quasithin.A10
