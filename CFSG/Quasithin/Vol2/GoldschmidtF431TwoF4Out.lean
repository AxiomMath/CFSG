module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Data

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.H13.F431 CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Generic

theorem commutator_mem_inner_of_cyclic {D : Type} [Group D] [IsCyclic (Outer D)]
    (x y : MulAut D) : ⁅x, y⁆ ∈ (MulAut.conj : D →* MulAut D).range := by
  have h : ((QuotientGroup.mk ⁅x, y⁆ : Outer D)) = 1 := by
    let _ := IsCyclic.commGroup (α := Outer D)
    simp [commutatorElement_def, mul_comm]
  exact (QuotientGroup.eq_one_iff (N := inner D) _).1 h

theorem odd_card_div_of_outer {D : Type} [Group D] [Finite D] (hcen : Subgroup.center D = ⊥)
    (S : Subgroup (MulAut D)) (hS : (MulAut.conj : D →* MulAut D).range ≤ S)
    (hodd : Odd (Nat.card (Outer D))) : Odd (Nat.card S / Nat.card D) := by
  have hfin : Finite (MulAut D) :=
    Finite.of_injective (fun φ : MulAut D => (φ : D → D)) DFunLike.coe_injective
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hdc : d ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut D => φ g) hd
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcen] at hdc
    exact Subgroup.mem_bot.mp hdc
  have hinn : Nat.card (inner D) = Nat.card D :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h1 : Nat.card D ∣ Nat.card S := hinn ▸ Subgroup.card_dvd_of_le hS
  have h2 : Nat.card S ∣ Nat.card (MulAut D) := Subgroup.card_subgroup_dvd_card S
  have h3 : Nat.card (MulAut D) = Nat.card (Outer D) * Nat.card D := by
    rw [← hinn]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (inner D)
  obtain ⟨m, hm⟩ := h1
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hdvd : m ∣ Nat.card (Outer D) := by
    rw [hm, h3, mul_comm (Nat.card (Outer D))] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hpos h2
  rw [hm, Nat.mul_div_cancel_left _ hpos]
  exact hodd.of_dvd_nat hdvd

end Generic


section Ree

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem outer_gm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsCyclic (Outer (Gm K a)) ∧ Nat.card (Outer (Gm K a)) = 2 * a + 1 := by
  obtain ⟨-, -, -, h4, h5, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  exact ⟨h4, h5⟩

theorem commutator_mem_inner_gm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (x y : MulAut (Gm K a)) : ⁅x, y⁆ ∈ (MulAut.conj : Gm K a →* MulAut (Gm K a)).range := by
  have := (outer_gm ha hK).1
  exact commutator_mem_inner_of_cyclic x y

end Ree

variable (f : ℕ)

theorem f431Out_twistedF4 : F431Out .twistedF4 0 f := by
  intro G _ _ _ _ M1 M2 _ D _ hD E
  obtain ⟨a, K, _, _, _, ha, hfa, hK0, ⟨e⟩⟩ := f4_model_data hD
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK0, hfa]
  have hmodel := f431ModelFacts_f4 f D hD
  have := hmodel.1
  refine odd_card_div_of_outer hmodel.2 E.K (f431Generation_f4 f D hD E.toLieAmalgamExt) ?_
  have h := Nat.card_congr (equivalence e).toEquiv
  rw [h, (outer_gm ha hK).2]
  exact odd_two_mul_add_one a

end CFSG.Quasithin.H13.F431.TwoF4
