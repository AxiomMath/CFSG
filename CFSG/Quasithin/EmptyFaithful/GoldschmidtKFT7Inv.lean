module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.ComponentClassification CFSG.Quasithin

@[expose] def r₁S : PSL3Four.S := ⟨PSL3Four.r₁, PSL3Four.r₁_mem_S⟩

theorem card_centralizer_r₁S :
    Nat.card (Subgroup.centralizer ({r₁S} : Set PSL3Four.S)) = 64 := by
  rw [← PSL3Four.card_C₁]
  refine Nat.card_congr
    ⟨fun x => ⟨(x.1 : Equiv.Perm (Fin 42)), Subgroup.mem_inf.mpr ⟨?_, x.1.2⟩⟩,
      fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).2⟩, ?_⟩, fun x => rfl, fun y => rfl⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp x.2
    exact congrArg Subtype.val this
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).1
    exact Subtype.ext this

theorem ncard_conjugatesOf_r₁S :
    (conjugatesOf r₁S).ncard = 315 := by
  rw [← Subgroup.index_centralizer_eq_ncard]
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({r₁S} : Set PSL3Four.S))
  rw [card_centralizer_r₁S, PSL3Four.card_S] at h
  omega

theorem isConj_r₁S_of_involution {y : PSL3Four.S} (hy : y * y = 1)
    (hy1 : y ≠ 1) : IsConj y r₁S := by
  let yR : PSL3Four.R := ⟨y, PSL3Four.S_le_R y.2⟩
  have hord : orderOf yR = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ fun h1 => hy1 (Subtype.ext
      (congrArg (fun z : PSL3Four.R => (z : Equiv.Perm (Fin 42))) h1))
    rw [pow_two]
    exact Subtype.ext (congrArg (fun z : PSL3Four.S => (z : Equiv.Perm (Fin 42))) hy)
  have hconj : IsConj yR PSL3Four.r₁R := by
    rcases (PSL3Four.orderOf_eq_two_iff yR).1 hord with h1 | h1 | h1 | h1
    · exact h1
    · exact absurd y.2 (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₂)
    · exact absurd y.2 (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₃)
    · exact absurd y.2 (PSL3Four.not_mem_S_of_isConj h1 PSL3Four.not_mem_S_r₄)
  have hmem : ∀ x : conjugatesOf r₁S,
      IsConj (Subgroup.inclusion PSL3Four.S_le_R x.1) PSL3Four.r₁R := by
    intro x
    obtain ⟨c, hc⟩ := isConj_iff.mp (x.2 : IsConj r₁S x.1)
    refine isConj_comm.mp (isConj_iff.mpr ⟨Subgroup.inclusion PSL3Four.S_le_R c, ?_⟩)
    have := congrArg (Subgroup.inclusion PSL3Four.S_le_R) hc
    rw [map_mul, map_mul, map_inv] at this
    exact this
  let f : conjugatesOf r₁S → (ConjClasses.mk PSL3Four.r₁R).carrier := fun x =>
    ⟨Subgroup.inclusion PSL3Four.S_le_R x.1, by
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
      exact hmem x⟩
  have hf : Function.Injective f := by
    intro x x' h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (ConjClasses.mk PSL3Four.r₁R).carrier => ((z.1 : PSL3Four.R) :
      Equiv.Perm (Fin 42))) h
  have hcard : Nat.card (ConjClasses.mk PSL3Four.r₁R).carrier ≤ Nat.card (conjugatesOf r₁S) := by
    rw [PSL3Four.conjClass₁.2, Nat.card_coe_set_eq, ncard_conjugatesOf_r₁S]
  obtain ⟨x, hx⟩ := (hf.bijective_of_nat_card_le hcard).2
    ⟨yR, by
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
      exact hconj⟩
  have hxy : x.1 = y := by
    have := congrArg (fun z : (ConjClasses.mk PSL3Four.r₁R).carrier => ((z.1 : PSL3Four.R) :
      Equiv.Perm (Fin 42))) hx
    exact Subtype.ext this
  rw [← hxy]
  exact isConj_comm.mp x.2

theorem isConj_of_involutions_psl34 {X : Type} [Group X]
    (h : IsPSL 3 2 2 X) {a b : X} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    IsConj a b := by
  obtain ⟨e⟩ := PSL3Four.exact_model.2.2.2.1 X h
  have key : ∀ z : X, z * z = 1 → z ≠ 1 → IsConj (e z) r₁S := fun z hz hz1 =>
    isConj_r₁S_of_involution (by rw [← map_mul, hz, map_one])
      (fun h1 => hz1 (e.injective (by rw [h1, map_one])))
  have := MonoidHom.map_isConj e.symm.toMonoidHom ((key a ha ha1).trans (key b hb hb1).symm)
  simpa using this

end CFSG.Quasithin.SBd19F
