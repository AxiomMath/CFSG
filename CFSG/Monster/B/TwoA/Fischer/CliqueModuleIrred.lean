module

public import CFSG.Sporadic.Mathieu.M22

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Sporadic.Mathieu
open scoped commutatorElement

theorem m22a_mul_m22b_ne : m22a * m22b ≠ m22b * m22a := fun h => by
  have h' := congrArg Subtype.val h
  revert h'
  decide

theorem not_forall_mul_comm_M22 :
    ¬∀ g h : CFSG.Blueprint.NativeSporadic.M22, g * h = h * g := fun h =>
  m22a_mul_m22b_ne (h _ _)

theorem commutator_M22 :
    commutator CFSG.Blueprint.NativeSporadic.M22 = ⊤ := by
  have := fam_m22_simplicity.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (commutator CFSG.Blueprint.NativeSporadic.M22) with h | h
  · refine absurd (fun g g' => ?_) not_forall_mul_comm_M22
    have hc : ⁅g, g'⁆ ∈ commutator CFSG.Blueprint.NativeSporadic.M22 := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top g')
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem center_M22 :
    Subgroup.center CFSG.Blueprint.NativeSporadic.M22 = ⊥ := by
  have := fam_m22_simplicity.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center CFSG.Blueprint.NativeSporadic.M22) with h | h
  · exact h
  · refine absurd (fun g g' => ?_) not_forall_mul_comm_M22
    have hg : g ∈ Subgroup.center CFSG.Blueprint.NativeSporadic.M22 := h ▸ Subgroup.mem_top g
    exact (Subgroup.mem_center_iff.1 hg g').symm

section Small

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

theorem natCard_units_end :
    Nat.card (Module.End (ZMod 2) X)ˣ = ∏ i : Fin (Module.finrank (ZMod 2) X),
      (2 ^ Module.finrank (ZMod 2) X - 2 ^ (i : ℕ)) := by
  rw [Nat.card_congr (Units.mapEquiv (LinearMap.toMatrixAlgEquiv
    (Module.finBasis (ZMod 2) X)).toMulEquiv).toEquiv, Matrix.card_GL_field, ZMod.card]

theorem not_eleven_dvd_prod {s : ℕ} (hs : s ≤ 9) : ¬11 ∣ ∏ i : Fin s, (2 ^ s - 2 ^ (i : ℕ)) := by
  intro h
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.1 (by norm_num)) _).1 h
  have key : ∀ s : Fin 10, ∀ i : Fin s, ¬11 ∣ 2 ^ (s : ℕ) - 2 ^ (i : ℕ) := by decide
  exact key ⟨s, by omega⟩ i hi

theorem rep_eq_one_of_finrank_le (hX : Module.finrank (ZMod 2) X ≤ 9)
    (ρ : Representation (ZMod 2) CFSG.Blueprint.NativeSporadic.M22 X)
    (g : CFSG.Blueprint.NativeSporadic.M22) : ρ g = 1 := by
  have := fam_m22_simplicity.2.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · refine absurd ?_ (not_eleven_dvd_prod hX)
    have hinj : Function.Injective ρ.toHomUnits := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : x ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        simpa using congrArg Units.val hx
      rwa [h, Subgroup.mem_bot] at hx'
    have hdvd := Subgroup.card_dvd_of_injective _ hinj
    rw [card_M22, natCard_units_end] at hdvd
    exact dvd_trans (by norm_num) hdvd
  · have hg : g ∈ ρ.ker := h ▸ Subgroup.mem_top g
    exact hg

end Small

section Irreducible

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
  (ρ : Representation (ZMod 2) CFSG.Blueprint.NativeSporadic.M22 X)

@[expose] def restrictRep (U : Submodule (ZMod 2) X) (hU : ∀ g, U ≤ U.comap (ρ g)) :
    Representation (ZMod 2) CFSG.Blueprint.NativeSporadic.M22 U where
  toFun g := (ρ g).restrict fun _ hx => hU g hx
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (by simp)

theorem coe_restrictRep_apply (U : Submodule (ZMod 2) X) (hU : ∀ g, U ≤ U.comap (ρ g)) (g)
    (x : U) : (restrictRep ρ U hU g x : X) = ρ g x := rfl

theorem eq_bot_or_eq_top_of_faithful [FiniteDimensional (ZMod 2) X]
    (hX : Module.finrank (ZMod 2) X = 10)
    (hfaith : ∀ g, ρ g = 1 → g = 1) (U : Submodule (ZMod 2) X) (hU : ∀ g, U ≤ U.comap (ρ g)) :
    U = ⊥ ∨ U = ⊤ := by
  by_contra hne
  rw [not_or] at hne
  have h1 : Module.finrank (ZMod 2) U ≠ 0 := fun h => hne.1 (Submodule.finrank_eq_zero.1 h)
  have h2 : Module.finrank (ZMod 2) U < 10 :=
    hX ▸ Submodule.finrank_lt hne.2
  have hq := Submodule.finrank_quotient_add_finrank U
  have hfix : ∀ g, ∀ u ∈ U, ρ g u = u := fun g u hu => by
    have := congrArg (fun f : Module.End (ZMod 2) U => (f ⟨u, hu⟩ : X))
      (rep_eq_one_of_finrank_le (by omega) (restrictRep ρ U hU) g)
    exact this
  have hsub : ∀ g v, ρ g v - v ∈ U := fun g v => by
    have := congrArg (fun f : Module.End (ZMod 2) (X ⧸ U) => f (U.mkQ v))
      (rep_eq_one_of_finrank_le (by omega) (ρ.quotient U hU) g)
    exact (Submodule.Quotient.eq U).1 this
  have hadd : ∀ g h v, ρ (g * h) v - v = (ρ g v - v) + (ρ h v - v) := fun g h v => by
    have e : ρ h v = v + (ρ h v - v) := by abel
    rw [map_mul, Module.End.mul_apply, e, map_add, hfix g _ (hsub h v)]
    abel
  refine not_forall_mul_comm_M22 fun g h => (commutatorElement_eq_one_iff_mul_comm).1
    (hfaith _ (LinearMap.ext fun v => ?_))
  have e1 := hadd (g * h * g⁻¹) h⁻¹ v
  have e2 := hadd (g * h) g⁻¹ v
  have e3 := hadd g h v
  have e4 := hadd g g⁻¹ v
  have e5 := hadd h h⁻¹ v
  rw [mul_inv_cancel, map_one, Module.End.one_apply, sub_self] at e4 e5
  have key : ρ ⁅g, h⁆ v - v =
      ((ρ g v - v) + (ρ g⁻¹ v - v)) + ((ρ h v - v) + (ρ h⁻¹ v - v)) := by
    rw [commutatorElement_def, e1, e2, e3]
    abel
  rw [← e4, ← e5, add_zero] at key
  rw [Module.End.one_apply]
  exact sub_eq_zero.1 key

end Irreducible

end CFSG.Monster.B.TwoA.Fischer
