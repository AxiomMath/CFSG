module

public import CFSG.Timmesfeld.ARS.Sec3Natural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule Matrix

namespace FrameSL3

variable {K : Type*} [Field K] {G : Type*} [Group G] {X : Subgroup G}

section Par

variable (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K)

@[expose] def upPar (t : K) : G := ((φ.symm (upperElt K t) : X) : G)

@[expose] def lowPar (t : K) : G := ((φ.symm (lowerElt K t) : X) : G)

@[expose] def torPar (c : Kˣ) : G := ((φ.symm (diagElt c) : X) : G)

theorem upPar_add (s t : K) : upPar φ (s + t) = upPar φ s * upPar φ t := by
  simp only [upPar, ← upperElt_mul, map_mul, Subgroup.coe_mul]

theorem lowPar_add (s t : K) : lowPar φ (s + t) = lowPar φ s * lowPar φ t := by
  simp only [lowPar, ← lowerElt_mul, map_mul, Subgroup.coe_mul]

theorem upPar_injective : Function.Injective (upPar φ) := fun _ _ h =>
  upperElt_injective K (φ.symm.injective (Subtype.ext h))

theorem lowPar_injective : Function.Injective (lowPar φ) := fun _ _ h =>
  lowerElt_injective K (φ.symm.injective (Subtype.ext h))

theorem upPar_zero : upPar φ 0 = 1 := by
  simp [upPar, upperElt_zero]

theorem lowPar_zero : lowPar φ 0 = 1 := by
  simp [lowPar, lowerElt_zero]

theorem torPar_conj_upPar (c : Kˣ) (t : K) :
    torPar φ c * upPar φ t * (torPar φ c)⁻¹ = upPar φ ((c : K) ^ 2 * t) := by
  have h : diagElt c * upperElt K t * (diagElt c)⁻¹ = upperElt K ((c : K) ^ 2 * t) := by
    rw [diagElt_mul_upperElt, mul_inv_cancel_right]
  simp only [torPar, upPar, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul, h]

end Par

section ParMem

variable {φ : ↥X ≃* SpecialLinearGroup (Fin 2) K} {P Q : Subgroup G}

theorem upPar_mem (hP : (P.subgroupOf X).map φ.toMonoidHom = upperUnipotent K) (t : K) :
    upPar φ t ∈ P :=
  (NaturalModule.coe_mem_iff hP _).2 (by
    rw [MulEquiv.apply_symm_apply]
    exact (mem_upperUnipotent_iff K).2 ⟨t, rfl⟩)

theorem exists_upPar_eq (hP : (P.subgroupOf X).map φ.toMonoidHom = upperUnipotent K)
    (hPX : P ≤ X) {a : G} (ha : a ∈ P) : ∃ t, upPar φ t = a := by
  obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff K).1
    ((NaturalModule.coe_mem_iff hP ⟨a, hPX ha⟩).1 ha)
  refine ⟨t, ?_⟩
  rw [upPar, ← ht, MulEquiv.symm_apply_apply]

theorem lowPar_mem (hQ : (Q.subgroupOf X).map φ.toMonoidHom = lowerUnipotent K) (t : K) :
    lowPar φ t ∈ Q :=
  (NaturalModule.coe_mem_iff hQ _).2 (by
    rw [MulEquiv.apply_symm_apply]
    exact (mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩)

theorem exists_lowPar_eq (hQ : (Q.subgroupOf X).map φ.toMonoidHom = lowerUnipotent K)
    (hQX : Q ≤ X) {a : G} (ha : a ∈ Q) : ∃ t, lowPar φ t = a := by
  obtain ⟨t, ht⟩ := (mem_lowerUnipotent_iff K).1
    ((NaturalModule.coe_mem_iff hQ ⟨a, hQX ha⟩).1 ha)
  refine ⟨t, ?_⟩
  rw [lowPar, ← ht, MulEquiv.symm_apply_apply]

end ParMem

theorem lowerElt_mulVec_sub (t : K) (v : Fin 2 → K) :
    (lowerElt K t : Matrix (Fin 2) (Fin 2) K) *ᵥ v - v = ![0, t * v 0] := by
  rw [lowerElt_mulVec]
  ext i
  fin_cases i <;> simp

theorem weylElt_mulVec [CharP K 2] (v : Fin 2 → K) :
    (weylElt K : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 1, v 0] := by
  ext i
  fin_cases i <;> simp [coe_weylElt, mulVec, dotProduct, Fin.sum_univ_two]

section Module

variable {φ : ↥X ≃* SpecialLinearGroup (Fin 2) K} {θ : (Fin 2 → K) → G}
  (hθ : IsNaturalModule φ θ)
include hθ

theorem commutatorElement_upPar (t : K) (v : Fin 2 → K) :
    ⁅upPar φ t, θ v⁆ = θ ![t * v 1, 0] := by
  rw [upPar, hθ.commutatorElement_eq, MulEquiv.apply_symm_apply, upperElt_mulVec_sub]

theorem commutatorElement_lowPar (t : K) (v : Fin 2 → K) :
    ⁅lowPar φ t, θ v⁆ = θ ![0, t * v 0] := by
  rw [lowPar, hθ.commutatorElement_eq, MulEquiv.apply_symm_apply, lowerElt_mulVec_sub]

theorem torPar_conj (c : Kˣ) (v : Fin 2 → K) :
    torPar φ c * θ v * (torPar φ c)⁻¹ = θ ![(c : K) * v 0, ((c⁻¹ : Kˣ) : K) * v 1] := by
  rw [torPar, ← hθ.map_mulVec, MulEquiv.apply_symm_apply, diagElt_mulVec]

theorem map_vec_add_left (s t : K) : θ ![s + t, 0] = θ ![s, 0] * θ ![t, 0] := by
  rw [← hθ.map_add]
  congr 1
  ext i
  fin_cases i <;> simp

theorem map_vec_add_right (s t : K) : θ ![0, s + t] = θ ![0, s] * θ ![0, t] := by
  rw [← hθ.map_add]
  congr 1
  ext i
  fin_cases i <;> simp

theorem map_vec_zero : θ ![0, 0] = 1 := by
  rw [NaturalModule.vec2_zero, hθ.map_zero]

theorem injective_left : Function.Injective fun s : K => θ ![s, 0] := fun _ _ h => by
  have := congrFun (hθ.injective h) 0
  simpa using this

theorem injective_right : Function.Injective fun s : K => θ ![0, s] := fun _ _ h => by
  have := congrFun (hθ.injective h) 1
  simpa using this

end Module

section Weyl

variable [CharP K 2] (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K)

@[expose] def weylPar : G := ((φ.symm (weylElt K) : X) : G)

theorem weylPar_conj_upPar (t : K) :
    weylPar φ * upPar φ t * (weylPar φ)⁻¹ = lowPar φ t := by
  have h : (weylElt K)⁻¹ = weylElt K := inv_eq_of_mul_eq_one_right (weylElt_mul_self (K := K))
  simp only [weylPar, upPar, lowPar, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv,
    ← map_mul, h, weylElt_mul_upperElt_mul_weylElt]

variable {φ} {θ : (Fin 2 → K) → G} (hθ : IsNaturalModule φ θ)
include hθ

theorem weylPar_conj (v : Fin 2 → K) :
    weylPar φ * θ v * (weylPar φ)⁻¹ = θ ![v 1, v 0] := by
  rw [weylPar, ← hθ.map_mulVec, MulEquiv.apply_symm_apply, weylElt_mulVec]

end Weyl

variable {R : Set (Subgroup G)}

theorem exists_natural_coords [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {P Q U : Subgroup G} (hP : P ∈ R) (hQ : Q ∈ R) (hPQ : Opposite P Q)
    (hUP : U ∈ lambdaSet R P) (hUQ : U ∈ psiSet R Q) [Finite K] [CharP K 2]
    (φ : ↥(P ⊔ Q) ≃* SpecialLinearGroup (Fin 2) K)
    (hφP : (P.subgroupOf (P ⊔ Q)).map φ.toMonoidHom = upperUnipotent K)
    (hφQ : (Q.subgroupOf (P ⊔ Q)).map φ.toMonoidHom = lowerUnipotent K)
    {w : G} (hw : w ∈ U) (hw1 : w ≠ 1) :
    ∃ θ : (Fin 2 → K) → G, IsNaturalModule φ θ ∧ θ ![1, 0] = w ∧
      (∀ s, θ ![s, 0] ∈ U) ∧ (∀ s, θ ![0, s] ∈ ⁅Q, U⁆) ∧
      (∀ u ∈ U, ∃ s, θ ![s, 0] = u) ∧ (∀ u ∈ ⁅Q, U⁆, ∃ s, θ ![0, s] = u) := by
  obtain ⟨θ, hθ, hrange, he⟩ :=
    Sec3.exists_isNaturalModule hR hiso hP hQ hPQ hUP hUQ φ hφP hw hw1
  have hmem : ∀ v, θ v ∈ U ⊔ ⁅Q, U⁆ := fun v => by
    rw [← SetLike.mem_coe, ← hrange]
    exact ⟨v, rfl⟩
  have hrng : ∀ u ∈ U ⊔ ⁅Q, U⁆, ∃ v, θ v = u := fun u hu => by
    rw [← SetLike.mem_coe, ← hrange] at hu
    exact hu
  refine ⟨θ, hθ, he, fun s => ?_, fun s => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hP hQ hPQ hUP hUQ (hmem _) ?_
    exact (hθ.forall_commute_upper_iff hφP le_sup_left _).2 (by simp)
  · have h := commutatorElement_lowPar hθ s ![1, 0]
    rw [show s * (![1, 0] : Fin 2 → K) 0 = s by simp, he] at h
    rw [← h]
    exact Subgroup.commutator_mem_commutator (lowPar_mem hφQ s) hw
  · obtain ⟨v, rfl⟩ := hrng u (Subgroup.mem_sup_left hu)
    have h1 : v 1 = 0 := (hθ.forall_commute_upper_iff hφP le_sup_left v).1
      fun a ha => hUP.1.2.2 a ha _ hu
    refine ⟨v 0, congrArg θ ?_⟩
    ext i
    fin_cases i <;> simp [h1]
  · obtain ⟨v, rfl⟩ := hrng u (Subgroup.mem_sup_right hu)
    have h0 : v 0 = 0 := (hθ.forall_commute_lower_iff hφQ le_sup_right v).1
      fun b hb => (hUQ.2.2.1 _ hu b hb).symm
    refine ⟨v 1, congrArg θ ?_⟩
    ext i
    fin_cases i <;> simp [h0]

end FrameSL3

end CFSG.Timmesfeld.ARS
