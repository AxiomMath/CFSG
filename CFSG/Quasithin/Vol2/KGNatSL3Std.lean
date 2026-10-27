module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3Basic

public section

namespace CFSG.Quasithin.Vol2.KGNat

open Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover

variable {K : Type} [Field K]

theorem uMat_mulVec (a b c : K) (x : Fin 3 → K) :
    uMat a b c *ᵥ x = ![x 0 + a * x 1 + b * x 2, x 1 + c * x 2, x 2] := by
  funext i
  fin_cases i <;> simp [uMat, mulVec, dotProduct, Fin.sum_univ_three]

variable (K) in
@[expose] def stdLine : Submodule K (Fin 3 → K) where
  carrier := {x | x 1 = 0 ∧ x 2 = 0}
  add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c x hx => ⟨by simp [hx.1], by simp [hx.2]⟩

variable (K) in
@[expose] def stdPlane : Submodule K (Fin 3 → K) where
  carrier := {x | x 2 = 0}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at hx hy ⊢
    simp [hx, hy]
  zero_mem' := rfl
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply] at hx ⊢
    simp [hx]

theorem mem_stdLine {x : Fin 3 → K} : x ∈ stdLine K ↔ x 1 = 0 ∧ x 2 = 0 := Iff.rfl

theorem mem_stdPlane {x : Fin 3 → K} : x ∈ stdPlane K ↔ x 2 = 0 := Iff.rfl

theorem stdLine_le_stdPlane : stdLine K ≤ stdPlane K := fun _ hx => hx.2

omit [Field K] in
theorem vec3_eq {x y : Fin 3 → K} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem card_stdLine [Finite K] : Nat.card (stdLine K) = Nat.card K := by
  refine (Nat.card_congr
    { toFun := fun x => (x : Fin 3 → K) 0
      invFun := fun c => ⟨![c, 0, 0], rfl, rfl⟩
      left_inv := fun x => Subtype.ext (vec3_eq rfl x.2.1.symm x.2.2.symm)
      right_inv := fun c => rfl })

theorem card_stdPlane [Finite K] : Nat.card (stdPlane K) = Nat.card K ^ 2 := by
  rw [sq, ← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun x => ((x : Fin 3 → K) 0, (x : Fin 3 → K) 1)
      invFun := fun c => ⟨![c.1, c.2, 0], rfl⟩
      left_inv := fun x => Subtype.ext (vec3_eq rfl rfl x.2.symm)
      right_inv := fun c => rfl }

theorem card_top3 [Finite K] : Nat.card (⊤ : Submodule K (Fin 3 → K)) = Nat.card K ^ 3 := by
  rw [Nat.card_congr (Submodule.topEquiv (R := K) (M := Fin 3 → K)).toEquiv, Nat.card_fun,
    Nat.card_fin]

theorem uMat_mem_stdLine (a b c : K) {x : Fin 3 → K} (hx : x ∈ stdLine K) :
    uMat a b c *ᵥ x ∈ stdLine K := by
  rw [uMat_mulVec]
  exact ⟨by simp [hx.1, hx.2], by simp [hx.2]⟩

theorem uMat_mem_stdPlane (a b c : K) {x : Fin 3 → K} (hx : x ∈ stdPlane K) :
    uMat a b c *ᵥ x ∈ stdPlane K := by
  rw [uMat_mulVec]
  have hx' : x 2 = 0 := hx
  show ![x 0 + a * x 1 + b * x 2, x 1 + c * x 2, x 2] 2 = 0
  simp [hx']

theorem eq_of_le_of_card_le {S T : Submodule K (Fin 3 → K)} [Finite K] (hle : S ≤ T)
    (hc : Nat.card T ≤ Nat.card S) : S = T := by
  apply Submodule.toAddSubgroup_injective
  exact AddSubgroup.eq_of_le_of_card_ge hle hc

theorem eq_top_of_stable {S : Submodule K (Fin 3 → K)}
    (hS : ∀ a b c : K, ∀ x ∈ S, uMat a b c *ᵥ x ∈ S) {v : Fin 3 → K} (hv : v ∈ S)
    (hv2 : v 2 ≠ 0) : S = ⊤ := by
  have e1 : ![0, v 2, 0] ∈ S := by
    have := S.sub_mem (hS 0 0 1 v hv) hv
    rwa [uMat_mulVec, show ![v 0 + 0 * v 1 + 0 * v 2, v 1 + 1 * v 2, v 2] - v = ![0, v 2, 0] from
      vec3_eq (by simp) (by simp) (by simp)] at this
  have e0 : ![v 2, 0, 0] ∈ S := by
    have := S.sub_mem (hS 0 1 0 v hv) hv
    rwa [uMat_mulVec, show ![v 0 + 0 * v 1 + 1 * v 2, v 1 + 0 * v 2, v 2] - v = ![v 2, 0, 0] from
      vec3_eq (by simp) (by simp) (by simp)] at this
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = ((x 0 - x 2 / v 2 * v 0) / v 2) • ![v 2, 0, 0] +
      ((x 1 - x 2 / v 2 * v 1) / v 2) • ![0, v 2, 0] + (x 2 / v 2) • v := by
    refine vec3_eq ?_ ?_ ?_
    · simp
      field_simp
      ring
    · simp
      field_simp
      ring
    · simp
      field_simp
  rw [hx]
  exact S.add_mem (S.add_mem (S.smul_mem _ e0) (S.smul_mem _ e1)) (S.smul_mem _ hv)

theorem stdPlane_le_of_stable {S : Submodule K (Fin 3 → K)}
    (hS : ∀ a b c : K, ∀ x ∈ S, uMat a b c *ᵥ x ∈ S) {v : Fin 3 → K} (hv : v ∈ S)
    (hv2 : v 2 = 0) (hv1 : v 1 ≠ 0) : stdPlane K ≤ S := by
  have e0 : ![v 1, 0, 0] ∈ S := by
    have := S.sub_mem (hS 1 0 0 v hv) hv
    rwa [uMat_mulVec, show ![v 0 + 1 * v 1 + 0 * v 2, v 1 + 0 * v 2, v 2] - v = ![v 1, 0, 0] from
      vec3_eq (by simp) (by simp) (by simp)] at this
  intro x hx
  have hx2 : x 2 = 0 := hx
  have hx' : x = ((x 0 - x 1 / v 1 * v 0) / v 1) • ![v 1, 0, 0] + (x 1 / v 1) • v := by
    refine vec3_eq ?_ ?_ ?_
    · simp
      field_simp
      ring
    · simp
      field_simp
    · simp [hx2, hv2]
  rw [hx']
  exact S.add_mem (S.smul_mem _ e0) (S.smul_mem _ hv)

theorem eq_std_of_stable [Finite K] {S : Submodule K (Fin 3 → K)}
    (hS : ∀ a b c : K, ∀ x ∈ S, uMat a b c *ᵥ x ∈ S) :
    (Nat.card S = Nat.card K → S = stdLine K) ∧
      (Nat.card S = Nat.card K ^ 2 → S = stdPlane K) ∧
      (Nat.card S = Nat.card K ^ 3 → S = ⊤) := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h12 : Nat.card K < Nat.card K ^ 2 := by nlinarith
  have h23 : Nat.card K ^ 2 < Nat.card K ^ 3 := by
    rw [pow_succ]
    exact lt_mul_of_one_lt_right (by positivity) hq
  have hle2 : Nat.card S < Nat.card K ^ 3 → S ≤ stdPlane K := by
    intro hc v hv
    by_contra hv2
    rw [eq_top_of_stable hS hv hv2, card_top3] at hc
    exact lt_irrefl _ hc
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · have hP := hle2 (by omega)
    have hL : S ≤ stdLine K := by
      intro v hv
      refine ⟨?_, hP hv⟩
      by_contra hv1
      have h : Nat.card (stdPlane K) ≤ Nat.card S :=
        Nat.card_mono (Set.toFinite _) (stdPlane_le_of_stable hS hv (hP hv) hv1)
      rw [card_stdPlane, hc] at h
      omega
    exact eq_of_le_of_card_le hL (by rw [card_stdLine, hc])
  · exact eq_of_le_of_card_le (hle2 (by omega)) (by rw [card_stdPlane, hc])
  · exact eq_of_le_of_card_le le_top (by rw [card_top3, hc])

end CFSG.Quasithin.Vol2.KGNat
