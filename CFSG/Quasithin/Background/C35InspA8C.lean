module

public import CFSG.Quasithin.Background.C35InspA8B
public import CFSG.Quasithin.Background.F918F2

public section

namespace CFSG.Quasithin.C35Pf

open Matrix CFSG.GH74.Exceptional CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

@[expose] def a8G0 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

@[expose] def a8T01 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def a8T23 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

@[expose] def a8C01 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def a8Conj : Fin 6 → Fin 6 → Matrix (Fin 4) (Fin 4) (ZMod 2)
  | 0, 0 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 0, 1 => !![0, 1, 0, 0; 1, 1, 0, 1; 1, 1, 0, 0; 0, 1, 1, 0]
  | 0, 2 => !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 1; 1, 0, 0, 0]
  | 0, 3 => !![0, 1, 0, 0; 1, 0, 0, 1; 1, 1, 0, 0; 1, 1, 1, 0]
  | 0, 4 => !![0, 1, 0, 0; 0, 0, 0, 1; 1, 1, 0, 0; 0, 0, 1, 0]
  | 0, 5 => !![0, 1, 0, 0; 0, 1, 0, 1; 1, 1, 0, 0; 1, 0, 1, 0]
  | 1, 0 => !![1, 0, 0, 0; 1, 1, 0, 1; 0, 1, 0, 0; 0, 1, 1, 0]
  | 1, 1 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 1, 2 => !![0, 1, 0, 0; 0, 0, 0, 1; 1, 1, 0, 0; 1, 1, 1, 0]
  | 1, 3 => !![0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0]
  | 1, 4 => !![1, 0, 1, 0; 1, 0, 0, 1; 0, 0, 1, 0; 1, 1, 0, 0]
  | 1, 5 => !![1, 0, 1, 0; 0, 0, 1, 1; 0, 0, 1, 0; 0, 1, 0, 0]
  | 2, 0 => !![0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0]
  | 2, 1 => !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 1, 1, 1, 0]
  | 2, 2 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 2, 3 => !![1, 0, 0, 0; 0, 1, 0, 1; 0, 1, 0, 0; 0, 1, 1, 0]
  | 2, 4 => !![1, 0, 0, 0; 1, 1, 0, 1; 0, 1, 0, 0; 1, 0, 1, 0]
  | 2, 5 => !![1, 0, 0, 0; 1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]
  | 3, 0 => !![1, 0, 0, 0; 1, 0, 0, 1; 0, 1, 0, 0; 1, 1, 1, 0]
  | 3, 1 => !![0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]
  | 3, 2 => !![0, 1, 0, 0; 0, 1, 0, 1; 1, 1, 0, 0; 0, 1, 1, 0]
  | 3, 3 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 3, 4 => !![1, 0, 0, 0; 1, 0, 1, 1; 1, 0, 1, 0; 0, 1, 0, 0]
  | 3, 5 => !![1, 0, 0, 0; 0, 0, 0, 1; 1, 0, 1, 0; 1, 1, 0, 0]
  | 4, 0 => !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]
  | 4, 1 => !![1, 0, 0, 0; 1, 0, 0, 1; 1, 0, 1, 0; 1, 1, 0, 0]
  | 4, 2 => !![0, 1, 0, 0; 1, 1, 0, 1; 1, 1, 0, 0; 1, 0, 1, 0]
  | 4, 3 => !![1, 0, 1, 0; 1, 0, 1, 1; 0, 0, 1, 0; 0, 1, 0, 0]
  | 4, 4 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 4, 5 => !![0, 1, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0]
  | 5, 0 => !![1, 0, 0, 0; 0, 1, 0, 1; 0, 1, 0, 0; 1, 0, 1, 0]
  | 5, 1 => !![1, 0, 0, 0; 0, 0, 1, 1; 1, 0, 1, 0; 0, 1, 0, 0]
  | 5, 2 => !![0, 1, 0, 0; 1, 0, 0, 1; 1, 1, 0, 0; 0, 0, 1, 0]
  | 5, 3 => !![1, 0, 1, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, 1, 0, 0]
  | 5, 4 => !![0, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0]
  | 5, 5 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem a8_mat_facts :
    a8G0.det = 1 ∧ a8T01.det = 1 ∧ a8T23.det = 1 ∧ a8C01.det = 1 ∧
      a8C01 * a8T01 = a8T23 * a8C01 ∧ a8T23 * a8G0 = a8G0 * a8T23 ∧
      a8T01 * a8G0 = a8G0 * a8T01 ∧ a8T23 * a8G0 = a8T01 ∧ a8T01 * a8G0 = a8T23 ∧
      a8G0 * a8G0 = 1 := by
  decide +kernel

theorem a8Conj_spec : ∀ i j : Fin 6, i ≠ j →
    a8Conj i j * (l42Mat i * l42Mat j) = a8G0 * a8Conj i j := by
  decide +kernel

theorem a8Conj_det : (∀ i j : Fin 6, (a8Conj i j).det = 1) ∧ ∀ i : Fin 6, (l42Mat i).det = 1 := by
  decide +kernel

@[expose] def a8G0SL : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨a8G0, a8_mat_facts.1⟩

@[expose] def a8T01SL : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨a8T01, a8_mat_facts.2.1⟩

@[expose] def a8T23SL : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨a8T23, a8_mat_facts.2.2.1⟩

@[expose] def l42SL (i : Fin 6) : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨l42Mat i, a8Conj_det.2 i⟩

theorem closure_l42SL :
    Subgroup.closure (Set.range fun k : CarmichaelIndex 8 => l42SL (carmichaelIndexToFin6 k)) =
      ⊤ := by
  obtain ⟨φ, hφ⟩ := CFSG.Quasithin.exists_iso_alt8_carm
  have hr1 : Set.range (⇑φ.toMonoidHom ∘ carmichaelCycle (n := 8)) = Set.range l42Gen := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hφ k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, hφ k⟩
  have hGL : Subgroup.closure (Set.range l42Gen) = ⊤ := by
    have h2 := congrArg (Subgroup.map φ.toMonoidHom)
      (closure_range_carmichaelCycle (n := 8) (by norm_num))
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ φ.surjective,
      ← Set.range_comp, hr1] at h2
    exact h2
  set f := Matrix.SpecialLinearGroup.toGL (n := Fin 4) (R := ZMod 2) with hf
  have hfL : ∀ k, f (l42SL (carmichaelIndexToFin6 k)) = l42Gen k := fun k => Units.ext rfl
  have hr2 : Set.range (⇑f ∘ fun k : CarmichaelIndex 8 => l42SL (carmichaelIndexToFin6 k)) =
      Set.range l42Gen := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hfL k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, hfL k⟩
  have hmap : (Subgroup.closure (Set.range fun k : CarmichaelIndex 8 =>
      l42SL (carmichaelIndexToFin6 k))).map f = ⊤ := by
    rw [MonoidHom.map_closure, ← Set.range_comp, hr2, hGL]
  rw [← Subgroup.comap_map_eq_self_of_injective Matrix.SpecialLinearGroup.toGL_injective
    (Subgroup.closure _), hmap, Subgroup.comap_top]

theorem card_alternatingGroup_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

section Cover

variable {K : Type} [Group K] {θ : K →* SpecialLinearGroup (Fin 4) (ZMod 2)} {z : K}

theorem not_sqOne_a8G0 (hθ : Function.Surjective θ) (hz : z ∈ Subgroup.center K) (hθz : θ z = 1)
    (hker : ∀ y, θ y = 1 → y = 1 ∨ y = z) (hzz : z * z = 1) (hperf : commutator K = ⊤)
    (hcard : 20160 < Nat.card K) : ¬ SqOne θ a8G0SL := by
  obtain ⟨k, l, hkl, h⟩ := exists_not_sqOne_carmichael (n := 8) (by norm_num) hθ hz hθz hker hzz
    hperf (fun k => l42SL (carmichaelIndexToFin6 k)) (fun k => Subtype.ext (by
      show l42Mat (carmichaelIndexToFin6 k) ^ 3 = 1
      exact l42Mat_pow_three _)) closure_l42SL (by rw [card_alternatingGroup_eight]; exact hcard)
  intro h0
  apply h
  have hij : carmichaelIndexToFin6 k ≠ carmichaelIndexToFin6 l :=
    carmichaelIndexToFin6_injective.ne hkl
  set c : SpecialLinearGroup (Fin 4) (ZMod 2) :=
    ⟨a8Conj (carmichaelIndexToFin6 k) (carmichaelIndexToFin6 l), a8Conj_det.1 _ _⟩ with hc
  have hconj : c * (l42SL (carmichaelIndexToFin6 k) * l42SL (carmichaelIndexToFin6 l)) * c⁻¹ =
      a8G0SL := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (a8Conj_spec _ _ hij)
  rw [← sqOne_conj_iff hθ _ c, hconj]
  exact h0

theorem sqOne_a8T01_iff (hθ : Function.Surjective θ) : SqOne θ a8T01SL ↔ SqOne θ a8T23SL := by
  set c : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨a8C01, a8_mat_facts.2.2.2.1⟩ with hc
  have hconj : c * a8T01SL * c⁻¹ = a8T23SL := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext a8_mat_facts.2.2.2.2.1
  rw [← sqOne_conj_iff hθ _ c, hconj]

theorem commutator_eq_z_of_lifts (hθ : Function.Surjective θ) (hz : z ∈ Subgroup.center K)
    (hθz : θ z = 1) (hker : ∀ y, θ y = 1 → y = 1 ∨ y = z) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hperf : commutator K = ⊤) (hcard : 20160 < Nat.card K)
    {t : SpecialLinearGroup (Fin 4) (ZMod 2)} (htg : t * a8G0SL = a8G0SL * t)
    (htg1 : SqOne θ (t * a8G0SL)) {v m : K} (hv : θ v = t) (hm : θ m = a8G0SL)
    (hv1 : v * v = 1) : ⁅v, m⁆ = z := by
  have hg0 : a8G0SL * a8G0SL = 1 := Subtype.ext a8_mat_facts.2.2.2.2.2.2.2.2.2
  refine commutator_eq_z hker hz1 (by rw [hv, hm]; exact htg) hv1
    (sq_eq_z_of_not_sqOne hz hker hzz (not_sqOne_a8G0 hθ hz hθz hker hzz hperf hcard) hg0 hm)
    (htg1 _ (by rw [map_mul, hv, hm]))

end Cover

end CFSG.Quasithin.C35Pf
