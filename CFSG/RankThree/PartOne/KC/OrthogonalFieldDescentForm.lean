module

public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Module

section Descend

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {k : Subfield K}
  {V₀ : Submodule k V}

theorem coe_smul_submodule (c : k) (w : V₀) : ((c • w : V₀) : V) = (c : K) • (w : V) := by
  rw [Submodule.coe_smul, Subfield.smul_def]

theorem polar_mem_of_mem {R : QuadraticForm K V} (hR : ∀ w ∈ V₀, R w ∈ k) (w w' : V₀) :
    QuadraticMap.polar R (w : V) (w' : V) ∈ k := by
  rw [QuadraticMap.polar]
  exact sub_mem (sub_mem (hR _ (V₀.add_mem w.2 w'.2)) (hR _ w.2)) (hR _ w'.2)

@[expose] def descendQuadratic (R : QuadraticForm K V) (hR : ∀ w ∈ V₀, R w ∈ k) :
    QuadraticForm k V₀ where
  toFun w := ⟨R (w : V), hR w w.2⟩
  toFun_smul a w := by
    apply Subtype.ext
    change R ((a • w : V₀) : V) = ((a * a) • (⟨R (w : V), hR w w.2⟩ : k) : k)
    rw [coe_smul_submodule, QuadraticMap.map_smul]
    simp
  exists_companion' := by
    refine ⟨LinearMap.mk₂ k (fun w w' => (⟨QuadraticMap.polar R (w : V) (w' : V),
        polar_mem_of_mem hR w w'⟩ : k)) ?_ ?_ ?_ ?_, fun w w' => ?_⟩
    · intro w₁ w₂ w'
      apply Subtype.ext
      exact QuadraticMap.polar_add_left R (w₁ : V) (w₂ : V) (w' : V)
    · intro c w w'
      apply Subtype.ext
      change QuadraticMap.polar R ((c • w : V₀) : V) (w' : V) = (c : K) * _
      rw [coe_smul_submodule]
      exact CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq R (c : K) (w : V) (w' : V)
    · intro w w₁ w₂
      apply Subtype.ext
      exact QuadraticMap.polar_add_right R (w : V) (w₁ : V) (w₂ : V)
    · intro c w w'
      apply Subtype.ext
      change QuadraticMap.polar R (w : V) ((c • w' : V₀) : V) = (c : K) * _
      rw [coe_smul_submodule]
      exact CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq R (c : K) (w : V) (w' : V)
    · apply Subtype.ext
      change R ((w + w' : V₀) : V) = R (w : V) + R (w' : V) + QuadraticMap.polar R (w : V) (w' : V)
      rw [Submodule.coe_add]
      exact QuadraticMap.map_add (⇑R) (w : V) (w' : V)

theorem coe_descendQuadratic (R : QuadraticForm K V) (hR : ∀ w ∈ V₀, R w ∈ k) (w : V₀) :
    ((descendQuadratic R hR w : k) : K) = R (w : V) :=
  rfl

theorem coe_polar_descendQuadratic (R : QuadraticForm K V) (hR : ∀ w ∈ V₀, R w ∈ k)
    (w w' : V₀) :
    ((QuadraticMap.polar (descendQuadratic R hR) w w' : k) : K) =
      QuadraticMap.polar R (w : V) (w' : V) := by
  rw [QuadraticMap.polar, QuadraticMap.polar]
  simp [coe_descendQuadratic]

end Descend

end CFSG.RankThree.PartOne.KCOrthogonalDescent
