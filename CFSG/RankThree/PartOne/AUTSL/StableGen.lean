module

public import CFSG.RankThree.PartOne.AUTSL.DiagCore
public import CFSG.RankThree.PartOne.AUTSL.FieldExt

public section

namespace CFSG.RankThree.PartOne.AUTSL

section Stable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K K' : Type*} [Field K] [Field K']
  [Algebra K K'] {E B : Type*} [CommGroup E] [Group B]

theorem rho_mem_span (ρ : E →* Matrix ι ι K) (ιB : B →* E) (P : GL ι K') (f : ι → (E →* K'ˣ))
    (hD : ∀ g : E, (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
      ((P⁻¹ : GL ι K') : Matrix ι ι K') = diagOf f g)
    (hinj : Function.Injective fun i => (f i).comp ιB) (g : E) :
    ρ g ∈ Submodule.span K (Set.range fun b : B => ρ (ιB b)) := by
  have hspan := diag_mem_span f ιB hinj g
  have hPiP : ((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K') = 1 := Units.inv_mul P
  let Cj : Matrix ι ι K' →ₗ[K'] Matrix ι ι K' :=
    (LinearMap.mulLeft K' ((P⁻¹ : GL ι K') : Matrix ι ι K')).comp
      (LinearMap.mulRight K' (P : Matrix ι ι K'))
  have hCj : ∀ z : E, Cj (diagOf f z) = (ρ z).map (algebraMap K K') := fun z => by
    have hz : diagOf f z = (P : Matrix ι ι K') * (ρ z).map (algebraMap K K') *
        ((P⁻¹ : GL ι K') : Matrix ι ι K') := (hD z).symm
    show ((P⁻¹ : GL ι K') : Matrix ι ι K') * (diagOf f z * (P : Matrix ι ι K')) = _
    rw [hz]
    calc ((P⁻¹ : GL ι K') : Matrix ι ι K') * ((P : Matrix ι ι K') *
          (ρ z).map (algebraMap K K') * ((P⁻¹ : GL ι K') : Matrix ι ι K') *
            (P : Matrix ι ι K'))
        = (((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K')) *
          (ρ z).map (algebraMap K K') * (((P⁻¹ : GL ι K') : Matrix ι ι K') *
            (P : Matrix ι ι K')) := by noncomm_ring
      _ = _ := by rw [hPiP, one_mul, mul_one]
  have hmem := Submodule.mem_map_of_mem (f := Cj) hspan
  rw [Submodule.map_span, ← Set.range_comp] at hmem
  have hmem2 : (ρ g).map (algebraMap K K') ∈ Submodule.span K'
      ((fun a : Matrix ι ι K => a.map (algebraMap K K')) '' Set.range fun b : B => ρ (ιB b)) := by
    rw [← Set.range_comp]
    have hrange : (Cj ∘ fun b : B => diagOf f (ιB b)) =
        ((fun a : Matrix ι ι K => a.map (algebraMap K K')) ∘ fun b : B => ρ (ιB b)) := by
      funext b
      exact hCj (ιB b)
    rw [← hrange]
    have h4 : (ρ g).map (algebraMap K K') = Cj (diagOf f g) := (hCj g).symm
    rw [h4]
    exact hmem
  exact mem_span_of_map_mem_span (K := K) (K' := K') _ _ hmem2

end Stable

end CFSG.RankThree.PartOne.AUTSL
