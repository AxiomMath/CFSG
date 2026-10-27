module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBasic
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Lift

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}

theorem vecIncl_smul (a : k) (v : Fin d → k) : vecIncl k (a • v) = (a : K) • vecIncl k v := by
  funext i
  simp [vecIncl]

theorem exists_vecIncl_iff (v : Fin d → K) : (∃ v₀, vecIncl k v₀ = v) ↔ ∀ j, v j ∈ k :=
  ⟨fun ⟨v₀, h⟩ j => h ▸ (v₀ j).2, fun h => ⟨fun j => ⟨v j, h j⟩, rfl⟩⟩

@[expose] noncomputable def liftLin :
    ((Fin d → k) ≃ₗ[k] (Fin d → k)) →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  (matrixLinearIso (d := d) (K := K)).toMonoidHom.comp
    ((glIncl k).comp (matrixLinearIso (d := d) (K := k)).symm.toMonoidHom)

theorem liftLin_matrixLinearIso (a : GL (Fin d) k) :
    liftLin k (matrixLinearIso (d := d) (K := k) a) = matrixLinearIso (glIncl k a) := by
  change matrixLinearIso (glIncl k ((matrixLinearIso (d := d) (K := k)).symm
    (matrixLinearIso (d := d) (K := k) a))) = _
  rw [MulEquiv.symm_apply_apply]

theorem liftLin_apply_vecIncl (g : (Fin d → k) ≃ₗ[k] (Fin d → k)) (v : Fin d → k) :
    liftLin k g (vecIncl k v) = vecIncl k (g v) := by
  change (glIncl k ((matrixLinearIso (d := d) (K := k)).symm g)).val *ᵥ vecIncl k v = _
  rw [mulVec_vecIncl]
  congr 1
  exact congrArg (fun h => h v) ((matrixLinearIso (d := d) (K := k)).apply_symm_apply g)

theorem linearEquiv_ext_vecIncl {M : Type*} [AddCommGroup M] [Module K M]
    (f g : (Fin d → K) ≃ₗ[K] M) (h : ∀ v : Fin d → k, f (vecIncl k v) = g (vecIncl k v)) :
    f = g := by
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun K (Fin d)).ext fun i => ?_)
  simpa [vecIncl_single] using h (Pi.single i 1)

variable {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem polar_vecIncl (hext : IsExtension k Q₀ Q) (x y : Fin d → k) :
    polar Q (vecIncl k x) (vecIncl k y) = ((polar Q₀ x y : k) : K) := by
  unfold QuadraticMap.polar
  rw [← vecIncl_add, hext, hext, hext]
  push_cast
  rfl

theorem liftLin_eichler (hext : IsExtension k Q₀ Q) {u w : Fin d → k} (hu : Q₀ u = 0)
    (huw : polar Q₀ u w = 0) :
    liftLin k (eichler Q₀ u w) = eichler Q (vecIncl k u) (vecIncl k w) := by
  have hQu : Q (vecIncl k u) = 0 := by rw [hext, hu]; rfl
  have hQuw : polar Q (vecIncl k u) (vecIncl k w) = 0 := by
    rw [polar_vecIncl k hext, huw]
    rfl
  refine linearEquiv_ext_vecIncl k _ _ fun v => ?_
  rw [liftLin_apply_vecIncl, eichler_apply hu huw, eichler_apply hQu hQuw, polar_vecIncl k hext,
    polar_vecIncl k hext, hext w]
  funext i
  simp only [vecIncl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end Lift

end CFSG.RankThree.PartOne.SEITZ2
