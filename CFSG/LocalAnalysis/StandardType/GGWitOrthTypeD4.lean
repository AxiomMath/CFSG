module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthNormal
public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulTypeA
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR34DataD4

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem owTD4_linWeyl_of_typeD4 {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) (c : ZMod 3)
    {A : Subgroup (U ≃ₗ[ZMod 3] U)}
    (h : Fin 4 → U) (α : Fin 4 → U →ₗ[ZMod 3] ZMod 3)
    (hP : ∀ i j, α i (h j) = (CartanMatrix.D 4 i j : ZMod 3))
    (s : Fin 4 → U ≃ₗ[ZMod 3] U) (hs : ∀ i v, s i v = v - α i v • h i)
    (hs_mem : ∀ i, s i ∈ ClassRefl 3 Q c)
    (hgen : closure (Set.range s) = A) : LinWeyl 3 A := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hα : ∀ i, α i (h i) = 2 := fun i => by
    rw [hP i i, owR34_diagD4 i]
  have hind : LinearIndependent (ZMod 3) h := by
    refine linearIndependent_of_det_ne_zero h α ?_
    have hmap : (Matrix.of fun i j => α i (h j)) =
        (CartanMatrix.D 4).map (fun x : ℤ => (x : ZMod 3)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.map_apply, hP]
    rw [hmap, owR34_detD4]
    decide
  have hM : ggCoxeterMatrixD 4 = (ggCoxeterMatrixD 4).reindex (Equiv.refl (Fin 4)) := by
    ext i j; simp [CoxeterMatrix.reindex_apply]
  have hMW : GGIsWeylMatrixFixed (ggCoxeterMatrixD 4) :=
    Or.inl ⟨4, Equiv.refl _, by omega, Or.inr (Or.inr ⟨le_rfl, hM⟩)⟩
  obtain ⟨f, hf⟩ := ggCoxeterIso_of_injective_lift (M := ggCoxeterMatrixD 4) (ggIntCartan_D 4)
    h α hα hP
    (ggCartanFaithfulInputFixed_holds 3 (by norm_num) (by norm_num) (Fin 4) _ (CartanMatrix.D 4)
      hMW (ggIntCartan_D 4) U h α hα hP hind)
    s hs
  refine ⟨Fin 4, ggCoxeterMatrixD 4, ?_, f.trans (MulEquiv.subgroupCongr hgen), ?_⟩
  · exact Or.inl ⟨4, Equiv.refl _, by omega, Or.inr (Or.inr ⟨le_rfl, hM⟩)⟩
  · intro i
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      show (f ((ggCoxeterMatrixD 4).simple i) : U ≃ₗ[ZMod 3] U) = s i from hf i]
    exact (hs_mem i).1

end CFSG.StandardType.ZS

end
