module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs
import CFSG.Quasithin.Vol2.KGFactSLnTwo

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

private noncomputable def caAut_reindexGL {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ≃ Fin n) : GL ι (ZMod 2) ≃* GL (Fin n) (ZMod 2) :=
  Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e).toMulEquiv

private theorem caAut_reindexGL_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ≃ Fin n) (g : GL ι (ZMod 2)) :
    ((caAut_reindexGL e g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      Matrix.reindex e e (g : Matrix ι ι (ZMod 2)) := rfl

private theorem caAut_reindexGL_inverseTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ≃ Fin n) (g : GL ι (ZMod 2)) :
    Matrix.GeneralLinearGroup.inverseTranspose (caAut_reindexGL e g) =
      caAut_reindexGL e (Matrix.GeneralLinearGroup.inverseTranspose g) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, caAut_reindexGL_apply, ← map_inv,
    caAut_reindexGL_apply, Matrix.GeneralLinearGroup.coe_inverseTranspose,
    Matrix.transpose_reindex]

private theorem caAut_exists_aut_form_of_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ≃ Fin n) (hn : 3 ≤ n) (α : MulAut (GL ι (ZMod 2))) :
    ∃ A : GL ι (ZMod 2), (∀ g, α g = A * g * A⁻¹) ∨
      ∀ g, α g = A * Matrix.GeneralLinearGroup.inverseTranspose g * A⁻¹ := by
  obtain ⟨c, hc⟩ :=
    CFSG.Quasithin.SLnTwo.exists_conj_or_conj_graph_GL (n := n) hn
      (MulAut.congr (caAut_reindexGL e) α)
  have hkey : ∀ g : GL ι (ZMod 2),
      MulAut.congr (caAut_reindexGL e) α (caAut_reindexGL e g) =
        caAut_reindexGL e (α g) := by
    intro g
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rcases hc with hc | hc
  · refine ⟨(caAut_reindexGL e).symm c, Or.inl ?_⟩
    intro g
    apply (caAut_reindexGL e).injective
    rw [← hkey g, hc (caAut_reindexGL e g)]
    simp
  · refine ⟨(caAut_reindexGL e).symm c, Or.inr ?_⟩
    intro g
    apply (caAut_reindexGL e).injective
    rw [← hkey g, hc (caAut_reindexGL e g)]
    have hnat : CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut n (ZMod 2)
        (caAut_reindexGL e g) =
        caAut_reindexGL e (Matrix.GeneralLinearGroup.inverseTranspose g) :=
      caAut_reindexGL_inverseTranspose e g
    rw [hnat]
    simp

theorem exists_eq_conj_or_conj_inverseTranspose {m : ℕ} (hm : 1 ≤ m)
    (α : MulAut (GL (BlkIdx 1 m) (ZMod 2))) : ∃ A : GL (BlkIdx 1 m) (ZMod 2),
      (∀ g, α g = A * g * A⁻¹) ∨
        ∀ g, α g = A * Matrix.GeneralLinearGroup.inverseTranspose g * A⁻¹ := by
  have hcard : Fintype.card (BlkIdx 1 m) = m + 2 := by
    have h : Fintype.card (BlkIdx 1 m) = 1 + (m + 1) := by
      change Fintype.card (Fin 1 ⊕ (Fin m ⊕ Fin 1)) = 1 + (m + 1)
      simp [Fintype.card_sum]
    omega
  exact caAut_exists_aut_form_of_equiv (Fintype.equivFinOfCardEq hcard) (by omega) α

end CFSG.StandardType.FF81.CentA

end
