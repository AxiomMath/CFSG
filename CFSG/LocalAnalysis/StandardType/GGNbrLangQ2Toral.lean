module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Rows
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


@[expose] def Q2LinearLift {P : Type} [Group P] (M : Subgroup (MulAut P)) : Prop :=
  ∃ (a : ℕ) (D : Type) (_ : Field D) (_ : Finite D)
    (ψ : P ≃* LargeEvenProj (LargeEvenSLGroup (Fin a) D))
    (G : Subgroup (GL (Fin a) D)), IsMulCommutative G ∧
    ∀ α ∈ M, ∃ g ∈ G, MulAut.congr ψ α = TableB.linConjAut (Fin a) D g

private theorem l02qq2a_slKerEquiv_conjNormal {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (h : LargeEvenSLGroup (Fin d) K) :
    TypeA.slKerEquiv d K (MulAut.conjNormal A h) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K A
        (TypeA.slKerEquiv d K h) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hc : ∀ h : LargeEvenSLGroup (Fin d) K,
      Matrix.SpecialLinearGroup.toGL (TypeA.slKerEquiv d K h) = (h : GL (Fin d) K) :=
    fun h => Units.ext (TypeA.coe_slKerEquiv h)
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, hc, hc,
    MulAut.conjNormal_apply]

private theorem l02qq2a_recipe_linConjAut {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (x : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    TypeA.recipeEquiv d K (TableB.linConjAut (Fin d) K A x) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A
        (TypeA.recipeEquiv d K x) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [TableB.linConjAut_mk]
  rw [show (TypeA.recipeEquiv d K) (↑(MulAut.conjNormal A h)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d K
        (TypeA.slKerEquiv d K (MulAut.conjNormal A h))
    from TypeA.recipeEquiv_mk (MulAut.conjNormal A h)]
  rw [show (TypeA.recipeEquiv d K) (↑h) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d K (TypeA.slKerEquiv d K h)
    from TypeA.recipeEquiv_mk h]
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj,
    l02qq2a_slKerEquiv_conjNormal]

theorem q2_commutative_of_linearLift {P : Type} [Group P] {M : Subgroup (MulAut P)} (h : Q2LinearLift M)
    {d : ℕ} {K : Type} [Field K] [Finite K] (hd : 3 ≤ d) {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (θ : P ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    IsMulCommutative ((M.map (MulAut.congr θ).toMonoidHom).comap (TableB.linConjAut (Fin d) K)) := by
  classical
  obtain ⟨a, D, hDf, hDfin, ψL, G, hG, hlift⟩ := h
  letI : Field D := hDf
  letI : Finite D := hDfin
  obtain ⟨ha, hcardD⟩ :=
    kgLangS1A_psl_typeDet (d := d) (d₁ := a) (m := m) (F₀ := K) (E := D) hd hm hK
      ((TypeA.recipeEquiv d K).symm.trans (θ.symm.trans ψL))
  subst a
  let ρK := TypeA.recipeEquiv d K
  let ρD := TypeA.recipeEquiv d D
  let Ψ : LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) D) := θ.symm.trans ψL
  let T := ρK.symm.trans (Ψ.trans ρD)
  have hconj : ∀ (A : GL (Fin d) K) (A' : GL (Fin d) D) (α₀ : MulAut P),
      MulAut.congr θ α₀ = TableB.linConjAut (Fin d) K A →
      MulAut.congr ψL α₀ = TableB.linConjAut (Fin d) D A' →
      ∀ z, T (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A z) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d D A' (T z) := by
    intro A A' α₀ hA hA' z
    have hΨconj : ∀ w, Ψ (TableB.linConjAut (Fin d) K A w) =
        TableB.linConjAut (Fin d) D A' (Ψ w) := by
      intro w
      rw [← hA, ← hA']
      simp only [Ψ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hsymmK : ρK.symm
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A z) =
        TableB.linConjAut (Fin d) K A (ρK.symm z) := by
      have h1 := l02qq2a_recipe_linConjAut (d := d) (K := K) A (ρK.symm z)
      rw [MulEquiv.apply_symm_apply] at h1
      rw [← h1, MulEquiv.symm_apply_apply]
    have hsymmD : ∀ w,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d D A' (ρD w) =
        ρD (TableB.linConjAut (Fin d) D A' w) :=
      fun w => (l02qq2a_recipe_linConjAut (d := d) (K := D) A' w).symm
    show ρD (Ψ (ρK.symm
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A z))) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d D A' (ρD (Ψ (ρK.symm z)))
    rw [hsymmK, hΨconj, hsymmD]
  rw [isMulCommutative_iff]
  intro x y
  obtain ⟨α, hαM, hαeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp x.2)
  obtain ⟨β, hβM, hβeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp y.2)
  obtain ⟨x', hx'G, hx'eq⟩ := hlift α hαM
  obtain ⟨y', hy'G, hy'eq⟩ := hlift β hβM
  have hαeq' : MulAut.congr θ α = TableB.linConjAut (Fin d) K x.1 := hαeq
  have hβeq' : MulAut.congr θ β = TableB.linConjAut (Fin d) K y.1 := hβeq
  have hgh : x' * y' = y' * x' := by
    have hcomm := (isMulCommutative_iff.mp hG) ⟨x', hx'G⟩ ⟨y', hy'G⟩
    simpa using congrArg (fun t : G => (t : GL (Fin d) D)) hcomm
  have htransfer : x.1 * y.1 = y.1 * x.1 :=
    kgLangS1A_commute_transfer (d := d) (F₀ := K) (E := D) hd hcardD T
      (hconj x.1 x' α hαeq' hx'eq) (hconj y.1 y' β hβeq' hy'eq) hgh
  exact Subtype.ext htransfer

end CFSG.StandardType
