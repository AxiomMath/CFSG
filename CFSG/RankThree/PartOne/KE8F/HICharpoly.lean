module

public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Polynomial

instance labelFinite (τ : Tag) : Finite (Label τ) := by
  have : Finite {v : Fin τ.rank → ℤ // IsRoot τ v} :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot τ).to_subtype
  infer_instance

instance labelFintype (τ : Tag) : Fintype (Label τ) := Fintype.ofFinite _

section Charpoly

variable {τ : Tag} {R S : Type} [Field R] [Field S]

theorem charpoly_baseChangeEnd (f : R →+* S) (A : Module.End R (RootModule τ R)) :
    (baseChangeEnd f A).charpoly = A.charpoly.map f := by
  classical
  rw [← LinearMap.charpoly_toMatrix A (Finsupp.basisSingleOne (R := R) (ι := Label τ)),
    ← LinearMap.charpoly_toMatrix (baseChangeEnd f A)
      (Finsupp.basisSingleOne (R := S) (ι := Label τ)), ← Matrix.charpoly_map]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, baseChangeEnd_single, Finsupp.mapRange_apply]

theorem charpoly_conj_unit (g : ModGL τ R) (A : Module.End R (RootModule τ R)) :
    ((g : Module.End R (RootModule τ R)) * A * ((g⁻¹ : ModGL τ R) :
      Module.End R (RootModule τ R))).charpoly = A.charpoly := by
  have h := LinearEquiv.charpoly_conj (LinearMap.GeneralLinearGroup.generalLinearEquiv R
    (RootModule τ R) g) A
  convert h using 2
  ext v
  simp [LinearEquiv.conj_apply]
  rfl

end Charpoly

section Diagonal

variable {τ : Tag} {L : Type} [Field L]

@[expose] def evLabel (b : Fin τ.rank → Lˣ) : Label τ → L
  | Sum.inl _ => 1
  | Sum.inr α => ((∏ i, b i ^ α.1 i : Lˣ) : L)

theorem charpoly_rootDiag (b : Fin τ.rank → Lˣ) :
    (rootDiag b : Module.End L (RootModule τ L)).charpoly =
      ∏ lbl : Label τ, (X - C (evLabel b lbl)) := by
  classical
  rw [← LinearMap.charpoly_toMatrix (rootDiag b) (Finsupp.basisSingleOne (R := L) (ι := Label τ))]
  have : LinearMap.toMatrix (Finsupp.basisSingleOne (R := L) (ι := Label τ))
      (Finsupp.basisSingleOne (R := L) (ι := Label τ)) (rootDiag b) =
        Matrix.diagonal (evLabel b) := by
    ext i j
    rcases j with k | γ
    · rw [LinearMap.toMatrix_apply]
      simp only [Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply]
      rw [rootDiag_single_inl]
      by_cases hij : i = Sum.inl k
      · subst hij
        simp [evLabel]
      · simp [hij]
    · rw [LinearMap.toMatrix_apply]
      simp only [Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply]
      rw [rootDiag_single_inr]
      by_cases hij : i = Sum.inr γ
      · subst hij
        simp [evLabel]
      · simp [hij]
  rw [this, Matrix.charpoly_diagonal]

theorem roots_prod_X_sub_C_univ {ι : Type*} [Fintype ι] (a : ι → L) :
    (∏ l, (X - C (a l)) : L[X]).roots = Multiset.map a Finset.univ.val := by
  rw [Finset.prod_eq_multiset_prod]
  have : Multiset.map (fun l => (X - C (a l) : L[X])) Finset.univ.val =
      Multiset.map (fun x : L => (X - C x : L[X])) (Multiset.map a Finset.univ.val) := by
    rw [Multiset.map_map]
    rfl
  rw [this]
  exact roots_multiset_prod_X_sub_C _

end Diagonal

end CFSG.RankThree.PartOne.KE8F
