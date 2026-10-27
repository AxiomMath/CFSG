module

public import CFSG.LocalAnalysis.StandardType.GGRankOneModel
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagDefs
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinPlus
import CFSG.LieType.Steinberg.Classical.SpecialLinear
import CFSG.LieType.Steinberg.Classical.SpinPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

section Helpers

private theorem sl_x_normalizer_scalar {m : ℕ} {F : Type} [Field F] {γ : Fin m → ℤ}
    (hγ : γ ∈ (SpecialLinear.rootDatum m F).roots)
    {h : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hh : h ∈ Subgroup.normalizer
      ((SpecialLinear.rootDatum m F).rootGroup γ : Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F))) :
    ∃ χ : F, ∀ c : F, h * SL.x m F γ c * h⁻¹ = SL.x m F γ (χ * c) := by
  obtain ⟨hij, hst⟩ := SL.pairOf_spec (m := m) hγ
  have hx : ∀ c : F, SL.x m F γ c = Matrix.SpecialLinearGroup.transvection hij c :=
    fun c => SL.x_eq hij hst c
  have hN : ∀ c : F,
      ((SL.x m F γ c : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        1 + c • Matrix.single (SL.pairOf m γ).1 (SL.pairOf m γ).2 (1 : F) := by
    intro c
    rw [hx c, Matrix.SpecialLinearGroup.transvection_coe, Matrix.smul_single, smul_eq_mul, mul_one]
  exact PsiDiag.conj_eq_of_affine
    (ι := (Matrix.SpecialLinearGroup.coeMonoidHom :
      Matrix.SpecialLinearGroup (Fin (m + 1)) F →* Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    Matrix.SpecialLinearGroup.coeMonoidHom_injective
    (X := (SpecialLinear.rootDatum m F).rootGroup γ) (y := SL.x m F γ)
    ((SL.isParametrization (m := m) (F := F)) γ hγ).1 hN hh

end Helpers

section Tag

theorem ggRankOneModel_PSL {n f : ℕ} (hadm : StatedLieAdmissible .PSL n 2 f)
    (hrank : 3 ≤ bnRank .PSL n) : GGRankOneModel (ggU .PSL n f).D (GaloisField 2 f) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at hrank; omega⟩
  have hm2 : 2 ≤ m := by simp only [bnRank] at hrank; omega
  show GGRankOneModel (SpecialLinear.rootDatum m (GaloisField 2 f)) (GaloisField 2 f)
  unfold GGRankOneModel
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan
    (SpecialLinear.rootDatum m (GaloisField 2 f)).isFiniteType
    (Dv := (SpecialLinear.rootDatum m (GaloisField 2 f)).divisible) rfl
  have hE := SL.chevalleyExtras hm2 O SL.commC (SL.commutatorFormula O)
  refine ⟨SL.x m (GaloisField 2 f), SL.commC, O, hE, ?_⟩
  intro h hh i
  have hγ : (Pi.single i 1 : Fin m → ℤ) ∈
      (SpecialLinear.rootDatum m (GaloisField 2 f)).roots :=
    single_mem_roots (D := SpecialLinear.rootDatum m (GaloisField 2 f)) i
  have hN : h ∈ Subgroup.normalizer
      ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (Pi.single i 1) :
        Set (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh _ hγ
  exact sl_x_normalizer_scalar hγ hN

theorem ggRankOneModel_POmegaPlus {n f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 2 f)
    (hrank : 3 ≤ bnRank .POmegaPlus n) :
    GGRankOneModel (ggU .POmegaPlus n f).D (GaloisField 2 f) := by
  have hn : 3 ≤ n := by simpa [bnRank] using hrank
  rw [ggU_pOmegaPlus hn]
  unfold GGRankOneModel
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan
    (Spin.plusDatum n (GaloisField 2 f) hn).isFiniteType
    (Dv := (Spin.plusDatum n (GaloisField 2 f) hn).divisible) rfl
  have hE := SpinPlus.chevalleyExtras hn O SpinPlus.commC (SpinPlus.commutatorFormula hn O)
  refine ⟨SpinPlus.x n (GaloisField 2 f) hn, SpinPlus.commC, O, hE, ?_⟩
  intro h hh i
  obtain ⟨N, hN⟩ := PsiDiag.SpinP.coe_x_eq (K := GaloisField 2 f) hn
    (single_mem_roots (D := Spin.plusDatum n (GaloisField 2 f) hn) i)
  refine PsiDiag.conj_eq_of_affine (spinGroup (Spin.quadPlus n (GaloisField 2 f))).subtype
    Subtype.val_injective
    ((hE.param _ (single_mem_roots (D := Spin.plusDatum n (GaloisField 2 f) hn) i)).1) hN ?_
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  exact hh _ (single_mem_roots (D := Spin.plusDatum n (GaloisField 2 f) hn) i)

end Tag

end CFSG.StandardType
