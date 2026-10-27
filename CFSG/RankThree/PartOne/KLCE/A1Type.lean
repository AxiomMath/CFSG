module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.RankThree.PartOne.KE.CTRational
public import CFSG.RankThree.PartOne.KLC.PRankTwo

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section A1

variable {τ : Tag} {K L : Type} [Field K] [Field L] [Algebra K L]

@[expose] def a1Hom (τ : Tag) (K L : Type) [Field K] [Field L] [Algebra K L]
    (θ : Fin τ.rank → ℤ) : SL(2, K) →* ModGL τ L :=
  (rootSL2 τ L θ).comp (Matrix.SpecialLinearGroup.map (algebraMap K L))

theorem a1Hom_apply (θ : Fin τ.rank → ℤ) (B : SL(2, K)) :
    a1Hom τ K L θ B = rootSL2 τ L θ (Matrix.SpecialLinearGroup.map (algebraMap K L) B) := rfl

omit [Algebra K L] in
theorem map_specialLinear_injective (f : K →+* L) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := by
  intro A B h
  ext i j
  have := congrFun (congrFun (congrArg (fun C : SL(2, L) => (C : Matrix (Fin 2) (Fin 2) L)) h) i) j
  simpa using f.injective this

theorem a1Hom_injective (θ : Fin τ.rank → ℤ) : Function.Injective (a1Hom τ K L θ) :=
  (rootSL2_injective_of_field θ).comp (map_specialLinear_injective _)

theorem rootSpan_pm_eq_range {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) :
    rootSpan τ L {θ, -θ} = (rootSL2 τ L θ).range := by
  rw [rootSpan, iSup_insert, iSup_singleton, ← range_rootSL2_of_isRoot hθ]

theorem a1_F0_compat {θ : Fin τ.rank → ℤ} {n₀ : ModGL τ L}
    (hn₀ : n₀ ∈ Subgroup.centralizer (rootRankOneGroup τ L θ : Set (ModGL τ L)))
    {Φ₀ : L →+* L} {σ : K ≃+* K}
    (hσ : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c)) (B : SL(2, K)) :
    n₀ * Units.map (entrywiseHom Φ₀) (a1Hom τ K L θ B) * n₀⁻¹ =
      a1Hom τ K L θ (Matrix.SpecialLinearGroup.map σ.toRingHom B) := by
  have hmap : Matrix.SpecialLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.map (algebraMap K L) B) =
      Matrix.SpecialLinearGroup.map (algebraMap K L)
        (Matrix.SpecialLinearGroup.map σ.toRingHom B) := by
    ext i j
    simp [hσ]
  rw [a1Hom_apply, a1Hom_apply, entrywise_rootSL2_of_field, hmap]
  have h := Subgroup.mem_centralizer_iff.1 hn₀
    (rootSL2 τ L θ (Matrix.SpecialLinearGroup.map (algebraMap K L)
      (Matrix.SpecialLinearGroup.map σ.toRingHom B))) ⟨_, rfl⟩
  rw [← h, mul_inv_cancel_right]

end A1

end CFSG.RankThree.PartOne.KLCE
