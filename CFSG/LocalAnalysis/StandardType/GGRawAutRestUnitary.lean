module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  InndiagSU RecipeFieldSU

namespace RawAutSU

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

theorem symm_primeFormFieldHom_mem (hd : 1 ≤ d) (σ : K ≃+* K) :
    (MulAut.congr (projEquiv h hd)).symm
        (primeFormFieldHom h (isPrimeFormGram_one (K := K) (n := d)) σ) ∈
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  refine ⟨σ, fun s s' hss' => ?_⟩
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  change (projEquiv h hd).symm (primeFormFieldAut h (isPrimeFormGram_one (K := K) (n := d)) σ
    (projEquiv h hd (s : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) =
      (s' : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
  rw [projEquiv_mk, primeFormFieldAut_mk, projEquiv_symm_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  change ((glAut σ (s : GL (Fin d) K) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = _
  rw [coe_glAut]
  exact hss'.symm

include h in
theorem ggOddAutInnField_unitary [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2)) (p : ℕ) :
    GGOddAutInnField p
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Θ, -, hker, hfield⟩ := exists_fieldFactor h hd hq
  refine RawAut.ggOddAutInnField_of_hom Θ (fun φ h1 => ?_) fun φ _ =>
    ⟨_, Subgroup.subset_closure (symm_primeFormFieldHom_mem h hd1 (Θ φ)), hfield (Θ φ)⟩
  rw [← coe_recIU h hK hd1]
  exact (hker φ).mp h1

end RawAutSU

open RawAutSU

theorem ggOddAutOn_unitary : GGOddAutOn GGInndiagUnitaryLabel := by
  intro p lab _ _ hlab hS _
  show LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    GGOddAutInnField p I F
  exact largeEvenLabelAll_unitary hlab hS fun _ _ _ _ _ hn hd hq hK _ _ =>
    ggOddAutInnField_unitary (unitaryFieldData_of_card hn hK) hK hd hq p

end CFSG.StandardType

end
