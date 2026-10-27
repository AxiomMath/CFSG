module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3Contracts
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases

public section

namespace S2MathAs3_1624

noncomputable section

theorem unitarySimilitudeNormalisation_holds : UnitarySimilitudeNormalisation := by
  intro K _ _ _ n h d hd S κ hκ hSgu hSpow hS
  obtain ⟨u, hu_mem⟩ :=
    CFSG.StandardType.TableBU63.exists_unitary_of_gu (K := K) (n := n) (d := d) h hSgu
  have hzu : Matrix.GeneralLinearGroup.scalar (Fin d) u ∈
      CFSG.Assembly.LargeEvenScalars (Fin d) K := by
    rw [CFSG.Assembly.largeEvenScalars_def]
    exact ⟨u, rfl⟩
  have hznorm : Matrix.GeneralLinearGroup.scalar (Fin d) u ∈
      Subgroup.normalizer
        ((CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d :
          Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)) :=
    CFSG.StandardType.TableB.scalar_mem_normalizer _ hzu
  have hS' : Matrix.GeneralLinearGroup.scalar (Fin d) u * S ∈
      Subgroup.normalizer
        ((CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d :
          Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)) :=
    Subgroup.mul_mem _ hznorm hS
  refine ⟨u, u ^ 3 * κ, hu_mem, hS', ?_, ?_, ?_⟩
  · intro e he
    refine hκ (e * u⁻¹) ?_
    rw [mul_pow, inv_pow, he, mul_assoc, mul_comm κ ((u ^ 3)⁻¹), ← mul_assoc, mul_inv_cancel,
      one_mul]
  · rw [CFSG.StandardType.TableBU63.scalar_mul_pow u S 3, hSpow]
    exact (map_mul (Matrix.GeneralLinearGroup.scalar (Fin d)) (u ^ 3) κ).symm
  · have hscal : CFSG.StandardType.TableB.projConj
        (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d)
        ⟨Matrix.GeneralLinearGroup.scalar (Fin d) u, hznorm⟩ = 1 :=
      CFSG.StandardType.TableB.projConj_of_scalar
        (H := CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d) hzu
    have hprod : (⟨Matrix.GeneralLinearGroup.scalar (Fin d) u * S, hS'⟩ :
        Subgroup.normalizer
          ((CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d :
            Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) =
        (⟨Matrix.GeneralLinearGroup.scalar (Fin d) u, hznorm⟩ :
          Subgroup.normalizer
            ((CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d :
              Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) *
        (⟨S, hS⟩ :
          Subgroup.normalizer
            ((CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d :
              Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) :=
      Subtype.ext rfl
    rw [hprod, map_mul, hscal, one_mul]

end

end S2MathAs3_1624

end
