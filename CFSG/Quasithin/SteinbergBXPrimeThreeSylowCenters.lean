module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.SteinbergBX

open Matrix CFSG.Assembly.LowTwoRank

namespace PrimeThreeSylow

theorem statedScalars_subgroupOf_statedSL_three_three :
    (StatedScalars (Fin 3) (ZMod 3)).subgroupOf (StatedSL 3 (ZMod 3)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hxSL : (x : GL (Fin 3) (ZMod 3)) ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 3) (ZMod 3) →* GL (Fin 3) (ZMod 3)).range := by
    rw [← statedSL_eq_range_toGL]
    exact x.2
  obtain ⟨A, hA⟩ := hxSL
  have hdet : (Matrix.scalar (Fin 3) (c : ZMod 3)).det = 1 := by
    have h1 := congrArg (fun g : GL (Fin 3) (ZMod 3) => (g : Matrix (Fin 3) (Fin 3) (ZMod 3)).det)
      (hc.trans hA.symm)
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at h1
    rw [h1]
    exact A.2
  rw [scalar_apply, det_diagonal, Fin.prod_univ_three] at hdet
  have hc1 : (c : ZMod 3) = 1 := by
    generalize (c : ZMod 3) = a at hdet ⊢
    revert hdet
    revert a
    decide
  have hc1' : c = 1 := Units.ext hc1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1', map_one]
  rfl

end PrimeThreeSylow

open PrimeThreeSylow

end CFSG.Quasithin.SteinbergBX
