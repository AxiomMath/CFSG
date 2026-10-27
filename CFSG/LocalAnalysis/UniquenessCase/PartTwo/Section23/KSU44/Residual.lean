module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.LineChar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Quasithin.H13.U4ParLevi
import CFSG.Quasithin.H13.U4ParCore
import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par KTabC KTabD

private theorem lineStab_eq_parP_S06 {m : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData 2 m K) :
    lineStab (hypSU hK 2 0) (Pi.single ie1 1) = parP hK := by
  ext g
  rw [mem_lineStab, mem_parP_iff hK g]
  constructor
  · rintro ⟨c, hc⟩ a ha
    have h := congrFun hc a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne ha,
      smul_zero] at h
    exact h
  · intro hcol
    refine ⟨((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1, ?_⟩
    funext a
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply]
    by_cases ha : a = ie1
    · rw [ha]
      simp [smul_eq_mul]
    · simp [hcol a ha, Pi.single_eq_of_ne ha]

private theorem Hinf_eq_perfectCore_S06 {G : Type} [Group G] (H : Subgroup G) :
    Hinf H = CFSG.Quasithin.perfectCore H :=
  (CFSG.Quasithin.perfectCore_eq_map_perfectResidual H).symm

private theorem parH_le_vecStab_S06 {m : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData 2 m K) :
    parH hK ≤ vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1) := by
  intro g hg
  rw [mem_vecStab]
  have hcol := (mem_parP_iff hK g).mp hg.1
  have hchi : ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = 1 := hg.2.1
  funext a
  rcases eq_or_ne a ie1 with rfl | ha
  · simp [Matrix.mulVec_single_one, Matrix.col_apply, hchi]
  · simp [Matrix.mulVec_single_one, Matrix.col_apply, hcol a ha, Pi.single_eq_of_ne ha]

theorem hinf_lineStab_le_vecStab {m : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 m K) :
    Hinf (lineStab (hypSU hK 2 0) (Pi.single ie1 1)) ≤
      vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1) := by
  rw [lineStab_eq_parP_S06 hK, Hinf_eq_perfectCore_S06]
  exact (perfectCore_parP_le_parH hK).trans (parH_le_vecStab_S06 hK)

theorem levHom_range_le_hinf_lineStab {m : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData 2 m K) (hm : 2 ≤ m) :
    (levHom hK).range ≤ Hinf (lineStab (hypSU hK 2 0) (Pi.single ie1 1)) := by
  rw [lineStab_eq_parP_S06 hK, Hinf_eq_perfectCore_S06]
  exact levHom_range_le_perfectCore hK hm

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
