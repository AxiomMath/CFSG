module

public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434OtherVacuity
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable def projectiveSL3FieldEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    projectiveSL 3 K ≃* projectiveSL 3 L :=
  QuotientGroup.congr (scalars 3 K) (scalars 3 L)
    (CFSG.ClassicalModels.specialLinearFieldEquiv e (Fin 3))
    (by
      rw [scalars_eq_center, scalars_eq_center]
      exact CFSG.ClassicalModels.specialLinearFieldEquiv_map_center e (Fin 3))

theorem rankLE1_projectiveSL_three_gf8 : RankLE1 3 (projectiveSL 3 (GaloisField 2 3)) := by
  unfold RankLE1
  intro B hB
  have hinj : Function.Injective
      (MulAut.conj : projectiveSL 3 (GaloisField 2 3) →*
        MulAut (projectiveSL 3 (GaloisField 2 3))) :=
    CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (by norm_num)
  have hBc := CFSG.RankThree.PartTwo.Sec4.isElemAbelian_map
    (MulAut.conj : projectiveSL 3 (GaloisField 2 3) →*
      MulAut (projectiveSL 3 (GaloisField 2 3))) hB
  have hle : B.map (MulAut.conj : projectiveSL 3 (GaloisField 2 3) →*
      MulAut (projectiveSL 3 (GaloisField 2 3))) ≤ linearAutGroup 3 (GaloisField 2 3) := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.RankThree.PartTwo.KFacts.innAut_le_linearAutGroup 3 (GaloisField 2 3) ⟨x, rfl⟩
  have h3 := CFSG.RankThree.PartTwo.Sec4.card_inf_linearAutGroup_eight_le_three hBc
  rw [inf_eq_left.mpr hle, Subgroup.card_map_of_injective hinj] at h3
  exact h3

theorem rankLE1_projectiveSL_three_eight {F : Type} [Field F] [Finite F] (h8 : Nat.card F = 8) :
    RankLE1 3 (projectiveSL 3 F) := by
  have e : F ≃+* GaloisField 2 3 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 3 (by norm_num) (h8.trans (by norm_num))
  exact RankLE1.of_mulEquiv (projectiveSL3FieldEquiv e).symm rankLE1_projectiveSL_three_gf8

theorem narrowScope_projectiveSL_eight {F : Type} [Field F] [Finite F] (h8 : Nat.card F = 8)
    (E : Subgroup (MulAut (projectiveSL 3 F))) (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    NarrowScope 3 E := by
  have h1 : RankLE1 3 (projectiveSL 3 F) := rankLE1_projectiveSL_three_eight h8
  unfold NarrowScope
  exact ⟨h1.rankLE2, Or.inl h1⟩

end CFSG.RankThree.PartTwo.Sec19
