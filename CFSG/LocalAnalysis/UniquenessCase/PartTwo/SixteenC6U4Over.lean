module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4OverAux2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par

theorem s16c6_u4_overgroup {U : Type} [Group U] [Finite U] {n : ℕ} (hn : 1 < n)
    (hU : IsU4 U n) {P X R : Subgroup U} (hP : IsParabolicTwo U P) (hX : X = F07.DerInf P)
    (hL2 : IsL2 (Bar2 X) (2 * n)) (hXR : X ≤ R) : R = ⊤ ∨ R ≤ P := by
  obtain ⟨K, hK, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hU
  letI : Field K := hK
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  let P' : Subgroup (hypSU h 2 0) := P.map e.symm.toMonoidHom
  let X' : Subgroup (hypSU h 2 0) := X.map e.symm.toMonoidHom
  let R' : Subgroup (hypSU h 2 0) := R.map e.symm.toMonoidHom
  have hP' : IsParabolicTwo (hypSU h 2 0) P' :=
    IsParabolicTwo.map hP e.symm.toMonoidHom e.symm.surjective
  have hX' : X' = F07.DerInf P' := by
    dsimp only [X', P']
    rw [hX]
    exact s16c6_derInf_map_equiv e.symm P
  have hL2' : IsL2 (Bar2 X') (2 * n) := by
    dsimp only [X']
    exact s16c6_isL2_bar2_map_equiv e.symm X hL2
  have hXR' : X' ≤ R' := Subgroup.map_mono hXR
  have hn2 : 2 ≤ n := by omega
  rcases s16c6_model h hn2 hP' hX' hL2' hXR' with htop | hle
  · exact Or.inl ((s16c6_map_equiv_eq_top_iff e.symm).mp htop)
  · exact Or.inr ((s16c6_map_equiv_le_iff e.symm).mp hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
