module

public import CFSG.RankThree.PartOne.SEITZ6.G2MaxSL2
public import CFSG.RankThree.Classical.SL2SemilinearRoots

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.RankThree.Classical

theorem simple_perfect_of_mulEquiv_SL2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) {R : Type*} [Group R]
    (e : Matrix.SpecialLinearGroup (Fin 2) F ≃* R) : IsSimpleGroup R ∧ Group.IsPerfect R := by
  classical
  have hs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.RankThree.PartOne.SEITZ6.isSimpleGroup_SL2 h4
  have : Fintype F := Fintype.ofFinite F
  have h4' : ∃ s : Finset F, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact h4
    obtain ⟨s, -, hs'⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs'⟩
  exact ⟨e.symm.isSimpleGroup,
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_SL2 h4')).1⟩

theorem nonempty_mulEquiv_of_comap_eq_conjSL {L F G : Type*} [Field L] [Field F] [Algebra F L]
    [Group G] {ι : Matrix.SpecialLinearGroup (Fin 2) L →* G} (hι : Function.Injective ι)
    {R : Subgroup G} (hR : R ≤ ι.range) {P : GL (Fin 2) L}
    (hRP : R.comap ι = (Matrix.SpecialLinearGroup.map (algebraMap F L)).range.map
      (conjSL P)) : Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* R) := by
  have hSLinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (algebraMap F L)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) L =>
      (X : Matrix (Fin 2) (Fin 2) L) i j) h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap F L).injective h1
  have hPinj : Function.Injective (conjSL P) := fun A B h => by
    have h1 := congrArg (conjSL P⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  have hmap : (R.comap ι).map ι = R := by
    rw [Subgroup.map_comap_eq]
    exact inf_of_le_right hR
  exact ⟨((((MonoidHom.ofInjective hSLinj).trans
    (Subgroup.equivMapOfInjective _ _ hPinj)).trans (MulEquiv.subgroupCongr hRP.symm)).trans
      (Subgroup.equivMapOfInjective _ _ hι)).trans (MulEquiv.subgroupCongr hmap)⟩

end CFSG.RankThree.PartOne.F106
