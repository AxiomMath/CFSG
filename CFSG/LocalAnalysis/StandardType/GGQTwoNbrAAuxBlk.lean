module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkClass
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup

public section

namespace CFSG.StandardType.QTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.StandardType CFSG.Blueprint CFSG.ClassicalInvolution.Phan

theorem qTwoNbrA_block_of_diag {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (hF : Nat.card F0 = (2 ^ 1) ^ 2) {m : ℕ} {L0 : Type} [Group L0]
    (φ : ↥(unitarySU 2 1 F0 m) →* L0) (hφ_surj : Function.Surjective φ)
    (hφ_ker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 F0 m)) {ρy : MulAut L0} (hne : ρy ≠ 1)
    {t : Fin m → F0} (ht : ∀ i, t i ≠ 0) {δ : MulAut ↥(unitarySU 2 1 F0 m)}
    (hδ : ∀ s : ↥(unitarySU 2 1 F0 m),
      (((δ s : ↥(unitarySU 2 1 F0 m)) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          Matrix.diagonal t =
        Matrix.diagonal t * ((s : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0))
    (hφδ : ∀ s : ↥(unitarySU 2 1 F0 m), ρy (φ s) = φ (δ s)) {M : Subgroup L0}
    (hM : IsComponentOf M (ggFix ρy)) :
    ∃ S : Finset (Fin m), 4 ≤ S.card ∧ S.card < m ∧
      M = (TableBUE.blockSU (K := F0) (n := 1) S).map φ := by
  classical
  have hKd : UnitaryFieldData 2 1 F0 := TableBU.unitaryFieldData_of_card hF le_rfl
  obtain ⟨Q, hQ, hQM⟩ := SCFourCover.exists_isComponentOf_map_eq hφ_surj hφ_ker hφδ hM
  obtain ⟨i₀, hS2, hQS⟩ := eq_blockSU_of_isComponentOf_ggFix_diag hKd ht δ hδ hQ
  let S : Finset (Fin m) := Finset.univ.filter fun i => t i = t i₀
  have hQS' : Q = TableBUE.blockSU (K := F0) (n := 1) S := hQS
  have hS2' : 2 ≤ S.card := hS2
  have h4 : 4 ≤ S.card := by
    by_contra hlt4
    have hlt4' : S.card < 4 := not_le.1 hlt4
    have hle3 : S.card ≤ 3 := by omega
    haveI : Group.IsSolvable ↥(TableBUE.blockSU (K := F0) (n := 1) S) := by
      haveI : Group.IsSolvable ↥(unitarySU 2 1 F0 S.card) :=
        WitSU.isSolvable_unitarySU_two_one hKd (by omega) (by omega)
      exact Group.isSolvable_of_surjective (f := (TableBUE.blockSUEquiv S hKd).toMonoidHom)
        (TableBUE.blockSUEquiv S hKd).surjective
    haveI : Group.IsSolvable Q := by rw [hQS']; infer_instance
    exact Line63.H5.isQuasisimple_not_isSolvable hQ.2.2 inferInstance
  have hlt : S.card < m := by
    have hcard_le : S.card ≤ m := by simpa using Finset.card_le_univ S
    by_contra hlt
    have hcard : S.card = m := le_antisymm hcard_le (not_lt.1 hlt)
    have hSuniv : S = Finset.univ :=
      Finset.eq_univ_of_card S (by rw [Fintype.card_fin]; exact hcard)
    have hconst : ∀ i, t i = t i₀ := by
      intro i
      have hi : i ∈ S := by rw [hSuniv]; exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hi).2
    have hc : t i₀ ≠ 0 := ht i₀
    have hmat : ∀ s : ↥(unitarySU 2 1 F0 m),
        (((δ s : ↥(unitarySU 2 1 F0 m)) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
          ((s : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
      intro s
      ext i j
      have h := congrFun (congrFun (hδ s) i) j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hconst i, hconst j,
        mul_comm (t i₀)
          (((s : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i j)] at h
      exact mul_right_cancel₀ hc h
    have hδeq : δ = 1 := by
      apply MulEquiv.ext
      intro s
      simpa using Subtype.ext (Units.ext (hmat s))
    have hρ : ρy = 1 := by
      apply MulEquiv.ext
      intro x
      obtain ⟨s, rfl⟩ := hφ_surj x
      rw [hφδ, hδeq]
      simp
    exact hne hρ
  refine ⟨S, h4, hlt, ?_⟩
  rw [← hQM, hQS']

end CFSG.StandardType.QTwo

end
