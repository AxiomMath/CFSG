module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Curtis
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
open scoped MatrixGroups

variable {K : Type} [Field K]

private theorem spEmbed_perm_eq_conj {n : ℕ} (π : Equiv.Perm (Fin n)) :
    spEmbed (K := K) (π : Fin n → Fin n) π.injective =
      (MulAut.conj (permSp K π)).toMonoidHom := by
  apply MonoidHom.ext
  intro h
  apply mat_injective
  ext a b
  obtain ⟨x, rfl⟩ := (sumMap_bijective π).surjective a
  obtain ⟨y, rfl⟩ := (sumMap_bijective π).surjective b
  change spEmbedMat (π : Fin n → Fin n) (mat n K h) (Sum.map π π x) (Sum.map π π y) =
    mat n K (permSp K π * h * (permSp K π)⁻¹) (Sum.map π π x) (Sum.map π π y)
  rw [spEmbedMat_apply_image π.injective, mat_conj_permSp_apply]

theorem conj_permSp_shortBlock {n : ℕ} (π : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : i ≠ j) (A : SL(2, K)) :
    permSp K π * shortBlock K hij A * (permSp K π)⁻¹ =
      shortBlock K (π.injective.ne hij) A := by
  have h := spEmbed_comp_shortBlock_of_injective (K := K) π.injective hij
  rw [spEmbed_perm_eq_conj] at h
  exact congrArg (fun f : SL(2, K) →* StatedSp n K => f A) h

theorem exists_conj_rootSL2_range [Finite K] [CharP K 2] (i : Fin 3) :
    ∃ (g : StatedSp 3 K) (ι : SL(2, K) →* StatedSp 2 K),
      (ι = shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) ∨ ι = longBlock K 2 1) ∧
      ((spEmbed Fin.succ (Fin.succ_injective 2)).comp ι).range =
        (((spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i).map
          (MulAut.conj g).toMonoidHom) := by
  have hshort : ((spEmbed Fin.succ (Fin.succ_injective 2)).comp
      (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1))) =
      shortBlock K (by decide : (1 : Fin 3) ≠ 2) :=
    spEmbed_comp_shortBlock_of_injective (Fin.succ_injective 2) zero_ne_one
  have hlong : ((spEmbed Fin.succ (Fin.succ_injective 2)).comp
      (longBlock K 2 1)) = longBlock K 3 2 :=
    MonoidHom.ext fun A => spEmbed_longBlock (Fin.succ_injective 2) 1 A
  fin_cases i
  · let π : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
    refine ⟨permSp K π, shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1), Or.inl rfl, ?_⟩
    rw [hshort]
    change (shortBlock K (by decide : (1 : Fin 3) ≠ 2)).range =
      (CFSG.LieType.CurtisTits.rankOne (rootGroup 3 K) 0).map
        (MulAut.conj (permSp K π)).toMonoidHom
    rw [← range_shortBlock_eq_rankOne (by decide : (0 : Fin 3).val + 1 < 3),
      ← MonoidHom.range_comp]
    congr 1
    apply MonoidHom.ext
    intro A
    have h := (conj_permSp_shortBlock (K := K) π (by decide : (0 : Fin 3) ≠ 1) A).symm
    have hπ0 : π 0 = (1 : Fin 3) := by decide
    have hπ1 : π 1 = (2 : Fin 3) := by decide
    simpa only [hπ0, hπ1, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] using h
  · refine ⟨1, shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1), Or.inl rfl, ?_⟩
    rw [hshort]
    change (shortBlock K (by decide : (1 : Fin 3) ≠ 2)).range =
      (CFSG.LieType.CurtisTits.rankOne (rootGroup 3 K) 1).map (MulAut.conj 1).toMonoidHom
    rw [range_shortBlock_eq_rankOne (by decide : (1 : Fin 3).val + 1 < 3)]
    have hconj : (MulAut.conj (1 : StatedSp 3 K)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [hconj, Subgroup.map_id]
  · refine ⟨1, longBlock K 2 1, Or.inr rfl, ?_⟩
    rw [hlong]
    change (longBlock K 3 2).range =
      (CFSG.LieType.CurtisTits.rankOne (rootGroup 3 K) 2).map (MulAut.conj 1).toMonoidHom
    rw [range_longBlock_eq_rankOne (by decide : ¬(2 : Fin 3).val + 1 < 3)]
    have hconj : (MulAut.conj (1 : StatedSp 3 K)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [hconj, Subgroup.map_id]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
