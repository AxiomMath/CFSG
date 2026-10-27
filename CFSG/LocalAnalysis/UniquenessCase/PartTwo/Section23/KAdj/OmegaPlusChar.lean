module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusHall
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
import CFSG.RankThree.PartOne.F106.OddRadSpTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

private theorem hom_eq_one_of_mem_hinf_E04 {G A : Type} [Group G] [CommGroup A] {Q : Subgroup G}
    (φ : ↥Q →* A) {g : G} (hg : g ∈ Hinf Q) : ∃ h : g ∈ Q, φ ⟨g, h⟩ = 1 := by
  rw [Hinf, CFSG.inSubgroup, Subgroup.mem_map] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  exact ⟨w.2, MonoidHom.mem_ker.mp
    (CFSG.RankThree.PartOne.F106.OddRadSp.perfectResidual_le_ker_of_comm φ hw)⟩

private lemma det_block_two_torusElt_E04 {K : Type} [Field K] (a : Fin 3 → Kˣ)
    (hq : torusElt 3 K a ∈ plusFlagStab K 3 ({2, 3} : Finset ℕ)) :
    (((Matrix.GeneralLinearGroup.det (plusEBlockHom (fun d hd => by simp at hd; omega)
        (b := 2) (by simp) ⟨torusElt 3 K a, hq⟩) : Kˣ)) : K) = a 0 * a 1 := by
  have hp : predCut ({2, 3} : Finset ℕ) 2 = 0 := by decide
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_plusEBlockHom, Subtype.coe_mk,
    autMat_torusElt, Matrix.submatrix_diagonal _ _ (plusEIdx_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, plusEIdx, Sum.elim_inl, Nat.add_zero, Nat.zero_add, hp,
    Nat.sub_zero]
  show (∏ x : Fin 2, ((a ⟨(x : ℕ), by omega⟩ : Kˣ) : K)) = (a 0 : K) * (a 1 : K)
  rw [Fin.prod_univ_two]
  congr 1 <;> exact congrArg (fun u : Kˣ => (u : K)) (congrArg a (Fin.ext rfl))

private lemma det_block_three_torusElt_E04 {K : Type} [Field K] (a : Fin 3 → Kˣ)
    (hq : torusElt 3 K a ∈ plusFlagStab K 3 ({2, 3} : Finset ℕ)) :
    (((Matrix.GeneralLinearGroup.det (plusEBlockHom (fun d hd => by simp at hd; omega)
        (b := 3) (by simp) ⟨torusElt 3 K a, hq⟩) : Kˣ)) : K) = ((a 2 : Kˣ) : K) := by
  have hp : predCut ({2, 3} : Finset ℕ) 3 = 2 := by decide
  have h3 : (3 : ℕ) - 2 = 1 := by norm_num
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_plusEBlockHom, Subtype.coe_mk,
    autMat_torusElt, Matrix.submatrix_diagonal _ _ (plusEIdx_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, plusEIdx, Sum.elim_inl, Nat.add_zero, Nat.zero_add, hp, h3]
  show (∏ x : Fin 1, ((a ⟨2 + (x : ℕ), by omega⟩ : Kˣ) : K)) = (a 2 : K)
  rw [Fin.prod_univ_one]
  exact congrArg (fun u : Kˣ => (u : K)) (congrArg a (Fin.ext rfl))

private lemma orderOf_torusElt_coroot_E04 {K : Type} [Field K] (c : Kˣ) :
    orderOf (torusElt 3 K ![c, c⁻¹, 1]) = orderOf c := by
  rw [orderOf_injective (torusElt 3 K) (torusElt_injective (r := 3) (K := K)) ![c, c⁻¹, 1]]
  refine orderOf_eq_orderOf_iff.mpr fun n => ?_
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h
    funext i
    fin_cases i <;> simp [h, inv_pow]

theorem torusElt_blocks_of_mem_hinf {K : Type} [Field K] [Finite K] [CharP K 2] {a : Fin 3 → Kˣ}
    (h : torusElt 3 K a ∈ Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ))) :
    a 0 * a 1 = 1 ∧ a 2 = 1 := by
  obtain ⟨hq, h2⟩ := hom_eq_one_of_mem_hinf_E04
    (Matrix.GeneralLinearGroup.det.comp (plusEBlockHom (fun d hd => by simp at hd; omega)
      (b := 2) (by simp))) h
  obtain ⟨hq', h3⟩ := hom_eq_one_of_mem_hinf_E04
    (Matrix.GeneralLinearGroup.det.comp (plusEBlockHom (fun d hd => by simp at hd; omega)
      (b := 3) (by simp))) h
  have h2d : Matrix.GeneralLinearGroup.det (plusEBlockHom (fun d hd => by simp at hd; omega)
      (b := 2) (by simp) ⟨torusElt 3 K a, hq⟩) = 1 := by
    simpa only [MonoidHom.comp_apply] using h2
  have h3d : Matrix.GeneralLinearGroup.det (plusEBlockHom (fun d hd => by simp at hd; omega)
      (b := 3) (by simp) ⟨torusElt 3 K a, hq'⟩) = 1 := by
    simpa only [MonoidHom.comp_apply] using h3
  have e2 := det_block_two_torusElt_E04 a hq
  have e3 := det_block_three_torusElt_E04 a hq'
  rw [h2d] at e2
  rw [h3d] at e3
  exact ⟨by apply Units.ext; simpa using e2.symm, by apply Units.ext; simpa using e3.symm⟩

theorem exists_conj_torusElt_coroot {K : Type} [Field K] [Finite K] [CharP K 2] {t : PlusLin K}
    (ht : t ∈ Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ)) ⊓ plusFlagStab K 3 ({1} : Finset ℕ))
    (hodd : Odd (orderOf t)) :
    ∃ e ∈ unipotent 3 K, ∃ c : Kˣ,
      e * t * e⁻¹ = torusElt 3 K ![c, c⁻¹, 1] ∧ orderOf c = orderOf t := by
  have htB : t ∈ borel 3 K := by
    have hle : Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ)) ≤ plusFlagStab K 3 ({2, 3} : Finset ℕ) :=
      Subgroup.map_subtype_le _
    rw [← plusFlagStab_inf_eq_borel K]
    exact ⟨ht.2, hle ht.1⟩
  obtain ⟨e, he, a, hae⟩ := exists_conj_torusElt_of_mem_borel htB hodd
  have heQ : e ∈ plusFlagStab K 3 ({2, 3} : Finset ℕ) := by
    have hb : e ∈ borel 3 K := unipotent_le_borel he
    rw [← plusFlagStab_inf_eq_borel K] at hb
    exact hb.2
  have hconj : e * t * e⁻¹ ∈ Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ)) := by
    have hN := uc22p22m_le_normalizer_Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ)) heQ
    exact (Subgroup.mem_normalizer_iff.mp hN t).mp ht.1
  have hblocks := torusElt_blocks_of_mem_hinf (a := a) (hae ▸ hconj)
  have ha : a = ![a 0, (a 0)⁻¹, 1] := by
    funext i
    fin_cases i
    · simp
    · simp [eq_inv_of_mul_eq_one_right hblocks.1]
    · simp [hblocks.2]
  have h1 : orderOf (e * t * e⁻¹) = orderOf t := by
    rw [← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective t
  refine ⟨e, he, a 0, ?_, ?_⟩
  · rw [hae]
    exact congrArg (torusElt 3 K) ha
  · rw [← h1, hae, ha, orderOf_torusElt_coroot_E04]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
