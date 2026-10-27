module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2

import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
open CFSG.Open
open Matrix

variable {k : ℕ} {K : Type} [Field K]

private lemma slMat_eq_symm_G11 (g : ↥(StatedSL k K)) :
    slMat g =
      (((specialLinearGroupEquivStatedSL k K).symm g :
          Matrix.SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) := by
  conv_lhs => rw [← MulEquiv.apply_symm_apply (specialLinearGroupEquivStatedSL k K) g]
  exact specialLinearGroupEquivStatedSL_coe k K _

private lemma map_flagSpace_eq_iff_G11 {M : Matrix (Fin k) (Fin k) K} (hM : IsUnit M) (c : ℕ) :
    (LinearFlag.flagSpace k K c).map M.mulVecLin = LinearFlag.flagSpace k K c ↔
      ∀ i j : Fin k, c ≤ (i : ℕ) → (j : ℕ) < c → M i j = 0 := by
  constructor
  · intro h i j hic hjc
    have he : (Pi.single j (1 : K) : Fin k → K) ∈ LinearFlag.flagSpace k K c := by
      rw [LinearFlag.mem_flagSpace]
      intro m hm
      rw [Pi.single_eq_of_ne (by rintro rfl; omega : m ≠ j)]
    have hmem : M *ᵥ (Pi.single j (1 : K) : Fin k → K) ∈ LinearFlag.flagSpace k K c := by
      rw [← h]
      exact Submodule.mem_map_of_mem he
    have hz := (LinearFlag.mem_flagSpace.mp hmem) i hic
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at hz
  · intro h
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro x ⟨v, hv, rfl⟩
      rw [LinearFlag.mem_flagSpace]
      intro i hi
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_eq_zero fun j _ => by
        by_cases hjc : (j : ℕ) < c
        · rw [h i j hi hjc, zero_mul]
        · rw [LinearFlag.mem_flagSpace.mp hv j (not_lt.mp hjc), mul_zero]
    · exact (Submodule.equivMapOfInjective M.mulVecLin
        (Matrix.mulVec_injective_iff_isUnit.mpr hM) (LinearFlag.flagSpace k K c)).finrank_eq.symm

private lemma mem_slQZero_iff_G11 [NeZero k] {g : ↥(StatedSL k K)} :
    g ∈ slQZero k K ↔ ∀ i : Fin k, i ≠ 0 → slMat g i 0 = 0 := by
  unfold slQZero
  rw [mem_lineStab]
  constructor
  · rintro ⟨c, hc⟩ i hi
    have h := congrFun hc i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne hi,
      smul_zero] at h
    exact h
  · intro h
    refine ⟨slMat g 0 0, ?_⟩
    ext i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply]
    by_cases hi : i = 0
    · subst hi
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [Pi.single_eq_of_ne hi, smul_zero]
      exact h i hi

private lemma mem_map_flagStabilizer_one_G11 [NeZero k] {g : ↥(StatedSL k K)} :
    g ∈ (LinearFlag.flagStabilizer k K ({1} : Set ℕ)).map
        (specialLinearGroupEquivStatedSL k K).toMonoidHom ↔
      ∀ i : Fin k, i ≠ 0 → slMat g i 0 = 0 := by
  have hu : IsUnit (((specialLinearGroupEquivStatedSL k K).symm g :
      Matrix.SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) := by
    rw [Matrix.isUnit_iff_isUnit_det, ((specialLinearGroupEquivStatedSL k K).symm g).2]
    exact isUnit_one
  rw [Subgroup.mem_map_equiv, LinearFlag.mem_flagStabilizer]
  constructor
  · intro h i hi
    have hmem : (specialLinearGroupEquivStatedSL k K).symm g ∈
        LinearFlag.stabilizer (LinearFlag.flagSpace k K 1) := h 1 (by simp)
    have h2 := (map_flagSpace_eq_iff_G11 (K := K) hu 1).mp (by
      rwa [LinearFlag.mem_stabilizer] at hmem)
    have hpos : 1 ≤ (i : ℕ) := by
      have := (Fin.pos_iff_ne_zero' i).mpr hi
      omega
    have hthis := h2 i 0 hpos (by simp)
    rw [slMat_eq_symm_G11 g]
    exact hthis
  · intro h i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    rw [LinearFlag.mem_stabilizer]
    refine (map_flagSpace_eq_iff_G11 (K := K) hu 1).mpr fun a b h1 hb => ?_
    have ha : a ≠ 0 := by
      rintro rfl
      simp at h1
    have hb' : b = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    subst hb'
    have := h a ha
    rwa [slMat_eq_symm_G11 g] at this

private lemma flagStabilizer_anti_G11 {I J : Set ℕ} (h : I ⊆ J) :
    LinearFlag.flagStabilizer k K J ≤ LinearFlag.flagStabilizer k K I := by
  intro g hg
  rw [LinearFlag.mem_flagStabilizer] at hg ⊢
  intro i hi
  exact hg i (h hi)

private lemma borelOvergroupCuts_subset_slAlphaCuts_G11
    {P' : Subgroup (SpecialLinearGroup (Fin k) K)}
    (h1 : 1 ∉ LinearFlag.borelOvergroupCuts P') :
    LinearFlag.borelOvergroupCuts P' ⊆ slAlphaCuts k := by
  intro i hi
  have hmem := hi
  simp only [LinearFlag.borelOvergroupCuts, Set.mem_setOf_eq] at hi
  obtain ⟨hi1, hik, -⟩ := hi
  have hne : i ≠ 1 := by
    intro h
    exact h1 (h ▸ hmem)
  have h2 : 2 ≤ i := by
    have : 1 < i := lt_of_le_of_ne hi1 (Ne.symm hne)
    omega
  exact ⟨h2, hik⟩

theorem exists_sylow_slU {k : ℕ} (hk : 1 ≤ k) {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ U : Sylow 2 ↥(StatedSL k K), (U : Subgroup ↥(StatedSL k K)) = slU k K := by
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 hk
  have hf : Function.Surjective (specialLinearGroupEquivStatedSL k K).toMonoidHom :=
    (specialLinearGroupEquivStatedSL k K).surjective
  refine ⟨P.mapSurjective (f := (specialLinearGroupEquivStatedSL k K).toMonoidHom) hf, ?_⟩
  rw [Sylow.coe_mapSurjective, hP]
  unfold slU
  rfl

theorem normalizer_slU (k : ℕ) (K : Type) [Field K] :
    Subgroup.normalizer (slU k K : Set ↥(StatedSL k K)) =
      (LinearFlag.upperTriangular k K).map (specialLinearGroupEquivStatedSL k K).toMonoidHom := by
  unfold slU
  rw [← Subgroup.map_equiv_normalizer_eq (LinearFlag.unitriangular k K)
    (specialLinearGroupEquivStatedSL k K), LinearFlag.normalizer_unitriangular]

theorem slU_le_slQAlpha (k : ℕ) (K : Type) [Field K] : slU k K ≤ slQAlpha k K := by
  unfold slU slQAlpha
  exact Subgroup.map_mono (le_trans (LinearFlag.unitriangular_le_upperTriangular k K)
    (LinearFlag.upperTriangular_le_flagStabilizer (K := K) (n := k) (slAlphaCuts k)))

theorem normalizer_slU_le_slQAlpha (k : ℕ) (K : Type) [Field K] :
    Subgroup.normalizer (slU k K : Set ↥(StatedSL k K)) ≤ slQAlpha k K := by
  rw [normalizer_slU k K]
  unfold slQAlpha
  exact Subgroup.map_mono (LinearFlag.upperTriangular_le_flagStabilizer (K := K) (n := k)
    (slAlphaCuts k))

theorem isParabolicTwo_slQAlpha {k : ℕ} (hk : 1 ≤ k) {K : Type} [Field K] [Finite K] [CharP K 2] :
    IsParabolicTwo ↥(StatedSL k K) (slQAlpha k K) := by
  obtain ⟨U, hU⟩ := exists_sylow_slU hk (K := K)
  refine ⟨U, ?_⟩
  show Subgroup.normalizer (((U : Subgroup ↥(StatedSL k K)) : Set ↥(StatedSL k K))) ≤ slQAlpha k K
  rw [hU]
  exact normalizer_slU_le_slQAlpha k K

theorem slQZero_eq_map_flagStabilizer (k : ℕ) [NeZero k] (K : Type) [Field K] :
    slQZero k K = (LinearFlag.flagStabilizer k K {1}).map
      (specialLinearGroupEquivStatedSL k K).toMonoidHom := by
  ext g
  rw [mem_slQZero_iff_G11, mem_map_flagStabilizer_one_G11]

theorem not_slQAlpha_le_slQZero {k : ℕ} [NeZero k] (hk : 2 ≤ k) {K : Type} [Field K] :
    ¬ slQAlpha k K ≤ slQZero k K := by
  intro hle
  have hk1 : 1 < k := by omega
  let r := LinearFlag.reflection k K 1 le_rfl hk1
  have hrA : r ∈ LinearFlag.flagStabilizer k K (slAlphaCuts k) := by
    have hiff := (LinearFlag.subflag_stabilizer_generation (K := K) (n := k)
      (slAlphaCuts k)).2.2 1 le_rfl hk1
    rw [hiff]
    intro h1
    exact absurd h1.1 (by omega)
  have hre : r ∉ LinearFlag.flagStabilizer k K ({1} : Set ℕ) := by
    intro hmem
    have hiff := (LinearFlag.subflag_stabilizer_generation (K := K) (n := k)
      ({1} : Set ℕ)).2.2 1 le_rfl hk1
    exact (hiff.mp hmem) (by simp)
  have hQa : (specialLinearGroupEquivStatedSL k K) r ∈ slQAlpha k K := by
    unfold slQAlpha
    exact Subgroup.mem_map_of_mem (specialLinearGroupEquivStatedSL k K).toMonoidHom hrA
  have hne : (specialLinearGroupEquivStatedSL k K) r ∉ slQZero k K := by
    rw [slQZero_eq_map_flagStabilizer k K, Subgroup.mem_map_equiv]
    simpa using hre
  exact hne (hle hQa)

theorem slQAlpha_le_of_parabolic {k : ℕ} [NeZero k] (hk : 2 ≤ k) {K : Type} [Field K] [Finite K]
    [CharP K 2] {P : Subgroup ↥(StatedSL k K)} (hP : IsParabolicTwo ↥(StatedSL k K) P)
    (hU : slU k K ≤ P) (hnot : ¬ P ≤ slQZero k K) : slQAlpha k K ≤ P := by
  have hk1 : 1 ≤ k := by omega
  set e := specialLinearGroupEquivStatedSL k K with he
  obtain ⟨U, hUcoe⟩ := exists_sylow_slU hk1 (K := K)
  have hnormU : Subgroup.normalizer (U : Set ↥(StatedSL k K)) ≤ P :=
    hP.normalizer_le U (by rw [hUcoe]; exact hU)
  have hBle : (LinearFlag.upperTriangular k K).map e.toMonoidHom ≤ P := by
    rw [he, ← normalizer_slU k K, ← hUcoe]
    exact hnormU
  set P' := P.comap e.toMonoidHom with hP'def
  have hBle' : LinearFlag.upperTriangular k K ≤ P' := by
    rw [hP'def, ← Subgroup.map_le_iff_le_comap]
    exact hBle
  obtain ⟨hP'I, -⟩ := LinearFlag.borel_overgroups P' hBle'
  set I := LinearFlag.borelOvergroupCuts P' with hI
  have hPmap : P'.map e.toMonoidHom = P := by
    rw [hP'def]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective P
  have h1I : 1 ∉ I := by
    intro h1mem
    have hsub : LinearFlag.flagStabilizer k K I ≤
        LinearFlag.flagStabilizer k K ({1} : Set ℕ) :=
      flagStabilizer_anti_G11 (Set.singleton_subset_iff.mpr h1mem)
    have hPle : P ≤ slQZero k K := by
      have hPeq : P = (LinearFlag.flagStabilizer k K I).map e.toMonoidHom := by
        rw [← hPmap, hP'I]
      rw [hPeq, slQZero_eq_map_flagStabilizer k K]
      exact Subgroup.map_mono hsub
    exact hnot hPle
  have hIA : I ⊆ slAlphaCuts k := by
    rw [hI] at h1I ⊢
    exact borelOvergroupCuts_subset_slAlphaCuts_G11 h1I
  have hfinal : slQAlpha k K =
      (LinearFlag.flagStabilizer k K (slAlphaCuts k)).map e.toMonoidHom := by
    unfold slQAlpha
    rw [he]
  rw [hfinal]
  have hPeq' : (LinearFlag.flagStabilizer k K I).map e.toMonoidHom = P := by
    rw [← hPmap, hP'I]
  rw [← hPeq']
  exact Subgroup.map_mono (flagStabilizer_anti_G11 hIA)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
