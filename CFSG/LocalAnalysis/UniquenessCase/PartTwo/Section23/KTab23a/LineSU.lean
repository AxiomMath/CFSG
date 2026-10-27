module

public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Open
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open Matrix
open scoped Matrix

private lemma exists_pow_two_of_card {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} (hK : Nat.card K = r ^ 2) : ∃ f, r = 2 ^ f := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, _h2, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card] at hK
  have hrn : r ^ 2 = 2 ^ (n : ℕ) := by rw [← hK, hcard]
  have hpp : IsPrimePow (r ^ 2) := by
    rw [hrn]
    exact (isPrimePow_nat_iff (2 ^ (n : ℕ))).mpr
      ⟨2, (n : ℕ), Nat.prime_two, n.pos, rfl⟩
  have hpr : IsPrimePow r := (isPrimePow_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpp
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff r).mp hpr
  have hp2 : p = 2 := by
    have hpr_dvd : p ∣ r := by rw [← hpk]; exact dvd_pow_self p hk.ne'
    have hr_dvd : r ∣ 2 ^ (n : ℕ) := by rw [← hrn]; exact dvd_pow_self r (by norm_num)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (hpr_dvd.trans hr_dvd))
  exact ⟨k, by rw [← hpk, hp2]⟩

private def suLine (d : ℕ) (K : Type) [Field K] [NeZero d] : Fin d → K :=
  Pi.single (0 : Fin d) 1 + Pi.single (1 : Fin d) 1

private lemma fin_zero_ne_one {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    (0 : Fin d) ≠ (1 : Fin d) := by
  rw [Fin.ne_iff_vne]
  have h1 : ((1 : Fin d) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < d)]
  have h0 : ((0 : Fin d) : ℕ) = 0 := rfl
  omega

private lemma gramForm_single_left {K : Type} [Field K] {d f : ℕ}
    (h : UnitaryFieldData 2 f K) (i : Fin d) (v : Fin d → K) :
    gramForm h 1 (Pi.single i 1 : Fin d → K) v = v i := by
  rw [gramForm_apply]
  have hfun : (fun c => h.bar ((Pi.single i (1 : K) : Fin d → K) c)) =
      (Pi.single i 1 : Fin d → K) := by
    funext c
    by_cases hc : c = i
    · subst hc; simp
    · simp [hc]
  rw [hfun, Matrix.one_mulVec, single_one_dotProduct]

private lemma gramForm_single_add_single {K : Type} [Field K] {d f : ℕ}
    (h : UnitaryFieldData 2 f K) (i j : Fin d) (v : Fin d → K) :
    gramForm h 1 (Pi.single i 1 + Pi.single j 1 : Fin d → K) v = v i + v j := by
  simp only [map_add, LinearMap.add_apply, gramForm_single_left h i v,
    gramForm_single_left h j v]

private lemma suLine_apply_zero {K : Type} [Field K] {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    suLine d K (0 : Fin d) = 1 := by
  unfold suLine
  simp [fin_zero_ne_one hd, (fin_zero_ne_one hd).symm]

private lemma suLine_apply_one {K : Type} [Field K] {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    suLine d K (1 : Fin d) = 1 := by
  unfold suLine
  simp [fin_zero_ne_one hd, (fin_zero_ne_one hd).symm]

private lemma suLine_apply_ne {K : Type} [Field K] {d : ℕ} [NeZero d] {i : Fin d}
    (h0 : i ≠ (0 : Fin d)) (h1 : i ≠ (1 : Fin d)) :
    suLine d K i = 0 := by
  unfold suLine
  simp [h0, h0.symm, h1, h1.symm]

private lemma gramForm_suLine_apply {K : Type} [Field K] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (v : Fin d → K) :
    gramForm h 1 (suLine d K) v = v (0 : Fin d) + v (1 : Fin d) := by
  unfold suLine
  exact gramForm_single_add_single h (0 : Fin d) (1 : Fin d) v

private lemma gramFormOne_isSymm {K : Type} [Field K] {f d : ℕ} (h : UnitaryFieldData 2 f K) :
    (gramForm h (1 : Matrix (Fin d) (Fin d) K)).IsSymm := by
  refine gramForm_isSymm h ?_
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij; simp [Matrix.map_apply, Matrix.one_apply, Matrix.transpose_apply]
  · have hji : j ≠ i := fun hh => hij hh.symm
    simp [Matrix.map_apply, Matrix.one_apply, Matrix.transpose_apply, hij, hji]

private lemma gramForm_suLine_self {K : Type} [Field K] [CharP K 2] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (hd : 2 ≤ d) :
    gramForm h 1 (suLine d K) (suLine d K) = 0 := by
  rw [gramForm_suLine_apply h (suLine d K), suLine_apply_zero hd, suLine_apply_one hd]
  exact CharTwo.add_self_eq_zero 1

private lemma gramForm_suLine_single_zero {K : Type} [Field K] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (hd : 2 ≤ d) {j : Fin d}
    (hj0 : j ≠ (0 : Fin d)) (hj1 : j ≠ (1 : Fin d)) :
    gramForm h 1 (suLine d K) (Pi.single j 1 : Fin d → K) = 0 := by
  rw [gramForm_suLine_apply h (Pi.single j 1 : Fin d → K)]
  simp [hj0, hj0.symm, hj1, hj1.symm]

private lemma gramForm_suLine_span_iso {K : Type} [Field K] [CharP K 2] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (hd : 2 ≤ d) {x y : Fin d → K}
    (hx : x ∈ Submodule.span K {suLine d K}) (hy : y ∈ Submodule.span K {suLine d K}) :
    gramForm h 1 x y = 0 := by
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, gramForm_suLine_self h hd,
    smul_zero]

private lemma suLine_fixed_mem_span {K : Type} [Field K] [CharP K 2] {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (v : Fin d → K) (hv0 : v (0 : Fin d) + v (1 : Fin d) = 0)
    (hvj : ∀ j, j ≠ (0 : Fin d) → j ≠ (1 : Fin d) → v j = 0) :
    v ∈ Submodule.span K {suLine d K} := by
  refine Submodule.mem_span_singleton.mpr ⟨v (0 : Fin d), ?_⟩
  funext i
  by_cases hi0 : i = (0 : Fin d)
  · subst hi0; rw [Pi.smul_apply, smul_eq_mul, suLine_apply_zero (K := K) hd, mul_one]
  · by_cases hi1 : i = (1 : Fin d)
    · subst hi1
      have hv : v (1 : Fin d) = v (0 : Fin d) := by
        have h := eq_neg_of_add_eq_zero_left hv0
        rw [CharTwo.neg_eq] at h
        exact h.symm
      rw [hv, Pi.smul_apply, smul_eq_mul, suLine_apply_one (K := K) hd, mul_one]
    · rw [hvj i hi0 hi1, Pi.smul_apply, smul_eq_mul, suLine_apply_ne hi0 hi1, mul_zero]

private lemma radical_transvection_fixed {K : Type} [Field K] [CharP K 2] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (hd : 2 ≤ d) (v : Fin d → K)
    (hfix : ∀ u ∈ isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
        (Submodule.span K {suLine d K}),
        ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = v) :
    gramForm h 1 (suLine d K) v = 0 := by
  have hH : (gramForm h (1 : Matrix (Fin d) (Fin d) K)).IsSymm := gramFormOne_isSymm h
  have hWiso : ∀ x ∈ Submodule.span K {suLine d K},
      ∀ y ∈ Submodule.span K {suLine d K}, gramForm h 1 x y = 0 :=
    fun x hx y hy => gramForm_suLine_span_iso h hd hx hy
  have haW : suLine d K ∈ Submodule.span K {suLine d K} := Submodule.mem_span_singleton_self _
  have h0W : (0 : Fin d → K) ∈
      (Submodule.span K {suLine d K}).orthogonalBilin (gramForm h 1) := Submodule.zero_mem _
  have hwy : gramForm h 1 (suLine d K) (0 : Fin d → K) = 0 :=
    Submodule.mem_orthogonalBilin.mp h0W (suLine d K) haW
  have hc : (1 : K) + h.bar 1 = -gramForm h 1 (0 : Fin d → K) (0 : Fin d → K) := by
    simp only [map_one, CharTwo.add_self_eq_zero, map_zero, LinearMap.zero_apply, neg_zero]
  let g : gramSU h (1 : Matrix (Fin d) (Fin d) K) :=
    ⟨unipotentGL (eichlerMatrix h 1 (suLine d K) (0 : Fin d → K) 1)
        (eichlerMatrix_sub_one_pow_three hH (hWiso _ haW _ haW) hwy 1),
      eichlerGL_mem hH (hWiso _ haW _ haW) hwy hc⟩
  have hg : g ∈ isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
      (Submodule.span K {suLine d K}) :=
    eichler_mem_radical hH hWiso haW h0W hc
  let T : ↥(isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
      (Submodule.span K {suLine d K})) := ⟨g, hg⟩
  have hT := hfix (T : gramSU h (1 : Matrix (Fin d) (Fin d) K)) T.2
  have hact : eichlerMatrix h 1 (suLine d K) (0 : Fin d → K) 1 *ᵥ v = v := by
    simpa [T, g, unipotentGL] using hT
  rw [eichlerMatrix_mulVec] at hact
  simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_smul, one_mul, zero_sub,
    sub_zero, add_zero] at hact
  have hx : gramForm h 1 (suLine d K) v • suLine d K = 0 := by
    have h' : v + gramForm h 1 (suLine d K) v • suLine d K = v + 0 := by
      rw [add_zero]; exact hact
    exact add_left_cancel h'
  have hval := congrFun hx (0 : Fin d)
  simpa [Pi.smul_apply, suLine_apply_zero (K := K) hd] using hval

private lemma exists_bar_add_eq_neg_one {K : Type} [Field K] {f : ℕ}
    (h : UnitaryFieldData 2 f K) : ∃ c : K, c + h.bar c = -1 := by
  obtain ⟨c, hc⟩ := h.traceLin_surjective (-1 : h.fixedField)
  refine ⟨c, ?_⟩
  have hval : h.trace c = -1 := by
    have := congrArg Subtype.val hc
    simpa using this
  exact hval

private lemma single_mem_orthogonal_suLine {K : Type} [Field K] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (hd : 2 ≤ d) {j : Fin d}
    (hj0 : j ≠ (0 : Fin d)) (hj1 : j ≠ (1 : Fin d)) :
    (Pi.single j 1 : Fin d → K) ∈
      (Submodule.span K {suLine d K}).orthogonalBilin (gramForm h 1) := by
  rw [Submodule.mem_orthogonalBilin_span]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact gramForm_suLine_single_zero h hd hj0 hj1

private lemma eichler_radical_action {K : Type} [Field K] [CharP K 2] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (hd : 2 ≤ d) (v : Fin d → K) {j : Fin d} {c : K}
    (hfix : ∀ u ∈ isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
        (Submodule.span K {suLine d K}),
        ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = v)
    (hbeta : gramForm h 1 (suLine d K) v = 0) (hj0 : j ≠ (0 : Fin d))
    (hj1 : j ≠ (1 : Fin d)) (hc : c + h.bar c = -gramForm h 1
      (Pi.single j 1 : Fin d → K) (Pi.single j 1 : Fin d → K)) :
    gramForm h 1 (Pi.single j 1 : Fin d → K) v • suLine d K = 0 := by
  have hH : (gramForm h (1 : Matrix (Fin d) (Fin d) K)).IsSymm := gramFormOne_isSymm h
  have hWiso : ∀ x ∈ Submodule.span K {suLine d K},
      ∀ y ∈ Submodule.span K {suLine d K}, gramForm h 1 x y = 0 :=
    fun x hx y hy => gramForm_suLine_span_iso h hd hx hy
  have haW : suLine d K ∈ Submodule.span K {suLine d K} := Submodule.mem_span_singleton_self _
  have hwy : gramForm h 1 (suLine d K) (Pi.single j 1 : Fin d → K) = 0 :=
    gramForm_suLine_single_zero h hd hj0 hj1
  have hy := single_mem_orthogonal_suLine h hd hj0 hj1
  let g : gramSU h (1 : Matrix (Fin d) (Fin d) K) :=
    ⟨unipotentGL (eichlerMatrix h 1 (suLine d K) (Pi.single j 1 : Fin d → K) c)
        (eichlerMatrix_sub_one_pow_three hH (hWiso _ haW _ haW) hwy c),
      eichlerGL_mem hH (hWiso _ haW _ haW) hwy hc⟩
  have hg : g ∈ isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
      (Submodule.span K {suLine d K}) :=
    eichler_mem_radical hH hWiso haW hy hc
  let S : ↥(isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
      (Submodule.span K {suLine d K})) := ⟨g, hg⟩
  have hS := hfix (S : gramSU h (1 : Matrix (Fin d) (Fin d) K)) S.2
  have hact : eichlerMatrix h 1 (suLine d K) (Pi.single j 1 : Fin d → K) c *ᵥ v = v := by
    simpa [S, g, unipotentGL] using hS
  rw [eichlerMatrix_mulVec] at hact
  rw [hbeta] at hact
  simp only [zero_smul, mul_zero, zero_add, add_zero, sub_zero] at hact
  have h' : v + (-(gramForm h 1 (Pi.single j 1 : Fin d → K) v • suLine d K)) = v + 0 := by
    rw [add_zero, ← sub_eq_add_neg]; exact hact
  have hneg := add_left_cancel h'
  simpa using hneg

private lemma radical_eichler_fixed {K : Type} [Field K] [CharP K 2] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (hd : 2 ≤ d) (v : Fin d → K)
    (hfix : ∀ u ∈ isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
        (Submodule.span K {suLine d K}),
        ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = v)
    (hbeta : gramForm h 1 (suLine d K) v = 0) (j : Fin d)
    (hj0 : j ≠ (0 : Fin d)) (hj1 : j ≠ (1 : Fin d)) :
    gramForm h 1 (Pi.single j 1 : Fin d → K) v = 0 := by
  obtain ⟨c, hc0⟩ := exists_bar_add_eq_neg_one h
  have hg1 : gramForm h 1 (Pi.single j 1 : Fin d → K) (Pi.single j 1 : Fin d → K) = 1 := by
    rw [gramForm_single_left h j (Pi.single j 1 : Fin d → K)]
    simp
  have hc : c + h.bar c = -gramForm h 1 (Pi.single j 1 : Fin d → K)
      (Pi.single j 1 : Fin d → K) := by
    rw [hg1]; exact hc0
  have hx := eichler_radical_action h hd v hfix hbeta hj0 hj1 hc
  have hval2 := congrFun hx (0 : Fin d)
  simpa [Pi.smul_apply, suLine_apply_zero (K := K) hd] using hval2

private lemma radical_fixed_mem_span {K : Type} [Field K] [CharP K 2] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) (hd : 2 ≤ d) (v : Fin d → K)
    (hfix : ∀ u ∈ isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
        (Submodule.span K {suLine d K}),
        ((u : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v = v) :
    v ∈ Submodule.span K {suLine d K} := by
  have hbeta : gramForm h 1 (suLine d K) v = 0 := radical_transvection_fixed h hd v hfix
  have hvj : ∀ j : Fin d, j ≠ (0 : Fin d) → j ≠ (1 : Fin d) → v j = 0 := by
    intro j hj0 hj1
    have := radical_eichler_fixed h hd v hfix hbeta j hj0 hj1
    rwa [gramForm_single_left h j v] at this
  have hv0 : v (0 : Fin d) + v (1 : Fin d) = 0 := by
    have := hbeta
    rwa [gramForm_suLine_apply h v] at this
  exact suLine_fixed_mem_span hd v hv0 hvj

private lemma isPGroup_radical {K : Type} [Field K] [CharP K 2] {f d : ℕ} [NeZero d]
    (h : UnitaryFieldData 2 f K) :
    IsPGroup 2 ↥(isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
      (Submodule.span K {suLine d K})) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨2, ?_⟩
  have hg := pow_four_eq_one_of_mem_radical g.2
  exact Subtype.ext (by simpa using hg)

private theorem exists_fixedLine_gramSU_large {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (h : UnitaryFieldData 2 f K) {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ (U : Subgroup ↥(gramSU h (1 : Matrix (Fin d) (Fin d) K))) (e : Fin d → K),
      IsPGroup 2 ↥U ∧
      ∀ v : Fin d → K,
        (∀ u ∈ U, ((u : GL (Fin d) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {e} := by
  refine ⟨isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
      (Submodule.span K {suLine d K}), suLine d K, isPGroup_radical h, ?_⟩
  intro v hv
  exact radical_fixed_mem_span h hd v hv

theorem exists_fixedLine_statedSU {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    (hK : Nat.card K = r ^ 2) (d : ℕ) :
    ∃ (U : Subgroup ↥(StatedSU d r K)) (e : Fin d → K), IsPGroup 2 ↥U ∧
      ∀ v : Fin d → K,
        (∀ u ∈ U, ((u : GL (Fin d) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {e} := by
  obtain ⟨f, hf⟩ := exists_pow_two_of_card hK
  haveI : Fintype K := Fintype.ofFinite K
  have hfpos : 1 ≤ f := by
    by_contra hle
    have hf0 : f = 0 := by omega
    have h1 : Nat.card K = 1 := by rw [hK, hf, hf0]; norm_num
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  let h : UnitaryFieldData 2 f K :=
    ⟨by norm_num, hfpos, by rw [hK, hf, ← pow_mul, mul_comm f 2]⟩
  rcases lt_or_ge d 2 with hd | hd
  · have hd01 : d = 0 ∨ d = 1 := by omega
    rcases hd01 with rfl | rfl
    · refine ⟨⊥, fun i => Fin.elim0 i, IsPGroup.of_bot, ?_⟩
      intro v _
      have hv : v = 0 := Subsingleton.elim v 0
      rw [hv]
      exact Submodule.zero_mem _
    · refine ⟨⊥, Pi.single (0 : Fin 1) 1, IsPGroup.of_bot, ?_⟩
      intro v _
      refine Submodule.mem_span_singleton.mpr ⟨v 0, ?_⟩
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
      rw [hi]
      simp [Pi.smul_apply]
  · haveI : NeZero d := ⟨by omega⟩
    have hSU : StatedSU d r K = gramSU h (1 : Matrix (Fin d) (Fin d) K) := by
      rw [hf]
      exact unitarySU_eq_gramSU h d
    rw [hSU]
    exact exists_fixedLine_gramSU_large h hd

theorem exists_fixedLine_statedSU_suLine {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    (hK : Nat.card K = r ^ 2) {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ U : Subgroup ↥(StatedSU d r K), IsPGroup 2 ↥U ∧
      ∀ v : Fin d → K,
        (∀ u ∈ U, ((u : GL (Fin d) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K
            {(Pi.single (0 : Fin d) 1 + Pi.single (1 : Fin d) 1 : Fin d → K)} := by
  obtain ⟨f, hf⟩ := exists_pow_two_of_card hK
  haveI : Fintype K := Fintype.ofFinite K
  have hfpos : 1 ≤ f := by
    by_contra hle
    have hf0 : f = 0 := by omega
    have h1 : Nat.card K = 1 := by rw [hK, hf, hf0]; norm_num
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    omega
  let h : UnitaryFieldData 2 f K :=
    ⟨by norm_num, hfpos, by rw [hK, hf, ← pow_mul, mul_comm f 2]⟩
  have hSU : StatedSU d r K = gramSU h (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hf]
    exact unitarySU_eq_gramSU h d
  rw [hSU]
  refine ⟨isotropicRadical h (1 : Matrix (Fin d) (Fin d) K)
    (Submodule.span K {suLine d K}), isPGroup_radical h, ?_⟩
  intro v hv
  simpa [suLine] using radical_fixed_mem_span h hd v hv

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
