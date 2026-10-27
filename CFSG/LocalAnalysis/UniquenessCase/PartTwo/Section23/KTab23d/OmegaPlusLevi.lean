module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusBlocks
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamData
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.AGLEmbedding.LeviBlock

open scoped commutatorElement

private theorem hD1_Q09 : ∀ d ∈ ({1} : Finset ℕ), 1 ≤ d := by
  intro d hd
  rw [Finset.mem_singleton] at hd
  omega

private theorem hD'_Q09 : ∀ d ∈ ({1} : Finset ℕ), d ≤ 3 := by
  intro d hd
  rw [Finset.mem_singleton] at hd
  omega

private theorem hD2_Q09 : ∀ d ∈ ({1} : Finset ℕ), 1 ≤ d ∧ d ≤ 3 - 2 := by
  intro d hd
  rw [Finset.mem_singleton] at hd
  subst d
  norm_num

private theorem hb_Q09 : 1 ∈ ({1} : Finset ℕ) := by simp

private theorem ht_Q09 :
    ({1} : Finset ℕ).sup id = 0 ∨ ({1} : Finset ℕ).sup id ∈ ({1} : Finset ℕ) :=
  sup_eq_zero_or_mem _

private theorem ht2_Q09 : ({1} : Finset ℕ).sup id + 2 = 3 := by simp

private theorem hDt_Q09 : ∀ d ∈ ({1} : Finset ℕ), d ≤ ({1} : Finset ℕ).sup id := by
  intro d hd
  rw [Finset.mem_singleton] at hd
  subst d
  simp

private theorem hr_Q09 : 3 ≤ 3 := le_refl 3

private theorem predCut1_Q09 : predCut ({1} : Finset ℕ) 1 = 0 := predCut_one hD1_Q09

private theorem hk_Q09 : 1 - predCut ({1} : Finset ℕ) 1 = 1 := by
  rw [predCut1_Q09]

private noncomputable def beta_Q09 (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(plusFlagStab K 3 ({1} : Finset ℕ)) →*
      GL (Fin (1 - predCut ({1} : Finset ℕ) 1)) K × GL (Fin 2) K × GL (Fin 2) K :=
  (plusEBlockHom (K := K) hD'_Q09 hb_Q09).prod
    ((plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 0).prod
      (plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 1))

private theorem beta_Q09_apply (K : Type) [Field K] [Finite K] [CharP K 2]
    (g : ↥(plusFlagStab K 3 ({1} : Finset ℕ))) :
    beta_Q09 K g = (plusEBlockHom (K := K) hD'_Q09 hb_Q09 g,
      plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 0 g,
      plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 1 g) :=
  rfl

private noncomputable def slSq_Q09 (K : Type) [Field K] :
    (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) →*
      GL (Fin (1 - predCut ({1} : Finset ℕ) 1)) K × GL (Fin 2) K × GL (Fin 2) K where
  toFun p := (1, Matrix.SpecialLinearGroup.toGL p.1, Matrix.SpecialLinearGroup.toGL p.2)
  map_one' := by ext <;> simp
  map_mul' p q := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

private theorem slSq_Q09_apply (K : Type) [Field K]
    (p : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    slSq_Q09 K p =
      (1, Matrix.SpecialLinearGroup.toGL p.1, Matrix.SpecialLinearGroup.toGL p.2) :=
  rfl

private theorem slSq_Q09_injective (K : Type) [Field K] :
    Function.Injective (slSq_Q09 K) := by
  intro p q h
  have h1 : Matrix.SpecialLinearGroup.toGL p.1 = Matrix.SpecialLinearGroup.toGL q.1 := by
    have := congrArg (fun z => z.2.1) h
    simpa only [slSq_Q09_apply] using this
  have h2 : Matrix.SpecialLinearGroup.toGL p.2 = Matrix.SpecialLinearGroup.toGL q.2 := by
    have := congrArg (fun z => z.2.2) h
    simpa only [slSq_Q09_apply] using this
  exact Prod.ext (Matrix.SpecialLinearGroup.toGL_injective h1)
    (Matrix.SpecialLinearGroup.toGL_injective h2)

private theorem equiv_Q09 (K : Type) [Field K] :
    Nonempty (↥(slSq_Q09 K).range ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :=
  ⟨(MonoidHom.ofInjective (slSq_Q09_injective K)).symm⟩

private theorem hker_Q09 (K : Type) [Field K] [Finite K] [CharP K 2] :
    IsPGroup 2 ↥(beta_Q09 K).ker := by
  refine isPGroup_of_plusBlocks (K := K) (r := 3) hD'_Q09 hD1_Q09 ?_
  intro g hg
  have hg1 : beta_Q09 K g = 1 := MonoidHom.mem_ker.mp hg
  rw [beta_Q09_apply, Prod.mk_eq_one, Prod.mk_eq_one] at hg1
  obtain ⟨he, h0, h1⟩ := hg1
  refine ⟨?_, ?_⟩
  · intro b hb
    have hb1 : b = 1 := Finset.mem_singleton.mp hb
    subst b
    rw [show hb = hb_Q09 from Subsingleton.elim _ _]
    exact he
  · intro x hx
    exact sub_mem_of_plusResBlockHom_eq_one hD'_Q09 ht_Q09 ht2_Q09
      (plusResBlockHom_eq_one_of_plusResAut hD'_Q09 ht_Q09 ht2_Q09
        (plusResAut_eq_one_of_plusFamHom hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 h0 h1)) hx

private theorem beta_Q09_resExt_iotaTwo (K : Type) [Field K] [Finite K] [CharP K 2]
    (x : Matrix.SpecialLinearGroup (Fin 2) K)
    (hq : plusResExt K ht2_Q09 (plusIotaTwo K x) ∈ plusFlagStab K 3 ({1} : Finset ℕ)) :
    beta_Q09 K ⟨plusResExt K ht2_Q09 (plusIotaTwo K x), hq⟩ =
      (1, Matrix.SpecialLinearGroup.toGL x, 1) := by
  rw [beta_Q09_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact plusEBlockHom_plusResExt (K := K) hD'_Q09 ht2_Q09 hDt_Q09 hb_Q09 hq
  · exact (plusFamHom_iotaTwo (K := K) hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 hq).1
  · exact (plusFamHom_iotaTwo (K := K) hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 hq).2

private theorem beta_Q09_resExt_iotaOne (K : Type) [Field K] [Finite K] [CharP K 2]
    (y : Matrix.SpecialLinearGroup (Fin 2) K)
    (hq : plusResExt K ht2_Q09 (plusIotaOne K y) ∈ plusFlagStab K 3 ({1} : Finset ℕ)) :
    beta_Q09 K ⟨plusResExt K ht2_Q09 (plusIotaOne K y), hq⟩ =
      (1, 1, Matrix.SpecialLinearGroup.toGL y) := by
  rw [beta_Q09_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact plusEBlockHom_plusResExt (K := K) hD'_Q09 ht2_Q09 hDt_Q09 hb_Q09 hq
  · exact (plusFamHom_iotaOne (K := K) hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 hq).1
  · exact (plusFamHom_iotaOne (K := K) hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 hq).2

private theorem hSR_Q09 (K : Type) [Field K] [Finite K] [CharP K 2] :
    (slSq_Q09 K).range ≤ (beta_Q09 K).range := by
  rintro _ ⟨⟨x, y⟩, rfl⟩
  have hq2 : plusResExt K ht2_Q09 (plusIotaTwo K x) ∈ plusFlagStab K 3 ({1} : Finset ℕ) :=
    plusResExt_iotaTwo_mem hr_Q09 ht2_Q09 hDt_Q09 x
  have hq1 : plusResExt K ht2_Q09 (plusIotaOne K y) ∈ plusFlagStab K 3 ({1} : Finset ℕ) :=
    plusResExt_iotaOne_mem hr_Q09 ht2_Q09 hDt_Q09 y
  refine ⟨⟨plusResExt K ht2_Q09 (plusIotaTwo K x), hq2⟩ *
    ⟨plusResExt K ht2_Q09 (plusIotaOne K y), hq1⟩, ?_⟩
  rw [map_mul, beta_Q09_resExt_iotaTwo K x hq2, beta_Q09_resExt_iotaOne K y hq1,
    slSq_Q09_apply]
  simp

private theorem commutator_prod_Q09 {A B C : Type} [Group A] [Group B] [Group C]
    (a b : A × B × C) :
    ⁅a, b⁆ = (⁅a.1, b.1⁆, (⁅a.2.1, b.2.1⁆, ⁅a.2.2, b.2.2⁆)) := by
  ext <;> simp [commutatorElement_def]

private theorem commutator_beta_Q09 (K : Type) [Field K] [Finite K] [CharP K 2]
    (g h : ↥(plusFlagStab K 3 ({1} : Finset ℕ))) :
    ⁅beta_Q09 K g, beta_Q09 K h⁆ =
      (⁅plusEBlockHom (K := K) hD'_Q09 hb_Q09 g,
          plusEBlockHom (K := K) hD'_Q09 hb_Q09 h⁆,
       (⁅plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 0 g,
          plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 0 h⁆,
        ⁅plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 1 g,
          plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 1 h⁆)) := by
  rw [beta_Q09_apply, beta_Q09_apply, commutator_prod_Q09]

private theorem plusFamHom_range_le_toGL_Q09 (K : Type) [Field K] [Finite K] [CharP K 2]
    (j : Fin 2) :
    (plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 j).range ≤
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →*
        GL (Fin 2) K).range := by
  fin_cases j <;> rintro _ ⟨g, rfl⟩ <;> exact ⟨_, rfl⟩

private theorem hcomm_Q09 (K : Type) [Field K] [Finite K] [CharP K 2] :
    ⁅(beta_Q09 K).range, (beta_Q09 K).range⁆ ≤ (slSq_Q09 K).range := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨h, rfl⟩ := hb
  obtain ⟨z0, hz0⟩ := plusFamHom_range_le_toGL_Q09 K 0 ⟨g, rfl⟩
  obtain ⟨z0', hz0'⟩ := plusFamHom_range_le_toGL_Q09 K 0 ⟨h, rfl⟩
  obtain ⟨z1, hz1⟩ := plusFamHom_range_le_toGL_Q09 K 1 ⟨g, rfl⟩
  obtain ⟨z1', hz1'⟩ := plusFamHom_range_le_toGL_Q09 K 1 ⟨h, rfl⟩
  have he : ⁅plusEBlockHom (K := K) hD'_Q09 hb_Q09 g,
      plusEBlockHom (K := K) hD'_Q09 hb_Q09 h⁆ = 1 := by
    have hle := commutator_range_plusEBlockHom_le (K := K) hD'_Q09 hb_Q09
    have hmem := Subgroup.commutator_le.mp hle _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    rw [range_toGL_eq_bot_of_eq_one hk_Q09] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hz0c : ⁅plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 0 g,
      plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 0 h⁆ =
      Matrix.SpecialLinearGroup.toGL ⁅z0, z0'⁆ := by
    rw [map_commutatorElement (f := Matrix.SpecialLinearGroup.toGL), hz0, hz0']
  have hz1c : ⁅plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 1 g,
      plusFamHom K hr_Q09 hD2_Q09 hD'_Q09 ht_Q09 ht2_Q09 1 h⁆ =
      Matrix.SpecialLinearGroup.toGL ⁅z1, z1'⁆ := by
    rw [map_commutatorElement (f := Matrix.SpecialLinearGroup.toGL), hz1, hz1']
  refine ⟨(⁅z0, z0'⁆, ⁅z1, z1'⁆), ?_⟩
  rw [slSq_Q09_apply, commutator_beta_Q09, he, hz0c, hz1c]

theorem exists_leviHom_plusFlagStab_three {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ (A : Type) (_ : Group A) (β : ↥(plusFlagStab K 3 ({1} : Finset ℕ)) →* A) (S : Subgroup A),
      Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) ∧
        IsPGroup 2 ↥β.ker ∧ S ≤ β.range ∧ ⁅β.range, β.range⁆ ≤ S := by
  refine ⟨GL (Fin (1 - predCut ({1} : Finset ℕ) 1)) K × GL (Fin 2) K × GL (Fin 2) K,
    inferInstance, beta_Q09 K, (slSq_Q09 K).range, equiv_Q09 K, hker_Q09 K, hSR_Q09 K,
    hcomm_Q09 K⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
