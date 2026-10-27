module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

theorem slLower2Hom_injective (m : ℕ) : Function.Injective (slLower2Hom m) :=
  (slLowerBlockHom_injective (n := m + 1 + 1) (F := F2)).comp
    (slLowerBlockHom_injective (n := m + 1) (F := F2))

theorem slUpper2Hom_injective (m : ℕ) : Function.Injective (slUpper2Hom m) :=
  (slUpperBlockHom_injective (n := m + 1 + 1) (F := F2)).comp
    (slUpperBlockHom_injective (n := m + 1) (F := F2))

private theorem slLowerBlockHom_weylRep {n : ℕ} (k : Fin n) :
    slLowerBlockHom (n + 1) F2 (weylRep n F2 k) = weylRep (n + 1) F2 k.succ := by
  rw [← slPerm_swap_castSucc_succ gf2_two k]
  rw [slLowerBlockHom_slPerm_swap gf2_two k.castSucc k.succ]
  rw [show (Equiv.swap (k.castSucc : Fin (n + 1)).succ (k.succ).succ :
        Equiv.Perm (Fin (n + 1 + 1))) =
      Equiv.swap (k.succ).castSucc (k.succ).succ by rw [Fin.succ_castSucc]]
  rw [slPerm_swap_castSucc_succ gf2_two k.succ]

private theorem slUpperBlockHom_weylRep {n : ℕ} (k : Fin n) :
    slUpperBlockHom (n + 1) F2 (weylRep n F2 k) = weylRep (n + 1) F2 k.castSucc := by
  rw [← slPerm_swap_castSucc_succ gf2_two k]
  rw [slUpperBlockHom_slPerm_swap gf2_two k.castSucc k.succ]
  rw [show (Equiv.swap (k.castSucc : Fin (n + 1)).castSucc (k.succ).castSucc :
        Equiv.Perm (Fin (n + 1 + 1))) =
      Equiv.swap (k.castSucc).castSucc (k.castSucc).succ by rw [Fin.succ_castSucc]]
  rw [slPerm_swap_castSucc_succ gf2_two k.castSucc]

private theorem slLowerBlockHom_omegaBlock {n : ℕ} (k : Fin n) :
    slLowerBlockHom (n + 1) F2 (omegaBlock n k) = omegaBlock (n + 1) k.succ := by
  simp only [omegaBlock, map_mul, slLowerBlockHom_weylRep, slLowerBlockHom_transvection]

private theorem slUpperBlockHom_omegaBlock {n : ℕ} (k : Fin n) :
    slUpperBlockHom (n + 1) F2 (omegaBlock n k) = omegaBlock (n + 1) k.castSucc := by
  simp only [omegaBlock, map_mul, slUpperBlockHom_weylRep, slUpperBlockHom_transvection]

private theorem coe_omegaBlock_eq (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      signedPerm (Equiv.swap k.castSucc k.succ) (1 : Fin (n + 1) → F2) +
        Matrix.single k.succ k.succ (1 : F2) := by
  rw [omegaBlock, Matrix.SpecialLinearGroup.coe_mul, ← slPerm_swap_castSucc_succ gf2_two k,
    coe_slPerm, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.mul_one,
    signedPerm_mul_single]
  congr 1
  rw [Equiv.swap_apply_left]
  simp

private theorem omegaBlock_apply_succ_castSucc (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) k.succ k.castSucc = 1 := by
  rw [coe_omegaBlock_eq, Matrix.add_apply, signedPerm_apply, Matrix.single_apply]
  simp [Equiv.swap_apply_left, (Fin.castSucc_lt_succ (i := k)).ne, (Fin.castSucc_lt_succ (i := k)).ne']

private theorem omegaBlock_apply_succ_succ (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) k.succ k.succ = 1 := by
  rw [coe_omegaBlock_eq, Matrix.add_apply, signedPerm_apply, Matrix.single_apply]
  simp [Equiv.swap_apply_right, (Fin.castSucc_lt_succ (i := k)).ne']

private theorem omegaBlock_apply_apply_castSucc (n : ℕ) (k : Fin n) (x : Fin (n + 1)) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) x k.castSucc =
      if x = k.succ then 1 else 0 := by
  rw [coe_omegaBlock_eq, Matrix.add_apply, signedPerm_apply, Matrix.single_apply]
  simp [Equiv.swap_apply_left, (Fin.castSucc_lt_succ (i := k)).ne, (Fin.castSucc_lt_succ (i := k)).ne']

private theorem omegaBlock_sq_apply_succ_castSucc (n : ℕ) (k : Fin n) :
    (((omegaBlock n k) ^ 2 : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) k.succ k.castSucc = 1 := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single k.succ]
  · rw [omegaBlock_apply_succ_succ, omegaBlock_apply_succ_castSucc, mul_one]
  · intro x _ hx
    rw [omegaBlock_apply_apply_castSucc, if_neg hx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k.succ) h

private theorem omegaBlock_zero_apply_one_zero (m : ℕ) :
    ((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 = 1 := by
  simpa using omegaBlock_apply_succ_castSucc (m + 1 + 1) (⟨0, by omega⟩ : Fin (m + 1 + 1))

private theorem omegaBlock_zero_sq_apply_one_zero (m : ℕ) :
    (((omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ 2 :
        SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 = 1 := by
  simpa using omegaBlock_sq_apply_succ_castSucc (m + 1 + 1) (⟨0, by omega⟩ : Fin (m + 1 + 1))

private theorem slLowerBlockHom_apply_one_zero (n : ℕ)
    (A : SpecialLinearGroup (Fin (n + 1)) F2) :
    ((slLowerBlockHom (n + 1) F2 A : SpecialLinearGroup (Fin (n + 2)) F2) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) F2) 1 0 = 0 := by
  rw [coe_slLowerBlockHom]
  have h0 : (0 : Fin (n + 2)) = slLowerBlockEquiv (n + 1) (Sum.inl (0 : Fin 1)) :=
    (slLowerBlockEquiv_inl (n := n + 1) (0 : Fin 1)).symm
  have h1 : (1 : Fin (n + 2)) = slLowerBlockEquiv (n + 1) (Sum.inr (0 : Fin (n + 1))) := by
    rw [slLowerBlockEquiv_inr]
    exact Fin.ext rfl
  rw [h0, h1, slLowerBlockMat_apply]
  simp [Matrix.fromBlocks_apply₁₂]

private theorem slLower2Hom_apply_one_zero (m : ℕ)
    (s : SpecialLinearGroup (Fin (m + 1)) F2) :
    ((slLower2Hom m s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 = 0 := by
  simp only [slLower2Hom, MonoidHom.comp_apply]
  exact slLowerBlockHom_apply_one_zero (n := m + 1)
    (A := slLowerBlockHom (m + 1) F2 s)

private theorem omegaBlock_last_apply (m : ℕ) :
    ((omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩ :
        SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
      (Fin.last (m + 2)) ((Fin.last (m + 1)).castSucc) = 1 := by
  have hk : (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ = (Fin.last (m + 2) : Fin (m + 1 + 1 + 1)) :=
    Fin.ext rfl
  have hk' : (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc = (Fin.last (m + 1)).castSucc :=
    Fin.ext rfl
  rw [← hk, ← hk']
  exact omegaBlock_apply_succ_castSucc (m + 1 + 1) (⟨m + 1, by omega⟩ : Fin (m + 1 + 1))

theorem slLower2Hom_omegaBlock (m : ℕ) (j : Fin m) :
    slLower2Hom m (omegaBlock m j) = omegaBlock (m + 1 + 1) ⟨j.val + 2, by omega⟩ := by
  simp only [slLower2Hom, MonoidHom.comp_apply]
  rw [slLowerBlockHom_omegaBlock (n := m) j,
    slLowerBlockHom_omegaBlock (n := m + 1) j.succ]
  have hidx : (j.succ).succ = (⟨j.val + 2, by omega⟩ : Fin (m + 1 + 1)) := Fin.ext rfl
  rw [hidx]

theorem slUpper2Hom_omegaBlock (m : ℕ) (j : Fin m) :
    slUpper2Hom m (omegaBlock m j) = omegaBlock (m + 1 + 1) ⟨j.val, by omega⟩ := by
  simp only [slUpper2Hom, MonoidHom.comp_apply]
  rw [slUpperBlockHom_omegaBlock (n := m) j,
    slUpperBlockHom_omegaBlock (n := m + 1) j.castSucc]
  have hidx : (j.castSucc).castSucc = (⟨j.val, by omega⟩ : Fin (m + 1 + 1)) := Fin.ext rfl
  rw [hidx]

theorem slLower2Hom_weylRep (m : ℕ) (j : Fin m) :
    slLower2Hom m (weylRep m F2 j) = weylRep (m + 1 + 1) F2 ⟨j.val + 2, by omega⟩ := by
  simp only [slLower2Hom, MonoidHom.comp_apply]
  rw [slLowerBlockHom_weylRep (n := m) j,
    slLowerBlockHom_weylRep (n := m + 1) j.succ]
  have hidx : (j.succ).succ = (⟨j.val + 2, by omega⟩ : Fin (m + 1 + 1)) := Fin.ext rfl
  rw [hidx]

theorem slUpper2Hom_weylRep (m : ℕ) (j : Fin m) :
    slUpper2Hom m (weylRep m F2 j) = weylRep (m + 1 + 1) F2 ⟨j.val, by omega⟩ := by
  simp only [slUpper2Hom, MonoidHom.comp_apply]
  rw [slUpperBlockHom_weylRep (n := m) j,
    slUpperBlockHom_weylRep (n := m + 1) j.castSucc]
  have hidx : (j.castSucc).castSucc = (⟨j.val, by omega⟩ : Fin (m + 1 + 1)) := Fin.ext rfl
  rw [hidx]

theorem halfTorus_succ_succ (m : ℕ) :
    halfTorus (m + 1 + 1) = Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩) ⊔
      (halfTorus m).map (slLower2Hom m) := by
  change Subgroup.closure {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 |
      ∃ k : Fin (m + 1 + 1), k.val % 2 = 0 ∧ t = omegaBlock (m + 1 + 1) k} =
    Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ⊔
      (Subgroup.closure {t : SpecialLinearGroup (Fin (m + 1)) F2 |
        ∃ k : Fin m, k.val % 2 = 0 ∧ t = omegaBlock m k}).map (slLower2Hom m)
  rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, ← Subgroup.closure_union]
  have hG : {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 |
      ∃ k : Fin (m + 1 + 1), k.val % 2 = 0 ∧ t = omegaBlock (m + 1 + 1) k} =
      ({omegaBlock (m + 1 + 1) ⟨0, by omega⟩} :
          Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ∪
        slLower2Hom m '' {t : SpecialLinearGroup (Fin (m + 1)) F2 |
          ∃ k : Fin m, k.val % 2 = 0 ∧ t = omegaBlock m k} := by
    ext t
    constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases h0 : k.val = 0
      · left
        rw [Set.mem_singleton_iff]
        congr 1
        exact Fin.ext h0
      · right
        have hk2 : 2 ≤ k.val := by omega
        refine ⟨omegaBlock m ⟨k.val - 2, by omega⟩, ?_, ?_⟩
        · refine ⟨⟨k.val - 2, by omega⟩, ?_, rfl⟩
          show (k.val - 2) % 2 = 0
          omega
        · rw [slLower2Hom_omegaBlock]
          congr 1
          exact Fin.ext (by simp only [Fin.val_mk]; omega)
    · rintro (ht | ht)
      · rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact ⟨⟨0, by omega⟩, by simp, rfl⟩
      · obtain ⟨g, hg, rfl⟩ := ht
        obtain ⟨k, hk, rfl⟩ := hg
        refine ⟨⟨k.val + 2, by omega⟩, ?_, ?_⟩
        · show (k.val + 2) % 2 = 0
          omega
        · rw [slLower2Hom_omegaBlock]
  rw [hG]

theorem halfTorusK_succ_succ (m : ℕ) :
    halfTorusK (m + 1 + 1) = Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, Nat.lt_succ_self _⟩) ⊔
      (halfTorus m).map (slUpper2Hom m) := by
  change Subgroup.closure {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 |
      ∃ k : Fin (m + 1 + 1),
        (k.val + 1 = m + 1 + 1 ∨ (k.val % 2 = 0 ∧ k.val + 2 < m + 1 + 1)) ∧
          t = omegaBlock (m + 1 + 1) k} =
    Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) ⊔
      (Subgroup.closure {t : SpecialLinearGroup (Fin (m + 1)) F2 |
        ∃ k : Fin m, k.val % 2 = 0 ∧ t = omegaBlock m k}).map (slUpper2Hom m)
  rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, ← Subgroup.closure_union]
  have hG : {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 |
      ∃ k : Fin (m + 1 + 1),
        (k.val + 1 = m + 1 + 1 ∨ (k.val % 2 = 0 ∧ k.val + 2 < m + 1 + 1)) ∧
          t = omegaBlock (m + 1 + 1) k} =
      ({omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩} :
          Set (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)) ∪
        slUpper2Hom m '' {t : SpecialLinearGroup (Fin (m + 1)) F2 |
          ∃ k : Fin m, k.val % 2 = 0 ∧ t = omegaBlock m k} := by
    ext t
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases hk with hlast | hother
      · left
        rw [Set.mem_singleton_iff]
        congr 1
        exact Fin.ext (by simp only [Fin.val_mk]; omega)
      · right
        have hkm : k.val < m := by omega
        refine ⟨omegaBlock m ⟨k.val, by omega⟩, ?_, ?_⟩
        · exact ⟨⟨k.val, by omega⟩, hother.1, rfl⟩
        · rw [slUpper2Hom_omegaBlock]
    · rintro (ht | ht)
      · rw [Set.mem_singleton_iff] at ht
        rw [ht]
        refine ⟨⟨m + 1, by omega⟩, ?_, rfl⟩
        left
        simp
      · obtain ⟨g, hg, rfl⟩ := ht
        obtain ⟨k, hk, rfl⟩ := hg
        refine ⟨((⟨k, by omega⟩ : Fin m).castSucc).castSucc, ?_, ?_⟩
        · right
          refine ⟨?_, by simp only [Fin.val_castSucc, Fin.val_mk]; omega⟩
          simpa only [Fin.val_castSucc, Fin.val_mk] using hk
        · rw [slUpper2Hom_omegaBlock]
          congr 1
  rw [hG]

theorem disjoint_zpowers_omegaBlock_lower (m : ℕ) :
    Disjoint (Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩))
      ((halfTorus m).map (slLower2Hom m)) := by
  rw [Subgroup.disjoint_def]
  intro x hx hximg
  obtain ⟨s, hs, rfl⟩ := hximg
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : omegaBlock (m + 1 + 1) ⟨0, by omega⟩ ^ (3 : ℕ) = 1 :=
    omegaBlock_pow_three (m + 1 + 1) ⟨0, by omega⟩
  have hem : omegaBlock (m + 1 + 1) ⟨0, by omega⟩ ^ n =
      omegaBlock (m + 1 + 1) ⟨0, by omega⟩ ^ (n % (3 : ℤ)) :=
    zpow_eq_zpow_emod' n h3
  have hr : n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1 ∨ n % (3 : ℤ) = 2 := by
    have h1 : 0 ≤ n % (3 : ℤ) := Int.emod_nonneg n (by norm_num)
    have h2 : n % (3 : ℤ) < 3 := Int.emod_lt_of_pos n (by norm_num)
    omega
  rcases hr with h | h | h
  · rw [hem, h, zpow_zero] at hn
    exact hn.symm
  · exfalso
    have hxa : (slLower2Hom m s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) =
        (omegaBlock (m + 1 + 1) ⟨0, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := by
      rw [← hn, hem, h, zpow_one]
    have hentry : ((slLower2Hom m s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 = 1 := by
      rw [hxa]
      exact omegaBlock_zero_apply_one_zero m
    rw [slLower2Hom_apply_one_zero m s] at hentry
    exact zero_ne_one hentry
  · exfalso
    have hxa : (slLower2Hom m s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) =
        (omegaBlock (m + 1 + 1) ⟨0, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) ^ (2 : ℤ) := by
      rw [← hn, hem, h]
    have h2 : ((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ :
          SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) ^ (2 : ℤ)) =
        (omegaBlock (m + 1 + 1) ⟨0, by omega⟩ :
          SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) ^ 2 := zpow_natCast _ 2
    have hentry : ((slLower2Hom m s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 = 1 := by
      rw [hxa, h2]
      exact omegaBlock_zero_sq_apply_one_zero m
    rw [slLower2Hom_apply_one_zero m s] at hentry
    exact zero_ne_one hentry

end CFSG.StandardType.GGHalf

end
