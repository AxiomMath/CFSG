module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBDescent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eleven_four_B {M V Q U : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) {g : G} (hg : g ∈ M)
    (hW : U ⊓ conjSubgroup U g ∈ gammaEleven M V) {Li Lj : Subgroup G}
    (hLi : Li ∈ elevenBlocksB M Q U) (hLj : Lj ∈ elevenBlocksB M Q U) :
    ⁅Li, conjSubgroup Lj g⁆ = ⊥ ∨ Li = conjSubgroup Lj g := by
  have hLi' : IsBlockOfInX (Subgroup.centralizer ((U ⊓ conjSubgroup U g : Subgroup G) : Set G))
      Li :=
    isBlockOfInX_of_eleven_four_descent_B hset hU.1 hW inf_le_left hLi
  have hW' : U ⊓ conjSubgroup U g⁻¹ ∈ gammaEleven M V := by
    have h1 := eleven_c_gamma hset.normal hW (M.inv_mem hg)
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_conj_inv, inf_comm] at h1
    exact h1
  have hLj' : IsBlockOfInX (Subgroup.centralizer ((U ⊓ conjSubgroup U g⁻¹ : Subgroup G) : Set G))
      Lj :=
    isBlockOfInX_of_eleven_four_descent_B hset hU.1 hW' inf_le_left hLj
  have hLj'' := isBlockOfInX_conjSubgroup g hLj'
  have hcw : conjSubgroup (Subgroup.centralizer ((U ⊓ conjSubgroup U g⁻¹ : Subgroup G) : Set G)) g =
      Subgroup.centralizer ((U ⊓ conjSubgroup U g : Subgroup G) : Set G) := by
    rw [E3.conjSubgroup_centralizer, E3.conjSubgroup_inf, conjSubgroup_conjSubgroup,
      inv_mul_cancel, conjSubgroup_one, inf_comm]
  rw [hcw] at hLj''
  have hchar : CFSG.IsCharacteristicP 2
      ↥(Subgroup.centralizer ((U ⊓ conjSubgroup U g : Subgroup G) : Set G)) :=
    eleven_e hset.charTwo hW.2.1
      ((CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hset.isElemAbelian).to_le hW.1)
  by_cases h : Li = conjSubgroup Lj g
  · exact Or.inr h
  · exact Or.inl (distinct_blocks_commute_of_isBlockOfInX hchar hLi' hLj'' h)

private theorem conjSubgroup_iSup' {ι : Sort*} (A : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, A i) g = ⨆ i, conjSubgroup (A i) g :=
  Subgroup.map_iSup _ _

theorem exists_blockSystem_of_B {M V Q U : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) :
    (∀ g ∈ M, U ⊓ conjSubgroup U g ∈ gammaEleven M V) →
      ∃ (E : Subgroup G) (L : Set (Subgroup G)), M ≤ Subgroup.normalizer (E : Set G) ∧
        (∀ A ∈ L, A ≤ E) ∧ (∀ A ∈ L, E ≤ Subgroup.normalizer (A : Set G)) ∧
        (∀ A ∈ L, ¬ A ≤ M → pCoreOf 2 A ≠ ⊥) ∧ ∃ A ∈ L, ¬ A ≤ M := by
  intro hall
  classical
  set L : Set (Subgroup G) := {A | ∃ Y ∈ elevenBlocksB M Q U, ∃ a ∈ M, A = conjSubgroup Y a}
    with hL
  set E : Subgroup G := ⨆ A ∈ L, A with hE
  have hLE : ∀ A ∈ L, A ≤ E := fun A hA => le_iSup₂ (f := fun A _ => A) A hA
  have hLconj : ∀ A ∈ L, ∀ m ∈ M, conjSubgroup A m ∈ L := by
    rintro A ⟨Y, hY, a, ha, rfl⟩ m hm
    exact ⟨Y, hY, a * m, M.mul_mem ha hm, conjSubgroup_conjSubgroup Y a m⟩
  have hEle : ∀ m ∈ M, conjSubgroup E m ≤ E := by
    intro m hm
    rw [hE, conjSubgroup_iSup']
    refine iSup_le fun A => ?_
    rw [conjSubgroup_iSup']
    exact iSup_le fun hA => hLE _ (hLconj A hA m hm)
  refine ⟨E, L, ?_, hLE, ?_, ?_, ?_⟩
  · intro m hm
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    refine le_antisymm (hEle m hm) ?_
    have h := hEle m⁻¹ (M.inv_mem hm)
    rwa [E3.conjSubgroup_le_iff_le_inv, inv_inv] at h
  · rintro A ⟨Y, hY, a, ha, rfl⟩
    refine iSup₂_le fun A' hA' => ?_
    obtain ⟨Y', hY', a', ha', rfl⟩ := hA'
    have hg : a' * a⁻¹ ∈ M := M.mul_mem ha' (M.inv_mem ha)
    have h4 := eleven_four_B hset hU hg (hall _ hg) hY hY'
    have hconj : conjSubgroup (conjSubgroup Y' (a' * a⁻¹)) a = conjSubgroup Y' a' := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right]
    rcases h4 with h4 | h4
    · have h5 : ⁅conjSubgroup Y a, conjSubgroup Y' a'⁆ = ⊥ := by
        have h := congrArg (fun K => conjSubgroup K a) h4
        simp only [E3.conjSubgroup_commutator, hconj] at h
        rw [h]
        exact (conjSubgroup_eq_bot_iff).2 rfl
      have h6 : conjSubgroup Y' a' ≤ Subgroup.centralizer (conjSubgroup Y a : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h5
      exact h6.trans (Subgroup.centralizer_le_normalizer _)
    · have h : conjSubgroup Y a = conjSubgroup Y' a' := by
        rw [← hconj, ← h4]
      rw [← h]
      exact Subgroup.le_normalizer
  · rintro A ⟨Y, hY, a, ha, rfl⟩ -
    exact (CFSG.QuasithinUnique.pCoreOf_map_equiv_ne_bot_iff 2 (MulAut.conj a⁻¹) Y).2
      (pCoreOf_ne_bot_of_mem_elevenBlocksB hset hU hY)
  · obtain ⟨Y, hY⟩ := exists_mem_elevenBlocksB hset hU
    exact ⟨Y, ⟨Y, hY, 1, M.one_mem, (conjSubgroup_one Y).symm⟩, hY.2⟩

theorem eleven_five_B {M V Q U : Subgroup G}
    (hset : Setting11 M V Q) (hU : U ∈ gammaEleven M V) :
    ∃ g ∈ M, U ⊓ conjSubgroup U g ∉ gammaEleven M V :=
  eleven_five hset.maxLocal (exists_blockSystem_of_B hset hU)

theorem eleven_six_B {M V Q : Subgroup G}
    (hset : Setting11 M V Q) :
    (mBar M ⊥ V hset.isElemAbelian : ℕ∞) ≤ 2 * rMV M V :=
  eleven_six hset.isElemAbelian hset.normal fun _ hU =>
    eleven_five_B hset (deltaEleven_subset_gammaEleven M V hU)

end CFSG.LocalAnalysis.WeakClosure81
