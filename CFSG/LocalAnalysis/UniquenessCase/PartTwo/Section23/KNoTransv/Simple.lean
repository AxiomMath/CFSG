module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon

theorem isSimpleGroup_of_isMcLaughlinGroup {W : Type} [Group W] [Finite W]
    (hW : UniquenessMaximal.IsMcLaughlinGroup W) {T : Subgroup W} (hTn : T.Normal)
    (hT : ⁅T, T⁆ = T) (hT1 : T ≠ ⊥) :
    IsSimpleGroup ↥T ∧ (∃ a b : ↥T, a * b ≠ b * a) ∧
      ∀ n : ℕ, Nonempty (W ≃* Equiv.Perm (Fin n)) → T ≠ ⊤ := by
  classical
  have hWnsolv : ¬ Group.IsSolvable W := by
    intro hsol
    haveI := hsol
    haveI : Group.IsPerfect ↥T := Subgroup.isPerfect_iff.mpr hT
    haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
    exact Group.IsPerfect.not_isSolvable ↥T inferInstance
  obtain ⟨⟨hDsimple, hDnonab⟩, -⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.inputMcLaughlinTypeFacts_holds W hW).2 hWnsolv
  let D : Subgroup W := ⨅ n : ℕ, derivedSeries W n
  have hTD : T ≤ D := by
    refine le_iInf fun n => ?_
    induction n with
    | zero => simp [derivedSeries_zero]
    | succ n ih =>
        calc T = ⁅T, T⁆ := hT.symm
          _ ≤ ⁅derivedSeries W n, derivedSeries W n⁆ := Subgroup.commutator_mono ih ih
          _ = derivedSeries W (n + 1) := (derivedSeries_succ W n).symm
  have hTDtop : T.subgroupOf D = ⊤ := by
    haveI : T.Normal := hTn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.subgroupOf D) with h | h
    · exfalso
      rw [Subgroup.subgroupOf_eq_bot] at h
      have hle : T ≤ ⊥ := by
        rw [← inf_eq_left.mpr hTD]
        exact disjoint_iff_inf_le.mp h
      exact hT1 (le_bot_iff.mp hle)
    · exact h
  have hTeqD : T = D := by
    refine le_antisymm hTD fun x hx => ?_
    have hmem : (⟨x, hx⟩ : ↥D) ∈ T.subgroupOf D := by
      rw [hTDtop]
      exact Subgroup.mem_top _
    exact hmem
  let e : ↥T ≃* ↥D := MulEquiv.subgroupCongr hTeqD
  have hTsimple : IsSimpleGroup ↥T := MulEquiv.isSimpleGroup e
  have hTnonab : ∃ a b : ↥T, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hDnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  refine ⟨hTsimple, hTnonab, ?_⟩
  intro n ⟨eW⟩ hTtop
  haveI : Group.IsPerfect W := by
    rw [Group.isPerfect_def, commutator_def, ← hTtop, hT]
  by_cases hn : n ≤ 1
  · haveI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
    haveI : Subsingleton W := eW.toEquiv.subsingleton
    exact hT1 (Subgroup.eq_bot_of_subsingleton T)
  · have hn2 : 2 ≤ n := by omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
    let f : W →* ℤˣ := Equiv.Perm.sign.comp eW.toMonoidHom
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨p, hp⟩ := (Equiv.Perm.sign_surjective (α := Fin n)) y
      obtain ⟨x, rfl⟩ := eW.surjective p
      exact ⟨x, by simpa [f] using hp⟩
    have hle : commutator W ≤ f.ker := Abelianization.commutator_subset_ker f
    rw [Group.IsPerfect.commutator_eq_top] at hle
    have hker : f.ker = ⊤ := top_unique hle
    obtain ⟨x, hx⟩ := hsurj (-1 : ℤˣ)
    have hx1 : f x = 1 := by
      have hmem : x ∈ f.ker := by
        rw [hker]
        exact Subgroup.mem_top x
      exact MonoidHom.mem_ker.mp hmem
    rw [hx1] at hx
    exact (neg_units_ne_self (1 : ℤˣ)) hx.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
