module

public import CFSG.Milestones.ASVolI.A3Aut.Case5b

public section

namespace CFSG.ASVolI

open CFSG.Open

section FamHelpers

theorem burnsideAut_inn_normal' (S : Type*) [Group S] :
    (MulAut.conj : S →* MulAut S).range.Normal :=
  ⟨fun _ ⟨y, hy⟩ χ => ⟨χ y, by rw [← hy, burnsideAut_mul_conj_mul_inv]⟩⟩

theorem burnsideAut_mem_normalizer_map_conj' {S : Type*} [Group S] {U : Subgroup S}
    {φ : MulAut S} (hφ : U.map φ.toMonoidHom = U) :
    φ ∈ Subgroup.normalizer ((U.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) :
      Set (MulAut S)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change Subgroup.map (MulAut.conj φ).toMonoidHom _ = _
  rw [burnsideAut_map_conj_map_conj', hφ]

theorem burnsideAut_map_inn_congr' {S M : Type*} [Group S] [Group M] (e : S ≃* M) :
    (MulAut.conj : M →* MulAut M).range.map (MulAut.congr e.symm).toMonoidHom =
      (MulAut.conj : S →* MulAut S).range :=
  CFSG.RankThree.PartTwo.KFacts.map_innAut_congr e.symm

theorem burnsideAut_ne_top_of_isSolvable {X : Type*} [Group X] [Nontrivial X] [Group.IsPerfect X]
    {Y : Subgroup X} (hY : Group.IsSolvable ↥Y) : Y ≠ ⊤ := by
  rintro rfl
  haveI : Group.IsSolvable X :=
    solvable_of_surjective (f := (⊤ : Subgroup X).subtype) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hc := Group.IsSolvable.commutator_lt_top_of_nontrivial X
  rw [(inferInstance : Group.IsPerfect X).commutator_eq_top] at hc
  exact lt_irrefl _ hc

theorem burnsideAut_nonabelian_of_perfect {X : Type*} [Group X] [Nontrivial X]
    [Group.IsPerfect X] : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have h1 : commutator X = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, hc a b, mul_inv_cancel_right, mul_inv_cancel, Subgroup.mem_bot]
  rw [(inferInstance : Group.IsPerfect X).commutator_eq_top] at h1
  exact top_ne_bot h1

theorem burnsideAut_inn_relIndex_self (S : Type*) [Group S] :
    ¬ 2 ∣ (MulAut.conj : S →* MulAut S).range.relIndex (MulAut.conj : S →* MulAut S).range := by
  rw [Subgroup.relIndex_self]
  norm_num

theorem burnsideAut_map_inn_le_innDiag {S M : Type} [Group S] [Group M] (e : S ≃* M) :
    (MulAut.conj : M →* MulAut M).range.map (MulAut.congr e.symm).toMonoidHom ≤
      ChA.innDiagSubgroup S := by
  rw [burnsideAut_map_inn_congr']
  exact burnsideAut_inn_le_innDiag S

end FamHelpers

end CFSG.ASVolI
