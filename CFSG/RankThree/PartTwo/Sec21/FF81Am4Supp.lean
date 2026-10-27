module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Model

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am4

open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

theorem spEmbed_mem_suppGroup {m n : ℕ} {σ : Fin m → Fin n} (hσ : Function.Injective σ)
    {T : Set (Fin m ⊕ Fin m)} {y : StatedSp m (ZMod 2)} (hy : y ∈ suppGroup T) :
    spEmbed σ hσ y ∈ suppGroup (Sum.map σ σ '' T) := by
  have hinj : Function.Injective (Sum.map σ σ : Fin m ⊕ Fin m → Fin n ⊕ Fin n) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  intro r t hrt
  rw [mat_spEmbed]
  by_cases hr : r ∈ Set.range (Sum.map σ σ) ∧ t ∈ Set.range (Sum.map σ σ)
  · obtain ⟨⟨r', rfl⟩, ⟨t', rfl⟩⟩ := hr
    rw [spEmbedMat_apply_image hσ]
    have hnot : ¬(r' ∈ T ∧ t' ∈ T) := fun h => hrt ⟨⟨r', h.1, rfl⟩, ⟨t', h.2, rfl⟩⟩
    rw [hy r' t' hnot]
    simp [Matrix.one_apply, hinj.eq_iff]
  · exact spEmbedMat_apply_of_not_mem _ hr

theorem image_succ_subset :
    Sum.map Fin.succ Fin.succ '' (coords (1 : Fin 3) ∪ coords (2 : Fin 3)) ⊆
      (coords (0 : Fin 4) ∪ coords (1 : Fin 4))ᶜ := by
  rintro _ ⟨a, ha, rfl⟩ hmem
  rcases a with i | i <;> simp only [coords, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, or_false, false_or,
    Sum.map_inl, Sum.map_inr] at ha hmem <;> revert ha hmem <;> revert i <;> decide

theorem image_castSucc_subset :
    Sum.map Fin.castSucc Fin.castSucc '' (coords (0 : Fin 3) ∪ coords (1 : Fin 3)) ⊆
      coords (0 : Fin 4) ∪ coords (1 : Fin 4) := by
  rintro _ ⟨a, ha, rfl⟩
  rcases a with i | i <;> simp only [coords, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, or_false, false_or,
    Sum.map_inl, Sum.map_inr] at ha ⊢ <;> revert ha <;> revert i <;> decide

theorem commute_shiftEmb_initEmb {x y : K3}
    (hx : x ∈ suppGroup (coords (1 : Fin 3) ∪ coords (2 : Fin 3)))
    (hy : y ∈ suppGroup (coords (0 : Fin 3) ∪ coords (1 : Fin 3))) :
    Commute (shiftEmb x) (initEmb y) := by
  have h1 := spEmbed_mem_suppGroup (Fin.succ_injective 3) hx
  have h2 := spEmbed_mem_suppGroup (Fin.castSucc_injective 3) hy
  have h1' : shiftEmb x ∈ suppGroup (coords (0 : Fin 4) ∪ coords (1 : Fin 4))ᶜ :=
    suppGroup_mono image_succ_subset h1
  have h2' : initEmb y ∈ suppGroup (coords (0 : Fin 4) ∪ coords (1 : Fin 4)) :=
    suppGroup_mono image_castSucc_subset h2
  exact (commute_suppGroup_compl h2' h1').symm

end CFSG.RankThree.PartTwo.Sec21.FF81.Am4
