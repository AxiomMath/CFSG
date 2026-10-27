module

public import CFSG.Sporadic.Recognition.LyonsFinalBInputs

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.CosetTable

theorem exists_surjective_of_subset {m : ℕ} {ws₁ ws₂ : List (List (Fin m × Bool))}
    (h : ∀ w ∈ ws₁, w ∈ ws₂) : ∃ f : PG m ws₁ →* PG m ws₂, Function.Surjective f := by
  set rels₂ := {r : FreeGroup (Fin m) | r ∈ ws₂.map FreeGroup.mk} with hrels₂
  have hmk : FreeGroup.lift (PresentedGroup.of (rels := rels₂)) = PresentedGroup.mk rels₂ := by
    apply FreeGroup.ext_hom
    intro i
    simp [PresentedGroup.of]
  refine ⟨PresentedGroup.toGroup (f := fun i => PresentedGroup.of (rels := rels₂) i)
    (fun r hr => ?_), ?_⟩
  · simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [hmk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (h w hw))
  · rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of (rels := rels₂),
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, by simp [PresentedGroup.toGroup.of]⟩

theorem card_PG_le_of_subset {m : ℕ} {ws₁ ws₂ : List (List (Fin m × Bool))}
    (h : ∀ w ∈ ws₁, w ∈ ws₂) [Finite (PG m ws₁)] :
    Finite (PG m ws₂) ∧ Nat.card (PG m ws₂) ≤ Nat.card (PG m ws₁) := by
  obtain ⟨f, hf⟩ := exists_surjective_of_subset h
  exact ⟨Finite.of_surjective f hf, Nat.card_le_card_of_surjective f hf⟩

abbrev RB5Bound : Prop := Finite (PG _ RB5) ∧ Nat.card (PG _ RB5) ≤ 5388768000

theorem RB5_subset_restrict {R : List (List (Fin 6 × Bool))} (hB : ∀ r ∈ RB, r ∈ R) :
    ∀ w ∈ RB5, w ∈ restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) R := by
  intro w hw
  simp only [restrictWords, List.mem_filterMap] at hw ⊢
  obtain ⟨w₀, hw₀, e⟩ := hw
  exact ⟨w₀, hB w₀ hw₀, e⟩

theorem card_genSub_le_of_RB {R : List (List (Fin 6 × Bool))} (hB : ∀ r ∈ RB, r ∈ R)
    (hbc : RB5Bound) :
    Finite (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk}
      (subsetOf 6 [0, 1, 2, 3, 4])) ∧
    Nat.card (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk}
      (subsetOf 6 [0, 1, 2, 3, 4])) ≤ 5388768000 := by
  obtain ⟨hf, hc⟩ := hbc
  obtain ⟨hf', hc'⟩ := card_PG_le_of_subset (RB5_subset_restrict hB)
  obtain ⟨hfin, hsub⟩ := card_genSub_le R (subsetOf 6 [0, 1, 2, 3, 4])
  exact ⟨hfin, hsub.trans (hc'.trans hc)⟩

theorem genSub_le_cdabe (R : List (List (Fin 6 × Bool))) {T : List ℕ} (hT : ∀ t ∈ T, t < 5) :
    genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 T) ≤
      genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 [0, 1, 2, 3, 4]) := by
  refine Subgroup.closure_mono (Set.image_mono fun x hx => ?_)
  simp only [subsetOf, List.mem_filter, List.mem_finRange, true_and, List.contains_iff_mem,
    Set.mem_ofPred_eq] at hx ⊢
  have := hT _ hx
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem card_genSub_le_of_RB' {R : List (List (Fin 6 × Bool))} (hB : ∀ r ∈ RB, r ∈ R)
    (hbc : RB5Bound) {T : List ℕ} (hT : ∀ t ∈ T, t < 5) :
    Finite (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 T)) ∧
    Nat.card (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 T)) ≤
      5388768000 := by
  obtain ⟨hfin, hc⟩ := card_genSub_le_of_RB hB hbc
  have hle := genSub_le_cdabe R hT
  exact ⟨Finite.of_injective _ (Subgroup.inclusion_injective hle),
    (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)).trans hc⟩

theorem card_cd_le {R : List (List (Fin 6 × Bool))} (hB : ∀ r ∈ RB, r ∈ R)
    (hbc : RB5Bound) :
    Finite (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 [0, 1])) ∧
    Nat.card (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 [0, 1])) ≤
      5388768000 :=
  card_genSub_le_of_RB' hB hbc (by decide)

theorem card_PG_le_of_index {m : ℕ} {ws : List (List (Fin m × Bool))} {H : Subgroup (PG m ws)}
    [Finite H] (hfi : H.FiniteIndex) {n k : ℕ} (hidx : H.index ≤ n) (hH : Nat.card H ≤ k) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * k := by
  have hfin : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient H
  refine ⟨hfin, ?_⟩
  rw [← H.index_mul_card]
  exact Nat.mul_le_mul hidx hH

theorem card_PG6_le_of_index {R : List (List (Fin 6 × Bool))} (hB : ∀ r ∈ RB, r ∈ R)
    (hbc : RB5Bound) {T : List ℕ} (hT : ∀ t ∈ T, t < 5) {n : ℕ}
    (hfi : (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 T)).FiniteIndex)
    (hidx : (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 T)).index ≤ n) :
    Finite (PG 6 R) ∧ Nat.card (PG 6 R) ≤ n * 5388768000 := by
  obtain ⟨hfin, hc⟩ := card_genSub_le_of_RB' hB hbc hT
  exact card_PG_le_of_index hfi hidx hc

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
