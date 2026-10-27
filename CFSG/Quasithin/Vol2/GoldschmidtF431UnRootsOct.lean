module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnRootsComm
public import CFSG.LieType.Steinberg.CentralExt.SUBruhatExtras

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits CFSG.LieType.CurtisTits
open scoped commutatorElement

section Octagon

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem octGroup_le_unU {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) : unOct hF k ≤ unU hF 4 :=
  rootGroup_le_posUnipotent (octRoot_mem_roots_un hF h1 h4) (octRoot_ht_pos h1 h4)

theorem octGroup_neg_le_unUneg {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    unOct hF (-k) ≤ unUneg hF 4 :=
  rootGroup_le_negUnipotent (octRoot_mem_roots' (isRoot_four_of_neg h1 h4))
    (octRoot_ht_neg h1 h4)

theorem unU_eq_iSup : unU hF 4 = ⨆ k ∈ intList 1 ((4 : ℕ) : ℤ), unOct hF k := by
  refine le_antisymm ?_ (iSup₂_le fun k hk => ?_)
  · show posUnipotent (rootDatum hF 4) ≤ _
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hr, hp⟩ := hγ
    rcases pos_root_cases hr hp with rfl | rfl | rfl | rfl
    · exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => unOct hF k) 1
        (by simp [mem_intList_iff]) le_rfl
    · exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => unOct hF k) 2
        (by simp [mem_intList_iff]) le_rfl
    · exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => unOct hF k) 3
        (by simp [mem_intList_iff]) le_rfl
    · exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => unOct hF k) 4
        (by simp [mem_intList_iff]) le_rfl
  · obtain ⟨h1, h4⟩ := mem_intList_iff.1 hk
    exact octGroup_le_unU hF h1 (by omega)

private def octIdx (γ : Fin 2 → ℤ) : ℤ := 1 + γ 1 * (3 - γ 0)

private theorem octIdx_one : octIdx (octRoot 1) = 1 := by simp [octIdx, octRoot_one]
private theorem octIdx_two : octIdx (octRoot 2) = 2 := by simp [octIdx, octRoot_two]
private theorem octIdx_three : octIdx (octRoot 3) = 3 := by simp [octIdx, octRoot_three]
private theorem octIdx_four : octIdx (octRoot 4) = 4 := by simp [octIdx, octRoot_four]

theorem prodInjective_heights_un :
    ∀ g g' : (Fin 2 → ℤ) → SU (unitaryInvolution F p f) 4,
      (∀ γ ∈ [octRoot 1, octRoot 4, octRoot 3, octRoot 2], g γ ∈ (rootDatum hF 4).rootGroup γ) →
      (∀ γ ∈ [octRoot 1, octRoot 4, octRoot 3, octRoot 2], g' γ ∈ (rootDatum hF 4).rootGroup γ) →
      ([octRoot 1, octRoot 4, octRoot 3, octRoot 2].map g).prod =
        ([octRoot 1, octRoot 4, octRoot 3, octRoot 2].map g').prod →
      ∀ γ ∈ [octRoot 1, octRoot 4, octRoot 3, octRoot 2], g γ = g' γ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF 4 (by norm_num) ζ hζ
  have hL : ∀ γ : Fin 2 → ℤ, γ ∈ [octRoot 1, octRoot 4, octRoot 3, octRoot 2] ↔
      γ ∈ (rootDatum hF 4).roots ∧ 0 < ht γ ∧ ∀ δ ∈ (rootDatum hF 4).roots, γ ≠ 2 • δ := by
    intro γ
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      rcases h with rfl | rfl | rfl | rfl
      · exact ⟨octRoot_mem_roots_un hF (by norm_num) (by norm_num),
          octRoot_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRoot_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRoot_mem_roots_un hF (by norm_num) (by norm_num),
          octRoot_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRoot_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRoot_mem_roots_un hF (by norm_num) (by norm_num),
          octRoot_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRoot_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRoot_mem_roots_un hF (by norm_num) (by norm_num),
          octRoot_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRoot_ne_two_smul (by norm_num) (by norm_num) δ⟩
    · rintro ⟨hr, hp, -⟩
      rcases pos_root_cases hr hp with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
  have hnd : [octRoot 1, octRoot 4, octRoot 3, octRoot 2].Nodup := by decide
  have hsort : [octRoot 1, octRoot 4, octRoot 3, octRoot 2].Pairwise
      (fun γ δ => ht γ ≤ ht δ) := by
    simp [List.pairwise_cons, ht_fin_two, octRoot_one, octRoot_two, octRoot_three, octRoot_four]
  exact hext.prodInjective_pos _ hnd hL hsort

theorem octUnique_un :
    ∀ g g' : ℤ → SU (unitaryInvolution F p f) 4,
      (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k ∈ unOct hF k) →
      (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g' k ∈ unOct hF k) →
      ((intList 1 ((4 : ℕ) : ℤ)).map g).prod = ((intList 1 ((4 : ℕ) : ℤ)).map g').prod →
        ∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k = g' k := by
  have hl : intList 1 ((4 : ℕ) : ℤ) = [1, 2, 3, 4] := by decide
  have reorder : ∀ e : ℤ → SU (unitaryInvolution F p f) 4, (∀ k ∈ [1, 2, 3, 4], e k ∈ unOct hF k) →
      e 1 * (e 4 * (e 3 * e 2)) = e 1 * (e 2 * (e 3 * e 4)) := by
    intro e he
    have h23 : e 2 * e 3 = e 3 * e 2 :=
      commutatorElement_eq_one_iff_mul_comm.1 (octComm_two_three_un hF _ (he 2 (by simp)) _
        (he 3 (by simp)))
    have h24 : e 2 * e 4 = e 4 * e 2 :=
      commutatorElement_eq_one_iff_mul_comm.1 (octComm_two_four_un hF _ (he 2 (by simp)) _
        (he 4 (by simp)))
    have h34 : e 3 * e 4 = e 4 * e 3 :=
      commutatorElement_eq_one_iff_mul_comm.1 (octComm_three_four_un hF _ (he 3 (by simp)) _
        (he 4 (by simp)))
    congr 1
    calc e 4 * (e 3 * e 2) = (e 4 * e 3) * e 2 := (mul_assoc _ _ _).symm
      _ = (e 3 * e 4) * e 2 := by rw [h34]
      _ = e 3 * (e 4 * e 2) := mul_assoc _ _ _
      _ = e 3 * (e 2 * e 4) := by rw [h24]
      _ = (e 3 * e 2) * e 4 := (mul_assoc _ _ _).symm
      _ = (e 2 * e 3) * e 4 := by rw [h23]
      _ = e 2 * (e 3 * e 4) := mul_assoc _ _ _
  intro g g' hg hg' hgg'
  rw [hl] at hg hg' hgg' ⊢
  have key := prodInjective_heights_un hF (fun γ => g (octIdx γ)) (fun γ => g' (octIdx γ))
    (by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl | rfl
      · simp only [octIdx_one]; exact hg 1 (by simp)
      · simp only [octIdx_four]; exact hg 4 (by simp)
      · simp only [octIdx_three]; exact hg 3 (by simp)
      · simp only [octIdx_two]; exact hg 2 (by simp))
    (by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl | rfl
      · simp only [octIdx_one]; exact hg' 1 (by simp)
      · simp only [octIdx_four]; exact hg' 4 (by simp)
      · simp only [octIdx_three]; exact hg' 3 (by simp)
      · simp only [octIdx_two]; exact hg' 2 (by simp))
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, octIdx_one,
        octIdx_two, octIdx_three, octIdx_four]
      rw [reorder g hg, reorder g' hg']
      simpa using hgg')
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · simpa [octIdx_one] using key (octRoot 1) (by simp)
  · simpa [octIdx_two] using key (octRoot 2) (by simp)
  · simpa [octIdx_three] using key (octRoot 3) (by simp)
  · simpa [octIdx_four] using key (octRoot 4) (by simp)

theorem unOctagon : UnOctagon hF where
  ne_bot i hi := by
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
    exact (steinbergExtras hF 4 (by norm_num) ζ hζ).ne_bot _ (octRoot_mem_roots' hi)
  invariant i hi h hh x hx := by
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
    have hct := isCTGroupDatum hF 4 (by norm_num) ζ hζ
    exact (Subgroup.mem_normalizer_iff.1
      (iSup_le_normalizer_rootGroup (D := rootDatum hF 4) hct (octRoot_mem_roots' hi) hh) x).1 hx
  carrier_eq := by
    have h := (octComm_un hF).carrier_eq (i := 1) (j := ((4 : ℕ) : ℤ)) le_rfl le_rfl
    rw [← unU_eq_iSup hF] at h
    exact h
  unique := octUnique_un hF
  reverse_eq i j hi _ hj := (octComm_un hF).reverse_eq hi hj
  subgroup i j hi _ hj := (octComm_un hF).exists_subgroup (U := unU hF 4)
    (fun k h1 h4 => octGroup_le_unU hF h1 (by omega)) hi hj
  meet_one x hxB hx := by
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
    have hU : x ∈ unUneg hF 4 := by
      refine chainProd_subset (unOct hF) (unUneg hF 4) _ (fun k hk => ?_) hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
      obtain ⟨h1, h4⟩ := mem_intList_iff.1 hj
      exact octGroup_neg_le_unUneg hF h1 (by omega)
    have hmem : x ∈ borel (rootDatum hF 4) (levelTorus (unitaryInvolution F p f)) ⊓
        negUnipotent (rootDatum hF 4) := ⟨hxB, hU⟩
    rw [(CentralExt.SUBruhat.bruhatExtras hF (by norm_num) ζ hζ).borel_inf_negUnipotent] at hmem
    exact Subgroup.mem_bot.1 hmem

end Octagon

end CFSG.Quasithin.H13.F431.Un
