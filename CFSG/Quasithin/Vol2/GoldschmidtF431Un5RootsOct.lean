module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5RootsRel

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits
open scoped commutatorElement

section Octagon

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem octGroup_le_un5U {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) : un5Oct hF k ≤ unU hF 5 :=
  rootGroup_le_posUnipotent (octRootB_mem_roots_un hF h1 h4) (octRootB_ht_pos h1 h4)

theorem octGroup_neg_le_un5Uneg {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    un5Oct hF (-k) ≤ unUneg hF 5 :=
  rootGroup_le_negUnipotent (octRootB_mem_roots' (isRoot_four_of_neg h1 h4))
    (octRootB_ht_neg h1 h4)

theorem un5U_eq_iSup : unU hF 5 = ⨆ k ∈ intList 1 ((4 : ℕ) : ℤ), un5Oct hF k := by
  have hk : ∀ k : ℤ, 1 ≤ k → k ≤ 4 → un5Oct hF k ≤
      ⨆ k ∈ intList 1 ((4 : ℕ) : ℤ), un5Oct hF k := fun k h1 h4 =>
    le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => un5Oct hF k) k
      (by simp only [mem_intList_iff]; omega) le_rfl
  refine le_antisymm ?_ (iSup₂_le fun k hk' => ?_)
  · show posUnipotent (rootDatum hF 5) ≤ _
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hr, hp⟩ := hγ
    rcases pos_root_cases5 hr hp with rfl | rfl | rfl | rfl | h | h
    · exact hk 1 (by norm_num) (by norm_num)
    · exact hk 2 (by norm_num) (by norm_num)
    · exact hk 3 (by norm_num) (by norm_num)
    · exact hk 4 (by norm_num) (by norm_num)
    · rw [eq_two_smul_two h] at hr ⊢
      exact (rootGroup_two_le_un hF (octRootB_mem_roots_un hF (by norm_num) (by norm_num))
        hr).trans (hk 2 (by norm_num) (by norm_num))
    · rw [eq_two_smul_four h] at hr ⊢
      exact (rootGroup_two_le_un hF (octRootB_mem_roots_un hF (by norm_num) (by norm_num))
        hr).trans (hk 4 (by norm_num) (by norm_num))
  · obtain ⟨h1, h4⟩ := mem_intList_iff.1 hk'
    exact octGroup_le_un5U hF h1 (by omega)

theorem prodInjective_heights_un5 :
    ∀ g g' : (Fin 2 → ℤ) → SU (unitaryInvolution F p f) 5,
      (∀ γ ∈ [octRootB 1, octRootB 4, octRootB 2, octRootB 3],
        g γ ∈ (rootDatum hF 5).rootGroup γ) →
      (∀ γ ∈ [octRootB 1, octRootB 4, octRootB 2, octRootB 3],
        g' γ ∈ (rootDatum hF 5).rootGroup γ) →
      ([octRootB 1, octRootB 4, octRootB 2, octRootB 3].map g).prod =
        ([octRootB 1, octRootB 4, octRootB 2, octRootB 3].map g').prod →
      ∀ γ ∈ [octRootB 1, octRootB 4, octRootB 2, octRootB 3], g γ = g' γ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF 5 (by norm_num) ζ hζ
  have hL : ∀ γ : Fin 2 → ℤ, γ ∈ [octRootB 1, octRootB 4, octRootB 2, octRootB 3] ↔
      γ ∈ (rootDatum hF 5).roots ∧ 0 < ht γ ∧ ∀ δ ∈ (rootDatum hF 5).roots, γ ≠ 2 • δ := by
    intro γ
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      rcases h with rfl | rfl | rfl | rfl
      · exact ⟨octRootB_mem_roots_un hF (by norm_num) (by norm_num),
          octRootB_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRootB_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRootB_mem_roots_un hF (by norm_num) (by norm_num),
          octRootB_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRootB_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRootB_mem_roots_un hF (by norm_num) (by norm_num),
          octRootB_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRootB_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRootB_mem_roots_un hF (by norm_num) (by norm_num),
          octRootB_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRootB_ne_two_smul (by norm_num) (by norm_num) δ⟩
    · rintro ⟨hr, hp, hd⟩
      rcases pos_root_cases5 hr hp with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inl h)
      · exact absurd (eq_two_smul_two h)
          (hd _ (octRootB_mem_roots_un hF (by norm_num) (by norm_num)))
      · exact absurd (eq_two_smul_four h)
          (hd _ (octRootB_mem_roots_un hF (by norm_num) (by norm_num)))
  have hnd : [octRootB 1, octRootB 4, octRootB 2, octRootB 3].Nodup := by decide
  have hsort : [octRootB 1, octRootB 4, octRootB 2, octRootB 3].Pairwise
      (fun γ δ => ht γ ≤ ht δ) := by
    simp [List.pairwise_cons, ht_fin_two, octRootB_one, octRootB_two, octRootB_three,
      octRootB_four]
  exact hext.prodInjective_pos _ hnd hL hsort

theorem octReorder_un5 (e : ℤ → SU (unitaryInvolution F p f) 5)
    (he : ∀ k ∈ [1, 2, 3, 4], e k ∈ un5Oct hF k) :
    e 1 * (e 2 * (e 3 * e 4)) = e 1 * (e 4 * (e 2 * (⁅e 2, e 4⁆ * e 3))) := by
  have hk3 : ⁅e 2, e 4⁆ ∈ un5Oct hF 3 :=
    octComm_two_four_un5 hF _ (he 2 (by simp)) _ (he 4 (by simp))
  have hbc : e 3 * e 4 = e 4 * e 3 :=
    commutatorElement_eq_one_iff_mul_comm.1 (octComm_three_four_un5 hF _ (he 3 (by simp)) _
      (he 4 (by simp)))
  have hak : e 2 * ⁅e 2, e 4⁆ = ⁅e 2, e 4⁆ * e 2 :=
    commutatorElement_eq_one_iff_mul_comm.1 (octComm_two_three_un5 hF _ (he 2 (by simp)) _ hk3)
  have hkc : ⁅e 2, e 4⁆ * e 4 = e 4 * ⁅e 2, e 4⁆ :=
    commutatorElement_eq_one_iff_mul_comm.1 (octComm_three_four_un5 hF _ hk3 _ (he 4 (by simp)))
  congr 1
  set a := e 2
  set b := e 3
  set c := e 4
  set k := ⁅a, c⁆ with hk
  calc a * (b * c) = a * (c * b) := by rw [hbc]
    _ = k * (c * (a * b)) := by simp only [hk, commutatorElement_def]; group
    _ = (k * c) * (a * b) := (mul_assoc _ _ _).symm
    _ = (c * k) * (a * b) := by rw [hkc]
    _ = c * (k * (a * b)) := mul_assoc _ _ _
    _ = c * ((k * a) * b) := by rw [mul_assoc]
    _ = c * ((a * k) * b) := by rw [hak]
    _ = c * (a * (k * b)) := by rw [mul_assoc]

end Octagon

end CFSG.Quasithin.H13.F431.Un
