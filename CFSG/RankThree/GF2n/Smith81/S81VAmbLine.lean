module

public import CFSG.RankThree.GF2n.Smith81.S81VBlock
public import CFSG.RankThree.GF2n.Smith81.S81VDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F}

private theorem gu1a_herm_ba (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (i j : Fin 3) :
    herm σ (b i) (a j) = if i = j then 1 else 0 := by
  rw [herm_conj σ hσ (a j) (b i), hf.ab j i]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem gu1a_expand (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (v : Fin 6 → F) :
    v = herm σ (b 0) v • a 0 + herm σ (b 1) v • a 1 + herm σ (b 2) v • a 2 +
      (herm σ (a 0) v • b 0 + herm σ (a 1) v • b 1 + herm σ (a 2) v • b 2) := by
  have hx : ∑ p, (fb hσ hf).repr v p • fam a b p = v := by
    simpa only [fb_apply] using (fb hσ hf).sum_repr v
  conv_lhs => rw [← hx]
  rw [Fintype.sum_sum_type]
  simp only [fam, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_three, repr_inl hσ hf, repr_inr hσ hf]

private theorem gu1a_herm_w (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (t : F) :
    herm σ (b 0 + t • a 0) (b 0 + t • a 0) = σ t + t := by
  simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hf.bb, hf.aa,
    gu1a_herm_ba hσ hf, hf.ab]

private theorem gu1a_span_iso {X : Set (Fin 6 → F)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0) :
    IsTotIso σ (Submodule.span F X) := by
  have h1 : ∀ x ∈ Submodule.span F X, ∀ y ∈ X, herm σ x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx => exact hX x hx y hy
    | zero => simp
    | add u v _ _ hu hv => rw [herm_add_left, hu, hv, add_zero]
    | smul c u _ hu => rw [herm_smul_left, hu, mul_zero]
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact h1 x hx y hy
  | zero => simp
  | add u v _ _ hu hv => rw [herm_add_right, hu, hv, add_zero]
  | smul c u _ hu => rw [herm_smul_right, hu, mul_zero]

private theorem gu1a_iso {t : F} (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (ht : σ t = t) :
    ∀ x ∈ ({b 0 + t • a 0, a 1, a 2} : Set (Fin 6 → F)),
      ∀ y ∈ ({b 0 + t • a 0, a 1, a 2} : Set (Fin 6 → F)), herm σ x y = 0 := by
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hf.aa, hf.bb, hf.ab,
      gu1a_herm_ba hσ hf, ht, CharTwo.add_self_eq_zero]

private theorem gu1a_alg {v : Fin 6 → F} {α₀ α₁ α₂ β : F}
    (hv : v = α₀ • a 0 + α₁ • a 1 + α₂ • a 2 + β • b 0) (hβ : β ≠ 0) :
    ∃ t : F, β • (b 0 + t • a 0) = v - α₁ • a 1 - α₂ • a 2 := by
  refine ⟨α₀ * β⁻¹, ?_⟩
  have e : β * (α₀ * β⁻¹) = α₀ := by
    rw [← mul_assoc, mul_comm β α₀, mul_assoc, mul_inv_cancel₀ hβ, mul_one]
  rw [hv, smul_add, smul_smul, e]
  abel

private theorem gu1a_pt (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) {t : F} (ht : σ t = t) :
    IsPt σ (Submodule.span F {b 0 + t • a 0, a 1, a 2}) := by
  have hli : LinearIndependent F ![b 0 + t • a 0, a 1, a 2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • (b 0 + t • a 0) + g 1 • a 1 + g 2 • a 2 = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have h0 : g 0 = 0 := by
      have h := congrArg (herm σ (a 0)) hg'
      simpa [herm_add_right, herm_smul_right, hf.aa, hf.ab] using h
    rw [h0, zero_smul, zero_add] at hg'
    have h1 : g 1 = 0 := by
      have h := congrArg (herm σ (b 1)) hg'
      simpa [herm_add_right, herm_smul_right, gu1a_herm_ba hσ hf] using h
    have h2 : g 2 = 0 := by
      have h := congrArg (herm σ (b 2)) hg'
      simpa [herm_add_right, herm_smul_right, gu1a_herm_ba hσ hf] using h
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hset : ({b 0 + t • a 0, a 1, a 2} : Set (Fin 6 → F)) =
      Set.range ![b 0 + t • a 0, a 1, a 2] := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union, Set.singleton_union]
  have hfin : Module.finrank F (Submodule.span F {b 0 + t • a 0, a 1, a 2}) = 3 := by
    rw [hset, finrank_span_eq_card hli, Fintype.card_fin]
  unfold IsPt
  exact ⟨gu1a_span_iso (gu1a_iso hσ hf ht), hfin⟩

private theorem gu1a_inter (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) {t : F} :
    Wa a ⊓ Submodule.span F {b 0 + t • a 0, a 1, a 2} = Submodule.span F {a 1, a 2} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hxS⟩ := hx
    obtain ⟨c0, z, hz, rfl⟩ := Submodule.mem_span_insert.1 hxS
    obtain ⟨c1, c2, rfl⟩ := Submodule.mem_span_pair.1 hz
    have h0 : c0 = 0 := by
      have h := (mem_Wa_iff hσ hf _).1 hxW 0
      simpa [herm_add_right, herm_smul_right, hf.aa, hf.ab] using h
    rw [h0, zero_smul, zero_add]
    exact Submodule.mem_span_pair.2 ⟨c1, c2, rfl⟩
  · apply le_inf
    · unfold Wa
      apply Submodule.span_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Set.mem_range_self 1
      · exact Set.mem_range_self 2
    · apply Submodule.span_mono
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto

theorem line_through_H₀ (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) {z : Submodule F (Fin 6 → F)}
    (hz : IsPt σ z) (hH : Submodule.span F {a 1, a 2} ≤ z) :
    z = Wa a ∨ ∃ t : F, σ t = t ∧ z = Submodule.span F {b 0 + t • a 0, a 1, a 2} := by
  have ha1 : a 1 ∈ z := hH (Submodule.subset_span (Set.mem_insert _ _))
  have ha2 : a 2 ∈ z := hH (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  by_cases hzW : z ≤ Wa a
  · left
    have hli : LinearIndependent F a := (fam_li hσ hf).comp Sum.inl Sum.inl_injective
    have hWa3 : Module.finrank F (Wa a) = 3 := by
      unfold Wa
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact Submodule.eq_of_le_of_finrank_eq hzW (hz.2.trans hWa3.symm)
  · right
    obtain ⟨v, hvz, hvW⟩ := SetLike.not_le_iff_exists.1 hzW
    have hv1 : herm σ (a 1) v = 0 := hz.1 _ ha1 _ hvz
    have hv2 : herm σ (a 2) v = 0 := hz.1 _ ha2 _ hvz
    have hβ : herm σ (a 0) v ≠ 0 := by
      intro h0
      apply hvW
      rw [mem_Wa_iff hσ hf]
      intro i
      fin_cases i
      · exact h0
      · exact hv1
      · exact hv2
    have hexp := gu1a_expand hσ hf v
    simp only [hv1, hv2, zero_smul, add_zero] at hexp
    obtain ⟨t, hkey⟩ := gu1a_alg hexp hβ
    have hβz : herm σ (a 0) v • (b 0 + t • a 0) ∈ z := by
      rw [hkey]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ hvz (Submodule.smul_mem _ _ ha1))
        (Submodule.smul_mem _ _ ha2)
    have hwz : b 0 + t • a 0 ∈ z := by
      have h := Submodule.smul_mem z (herm σ (a 0) v)⁻¹ hβz
      rwa [inv_smul_smul₀ hβ] at h
    have hw0 : herm σ (b 0 + t • a 0) (b 0 + t • a 0) = 0 := hz.1 _ hwz _ hwz
    rw [gu1a_herm_w hσ hf] at hw0
    have ht : σ t = t := by linear_combination hw0 - CharTwo.add_self_eq_zero t
    have hpt := gu1a_pt hσ hf ht
    have hle : Submodule.span F {b 0 + t • a 0, a 1, a 2} ≤ z := by
      apply Submodule.span_le.2
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hwz
      · exact ha1
      · exact ha2
    exact ⟨t, ht, (Submodule.eq_of_le_of_finrank_eq hle (hpt.2.trans hz.2.symm)).symm⟩

theorem isPt_line_point (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) {t : F} (ht : σ t = t) :
    IsPt σ (Submodule.span F {b 0 + t • a 0, a 1, a 2}) ∧
      Wa a ⊓ Submodule.span F {b 0 + t • a 0, a 1, a 2} = Submodule.span F {a 1, a 2} :=
  ⟨gu1a_pt hσ hf ht, gu1a_inter hσ hf⟩

end CFSG.RankThree.GF2n.Smith81.S81V
