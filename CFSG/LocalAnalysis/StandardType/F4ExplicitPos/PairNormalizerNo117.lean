module

public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatNo117Part2

@[expose] public section

public noncomputable section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.UnipotentNo117

open scoped Pointwise

namespace CFSG.StandardType.F4ExplicitPos.PairNormalizerNo117

variable {K : Type} [Field K]

theorem f4_borelGroup_le_normalizer_Uθ :
    borelGroup Tag.F4 K ≤ Subgroup.normalizer (Uθ Tag.F4 K : Set (ModGL Tag.F4 K)) := by
  have hmain := f4_positive_root_ideal_normality K (J := {highRoot Tag.F4})
    (S := {α | IsRoot Tag.F4 α ∧ 0 < height α})
    (fun α hα => by
      rw [Set.mem_singleton_iff] at hα
      subst hα
      exact ⟨isRoot_highRoot Tag.F4, height_highRoot_pos Tag.F4⟩)
    (fun _ hα => hα)
    (fun α hα β hβ a b ha hb hr => by
      rw [Set.mem_singleton_iff] at hβ
      subst hβ
      exact absurd hr (not_isRoot_nsmul_add_nsmul_highRoot hα.2 ha hb))
  refine sup_le ?_ ?_
  · exact CFSG.StandardType.RootCentExc.torusGroup_le_normalizer_rootSubgroup
      (isRoot_highRoot Tag.F4)
  · have hnorm := (Subgroup.normal_subgroupOf_iff_le_normalizer hmain.1).1 hmain.2
    rwa [show rootSpan Tag.F4 K {highRoot Tag.F4} =
        rootSubgroup Tag.F4 K (highRoot Tag.F4) from by simp [rootSpan]] at hnorm

theorem f4_eq_highRoot_of_pinnedX_eq
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    {d e : K} (hd : d ≠ 0)
    (h : pinnedX Tag.F4 K β d = pinnedX Tag.F4 K (highRoot Tag.F4) e) :
    β = highRoot Tag.F4 := by
  by_contra hne
  rcases IsRoot.height_pos_or_neg hβ with hpos | hneg
  · have hinj : Function.Injective ![β, highRoot Tag.F4] := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij hne
      · exact absurd hij.symm hne
      · rfl
    have hposα : ∀ i, IsRoot Tag.F4 (![β, highRoot Tag.F4] i) ∧
        0 < height (![β, highRoot Tag.F4] i) := by
      intro i
      fin_cases i
      · exact ⟨hβ, hpos⟩
      · exact ⟨isRoot_highRoot Tag.F4, height_highRoot_pos Tag.F4⟩
    have hprod := (positive_root_product_injectivity_w (τ := Tag.F4) K
      ![β, highRoot Tag.F4] hinj hposα).2 (a₁ := ![d, 0]) (a₂ := ![0, e]) (by
        simp [List.ofFn_succ, pinnedX_zero, h])
    have := congrFun hprod 0
    exact hd (by simpa using this)
  · have hbot := borelGroup_inf_negUnipotent (τ := Tag.F4) (K := K)
    have hmem : pinnedX Tag.F4 K β d ∈ borelGroup Tag.F4 K ⊓ negUnipotent Tag.F4 K := by
      refine Subgroup.mem_inf.2 ⟨?_, pinnedX_mem_rootSpan
        (S := {α | IsRoot Tag.F4 α ∧ height α < 0}) ⟨hβ, hneg⟩ d⟩
      rw [h]
      exact Subgroup.mem_sup_right
        (CFSG.StandardType.RootCentExc.pinnedX_mem_posUnipotent
          (isRoot_highRoot Tag.F4) (height_highRoot_pos Tag.F4) e)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hd (pinnedX_injective Tag.F4 K β (hmem.trans (pinnedX_zero Tag.F4 K β).symm))

theorem f4_mem_parabolicWeylGroup_of_smul_highRoot
    {w : WeylGroup Tag.F4}
    (hw : w • highRoot Tag.F4 = highRoot Tag.F4) :
    w ∈ parabolicWeylGroup Tag.F4 (Jθ Tag.F4) :=
  CFSG.StandardType.RootCentExc.mem_parabolicWeylGroup_of_smul_eq (τ := Tag.F4)
    (θ := highRoot Tag.F4) (i₀ := iθ Tag.F4) (c := cθ Tag.F4)
    (cθ_ne_zero Tag.F4) (iform_highRoot_apply Tag.F4) hw

theorem f4_Pθ_le_normalizer_Uθ :
    Pθ Tag.F4 K ≤ Subgroup.normalizer (Uθ Tag.F4 K : Set (ModGL Tag.F4 K)) := by
  refine sup_le (f4_borelGroup_le_normalizer_Uθ (K := K)) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, rfl⟩
  refine mem_normalizer_of_map_eq ?_
  rw [map_conj_weylElt_rootSubgroup K j (isRoot_highRoot Tag.F4),
    reflect_highRoot_of_ne Tag.F4 j hj]

theorem f4_mem_Pθ_of_conj_le
    {g : ModGL Tag.F4 K} (hg : g ∈ adjointGroup Tag.F4 K)
    (hc : conjSub g (Uθ Tag.F4 K) ≤ Uθ Tag.F4 K) : g ∈ Pθ Tag.F4 K := by
  have hg' : g ∈ ⋃ w, bruhatCell Tag.F4 K w := by
    rw [← f4_adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  have hw' := hw
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw'
  have hB := f4_borelGroup_le_normalizer_Uθ (K := K)
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB hb') _).1
    (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hd
    have h1 : pinnedX Tag.F4 K (highRoot Tag.F4) (1 : K) = 1 := by
      calc pinnedX Tag.F4 K (highRoot Tag.F4) (1 : K)
          = b'⁻¹ * (b' * pinnedX Tag.F4 K (highRoot Tag.F4) 1 * b'⁻¹) * b' := by group
        _ = 1 := by rw [← hd]; group
    exact one_ne_zero (pinnedX_injective Tag.F4 K (highRoot Tag.F4)
      (h1.trans (pinnedX_zero Tag.F4 K _).symm))
  have hmem : (b * canonicalRep (coxeterSystem Tag.F4) K w * b') *
      pinnedX Tag.F4 K (highRoot Tag.F4) 1 *
      (b * canonicalRep (coxeterSystem Tag.F4) K w * b')⁻¹ ∈ Uθ Tag.F4 K :=
    hc ⟨pinnedX Tag.F4 K (highRoot Tag.F4) 1, mem_rootSubgroup.2 ⟨1, rfl⟩, rfl⟩
  obtain ⟨c, hc'⟩ := mem_rootSubgroup.1 hmem
  obtain ⟨e, he⟩ := mem_rootSubgroup.1 ((Subgroup.mem_normalizer_iff.1 (hB (inv_mem hb)) _).1
    (mem_rootSubgroup.2 ⟨c, rfl⟩))
  obtain ⟨ε, hε, hn⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_highRoot Tag.F4)
  have hε0 : ε ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hε
    exact zero_ne_one hε
  have hkey : pinnedX Tag.F4 K (w • highRoot Tag.F4) (ε * d) =
      pinnedX Tag.F4 K (highRoot Tag.F4) e := by
    rw [← hn, he, hd, hc']
    group
  have hwθ := f4_eq_highRoot_of_pinnedX_eq (IsRoot.smul (isRoot_highRoot Tag.F4) w)
    (mul_ne_zero hε0 hd0) hkey
  exact bruhatCell_subset_parabolicSubgroup (K := K) (J := Jθ Tag.F4)
    (f4_mem_parabolicWeylGroup_of_smul_highRoot hwθ) hw

theorem f4_Pθ_eq_inf_normalizer :
    Pθ Tag.F4 K = adjointGroup Tag.F4 K ⊓
      Subgroup.normalizer (Uθ Tag.F4 K : Set (ModGL Tag.F4 K)) := by
  refine le_antisymm (le_inf (parabolicSubgroup_le_adjointGroup Tag.F4 K (Jθ Tag.F4))
    (f4_Pθ_le_normalizer_Uθ (K := K))) ?_
  rintro g ⟨hgA, hgN⟩
  refine f4_mem_Pθ_of_conj_le hgA ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (Subgroup.mem_normalizer_iff.1 hgN x).1 hx

end CFSG.StandardType.F4ExplicitPos.PairNormalizerNo117

end

end
