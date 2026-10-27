module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart25
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PairNormalizerNo117

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.PairStabilizerNative

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley

open CFSG.SeitzReduction CFSG.LieType.AlgebraicGroups WithConv

open scoped CFSG.ConvolutionPoints

open CFSG.LieType.Steinberg.Adjoint

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.StandardType.RootCentExc

open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.PositiveNo117

open CFSG.StandardType.F4ExplicitPos.PairNormalizerNo117

open scoped Pointwise

variable {K : Type} [Field K]

theorem f4_posUnipotent_le_normalizer_of_absorbs
    {S : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.F4 α ∧ 0 < height α)
    (habs : ∀ α, IsRoot Tag.F4 α ∧ 0 < height α → ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot Tag.F4 (a • α + b • β) → a • α + b • β ∈ S) :
    posUnipotent Tag.F4 K ≤
      Subgroup.normalizer (rootSpan Tag.F4 K S : Set (ModGL Tag.F4 K)) := by
  obtain ⟨hle, hnorm⟩ := f4_positive_root_ideal_normality K (J := S)
    (S := {α | IsRoot Tag.F4 α ∧ 0 < height α}) (fun α hα => hS α hα) (fun α hα => hα)
    (fun α hα β hβ a b ha hb hr => habs α hα β hβ a b ha hb hr)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnorm

theorem f4_borelGroup_le_normalizer_parabolicRadical
    (J : Set (Fin Tag.F4.rank)) :
    borelGroup Tag.F4 K ≤
      Subgroup.normalizer (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) :=
  sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1.1)
    (f4_posUnipotent_le_normalizer_of_absorbs (fun _ hα => hα.1)
      fun _ hα _ hβ _ _ ha hb hr => add_mem_parabolicRadicalRoots hα hβ ha hb hr)

theorem f4_parabolicSubgroup_le_normalizer_parabolicRadical
    (J : Set (Fin Tag.F4.rank)) :
    parabolicSubgroup Tag.F4 K J ≤
      Subgroup.normalizer (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) :=
  sup_le (f4_borelGroup_le_normalizer_parabolicRadical J) ((Subgroup.closure_le _).2
    fun _ ⟨_, hj, he⟩ => he ▸ weylElt_mem_normalizer_parabolicRadical hj)

theorem exists_mem_parabolicWeylGroup_smul_w
    {τ : Tag} {J : Set (Fin τ.rank)} :
    ∀ (n : ℕ) (α : Fin τ.rank → ℤ), (height α).toNat = n → α ∈ parabolicPosRoots τ J →
      ∃ w ∈ parabolicWeylGroup τ J, ∃ j ∈ J,
        w • (Pi.single j 1 : Fin τ.rank → ℤ) = α := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α hn hα
    obtain ⟨⟨hroot, hzero⟩, -, hpos⟩ := hα
    have hnn := (IsRoot.height_pos_iff hroot).1 hpos
    obtain ⟨i, hαi, hci⟩ := exists_cartan_pos_w (IsRoot.ne_zero hroot) hnn
    have hiJ : i ∈ J := by
      by_contra hi
      rw [hzero i hi] at hαi
      exact lt_irrefl 0 hαi
    by_cases hsimple : α = Pi.single i 1
    · exact ⟨1, one_mem _, i, hiJ, by rw [one_smul, hsimple]⟩
    · have hβ : reflect τ i α ∈ {β | IsRoot τ β ∧ 0 < height β ∧ β ≠ Pi.single i 1} :=
        (bijOn_reflect i).mapsTo ⟨hroot, hpos, hsimple⟩
      have hht : height (reflect τ i α) = height α - ∑ j, τ.cartan i j * α j := by
        simp [reflect, height, Finset.sum_sub_distrib, Pi.single_apply]
      have hβJ : reflect τ i α ∈ parabolicPosRoots τ J := by
        refine ⟨⟨hβ.1, fun k hk => ?_⟩, hβ.1, hβ.2.1⟩
        rw [reflect, Pi.sub_apply, Pi.smul_apply,
          Pi.single_eq_of_ne (fun h => hk (by rw [h]; exact hiJ)), smul_zero, sub_zero,
          hzero k hk]
      have hlt : (height (reflect τ i α)).toNat < n := by
        rw [← hn, hht]
        have := hβ.2.1
        omega
      obtain ⟨w, hw, j, hj, hwj⟩ := ih _ hlt _ rfl hβJ
      refine ⟨simple τ i * w, mul_mem (Subgroup.subset_closure ⟨i, hiJ, rfl⟩) hw, j, hj, ?_⟩
      rw [mul_smul, hwj, simple_smul, reflect_reflect]

theorem f4_parabolicLeviUnipotent_le_parabolicLevi
    (J : Set (Fin Tag.F4.rank)) :
    parabolicLeviUnipotent Tag.F4 K J ≤ parabolicLevi Tag.F4 K J := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨w, hw, j, hj, rfl⟩ := exists_mem_parabolicWeylGroup_smul_w _ α rfl hα
  rw [← (canonical_weyl_root_transport Tag.F4 K).2.1 w _ (isRoot_single Tag.F4 j)]
  rintro _ ⟨u, hu, rfl⟩
  have huM : u ∈ parabolicLevi Tag.F4 K J := by
    refine (Subgroup.closure_le _).2 ?_ hu
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_parabolicLevi hj c
  have hn := canonicalRep_mem_parabolicLevi (K := K) hw
  exact mul_mem (mul_mem hn huM) (inv_mem hn)

theorem f4_posUnipotent_eq_mul_parabolic
    (J : Set (Fin Tag.F4.rank)) :
    (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) =
      (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) *
        (parabolicLeviUnipotent Tag.F4 K J : Set (ModGL Tag.F4 K)) := by
  refine Set.Subset.antisymm (fun u hu => ?_) ?_
  · obtain ⟨αR, hRinj, hRrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos
      (S := parabolicRadicalRoots Tag.F4 J) fun α h => h.1)
    obtain ⟨αL, hLinj, hLrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos
      (S := parabolicPosRoots Tag.F4 J) fun α h => h.2)
    have hR : ∀ k, αR k ∈ parabolicRadicalRoots Tag.F4 J :=
      fun k => hRrange ▸ Set.mem_range_self k
    have hL : ∀ k, αL k ∈ parabolicPosRoots Tag.F4 J :=
      fun k => hLrange ▸ Set.mem_range_self k
    set α := Fin.append αR αL
    have hdisj : ∀ k l, αR k ≠ αL l := fun k l h => by
      have h1 : αR k ∈ parabolicRadicalRoots Tag.F4 J := hR k
      rw [h] at h1
      exact (Set.disjoint_left.1 (disjoint_parabolicRadicalRoots_parabolicPosRoots J)) h1 (hL l)
    have hinj : Function.Injective α := by
      intro k l h
      induction k using Fin.addCases with
      | left k =>
        induction l using Fin.addCases with
        | left l => simp only [α, Fin.append_left] at h; rw [hRinj h]
        | right l =>
          simp only [α, Fin.append_left, Fin.append_right] at h
          exact absurd h (hdisj k l)
      | right k =>
        induction l using Fin.addCases with
        | left l =>
          simp only [α, Fin.append_left, Fin.append_right] at h
          exact absurd h.symm (hdisj l k)
        | right l => simp only [α, Fin.append_right] at h; rw [hLinj h]
    have hrange : Set.range α = {β | IsRoot Tag.F4 β ∧ 0 < height β} := by
      ext β
      constructor
      · rintro ⟨k, rfl⟩
        induction k using Fin.addCases with
        | left k => simpa [α] using (hR k).1
        | right k => simpa [α] using (hL k).2
      · rintro ⟨hβ, hβp⟩
        have hmem : β ∈ parabolicRadicalRoots Tag.F4 J ∪ parabolicPosRoots Tag.F4 J := by
          rw [parabolicRadicalRoots_union]
          exact ⟨hβ, hβp⟩
        rcases hmem with h | h
        · obtain ⟨k, hk⟩ : β ∈ Set.range αR := by rw [hRrange]; exact h
          exact ⟨Fin.castAdd _ k, by simp [α, hk]⟩
        · obtain ⟨k, hk⟩ : β ∈ Set.range αL := by rw [hLrange]; exact h
          exact ⟨Fin.natAdd _ k, by simp [α, hk]⟩
    obtain ⟨c, -, rfl⟩ := ((f4_positive_root_collection K).2 α hinj hrange).2.2 hu
    refine ⟨_, list_prod_pinnedX_mem_rootSpan αR hR (fun k => c (Fin.castAdd _ k)), _,
      list_prod_pinnedX_mem_rootSpan αL hL (fun k => c (Fin.natAdd _ k)), ?_⟩
    simp only
    rw [← List.prod_append, ← List.ofFn_fin_append]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    induction k using Fin.addCases with
    | left k => simp [α]
    | right k => simp [α]
  · rintro _ ⟨u, hu, v, hv, rfl⟩
    exact mul_mem (rootSpan_le_posUnipotent (fun _ hα => hα.1) hu)
      (rootSpan_le_posUnipotent (fun _ hα => hα.2) hv)

theorem f4_borelGroup_eq_mul_parabolic
    (J : Set (Fin Tag.F4.rank)) :
    (borelGroup Tag.F4 K : Set (ModGL Tag.F4 K)) =
      (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) *
        ((torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) *
          (parabolicLeviUnipotent Tag.F4 K J : Set (ModGL Tag.F4 K))) := by
  have hHU := (triangular_borel_structure.{0, 0} Tag.F4 K).2.2.2.2.1
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · rw [hHU] at hb
    obtain ⟨h, hh, u, hu, rfl⟩ := hb
    rw [SetLike.mem_coe, ← SetLike.mem_coe, f4_posUnipotent_eq_mul_parabolic J] at hu
    obtain ⟨q, hq, v, hv, rfl⟩ := hu
    have hq' : h * q * h⁻¹ ∈ parabolicRadical Tag.F4 K J :=
      (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan
        (fun _ hα => hα.1.1) hh) q).1 hq
    exact ⟨h * q * h⁻¹, hq', h * v, ⟨h, hh, v, hv, rfl⟩, by group⟩
  · rintro _ ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩
    exact mul_mem (le_trans (parabolicRadical_le_posUnipotent J) le_sup_right hq)
      (mul_mem (le_sup_left (b := posUnipotent Tag.F4 K) hh)
        (le_trans (parabolicLeviUnipotent_le_posUnipotent J) le_sup_right hv))

theorem f4_parabolicRadical_sup_parabolicLevi
    (J : Set (Fin Tag.F4.rank)) :
    parabolicRadical Tag.F4 K J ⊔ parabolicLevi Tag.F4 K J =
      parabolicSubgroup Tag.F4 K J := by
  refine le_antisymm (sup_le (le_trans (parabolicRadical_le_posUnipotent J)
    (posUnipotent_le_parabolicSubgroup J)) (parabolicLevi_le_parabolicSubgroup J)) ?_
  refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
  · have hb' : b ∈ (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) *
        ((torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) *
          (parabolicLeviUnipotent Tag.F4 K J : Set (ModGL Tag.F4 K))) := by
      rw [← f4_borelGroup_eq_mul_parabolic J]
      exact hb
    obtain ⟨q, hq, _, ⟨h, hh, v, hv, rfl⟩, rfl⟩ := hb'
    exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right
      (mul_mem (torusGroup_le_parabolicLevi J hh)
        (f4_parabolicLeviUnipotent_le_parabolicLevi J hv)))
  · rintro _ ⟨j, hj, rfl⟩
    exact Subgroup.mem_sup_right (weylElt_mem_parabolicLevi hj)

theorem f4_parabolicSubgroup_eq_mul_parabolic
    (J : Set (Fin Tag.F4.rank)) :
    (parabolicSubgroup Tag.F4 K J : Set (ModGL Tag.F4 K)) =
      (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) *
        (parabolicLevi Tag.F4 K J : Set (ModGL Tag.F4 K)) := by
  have hMN : parabolicLevi Tag.F4 K J ≤
      Subgroup.normalizer (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) :=
    le_trans (parabolicLevi_le_parabolicSubgroup J)
      (f4_parabolicSubgroup_le_normalizer_parabolicRadical J)
  rw [← f4_parabolicRadical_sup_parabolicLevi J,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hMN]

theorem f4_exists_factor_parabolicSubgroup
    (J : Set (Fin Tag.F4.rank)) {g : ModGL Tag.F4 K}
    (hg : g ∈ parabolicSubgroup Tag.F4 K J) :
    ∃ q ∈ parabolicRadical Tag.F4 K J, ∃ m ∈ parabolicLevi Tag.F4 K J, g = q * m := by
  have hg' : g ∈ (parabolicRadical Tag.F4 K J : Set (ModGL Tag.F4 K)) *
      (parabolicLevi Tag.F4 K J : Set (ModGL Tag.F4 K)) := by
    rw [← f4_parabolicSubgroup_eq_mul_parabolic J]
    exact hg
  obtain ⟨q, hq, m, hm, rfl⟩ := hg'
  exact ⟨q, hq, m, hm, rfl⟩

theorem f4_pinnedX_eq_coe_xPar
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α) (c : K) :
    pinnedX Tag.F4 K α c =
      ((xPar (rootOperatorFamily Tag.F4) α
        (((rootOperatorFamily Tag.F4).pinnedFamilySign α : K) * c) :
          adjointGroup Tag.F4 K) : ModGL Tag.F4 K) := by
  rw [(rootOperatorFamily Tag.F4).pinnedX_eq_eltUnit K hα,
    xPar_of_isRoot_without117 (rootOperatorFamily Tag.F4) hα,
    RootOperatorFamily.coe_eltElement]

theorem f4_commute_pinnedX_of_not_isRoot
    {α β : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot Tag.F4 α) (hβ : IsRoot Tag.F4 β) (hne : α + β ≠ 0)
    (h : ¬ IsRoot Tag.F4 (α + β)) (c d : K) :
    Commute (pinnedX Tag.F4 K α c) (pinnedX Tag.F4 K β d) := by
  rw [f4_pinnedX_eq_coe_xPar hα c, f4_pinnedX_eq_coe_xPar hβ d]
  exact (commute_xPar_without117 (rootOperatorFamily Tag.F4)
    CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117 noG2_F4 hα hβ hne h
      (((rootOperatorFamily Tag.F4).pinnedFamilySign α : K) * c)
      (((rootOperatorFamily Tag.F4).pinnedFamilySign β : K) * d)).map
    (adjointGroup Tag.F4 K).subtype

theorem f4_neg_highRoot_mem : (-highRoot Tag.F4 : Fin Tag.F4.rank → ℤ) ∈ rootFinset Tag.F4 := by
  decide +kernel

theorem f4_isRoot_neg_highRoot : IsRoot Tag.F4 (-highRoot Tag.F4) :=
  mem_rootFinset.1 f4_neg_highRoot_mem

theorem f4_single_ne_highRoot (j : Fin Tag.F4.rank) :
    (Pi.single j 1 : Fin Tag.F4.rank → ℤ) ≠ highRoot Tag.F4 ∧
    (Pi.single j 1 : Fin Tag.F4.rank → ℤ) ≠ -highRoot Tag.F4 ∧
    (-Pi.single j 1 : Fin Tag.F4.rank → ℤ) ≠ highRoot Tag.F4 ∧
    (-Pi.single j 1 : Fin Tag.F4.rank → ℤ) ≠ -highRoot Tag.F4 := by
  fin_cases j <;> decide +kernel

theorem f4_not_isRoot_single_neg_highRoot (j : Fin Tag.F4.rank) (hj : j ≠ iθ Tag.F4) :
    (Pi.single j 1 + -highRoot Tag.F4 : Fin Tag.F4.rank → ℤ) ∉ rootFinset Tag.F4 ∧
      (-Pi.single j 1 + -highRoot Tag.F4 : Fin Tag.F4.rank → ℤ) ∉ rootFinset Tag.F4 := by
  fin_cases j
  · exact absurd rfl hj
  all_goals decide +kernel

theorem f4_Lθ_le_normalizer_Uneg :
    Lθ Tag.F4 K ≤ Subgroup.normalizer (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K : Set (ModGL Tag.F4 K)) := by
  have hsingle : (rootSpan Tag.F4 K ({-highRoot Tag.F4} : Set (Fin Tag.F4.rank → ℤ))) =
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Uneg Tag.F4 K := by
    refine le_antisymm (iSup₂_le fun β hβ => ?_)
      (le_iSup₂_of_le (-highRoot Tag.F4) (Set.mem_singleton _) le_rfl)
    rw [Set.mem_singleton_iff.1 hβ]
  refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
  · rw [← hsingle]
    exact torusGroup_le_normalizer_rootSpan (fun α hα => by
      rw [Set.mem_singleton_iff.1 hα]
      exact f4_isRoot_neg_highRoot)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · refine mem_normalizer_of_forall_mul_eq fun x hx => ?_
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hx
    rw [← pinnedX_single]
    refine (f4_commute_pinnedX_of_not_isRoot (isRoot_single Tag.F4 j)
      (f4_isRoot_neg_highRoot) ?_ ?_ c d).eq
    · intro h
      have h' := congrArg (fun v => v + highRoot Tag.F4) h
      rw [add_assoc, neg_add_cancel, add_zero, zero_add] at h'
      exact (f4_single_ne_highRoot j).1 h'
    · intro h
      exact (f4_not_isRoot_single_neg_highRoot j hj).1 (mem_rootFinset.2 h)
  · refine mem_normalizer_of_forall_mul_eq fun x hx => ?_
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hx
    rw [← pinnedX_neg_single]
    refine (f4_commute_pinnedX_of_not_isRoot (isRoot_neg_single Tag.F4 j)
      (f4_isRoot_neg_highRoot) ?_ ?_ c d).eq
    · intro h
      have h' := congrArg (fun v => v + highRoot Tag.F4) h
      rw [add_assoc, neg_add_cancel, add_zero, zero_add] at h'
      exact (f4_single_ne_highRoot j).2.2.1 h'
    · intro h
      exact (f4_not_isRoot_single_neg_highRoot j hj).2 (mem_rootFinset.2 h)

end CFSG.StandardType.F4ExplicitPos.PairStabilizerNative
end

end
