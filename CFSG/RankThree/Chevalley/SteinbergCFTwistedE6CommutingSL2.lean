module

public import CFSG.RankThree.Chevalley.EvenTrialityElementaryNine

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

theorem orbitRankOneHom_E6_singleton_injective (hK : ringChar K ≠ 2) (σ : K →+* K)
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : (TwistTag.E6.orbit a).card = 1) :
    Function.Injective (orbitRankOneHom TwistTag.E6 K σ a) := by
  obtain ⟨R, hRu, -, hRH, hRW, -, -, -, -, hRformula⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.E6 K σ a
  have hR : R = orbitRankOneHom TwistTag.E6 K σ a :=
    SL2_hom_ext (fun s => by rw [hRu, orbitRankOneHom_uSL])
      (fun u => by rw [hRH, orbitRankOneHom_HSL]) (by rw [hRW, orbitRankOneHom_WSL])
  have hform : ∀ g, R g = simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a)
      (Matrix.SpecialLinearGroup.map (orbitField TwistTag.E6 K σ a).subtype g) := by
    intro g
    rw [hRformula (simpleRootSL2 TwistTag.E6.tag K) (fun i c => simpleRootSL2_uSL i c)
      (fun i u => simpleRootSL2_HSL i u) (fun i => simpleRootSL2_WSL i) g, ha]
    simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, pow_zero, Equiv.Perm.coe_one, id_eq]
    rfl
  rw [← hR]
  intro A B hAB
  rw [hform, hform] at hAB
  exact SL2_map_injective _ (simpleRootSL2_injective hK _ hAB)

theorem twisted_E6_four_commuting_faithful_fixed_SL2 (K : Type) [Field K] (hK : ringChar K ≠ 2)
    (σ : K →+* K) :
    ∃ ι : Fin 4 → (SL2 (RingHom.eqLocusField σ (RingHom.id K)) →* graphFixedRootGroup .E6 K σ),
      (∀ i, Function.Injective (ι i)) ∧
      ∀ i j, i ≠ j → ∀ A B, ι i A * ι j B = ι j B * ι i A := by
  set a₃ : Fin TwistTag.E6.foldedTag.rank := ⟨2, by decide⟩
  set R := orbitRankOneHom TwistTag.E6 K σ a₃
  have hRinj : Function.Injective R := orbitRankOneHom_E6_singleton_injective hK σ a₃ (by decide)
  have hle : RingHom.eqLocusField σ (RingHom.id K) ≤ orbitField .E6 K σ a₃ := fun c hc => by
    rw [mem_orbitField]
    exact (pow_one σ).symm ▸ hc
  let incl : SL2 (RingHom.eqLocusField σ (RingHom.id K)) →* SL2 (orbitField .E6 K σ a₃) :=
    Matrix.SpecialLinearGroup.map (Subfield.inclusion hle)
  have hincl : Function.Injective incl := SL2_map_injective _
  have hj : ∀ k, (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a₃) = ⟨3, by decide⟩ := fun k => by
    have h := TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a₃) k
    have h3 : TwistTag.E6.orbit a₃ = {⟨3, by decide⟩} := by decide
    rwa [h3, Finset.mem_singleton] at h
  have hRQ : R.range ≤ rootSubgroup TwistTag.E6.tag K (Pi.single ⟨3, by decide⟩ 1) ⊔
      rootSubgroup TwistTag.E6.tag K (-Pi.single ⟨3, by decide⟩ 1) := by
    rw [orbitRankOneHom_range, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_single]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_neg_single]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  have hRC : R.range ≤ graphFixedRootGroup .E6 K σ := by
    rw [orbitRankOneHom_range]
    exact (exceptional_fixed_rank_one_central_image .E6 K σ a₃).choose_spec.2.2.2.2.2.2.1
  have hNC : ∀ a, (orbitN .E6 K σ a 1 : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootGroup .E6 K σ := fun a => by
    rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
      (orbitX_mem_graphFixedPosUnipotent _ σ a _)) (graphFixedNegUnipotent_le_graphFixedRootGroup
        _ K σ (orbitY_mem_graphFixedNegUnipotent _ σ a _)))
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
        (orbitX_mem_graphFixedPosUnipotent _ σ a _))
  let seq : Fin 4 → List (Fin TwistTag.E6.foldedTag.rank) := ![[], [⟨1, by decide⟩],
    [⟨1, by decide⟩, ⟨0, by decide⟩], [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩,
      ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]]
  let h : Fin 4 → ModGL TwistTag.E6.tag K := fun i =>
    ((seq i).map fun a => (orbitN .E6 K σ a 1 : ModGL TwistTag.E6.tag K)).reverse.prod
  have hhC : ∀ i, h i ∈ graphFixedRootGroup .E6 K σ := fun i =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
      exact hNC a
  have hmem : ∀ i A, (MulAut.conj (h i)).toMonoidHom.comp (R.comp incl) A ∈
      graphFixedRootGroup .E6 K σ := fun i A =>
    mul_mem (mul_mem (hhC i) (hRC ⟨_, rfl⟩)) (inv_mem (hhC i))
  obtain ⟨hroot, hcheck⟩ := e6_four_roots_check
  have he3 : (Pi.single ⟨3, by decide⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      e6Vec ![0, 0, 0, 1, 0, 0] := by decide +kernel
  have hfold : ∀ i, (seq i).foldl (fun v a => TwistTag.E6.orbitReflection a • v)
      (Pi.single ⟨3, by decide⟩ 1) = (![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) i := by
    obtain ⟨h1, h2, h3⟩ := e6_fold_roots
    intro i
    fin_cases i
    · exact he3
    · rw [he3]; exact h1
    · rw [he3]; exact h2
    · rw [he3]; exact h3
  have hQ : ∀ i A, (MulAut.conj (h i)).toMonoidHom.comp (R.comp incl) A ∈
      rootSubgroup TwistTag.E6.tag K ((![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) i) ⊔
      rootSubgroup TwistTag.E6.tag K (-(![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) i) := fun i A => by
    rw [← hfold i, ← map_conj_orbitN_list_rootPair .E6 σ (seq i) (isRoot_single _ _)]
    exact ⟨_, hRQ ⟨_, rfl⟩, rfl⟩
  refine ⟨fun i => ((MulAut.conj (h i)).toMonoidHom.comp (R.comp incl)).codRestrict _ (hmem i),
    fun i A B hAB => ?_, fun i j hij A B => ?_⟩
  · exact (hRinj.comp hincl) ((MulAut.conj (h i)).injective (congrArg Subtype.val hAB))
  · obtain ⟨h0, hp, hm⟩ := hcheck i j hij
    exact Subtype.ext (commute_of_mem_rootPair_of_check (hroot i) (hroot j) h0 hp hm
      (hQ i A) (hQ j B))

end CFSG.RankThree.Chevalley
