module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddShapesPart1

@[expose] public section

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacNodes CFSG.SeitzReduction.F4Pilot
open scoped MatrixGroups Matrix

theorem f4_rank_ge_three_component_is_levi_odd
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {N : ℕ} (hN : 0 < N) (hNodd : N % 2 = 1) (hNΩ : (N : Ω) ≠ 0)
    {a : Fin Tag.F4.rank → Ωˣ}
    (haN : rootDiagUnit Tag.F4 a ^ N = 1)
    (ha1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (v : WeylGroup Tag.F4) (J : Set (Fin Tag.F4.rank)),
      (J = f4LeviB3 ∨ J = f4LeviC3) ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 J ∧
      compRank (componentRoots (rootCharHom a) i) = 3 ∧
      (componentRoots (rootCharHom a) i).ncard = 18 := by
  classical
  have hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) := by
    rintro ⟨-, hn⟩
    have hle := f4_typeA_rank_le_two_odd hN hNodd hNΩ haN i hn
    omega
  obtain ⟨v, μ, hμ, hall⟩ := exists_kacT_of_pos hN hNΩ facts_F4 haN
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := kacF4.exists_comp_eq_of_check f4_tree f4_adj (adm := fun _ => true)
    f4_check rfl hx
  set C : Finset (Option (Fin Tag.F4.rank)) := (c.map (idxNode (r := Tag.F4.rank))).toFinset
    with hCdef
  have hCset : kacF4.comp N μ x = (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (f4_lt c hc w hw)]
      exact hw
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacF4 hN μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hlen : c.length ≤ 4 := by
    obtain ⟨y, hy⟩ := hCp
    have h1 : C.card < Fintype.card (Option (Fin Tag.F4.rank)) :=
      Finset.card_lt_univ_of_notMem hy
    have h2 : Fintype.card (Option (Fin Tag.F4.rank)) = 5 := by
      rw [Fintype.card_option, Fintype.card_fin]
      rfl
    rw [h2, f4_card c hc] at h1
    omega
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hi, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image, compRank_rootsOf kacF4 facts_F4 hCp, f4_card c hc]
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      kacCount Tag.F4 kacF4.θ (c.map (idxNode (r := Tag.F4.rank))).toFinset := by
    rw [hi', ncard_image_smul, ncard_rootsOf kacF4 facts_F4 hCp]
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2]
      (c.map (idxNode (r := Tag.F4.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hnonA
    exact hnonA
  rcases f4_nonA_cases c hc hlen hnonA' with rfl | rfl | rfl | rfl | rfl
  · exfalso
    rw [hrank] at h3
    simp only [List.length_cons, List.length_nil] at h3
    omega
  · refine ⟨v, f4LeviB3, Or.inl rfl, ?_,
      by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_B3⟩
    rw [hi', rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4LeviB3)
      (by rw [hCdef]; decide)
      (fun j => by rw [hCdef, mem_f4LeviB3_narrow]; revert j; decide)]
  · refine ⟨v, f4LeviC3, Or.inr rfl, ?_,
      by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_C3⟩
    rw [hi', rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4LeviC3)
      (by rw [hCdef]; decide)
      (fun j => by rw [hCdef, mem_f4LeviC3_narrow]; revert j; decide)]
  · exact (not_comp_eq_B4_F4_odd hNodd hμ hcomp).elim
  · exfalso
    apply ha1
    refine eq_one_of_simple_mem_class_narrow i (fun j => ?_)
    rw [hi', rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := Set.univ) (by rw [hCdef]; decide)
      (fun j => by simp only [Set.mem_univ, iff_true]; rw [hCdef]; revert j; decide)]
    exact ⟨v⁻¹ • Pi.single j 1, ⟨IsRoot.smul (isRoot_single _ j) v⁻¹, fun i hi =>
      (hi (Set.mem_univ i)).elim⟩, smul_inv_smul v _⟩

theorem f4_rank_ge_three_component_is_levi_odd_of_coord
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {N : ℕ} (hN : 0 < N) (hNodd : N % 2 = 1) (hNΩ : (N : Ω) ≠ 0)
    {a : Fin Tag.F4.rank → Ωˣ}
    (haN : ∀ i, a i ^ N = 1)
    (ha1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (v : WeylGroup Tag.F4) (J : Set (Fin Tag.F4.rank)),
      (J = f4LeviB3 ∨ J = f4LeviC3) ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 J ∧
      compRank (componentRoots (rootCharHom a) i) = 3 ∧
      (componentRoots (rootCharHom a) i).ncard = 18 :=
  f4_rank_ge_three_component_is_levi_odd hN hNodd hNΩ
    (rootDiagUnit_pow_eq_one_of_coord haN) ha1 i h3

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end

end
