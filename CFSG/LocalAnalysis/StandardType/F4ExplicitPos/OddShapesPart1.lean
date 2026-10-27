module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.F4LowRankShapes

@[expose] public section

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacNodes CFSG.SeitzReduction.F4Pilot

open scoped MatrixGroups Matrix

theorem not_comp_eq_longA3_F4_odd
    {N : ℕ} (hNodd : N % 2 = 1) {μ : Fin Tag.F4.rank → ℤ} (_hμ : kacF4.IsNormal N μ)
    {x : Option (Fin Tag.F4.rank)}
    (hc : kacF4.comp N μ x = {y | nodeIdx y ∈ ([0, 1, 2] : List ℕ)}) : False := by
  have hmem : ∀ y : Option (Fin Tag.F4.rank), nodeIdx y ∈ ([0, 1, 2] : List ℕ) →
      kacF4.IsZ N μ y := fun y hy => by
    have : y ∈ kacF4.comp N μ x := by rw [hc]; exact hy
    exact this.1
  have hz0 : kacF4.IsZ N μ none := hmem none (by decide)
  have hz1 : kacF4.IsZ N μ (some 0) := hmem (some 0) (by decide)
  have hz2 : kacF4.IsZ N μ (some 1) := hmem (some 1) (by decide)
  change kacF4.θ ⬝ᵥ μ = (N : ℤ) at hz0
  change μ 0 = 0 at hz1
  change μ 1 = 0 at hz2
  rw [f4_theta_dot, hz1, hz2] at hz0
  have hdiv : (2 : ℤ) ∣ (N : ℤ) := ⟨2 * μ 2 + μ 3, by linarith⟩
  have hdiv' : 2 ∣ N := Int.natCast_dvd_natCast.1 hdiv
  have hmod : N % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv'
  omega

theorem f4_typeA_rank_le_two_odd
    {L : Type} [Field L] [IsAlgClosed L] {N : ℕ} (hN : 0 < N) (hNodd : N % 2 = 1)
    (hNL : (N : L) ≠ 0) {a : Fin Tag.F4.rank → Lˣ}
    (hTN : rootDiagUnit Tag.F4 a ^ N = 1)
    (i : KernelComponent (rootCharHom a))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    compRank (componentRoots (rootCharHom a) i) ≤ 2 := by
  classical
  by_cases h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i)
  · obtain ⟨v, μ, hμ, hall⟩ := exists_kacT_of_pos hN hNL facts_F4 hTN
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
    have hi' : componentRoots (rootCharHom a) i =
        (fun α => v • α) '' kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) := by
      rw [hi, hCset]
    have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
      rw [hi', compRank_image, compRank_rootsOf kacF4 facts_F4 hCp, f4_card c hc]
    have hncard : (componentRoots (rootCharHom a) i).ncard =
        kacCount Tag.F4 kacF4.θ (c.map (idxNode (r := Tag.F4.rank))).toFinset := by
      rw [hi', ncard_image_smul, ncard_rootsOf kacF4 facts_F4 hCp]
    rw [hrank] at h2 hn
    rw [hncard] at hn
    rcases f4_count_raw c hc h2 hn with rfl | rfl | rfl | rfl
    · rw [hrank]; decide
    · rw [hrank]; decide
    · rw [hrank]; decide
    · exact (not_comp_eq_longA3_F4_odd hNodd hμ hcomp).elim
  · omega

private theorem image_image_smul_odd {S : Set (Fin Tag.F4.rank → ℤ)}
    {v w : WeylGroup Tag.F4} :
    (fun α => v • α) '' ((fun α => w • α) '' S) =
      (fun α => (v * w) • α) '' S := by
  rw [Set.image_image]
  congr 1
  funext α
  exact (mul_smul v w α).symm

private theorem singleton_shape_odd
    (x : Option (Fin Tag.F4.rank)) :
    ∃ (w : WeylGroup Tag.F4) (j : Fin Tag.F4.rank),
      kacF4.rootsOf ({x} : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
  obtain ⟨w, j, hwj⟩ :=
    isRoot_iff_exists_smul_single.1 (KacData.isRoot_extRoot kacF4 x)
  refine ⟨w, j, ?_⟩
  rw [rootsOf_singleton kacF4 x]
  ext γ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨Pi.single j 1, Or.inl rfl, hwj⟩
    · exact ⟨-Pi.single j 1, Or.inr rfl, by rw [smul_neg, hwj]⟩
  · rintro ⟨α, hα, rfl⟩
    rcases hα with rfl | rfl
    · left
      exact hwj
    · right
      rw [smul_neg, hwj]

theorem f4_rank_le_two_component_shape_odd
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {N : ℕ} (hN : 0 < N) (_hNodd : N % 2 = 1) (hNΩ : (N : Ω) ≠ 0)
    {a : Fin Tag.F4.rank → Ωˣ}
    (haN : rootDiagUnit Tag.F4 a ^ N = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : compRank (componentRoots (rootCharHom a) i) ≤ 2) :
    ∃ v : WeylGroup Tag.F4,
      (∃ j : Fin Tag.F4.rank, componentRoots (rootCharHom a) i =
          (fun α => v • α) ''
            ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LongSupport ∨
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4ShortSupport ∨
      componentRoots (rootCharHom a) i = (fun α => v • α) '' b2LeviRoots := by
  classical
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
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hi, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image, compRank_rootsOf kacF4 facts_F4 hCp, f4_card c hc]
  have hlen : c.length ≤ 2 := by omega
  rcases f4_low_rank_cases c hc hlen with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hC : C = ({none} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape_odd none
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul_odd]⟩⟩
  ·
    have hC : C = ({some 0} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape_odd (some 0)
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul_odd]⟩⟩
  ·
    have hC : C = ({some 1} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape_odd (some 1)
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul_odd]⟩⟩
  ·
    have hC : C = ({some 2} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape_odd (some 2)
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul_odd]⟩⟩
  ·
    have hC : C = ({some 3} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape_odd (some 3)
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul_odd]⟩⟩
  ·
    have hC : C = ({none, some 0} : Finset (Option (Fin Tag.F4.rank))) := by
      rw [hCdef]; decide +kernel
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => (coxeterSystem Tag.F4).wordProd f4WordLong • α) ''
          parabolicRoots Tag.F4 f4LongSupport := by
      rw [f4_rootsOf_eq (C := C) hCp (σ := f4Sigma01)
        (fun r hr hk => f4_long01_roots r hr (by simpa [hC] using hk))
        (fun a b hab => ⟨(f4_long01_isRoot a b hab).1,
          by simpa [hC] using (f4_long01_isRoot a b hab).2.1⟩),
        frameRoots_f4Sigma01]
    exact ⟨v * (coxeterSystem Tag.F4).wordProd f4WordLong,
      Or.inr (Or.inl (by rw [hi', hroots, image_image_smul_odd]))⟩
  ·
    have hC : C = ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) := by
      rw [hCdef]; decide +kernel
    have hnone : none ∉ C := by rw [hC]; decide +kernel
    have hCJ : ∀ j : Fin Tag.F4.rank, some j ∈ C ↔ j ∈ f4LongSupport := by
      intro j
      rw [hC, mem_f4LongSupport]
      revert j
      decide +kernel
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        parabolicRoots Tag.F4 f4LongSupport :=
      rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4LongSupport) hnone hCJ
    exact ⟨v, Or.inr (Or.inl (by rw [hi', hroots]))⟩
  ·
    have hC : C = ({some 1, some 2} : Finset (Option (Fin Tag.F4.rank))) := by
      rw [hCdef]; decide +kernel
    have hnone : none ∉ C := by rw [hC]; decide +kernel
    have hCJ : ∀ j : Fin Tag.F4.rank, some j ∈ C ↔ j ∈ nodesTU := by
      intro j
      rw [hC, mem_nodesTU]
      revert j
      decide +kernel
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) = b2LeviRoots := by
      rw [b2LeviRoots]
      exact rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := nodesTU) hnone hCJ
    exact ⟨v, Or.inr (Or.inr (Or.inr (by rw [hi', hroots])))⟩
  ·
    have hC : C = ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) := by
      rw [hCdef]; decide +kernel
    have hnone : none ∉ C := by rw [hC]; decide +kernel
    have hCJ : ∀ j : Fin Tag.F4.rank, some j ∈ C ↔ j ∈ f4ShortSupport := by
      intro j
      rw [hC, mem_f4ShortSupport]
      revert j
      decide +kernel
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        parabolicRoots Tag.F4 f4ShortSupport :=
      rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4ShortSupport) hnone hCJ
    exact ⟨v, Or.inr (Or.inr (Or.inl (by rw [hi', hroots])))⟩

theorem rootDiagUnit_pow_eq_one_of_coord {Ω : Type} [Field Ω] {N : ℕ}
    {a : Fin Tag.F4.rank → Ωˣ} (h : ∀ i, a i ^ N = 1) :
    rootDiagUnit Tag.F4 a ^ N = 1 := by
  have ha : a ^ N = 1 := funext h
  have hm : rootDiagUnit Tag.F4 (a ^ N) = rootDiagUnit Tag.F4 a ^ N :=
    map_pow (rootDiagUnitHom Tag.F4 Ω) a N
  rw [ha, rootDiagUnit_one] at hm
  exact hm.symm

theorem f4_rank_le_two_component_shape_odd_of_coord
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {N : ℕ} (hN : 0 < N) (hNodd : N % 2 = 1) (hNΩ : (N : Ω) ≠ 0)
    {a : Fin Tag.F4.rank → Ωˣ}
    (haN : ∀ i, a i ^ N = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : compRank (componentRoots (rootCharHom a) i) ≤ 2) :
    ∃ v : WeylGroup Tag.F4,
      (∃ j : Fin Tag.F4.rank, componentRoots (rootCharHom a) i =
          (fun α => v • α) ''
            ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LongSupport ∨
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4ShortSupport ∨
      componentRoots (rootCharHom a) i = (fun α => v • α) '' b2LeviRoots :=
  f4_rank_le_two_component_shape_odd hN hNodd hNΩ
    (rootDiagUnit_pow_eq_one_of_coord haN) i h2

end CFSG.HardMathSupport.Timmesfeld.CrossChar
end

end
