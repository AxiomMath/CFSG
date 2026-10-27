module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResKacNodes
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart28

@[expose] public section

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacNodes CFSG.SeitzReduction.F4Pilot

open scoped MatrixGroups Matrix

theorem f4_low_rank_cases : ∀ c ∈ f4Conn, c.length ≤ 2 →
    c = [0] ∨ c = [1] ∨ c = [2] ∨ c = [3] ∨ c = [4] ∨
      c = [0, 1] ∨ c = [1, 2] ∨ c = [2, 3] ∨ c = [3, 4] := by
  decide +kernel

theorem frameRoots_f4chainLong :
    frameRoots (CFSG.RankThree.E6.chainRoot f4chainLong) =
      parabolicRoots Tag.F4 f4LongSupport := by
  ext α
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact f4chainLong_mem_parabolicRoots hij
  · intro hα
    obtain ⟨i, j, hij, h⟩ := exists_f4chainLong_of_mem hα
    exact ⟨i, j, hij, h.symm⟩

theorem frameRoots_f4Sigma01 :
    frameRoots f4Sigma01 =
      (fun α => (coxeterSystem Tag.F4).wordProd f4WordLong • α) ''
        parabolicRoots Tag.F4 f4LongSupport := by
  have hword : ∀ v : Fin Tag.F4.rank → ℤ,
      wordMat Tag.F4 f4WordLong *ᵥ v =
        (coxeterSystem Tag.F4).wordProd f4WordLong • v := by
    intro v
    rw [CFSG.Monster.B.Geometry.wordProd_smul, wordMat_mulVec_eq_foldr]
    rfl
  have hsig : f4Sigma01 =
      fun a b => (coxeterSystem Tag.F4).wordProd f4WordLong •
        CFSG.RankThree.E6.chainRoot f4chainLong a b := by
    funext a b
    rw [f4Sigma01]
    exact hword _
  rw [hsig, ← frameRoots_f4chainLong]
  ext α
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨CFSG.RankThree.E6.chainRoot f4chainLong i j, ⟨i, j, hij, rfl⟩, rfl⟩
  · rintro ⟨β, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨i, j, hij, rfl⟩

theorem mem_nodesTU (j : Fin Tag.F4.rank) : j ∈ nodesTU ↔ j = 1 ∨ j = 2 := by
  unfold nodesTU
  revert j
  decide

private theorem image_image_smul {S : Set (Fin Tag.F4.rank → ℤ)}
    {v w : WeylGroup Tag.F4} :
    (fun α => v • α) '' ((fun α => w • α) '' S) =
      (fun α => (v * w) • α) '' S := by
  rw [Set.image_image]
  congr 1
  funext α
  exact (mul_smul v w α).symm

private theorem singleton_shape
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

theorem f4_rank_le_two_component_shape
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {p : ℕ} (hp : p.Prime) (hpΩ : (p : Ω) ≠ 0)
    {a : Fin Tag.F4.rank → Ωˣ}
    (hap : rootDiagUnit Tag.F4 a ^ p = 1)
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
  obtain ⟨v, μ, hμ, hall⟩ := exists_kacT_of_pos hp.pos hpΩ facts_F4 hap
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := kacF4.exists_comp_eq_of_check f4_tree f4_adj (adm := fun _ => true)
    f4_check rfl hx
  set C : Finset (Option (Fin Tag.F4.rank)) := (c.map (idxNode (r := Tag.F4.rank))).toFinset
    with hCdef
  have hCset : kacF4.comp p μ x = (C : Set (Option (Fin Tag.F4.rank))) := by
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
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacF4 hp.pos μ x
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
    obtain ⟨w, j, hw⟩ := singleton_shape none
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul]⟩⟩
  ·
    have hC : C = ({some 0} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape (some 0)
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul]⟩⟩
  ·
    have hC : C = ({some 1} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape (some 1)
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul]⟩⟩
  ·
    have hC : C = ({some 2} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape (some 2)
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul]⟩⟩
  ·
    have hC : C = ({some 3} : Finset (Option (Fin Tag.F4.rank))) := by rw [hCdef]; decide +kernel
    obtain ⟨w, j, hw⟩ := singleton_shape (some 3)
    have hroots : kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) := by
      simpa [hC] using hw
    exact ⟨v * w, Or.inl ⟨j, by rw [hi', hroots, image_image_smul]⟩⟩
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
      Or.inr (Or.inl (by rw [hi', hroots, image_image_smul]))⟩
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

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end

end
