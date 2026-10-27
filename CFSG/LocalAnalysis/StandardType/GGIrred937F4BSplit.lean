module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Base
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BDescent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4Block

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private def f4ThreeA2A2RepRoots : List (List ℤ) :=
  [[1, 0, 0, 0], [-1, 0, 0, 0], [1, 3, 4, 2], [-1, -3, -4, -2], [2, 3, 4, 2], [-2, -3, -4, -2],
   [0, 0, 1, 0], [0, 0, -1, 0], [0, 0, 0, 1], [0, 0, 0, -1], [0, 0, 1, 1], [0, 0, -1, -1]]

open CFSG.HardMathSupport.Timmesfeld.Steinberg in
theorem f4_a2a2_rep_split :
    IsA2Pair (f4vec [1, 0, 0, 0]) (f4vec [1, 3, 4, 2]) ∧
    IsA2Pair (f4vec [0, 0, 1, 0]) (f4vec [0, 0, 0, 1]) ∧
    PairsStrOrth (f4vec [1, 0, 0, 0], f4vec [1, 3, 4, 2]) (f4vec [0, 0, 1, 0], f4vec [0, 0, 0, 1]) ∧
    kernelRoots (triChar (vec3 (τ:= Tag.F4) [0, 1, 0, 0])) =
      a2Roots (f4vec [1, 0, 0, 0]) (f4vec [1, 3, 4, 2]) ∪
        a2Roots (f4vec [0, 0, 1, 0]) (f4vec [0, 0, 0, 1]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [isRoot_iff_mem_artifactRoots]; decide +kernel
    · rw [isRoot_iff_mem_artifactRoots]; decide +kernel
    · rw [isRoot_iff_mem_artifactRoots]; decide +kernel
    · decide +kernel
    · decide +kernel
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [isRoot_iff_mem_artifactRoots]; decide +kernel
    · rw [isRoot_iff_mem_artifactRoots]; decide +kernel
    · rw [isRoot_iff_mem_artifactRoots]; decide +kernel
    · decide +kernel
    · decide +kernel
  · intro γ hγ δ hδ
    simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ hδ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hδ with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by decide +kernel, ?_, ?_⟩ <;>
      rw [isRoot_iff_mem_artifactRoots] <;> decide +kernel
  · have H : ∀ l ∈ Tag.F4.artifactRoots,
        triPairing (vec3 (τ := Tag.F4) [0, 1, 0, 0]) (f4vec l) = 0 → l ∈ f4ThreeA2A2RepRoots := by
      decide +kernel
    have hroots : ∀ l ∈ f4ThreeA2A2RepRoots, l ∈ Tag.F4.artifactRoots := by decide +kernel
    have htri : ∀ l ∈ f4ThreeA2A2RepRoots, triPairing (vec3 (τ := Tag.F4) [0, 1, 0, 0]) (f4vec l) = 0 := by
      decide +kernel
    have key : ∀ l ∈ f4ThreeA2A2RepRoots, f4vec l ∈ a2Roots (f4vec [1, 0, 0, 0]) (f4vec [1, 3, 4, 2]) ∪
        a2Roots (f4vec [0, 0, 1, 0]) (f4vec [0, 0, 0, 1]) := by
      intro l hl
      simp only [f4ThreeA2A2RepRoots, List.mem_cons, List.not_mem_nil, or_false] at hl
      simp only [Set.mem_union, a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide +kernel
    have hall : ∀ γ : Fin Tag.F4.rank → ℤ, γ ∈ a2Roots (f4vec [1, 0, 0, 0]) (f4vec [1, 3, 4, 2]) ∪
        a2Roots (f4vec [0, 0, 1, 0]) (f4vec [0, 0, 0, 1]) → List.ofFn γ ∈ f4ThreeA2A2RepRoots := by
      intro γ hγ
      simp only [Set.mem_union, a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
      rcases hγ with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        decide +kernel
    ext γ
    rw [mem_kernelRoots_triChar]
    have hγ : γ = f4vec (List.ofFn γ) := (f4vec_ofFn γ).symm
    constructor
    · rintro ⟨hr, hk⟩
      have hr' := isRoot_iff_mem_artifactRoots.1 hr
      have hk' : triPairing (vec3 (τ := Tag.F4) [0, 1, 0, 0]) (f4vec (List.ofFn γ)) = 0 := by
        rwa [← hγ]
      have hmem := H _ hr' hk'
      rw [hγ]
      exact key _ hmem
    · intro h
      have hmem : List.ofFn γ ∈ f4ThreeA2A2RepRoots := hall γ h
      refine ⟨isRoot_iff_mem_artifactRoots.2 (hroots _ hmem), ?_⟩
      have := htri _ hmem
      rwa [← hγ] at this

theorem a2Pairs_smul {τ : Tag}
    (t : WeylGroup τ) {α β α' β' : Fin τ.rank → ℤ} :
    (IsA2Pair α β → IsA2Pair (t • α) (t • β)) ∧
    (PairsStrOrth (α, β) (α', β') → PairsStrOrth (t • α, t • β) (t • α', t • β')) ∧
    ((fun γ => t • γ) '' a2Roots α β = a2Roots (t • α) (t • β)) := by
  have hroot : ∀ x : Fin τ.rank → ℤ, IsRoot τ (t • x) ↔ IsRoot τ x := fun x =>
    ⟨fun h => by simpa using IsRoot.smul h t⁻¹, fun h => IsRoot.smul h t⟩
  have himg : (fun γ => t • γ) '' a2Roots α β = a2Roots (t • α) (t • β) := by
    ext x
    simp only [Set.mem_image, a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [smul_neg, smul_add]
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨α, Or.inl rfl, rfl⟩
      · exact ⟨-α, Or.inr (Or.inl rfl), by simp [smul_neg]⟩
      · exact ⟨β, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
      · exact ⟨-β, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by simp [smul_neg]⟩
      · exact ⟨α + β, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by simp [smul_add]⟩
      · exact ⟨-(α + β), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), by simp [smul_neg, smul_add]⟩
  refine ⟨fun h => ⟨IsRoot.smul h.isRoot_fst t, IsRoot.smul h.isRoot_snd t, ?_, ?_, ?_⟩, ?_, himg⟩
  · rw [← smul_add]; exact IsRoot.smul h.isRoot_add t
  · rw [iform_smul, iform_smul]; exact h.iform_snd
  · rw [iform_smul, iform_smul]; exact h.two_iform
  · intro h γ hγ δ hδ
    change γ ∈ a2Roots (t • α) (t • β) at hγ
    change δ ∈ a2Roots (t • α') (t • β') at hδ
    have himg' : (fun γ => t • γ) '' a2Roots α' β' = a2Roots (t • α') (t • β') := by
      ext x
      simp only [Set.mem_image, a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [smul_neg, smul_add]
      · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
        · exact ⟨α', Or.inl rfl, rfl⟩
        · exact ⟨-α', Or.inr (Or.inl rfl), by simp [smul_neg]⟩
        · exact ⟨β', Or.inr (Or.inr (Or.inl rfl)), rfl⟩
        · exact ⟨-β', Or.inr (Or.inr (Or.inr (Or.inl rfl))), by simp [smul_neg]⟩
        · exact ⟨α' + β', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by simp [smul_add]⟩
        · exact ⟨-(α' + β'), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), by simp [smul_neg, smul_add]⟩
    rw [← himg] at hγ
    rw [← himg'] at hδ
    obtain ⟨γ0, hγ0, rfl⟩ := hγ
    obtain ⟨δ0, hδ0, rfl⟩ := hδ
    obtain ⟨h1, h2, h3⟩ := h γ0 hγ0 δ0 hδ0
    refine ⟨by rw [iform_smul]; exact h1, ?_, ?_⟩
    · rw [← smul_add, hroot]; exact h2
    · rw [← smul_sub, hroot]; exact h3

open CFSG.HardMathSupport.Timmesfeld.Steinberg in
theorem f4_a2a2_kernel_split
    (L : Type) [Field L] (a : Fin Tag.F4.rank → Lˣ)
    (ha : ∀ i, a i ^ 3 = 1) (h12 : (rootCharKernel (τ := Tag.F4) a).ncard = 12) :
    ∃ α β α' β' : Fin Tag.F4.rank → ℤ, IsA2Pair α β ∧ IsA2Pair α' β' ∧
      PairsStrOrth (α, β) (α', β') ∧
      rootCharKernel (τ := Tag.F4) a = a2Roots α β ∪ a2Roots α' β' := by
  classical
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a ha)
  have hK : rootCharKernel (τ := Tag.F4) a = kernelRoots χ' := by
    rw [← kernelRoots_congr_ker hker]
    rfl
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 f4ThreeOrbit_check χ'
  have himg : kernelRoots χ' =
      (fun α => t • α) '' kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD ρ []))) := by
    ext α
    rw [kernelRoots_iff_of_isCharConj ht]
    constructor
    · intro h
      exact ⟨t⁻¹ • α, h, smul_inv_smul t α⟩
    · rintro ⟨β, hβ, rfl⟩
      rwa [inv_smul_smul]
  have hlen : f4ThreeReps.length = 4 := rfl
  rw [hlen] at hρ
  have hcard : (kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD ρ [])))).ncard = 12 := by
    rw [hK, himg, Set.ncard_image_of_injective _ (MulAction.injective t)] at h12
    exact h12
  interval_cases ρ
  · exfalso
    have := f4_kernelSizes_F4.1
    change (kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD 0 [])))).ncard = 48 at this
    omega
  · exfalso
    have := f4_kernelSizes_C3.1
    change (kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD 1 [])))).ncard = 18 at this
    omega
  · have hrep : f4ThreeReps.getD 2 [] = [0, 1, 0, 0] := rfl
    rw [hrep] at himg
    obtain ⟨hp1, hp2, ho, hk⟩ := f4_a2a2_rep_split
    obtain ⟨hs1, -, hi1⟩ := a2Pairs_smul t (α := f4vec [1, 0, 0, 0]) (β := f4vec [1, 3, 4, 2])
      (α' := f4vec [0, 0, 1, 0]) (β' := f4vec [0, 0, 0, 1])
    obtain ⟨hs2, hso, hi2⟩ := a2Pairs_smul t (α := f4vec [1, 0, 0, 0]) (β := f4vec [1, 3, 4, 2])
      (α' := f4vec [0, 0, 1, 0]) (β' := f4vec [0, 0, 0, 1])
    obtain ⟨hs3, -, hi3⟩ := a2Pairs_smul t (α := f4vec [0, 0, 1, 0]) (β := f4vec [0, 0, 0, 1])
      (α' := f4vec [0, 0, 1, 0]) (β' := f4vec [0, 0, 0, 1])
    refine ⟨t • f4vec [1, 0, 0, 0], t • f4vec [1, 3, 4, 2], t • f4vec [0, 0, 1, 0],
      t • f4vec [0, 0, 0, 1], hs1 hp1, hs3 hp2, hso ho, ?_⟩
    rw [hK, himg, hk, Set.image_union, hi2, hi3]
  · exfalso
    have := f4_kernelSizes_B3.1
    change (kernelRoots (triChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD 3 [])))).ncard = 18 at this
    omega

theorem f4_a2a2_group_split
    (L : Type) [Field L] (a : Fin Tag.F4.rank → Lˣ) (ha : ∀ i, a i ^ 3 = 1)
    {α β α' β' : Fin Tag.F4.rank → ℤ} (h₁ : IsA2Pair α β) (h₂ : IsA2Pair α' β')
    (horth : PairsStrOrth (α, β) (α', β'))
    (hker : rootCharKernel (τ := Tag.F4) a = a2Roots α β ∪ a2Roots α' β') :
    toralCentralizer Tag.F4 L a =
        torusGroup Tag.F4 L ⊔ (rootSpan Tag.F4 L (a2Roots α β) ⊔ rootSpan Tag.F4 L (a2Roots α' β')) ∧
      (∀ x ∈ rootSpan Tag.F4 L (a2Roots α β), ∀ y ∈ rootSpan Tag.F4 L (a2Roots α' β'),
        x * y = y * x) ∧
      (∀ m ∈ toralCentralizer Tag.F4 L a, ∀ y ∈ rootSpan Tag.F4 L (a2Roots α β),
        m * y * m⁻¹ ∈ rootSpan Tag.F4 L (a2Roots α β)) ∧
      (∀ m ∈ toralCentralizer Tag.F4 L a, ∀ y ∈ rootSpan Tag.F4 L (a2Roots α' β'),
        m * y * m⁻¹ ∈ rootSpan Tag.F4 L (a2Roots α' β')) := by
  have hM : toralCentralizer Tag.F4 L a =
      torusGroup Tag.F4 L ⊔ (rootSpan Tag.F4 L (a2Roots α β) ⊔ rootSpan Tag.F4 L (a2Roots α' β')) := by
    rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_F4_three L a ha,
      toralRootGroup, hker,
      CFSG.RankThree.PartOne.KE.rootSpan_union_eq]
  have hcomm : ∀ x ∈ rootSpan Tag.F4 L (a2Roots α β), ∀ y ∈ rootSpan Tag.F4 L (a2Roots α' β'),
      x * y = y * x :=
    commute_rootSpan_of_strOrth (a2Roots_isRoot h₁) (a2Roots_isRoot h₂) horth
  refine ⟨hM, hcomm, ?_, ?_⟩
  · intro m hm y hy
    have hle : toralCentralizer Tag.F4 L a ≤
        Subgroup.normalizer (rootSpan Tag.F4 L (a2Roots α β) : Set (ModGL Tag.F4 L)) := by
      rw [hM]
      refine sup_le (torusGroup_le_normalizer_rootSpan (a2Roots_isRoot h₁))
        (sup_le Subgroup.le_normalizer ?_)
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro y2 hy2
      exact Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x hx y2 hy2
    exact (Subgroup.mem_normalizer_iff.1 (hle hm) y).1 hy
  · intro m hm y hy
    have hle : toralCentralizer Tag.F4 L a ≤
        Subgroup.normalizer (rootSpan Tag.F4 L (a2Roots α' β') : Set (ModGL Tag.F4 L)) := by
      rw [hM]
      refine sup_le (torusGroup_le_normalizer_rootSpan (a2Roots_isRoot h₂))
        (sup_le ?_ Subgroup.le_normalizer)
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro y1 hy1
      exact Subgroup.mem_centralizer_iff.2 fun x hx => (hcomm y1 hy1 x hx).symm
    exact (Subgroup.mem_normalizer_iff.1 (hle hm) y).1 hy

end Irred937

end CFSG.StandardType

end
