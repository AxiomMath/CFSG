module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.JointShapes
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.StandardType.TableCRes
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.LieCore Matrix
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacNodes CFSG.SeitzReduction.F4Pilot
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.F4ExplicitPos.JointIsolator
open scoped MatrixGroups Matrix
open Classical
variable {Ω : Type} [Field Ω]

theorem f4_joint_six_shape_generic
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {p : ℕ} (hp : 0 < p) (hpodd : p % 2 = 1)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    (a d : Fin Tag.F4.rank → Ωˣ)
    (hinter : kernelRoots χ = kernelRoots (rootCharHom a) ∩ kernelRoots (rootCharHom d))
    (ha : ∀ i, a i ^ p = 1) (hd : ∀ i, d i ^ p = 1)
    (ha1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent χ) :
    ∃ w : WeylGroup Tag.F4,
      (∃ j, componentRoots χ i =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LongSupport ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4ShortSupport ∨
      componentRoots χ i = (fun α => w • α) '' b2LeviRoots ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviB3 ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
  classical
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
  have hsub : kernelRoots χ ⊆ kernelRoots (rootCharHom a) := by
    intro x hx
    rw [hinter] at hx
    exact hx.1
  have hγa : γ ∈ kernelRoots (rootCharHom a) := hsub hγ
  let j : KernelComponent (rootCharHom a) := (⟦⟨γ, hγa⟩⟧ : KernelComponent (rootCharHom a))
  have hγj : γ ∈ componentRoots (rootCharHom a) j := ⟨hγa, rfl⟩
  have hpΩ : (p : Ω) ≠ 0 := natCast_ne_zero_of_odd hpodd
  by_cases h2 : compRank (componentRoots (rootCharHom a) j) ≤ 2
  · obtain ⟨v, hshape⟩ :=
      f4_rank_le_two_component_shape_odd_of_coord hp hpodd hpΩ ha j h2
    rcases hshape with hA1 | hlong | hshort | hb2
    ·
      obtain ⟨j', hj'⟩ := hA1
      refine ⟨v, Or.inl ⟨j', ?_⟩⟩
      have hsubset : componentRoots χ (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) ⊆
          (fun α => v • α) ''
            ({Pi.single j' 1, -Pi.single j' 1} : Set (Fin Tag.F4.rank → ℤ)) :=
        hj' ▸ componentRoots_subset_of_kernel_subset hsub ⟨hγ, rfl⟩ hγj
      exact eq_pair_of_subset_wely_pair hsubset ⟨γ, hγ, rfl⟩
        (fun α hα => (isRootComponent_componentRoots (χ := χ) _).neg_mem α hα)
    · exact proper_levi_case hp hpodd χ a d hinter hd v f4LongSupport
        ⟨f4Index 3, by rw [mem_f4LongSupport]; decide⟩ hlong hγ hγj rfl
    · exact proper_levi_case hp hpodd χ a d hinter hd v f4ShortSupport
        ⟨f4Index 0, by rw [mem_f4ShortSupport]; decide⟩ hshort hγ hγj rfl
    · exact proper_levi_case hp hpodd χ a d hinter hd v nodesTU
        ⟨f4Index 0, by rw [mem_nodesTU]; decide⟩ hb2 hγ hγj rfl
  · have h3 : 3 ≤ compRank (componentRoots (rootCharHom a) j) := by omega
    obtain ⟨v, J, hJ, hH, -, -⟩ :=
      f4_rank_ge_three_component_is_levi_odd_of_coord hp hpodd hpΩ ha ha1 j h3
    rcases hJ with hJ | hJ
    · subst hJ
      exact proper_levi_case hp hpodd χ a d hinter hd v f4LeviB3
        ⟨f4Index 3, by rw [mem_f4LeviB3_narrow]; decide⟩ hH hγ hγj rfl
    · subst hJ
      exact proper_levi_case hp hpodd χ a d hinter hd v f4LeviC3
        ⟨f4Index 0, by rw [mem_f4LeviC3_narrow]; decide⟩ hH hγ hγj rfl

theorem f4_joint_component_six_shape
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {p : ℕ} (hp : 0 < p) (hpodd : p % 2 = 1)
    (a d : Fin Tag.F4.rank → Ωˣ)
    (ha : ∀ j, a j ^ p = 1) (hd : ∀ j, d j ^ p = 1)
    (hne : rootDiagUnit Tag.F4 a ≠ 1 ∨ rootDiagUnit Tag.F4 d ≠ 1)
    (i : KernelComponent (jointChar a d)) :
    ∃ w : WeylGroup Tag.F4,
      (∃ j, componentRoots (jointChar a d) i =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
      componentRoots (jointChar a d) i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LongSupport ∨
      componentRoots (jointChar a d) i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4ShortSupport ∨
      componentRoots (jointChar a d) i = (fun α => w • α) '' b2LeviRoots ∨
      componentRoots (jointChar a d) i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviB3 ∨
      componentRoots (jointChar a d) i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
  have hinter : kernelRoots (jointChar a d) =
      kernelRoots (rootCharHom a) ∩ kernelRoots (rootCharHom d) := kernelRoots_jointChar a d
  rcases hne with ha1 | hd1
  · exact f4_joint_six_shape_generic hp hpodd (jointChar a d) a d hinter ha hd ha1 i
  · have hinter' : kernelRoots (jointChar a d) =
        kernelRoots (rootCharHom d) ∩ kernelRoots (rootCharHom a) := by
      rw [hinter, Set.inter_comm]
    exact f4_joint_six_shape_generic hp hpodd (jointChar a d) d a hinter' hd ha hd1 i

end CFSG.StandardType.F4ExplicitPos.JointShapes

end

end
