module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem s16g_pairGL_injective {a b : ι} (hab : a ≠ b) :
    Function.Injective (pairGL (ι := ι) (k := K) hab) := by
  intro g g' h
  have h' := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) h
  simp only [coe_pairGL] at h'
  obtain ⟨g1, g2, g3, g4⟩ := pairMat_apply_pair hab (g : Matrix (Fin 2) (Fin 2) K)
  obtain ⟨g1', g2', g3', g4'⟩ := pairMat_apply_pair hab (g' : Matrix (Fin 2) (Fin 2) K)
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  revert i j
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← g1, ← g1', h']
  · rw [← g2, ← g2', h']
  · rw [← g3, ← g3', h']
  · rw [← g4, ← g4', h']

private theorem s16g_disjoint_pairs {a b c d : ι} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : Disjoint ({a, b} : Set ι) {c, d} := by
  rw [Set.disjoint_left]
  rintro x (rfl | rfl) (rfl | rfl) <;> contradiction

theorem s16g_pairGL_commute {a b c d : ι} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (g h : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (pairGL hab g) (pairGL hcd h) := by
  have h1 := (isSupp_pairMat (a := a) (b := b) (g : Matrix (Fin 2) (Fin 2) K)).commute
    (isSupp_pairMat (a := c) (b := d) (h : Matrix (Fin 2) (Fin 2) K))
    (s16g_disjoint_pairs hac had hbc hbd)
  exact Units.ext (by simpa [coe_pairGL] using h1.eq)

theorem s16g_pairGL_eq_pairGL_disjoint {a b c d : ι} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) {g h : Matrix.SpecialLinearGroup (Fin 2) K}
    (e : pairGL hab g = pairGL hcd h) : g = 1 := by
  have e' := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) e
  simp only [coe_pairGL] at e'
  obtain ⟨g1, g2, g3, g4⟩ := pairMat_apply_pair hab (g : Matrix (Fin 2) (Fin 2) K)
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  revert i j
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_one, ← g1, e', pairMat_apply_of_ne hac had]
    simp
  · rw [Matrix.SpecialLinearGroup.coe_one, ← g2, e', pairMat_apply_of_ne hac had]
    simp [hab]
  · rw [Matrix.SpecialLinearGroup.coe_one, ← g3, e', pairMat_apply_of_ne hbc hbd]
    simp [hab.symm]
  · rw [Matrix.SpecialLinearGroup.coe_one, ← g4, e', pairMat_apply_of_ne hbc hbd]
    simp

theorem s16g_pairGL_mulVec_single {a b c : ι} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((pairGL hab g : GL ι K) : Matrix ι ι K) *ᵥ (Pi.single c 1 : ι → K) = Pi.single c 1 := by
  rw [Matrix.mulVec_single_one, coe_pairGL]
  funext x
  rw [Matrix.col_apply, pairMat_apply_of_ne' hca hcb]
  simp [Matrix.one_apply, Pi.single_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
