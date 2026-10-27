module

public import CFSG.LocalAnalysis.ZStar.CharacterKernel
public import CFSG.LocalAnalysis.ZStar.StepVI
public import CFSG.LocalAnalysis.ZStar.TwoAdicStepVII

public section

namespace CFSG

namespace ZStar.TwoAdicCharacterTerminal

open ZStar.AbstractStepV
open ZStar.CentralizerInduction
open ZStar.CharacterKernel
open ZStar.PadicBlockField
open ZStar.StepVI
open ZStar.TransferReduction
open ZStar.TwoAdicStepVII
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnBlock
open ZStar.WedderburnCharacters

noncomputable section

universe u

variable {X : Type u} [Group X] [Fintype X]

private theorem eq_trivialIndex_of_group_component_eq_one
    (D : Decomposition X) (i : Fin D.blockCount)
    (hgroup : ∀ g : X, D.equiv (MonoidAlgebra.single g 1) i = 1) :
    i = trivialIndex D := by
  classical
  by_contra hne
  let p : Fin (D.blockSize i) :=
    ⟨0, Nat.pos_of_ne_zero (D.blockSize_neZero i).out⟩
  let q : Fin (D.blockSize (trivialIndex D)) :=
    ⟨0, Nat.pos_of_ne_zero (D.blockSize_neZero (trivialIndex D)).out⟩
  let y : BlockProduct TwoAdicComplex D.blockSize := Pi.single i 1
  let x : MonoidAlgebra TwoAdicComplex X := D.equiv.symm y
  have hi := congrArg
    (fun M : Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i))
      TwoAdicComplex ↦ M p p)
    (component_eq_augmentation_smul_one D i hgroup x)
  have htriv := congrArg
    (fun M : Matrix (Fin (D.blockSize (trivialIndex D)))
      (Fin (D.blockSize (trivialIndex D))) TwoAdicComplex ↦ M q q)
    (component_eq_augmentation_smul_one D (trivialIndex D)
      (trivialIndex_group_component D) x)
  have hi' : (1 : TwoAdicComplex) = augmentationTwoAdic x := by
    simpa [x, y, p] using hi
  have htriv' : (0 : TwoAdicComplex) = augmentationTwoAdic x := by
    simpa [x, y, q, hne] using htriv
  exact one_ne_zero (hi'.trans htriv'.symm)

private theorem eq_trivialIndex_of_componentCharacter_eq_degree
    (D : Decomposition X) (i : Fin D.blockCount) (t : X)
    (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup X, H.Normal → t ∈ H → H = ⊤)
    (hchar : componentCharacter D.equiv i t =
      (D.blockSize i : TwoAdicComplex)) :
    i = trivialIndex D := by
  have hchar' :
      (componentRepresentation D i).character t =
        (D.blockSize i : TwoAdicComplex) := by
    rw [componentCharacter_eq_matrixTrace]
    exact hchar
  have htcomponent :
      D.equiv (MonoidAlgebra.single t 1) i = 1 :=
    component_eq_one_of_character_eq_degree D i t ht2 hchar'
  let ρ := componentRepresentation D i
  have htker : t ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    change componentRepresentation D i t = 1
    rw [componentRepresentation_apply, htcomponent, map_one]
  have hkertop : ρ.ker = ⊤ := hmin ρ.ker inferInstance htker
  apply eq_trivialIndex_of_group_component_eq_one D i
  intro g
  have hgker : g ∈ ρ.ker := by
    rw [hkertop]
    trivial
  have hρg : ρ g = 1 := MonoidHom.mem_ker.mp hgker
  apply Matrix.toLinAlgEquiv'.injective
  simpa only [map_one] using
    (componentRepresentation_apply D i g).symm.trans hρg

theorem zStarConclusion_of_stable_selected_components
    {t sigma : X}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup X, H.Normal → t ∈ H → H = ⊤)
    (ih :
      ∀ {Y : Type u} [Group Y] [Fintype Y] {y : Y},
        Nat.card Y < Nat.card X → Isolated y → y * y = 1 →
          ZStarConclusion Y y)
    (hsigma1 : sigma ≠ 1) (hsigma2 : sigma * sigma = 1)
    (htsigma : Commute t sigma)
    (htsigma_not_conj : ¬ IsConj t sigma)
    (D : Decomposition X)
    (hstable :
      ∀ i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := X)),
        CentralizerOddCoreStable (componentCharacter D.equiv i)) :
    ZStarConclusion X t := by
  classical
  by_contra hZ
  apply stepVII_contradiction D t sigma ht2 hsigma2 hsigma1
    (fun h ↦ htsigma_not_conj h.symm)
  intro i hi hine
  by_cases hcharsigma : componentCharacter D.equiv i sigma = 0
  · exact Or.inl hcharsigma
  · right
    have hchart : componentCharacter D.equiv i t ≠
        (D.blockSize i : TwoAdicComplex) := by
      intro hdegree
      exact hine
        (eq_trivialIndex_of_componentCharacter_eq_degree
          D i t ht2 hmin hdegree)
    rcases component_character_eq_neg_degree_or_zStar
        ht ht2 hmin ih hsigma1 hsigma2 htsigma htsigma_not_conj
        D i (hstable i hi) hcharsigma hchart with hZ' | hneg
    · exact (hZ hZ').elim
    · exact hneg

end

end ZStar.TwoAdicCharacterTerminal

end CFSG
