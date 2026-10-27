module

public import CFSG.LocalAnalysis.ZStar.TwoAdicCharacterTerminal
public import CFSG.LocalAnalysis.ZStar.InductiveTerminal
public import CFSG.LocalAnalysis.ZStar.TerminalIndexTwo

public section

namespace CFSG

namespace ZStar.TerminalAssembly

open ZStar.AbstractStepV
open ZStar.CentralizerInduction
open ZStar.InductiveTerminal
open ZStar.PadicBlockField
open ZStar
open ZStar.TransferReduction
open ZStar.TwoAdicCharacterTerminal
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnBlock
open ZStar.WedderburnCharacters

noncomputable section

universe u

variable {X : Type u} [Group X] [Fintype X]

theorem zStarConclusion_one : ZStarConclusion X (1 : X) := by
  refine ⟨⊥, inferInstance, ?_, ?_⟩
  · simp
  · intro g
    simp

private theorem zStarConclusion_of_distinct_sylow_involution
    {t sigma : X}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup X, H.Normal → t ∈ H → H = ⊤)
    (ih :
      ∀ {Y : Type u} [Group Y] [Fintype Y] {y : Y},
        Nat.card Y < Nat.card X → Isolated y → y * y = 1 →
          ZStarConclusion Y y)
    (P : Sylow 2 X) (htP : t ∈ P) (hsigmaP : sigma ∈ P)
    (hsigma1 : sigma ≠ 1) (hsigma2 : sigma * sigma = 1)
    (hsigma_ne : sigma ≠ t)
    (hstable :
      ∀ (D : Decomposition X) (i : Fin D.blockCount),
        i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := X)) →
          CentralizerOddCoreStable (componentCharacter D.equiv i)) :
    ZStarConclusion X t := by
  have htcenter := mem_center_sylow_two ht P htP
  have htsigma : Commute t sigma := by
    have hcomm := Subgroup.mem_center_iff.mp htcenter
      (⟨sigma, hsigmaP⟩ : P)
    exact (congrArg Subtype.val hcomm).symm
  have htsigma_not_conj : ¬ IsConj t sigma := by
    intro hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    apply hsigma_ne
    have hfix : g * t * g⁻¹ = t := by
      apply ht g
      rw [hg]
      exact htsigma.eq.symm
    exact hg.symm.trans hfix
  let D : Decomposition X := decomposition
  exact zStarConclusion_of_stable_selected_components
    ht ht2 hmin ih hsigma1 hsigma2 htsigma htsigma_not_conj D
      (fun i hi ↦ hstable D i hi)

private theorem terminal_zStar_of_stable_components_and_unique_involution
    {t : X}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup X, H.Normal → t ∈ H → H = ⊤)
    (hcomm : commutator X = ⊤ ∨ (commutator X).index = 2)
    (ih :
      ∀ {Y : Type u} [Group Y] [Fintype Y] {y : Y},
        Nat.card Y < Nat.card X → Isolated y → y * y = 1 →
          ZStarConclusion Y y)
    (hstable :
      ∀ (D : Decomposition X) (i : Fin D.blockCount),
        i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := X)) →
          CentralizerOddCoreStable (componentCharacter D.equiv i))
    (hunique :
      ∀ (P : Sylow 2 X), t ∈ P → UniqueInvolutionIn (P : Subgroup X) t →
        commutator X = ⊤ → ZStarConclusion X t) :
    ZStarConclusion X t := by
  by_cases ht1 : t = 1
  · subst t
    exact zStarConclusion_one
  have ht1' : t ≠ 1 := ht1
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    isPGroup_zpowers_two_of_sq_eq_one t ht2
  obtain ⟨P, hP⟩ := htp.exists_le_sylow
  have htP : t ∈ (P : Subgroup X) :=
    hP (Subgroup.mem_zpowers t)
  rcases uniqueInvolutionIn_or_exists_distinct (P : Subgroup X) t with
    hPunique | ⟨sigma, hsigmaP, hsigma1, hsigma2, hsigma_ne⟩
  · rcases hcomm with hperfect | hindex
    · exact hunique P htP hPunique hperfect
    · exact zStar_of_terminal_index_two_unique
        ht ht1' ht2 hmin hindex P htP hPunique
  · exact zStarConclusion_of_distinct_sylow_involution
      ht ht2 hmin ih P htP hsigmaP hsigma1 hsigma2 hsigma_ne hstable

theorem zStar_of_stable_components_and_unique_involution
    {G : Type u} [Group G] [Fintype G] {t : G}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hstable :
      ∀ {X : Type u} [Group X] [Fintype X]
        (D : Decomposition X) (i : Fin D.blockCount),
        i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := X)) →
          CentralizerOddCoreStable (componentCharacter D.equiv i))
    (hunique :
      ∀ {X : Type u} [Group X] [Fintype X] {x : X},
        Isolated x → x * x = 1 →
        (∀ H : Subgroup X, H.Normal → x ∈ H → H = ⊤) →
        ∀ (P : Sylow 2 X), x ∈ P →
          UniqueInvolutionIn (P : Subgroup X) x →
          commutator X = ⊤ → ZStarConclusion X x) :
    ZStarConclusion G t := by
  apply zStar_of_commutator_terminal_with_ih
    (ht := ht) (ht2 := ht2)
  intro X _ _ x hx hx2 hmin hcomm ih
  exact terminal_zStar_of_stable_components_and_unique_involution
    hx hx2 hmin hcomm ih
      (fun D i hi ↦ hstable D i hi)
      (fun P hxP hPunique hperfect ↦
        hunique hx hx2 hmin P hxP hPunique hperfect)

end

end ZStar.TerminalAssembly

end CFSG
