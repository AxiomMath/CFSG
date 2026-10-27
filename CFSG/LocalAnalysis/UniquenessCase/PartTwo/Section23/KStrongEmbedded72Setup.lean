module

public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Sec1511
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.LocalAnalysis.UniquenessCase.UCK

theorem kf7_setup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hN : IsStronglyPEmbedded p N) :
    IsSimpleGroup ↥(genFittingFStar X) ∧
      (∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) ∧
      (genFittingFStar X).Normal ∧
      Subgroup.centralizer ((genFittingFStar X : Subgroup X) : Set X) = ⊥ ∧
      ∃ (P : Sylow p X) (T : Sylow p ↥(genFittingFStar X)),
        (P : Subgroup X) ≤ N ∧ (P : Subgroup X) ⊓ genFittingFStar X ≠ ⊥ ∧
        (T : Subgroup ↥(genFittingFStar X)) =
          ((P : Subgroup X) ⊓ genFittingFStar X).subgroupOf (genFittingFStar X) ∧
        Subgroup.normalizer (T : Set ↥(genFittingFStar X)) ≤ N.subgroupOf (genFittingFStar X) ∧
        N.subgroupOf (genFittingFStar X) ≠ ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set K : Subgroup X := genFittingFStar X with hKdef
  have hKeq : K = CFSG.generalizedFitting X :=
    CFSG.Adapters.genFittingFStar_eq_foundations (G := X)
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := spe_fstar (H := X) hp hO hN
  rw [← hKeq] at hKs hKnab hKn hKC
  haveI : IsSimpleGroup ↥K := hKs
  have hKne : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  refine ⟨hKs, hKnab, hKn, hKC, ?_⟩
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded (X := X) hO hKne hN
  refine ⟨P, T, hPN, hPK, hT, ?_, ?_⟩
  ·
    have h := normalizer_subgroupOf_le_of_isStronglyPEmbedded hN hPK
      (P.isPGroup'.to_inf_left) (inf_le_left.trans hPN) inf_le_right
    rwa [← hT] at h
  ·
    intro htop
    exact not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      ((Subgroup.subgroupOf_eq_top (H := N) (K := K)).1 htop)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
