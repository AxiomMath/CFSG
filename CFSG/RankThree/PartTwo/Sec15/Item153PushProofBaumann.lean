module

import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

namespace Push153

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem nontrivial_of_type315
    (htype : (∃ n : ℕ, 1 ≤ n ∧ Even n ∧ Nonempty (oResidual 2 (X ⧸ CFSG.pCore 2 X) ≃*
          projSL 2 (GaloisField 2 n))) ∨
      Sec4.IsTripleCover (oResidual 2 (X ⧸ CFSG.pCore 2 X)) (alternatingGroup (Fin 6)) ∨
      Nonempty (oResidual 2 (X ⧸ CFSG.pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    Nontrivial X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  have hQ : Subsingleton (X ⧸ CFSG.pCore 2 X) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  have hR : Subsingleton ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) := inferInstance
  rcases htype with ⟨n, hn, -, ⟨e⟩⟩ | ⟨hc, -⟩ | ⟨e⟩
  · obtain ⟨ι⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := GaloisField 2 n)
      (GaloisField.card 2 n (by omega))
    have := KFacts.nontrivial_sl2 (GaloisField 2 n)
    have hP : Nontrivial ↥(projSL 2 (GaloisField 2 n)) := ι.injective.nontrivial
    have := e.symm.injective.subsingleton
    exact not_nontrivial _ hP
  · have h1 : Nat.card (Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X))) = 1 :=
      Nat.card_unique
    omega
  · obtain ⟨e⟩ := e
    have := e.symm.injective.subsingleton
    exact not_nontrivial (alternatingGroup (Fin 7)) inferInstance

end Push153

end CFSG.RankThree.PartTwo.Sec15
