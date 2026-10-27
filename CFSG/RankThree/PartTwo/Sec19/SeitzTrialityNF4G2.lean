module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4G2Aux

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec19

section Model


variable {n : ℕ} {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem g2_pair_conj_AB (P : D4Par n X σ) (hK : ringChar X = 2)
    (hk4 : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ w : adjointGroup Tag.G2 (fixSubfield σ),
      (((KS11Lie4Proof.g2ShortSL2 (fixSubfield σ)).map (MulAut.conj w).toMonoidHom).map
          (KFacts.trialityG2Incl σ hK) ≤ A0sub σ) ∧
      (((KS11Lie4Proof.g2LongSL2 (fixSubfield σ)).map (MulAut.conj w).toMonoidHom).map
          (KFacts.trialityG2Incl σ hK) ≤ Bsub σ) := by
  refine ⟨(g2WeylRep (fixSubfield σ))⁻¹, ?_, ?_⟩
  · rw [Subgroup.map_map, Subgroup.map_le_iff_le_comap]
    intro g hg
    obtain ⟨x, hx⟩ := short_conj_mem (fixSubfield σ) g hg
    rw [Subgroup.mem_comap]
    show KFacts.trialityG2Incl σ hK (MulAut.conj (g2WeylRep (fixSubfield σ))⁻¹ g) ∈ A0sub σ
    rw [hx]
    exact g2RootSL2_short_le_A0 σ P hK x
  · rw [Subgroup.map_map, Subgroup.map_le_iff_le_comap]
    intro g hg
    obtain ⟨x, rfl⟩ := long_conj_mem (fixSubfield σ) g hg
    rw [Subgroup.mem_comap]
    exact g2RootSL2_long_conj_le_B σ P hK x

end Model

end CFSG.RankThree.PartTwo.Sec19
