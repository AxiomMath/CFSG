module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1AutDefs
public import CFSG.Open.PGLModelDefs
public import CFSG.Open.StatedDefs
import CFSG.HardMathSupport.Solomon.Proving.L3Center
import CFSG.Models.PGL
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL3Core
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL3Inputs
import CFSG.HardMathSupport.Solomon.LocalBalance.Extremal
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Defs
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.Open (StatedClassicalModel)

theorem res1AutCent_of_stated_three {S : Type} [Group S] [Finite S] {p e : ℕ} (hp2 : p ≠ 2)
    (hS : StatedClassicalModel S .PSL 3 p e ∨ StatedClassicalModel S .PSU 3 p e) :
    Res1AutCent S := by
  refine res1AutCent_of_abelian_index_two ?_ (res1OddL3_odd_commutator_outer hS)
    (res1OddL3_abelian_index_le_two hp2 hS) (res1OddL3_card_elemAbelian_le_four hp2 hS)
  rcases hS with ⟨-, K, _, _, -, ⟨eK⟩⟩ | ⟨⟨-, -, -, h32⟩, K, _, _, hK, ⟨eK⟩⟩
  · exact CFSG.HardMathSupport.Solomon.Proving.center_eq_bot_of_sl_three K S eK
  · exact CFSG.HardMathSupport.Solomon.Proving.center_eq_bot_of_su_three_ne_two S K (p ^ e) hK
      (fun h => h32 (by rw [h])) eK

theorem res1AutCent_projSL_three_of_odd {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Res1AutCent ↥(CFSG.PGLModel.projSL 3 (GaloisField p f)) := by
  have hS : StatedClassicalModel ↥(CFSG.PGLModel.projSL 3 (GaloisField p f)) .PSL 3 p f :=
    CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL
      ⟨Fact.out, hf, by norm_num, by simp, by simp⟩ (MulEquiv.refl _)
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField p f)) :=
    Finite.of_surjective
      (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 3) (GaloisField p f) →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  exact res1AutCent_of_stated_three hp2 (Or.inl hS)

theorem res1AutCent_projSU_three_of_odd {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 1) : Res1AutCent ↥(CFSG.PGLModel.projSU 3 p f) := by
  have hS : StatedClassicalModel ↥(CFSG.PGLModel.projSU 3 p f) .PSU 3 p f := by
    refine CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      ⟨Fact.out, hf, le_rfl, ?_⟩ (MulEquiv.refl _)
    intro h
    have h2 := congrArg Prod.snd h
    simp only at h2
    omega
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField p (2 * f))) :=
    Finite.of_surjective
      (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 3) (GaloisField p (2 * f)) →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  exact res1AutCent_of_stated_three hp2 (Or.inr hS)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
