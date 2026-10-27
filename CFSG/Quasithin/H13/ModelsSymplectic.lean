module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

noncomputable def statedSpThreeTwoEquivSymplecticGroup :
    StatedSp 3 (ZMod 2) ≃* Matrix.symplecticGroup (Fin 3) (ZMod 2) :=
  (MulEquiv.subgroupCongr statedSp_eq_GLSymplectic).trans
    (TauCeti.GLSymplectic.mulEquivSymplecticGroup (Fin 3) (ZMod 2))

theorem nonempty_mulEquiv_symplecticGroup_of_lieModel {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSp 3 2 1) :
    Nonempty (X ≃* Matrix.symplecticGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSp_of_lieModel h
  exact ⟨e.trans statedSpThreeTwoEquivSymplecticGroup⟩

noncomputable def statedProjStatedSpThreeTwoEquiv :
    StatedProj (StatedSp 3 (ZMod 2)) ≃* StatedSp 3 (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq
    (statedScalars_subgroupOf_eq_bot (by rw [Nat.card_zmod]) 3)).trans QuotientGroup.quotientBot

theorem lieModel_of_mulEquiv_symplecticGroup {X : Type} [Group X]
    (e : X ≃* Matrix.symplecticGroup (Fin 3) (ZMod 2)) :
    CFSG.Blueprint.LieModel X .PSp 3 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(e.trans statedSpThreeTwoEquivSymplecticGroup.symm).trans
      statedProjStatedSpThreeTwoEquiv.symm⟩⟩

theorem lieModel_symplecticGroup :
    CFSG.Blueprint.LieModel (Matrix.symplecticGroup (Fin 3) (ZMod 2)) .PSp 3 2 1 :=
  lieModel_of_mulEquiv_symplecticGroup (MulEquiv.refl _)

theorem card_symplecticGroup_three_two :
    Nat.card (Matrix.symplecticGroup (Fin 3) (ZMod 2)) = 1451520 := by
  rw [← Nat.card_congr statedSpThreeTwoEquivSymplecticGroup.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
  decide

end CFSG.Quasithin.H13
