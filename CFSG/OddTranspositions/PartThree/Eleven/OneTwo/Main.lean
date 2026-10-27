module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.MinusModel
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Kernel
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Index
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Wong
public import CFSG.OddTranspositions.PartThree.Eleven.FiveMinusModel

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section Main

theorem ElevenTwoHyp.centralizer_commutator {G : Type} [Group G] [Finite G] {D : Set G}
    {hC : HypothesisC D} (h : ElevenTwoHyp hC) :
    Subgroup.centralizer (commutator G : Set G) = ⊥ := by
  let C : Subgroup G := Subgroup.centralizer (commutator G : Set G)
  have hNbot : C ⊓ commutator G = ⊥ := by
    refine h.rad (C ⊓ commutator G) ?_ ?_
    · infer_instance
    · apply Group.isSolvable_of_comm
      intro a b
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp a.2).1 (b : G)
        (Subgroup.mem_inf.mp b.2).2).symm
  have hCsolv : Group.IsSolvable ↥C := by
    apply Group.isSolvable_of_comm
    intro a b
    apply Subtype.ext
    have hmemG := Subgroup.commutator_mem_commutator (Subgroup.mem_top (a : G))
      (Subgroup.mem_top (b : G))
    have hmemC := Subgroup.commutator_le_self C (Subgroup.commutator_mem_commutator a.2 b.2)
    have hmem1 := Subgroup.mem_bot.mp (hNbot ▸ Subgroup.mem_inf.mpr ⟨hmemC, hmemG⟩)
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem1
  exact h.rad C inferInstance hCsolv

theorem theorem11_2_holds (h91 : Theorem9_1) (hW : WongPSp4Five) : Theorem11_2 := by
  intro G _ _ D hC hrad hZ hmod
  obtain ⟨π, hmod⟩ := hmod
  have h : ElevenTwoHyp hC := ⟨hrad, hZ, o4MinusFacts_of_isFiveReflectionModel hmod⟩
  have hu : orderOf hC.d = 2 := hC.setup.oddT.1 hC.d hC.hd
  rw [hC.setup.eq_setOf_isConj hC.hd]
  exact isFiveReflectionModel_four_true_false_of_derived hC.d
    (h.statedClassicalModel_commutator h91 hW) (h.centralizer_commutator) hu
    (h.not_mem_commutator hC.d hC.hd) (by rw [h.card_centralizer_d]; norm_num)

end Main

end CFSG.OddTranspositions.PartThree
