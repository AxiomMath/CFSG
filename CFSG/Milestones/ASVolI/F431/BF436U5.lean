module

public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
import all CFSG.ClassicalGroups.UnitaryFlag.GramForm
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenBN.U5.Setting
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.RankThree.PartOne.U5K.Hyp

section F4Witness

@[expose] def burnsideF4m_u5pos : HypIndex 2 1 ≃ Fin 5 where
  toFun a := match a with
    | .inl i => ⟨i.val, by omega⟩
    | .inr (.inl _) => 2
    | .inr (.inr i) => ⟨4 - i.val, by omega⟩
  invFun j := ![.inl 0, .inl 1, .inr (.inl 0), .inr (.inr 1), .inr (.inr 0)] j
  left_inv := by decide
  right_inv := by decide

@[expose] def burnsideF4m_u5X (A : Matrix (Fin 5) (Fin 5) CFSG.Fischer.F4) :
    Matrix (HypIndex 2 1) (HypIndex 2 1) CFSG.Fischer.F4 :=
  A.submatrix burnsideF4m_u5pos burnsideF4m_u5pos

end F4Witness

section Transport

variable {K : Type} [Field K]

@[expose] noncomputable def burnsideF4m_eF4 (h : UnitaryFieldData 2 1 K) : CFSG.Fischer.F4 →+* K :=
  letI := h.finite
  letI : CharP K 2 := h.charP
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  ((CFSG.Fischer.F4.equivGaloisField).trans
    (GaloisField.algEquivGaloisField 2 2 (by rw [h.card])).toRingEquiv.symm).toRingHom

end Transport

end CFSG.ASVolI
