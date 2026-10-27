module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
public import CFSG.LieType.Universal.SpinCenterMinus
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.LieType.Universal.Spin (quadMinus binaryForm)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def planeVec (p : Fin 2 → K) : ιM → K := Sum.elim 0 (Sum.elim 0 p)

@[simp] theorem planeVec_inl (p : Fin 2 → K) (i : Fin (2 - 1)) : planeVec p (Sum.inl i) = 0 :=
  rfl

@[simp] theorem planeVec_inr_inl (p : Fin 2 → K) (i : Fin (2 - 1)) :
    planeVec p (Sum.inr (Sum.inl i)) = 0 :=
  rfl

@[simp] theorem planeVec_inr_inr (p : Fin 2 → K) (i : Fin 2) :
    planeVec p (Sum.inr (Sum.inr i)) = p i :=
  rfl

theorem quadMinus_e1M (b c : K) : quadMinus 2 K b c (KTabC.e1M K) = 0 := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
  simp [KTabC.e1M]

theorem e1M_ne_zero : KTabC.e1M K ≠ 0 := by
  simp [KTabC.e1M]

theorem quadMinus_planeVec (b c : K) (p : Fin 2 → K) :
    quadMinus 2 K b c (planeVec p) = binaryForm K b c p := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply,
    CFSG.LieType.Universal.Spin.binaryForm_apply]
  simp [planeVec]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
