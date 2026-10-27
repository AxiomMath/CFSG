module

public import CFSG.GH74.KGroups.L3EpsBlockLin
import CFSG.GH74.KGroups.L3EpsBlockAut
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped MatrixGroups

abbrev L33P : Type := projectiveSL 3 (ZMod 3)

@[expose] noncomputable def l33Blk : GL (Fin 2) (ZMod 3) →* GL (Fin 3) (ZMod 3) :=
  Units.map { toFun := bM, map_one' := bM_one, map_mul' := bM_mul }

@[expose] noncomputable def l33Kap : GL (Fin 2) (ZMod 3) →* MulAut L33P :=
  (conjAut 3 (ZMod 3)).comp l33Blk

private theorem a1413L33Blk_bM_injective :
    Function.Injective
      (bM : Matrix (Fin 2) (Fin 2) (ZMod 3) → Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
  intro X Y h
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | simpa [bM] using congrFun (congrFun h 0) 0
      | simpa [bM] using congrFun (congrFun h 0) 1
      | simpa [bM] using congrFun (congrFun h 1) 0
      | simpa [bM] using congrFun (congrFun h 1) 1

theorem l33Kap_injective : Function.Injective l33Kap := by
  rw [injective_iff_map_eq_one]
  intro N hN
  have hN' : conjAut 3 (ZMod 3) (l33Blk N) * fieldAut 3 (ZMod 3) 1 = 1 := by
    rw [map_one, mul_one]
    exact hN
  obtain ⟨-, c, hc⟩ :=
    eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (by norm_num) (l33Blk N) 1 hN'
  have hc22 : c = 1 := by
    apply Units.ext
    have h := congrArg
      (fun A : GL (Fin 3) (ZMod 3) => (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 2) hc
    simpa [l33Blk, Matrix.GeneralLinearGroup.coe_scalar, bM] using h
  have hN1 : l33Blk N = 1 := by
    calc l33Blk N = GeneralLinearGroup.scalar (Fin 3) c := hc.symm
      _ = GeneralLinearGroup.scalar (Fin 3) (1 : (ZMod 3)ˣ) := by rw [hc22]
      _ = 1 := map_one _
  have hmat : (N : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 := by
    apply a1413L33Blk_bM_injective
    have h := congrArg
      (fun A : GL (Fin 3) (ZMod 3) => (A : Matrix (Fin 3) (Fin 3) (ZMod 3))) hN1
    simpa [l33Blk, bM_one] using h
  exact Units.ext hmat

theorem l33_conjAut_mem_inner (A : GL (Fin 3) (ZMod 3)) :
    conjAut 3 (ZMod 3) A ∈ inner L33P := by
  have hunit : ∀ u : (ZMod 3)ˣ, u = 1 ∨ u = -1 := by decide
  rcases hunit (GeneralLinearGroup.det A) with hdet | hdet
  · have hA1 : (A : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := by
      have := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hdet
      simpa using this
    let g : SL(3, ZMod 3) := ⟨(A : Matrix (Fin 3) (Fin 3) (ZMod 3)), hA1⟩
    refine ⟨proj 3 (ZMod 3) g, ?_⟩
    rw [← CFSG.GH74.KGroups.L3Eps.conjAut_toGL g]
    exact congrArg (conjAut 3 (ZMod 3)) (Units.ext rfl)
  · let A' : GL (Fin 3) (ZMod 3) := GeneralLinearGroup.scalar (Fin 3) (-1) * A
    have hdet' : GeneralLinearGroup.det A' = 1 := by
      dsimp [A']
      rw [map_mul, GeneralLinearGroup.det_scalar, hdet]
      decide
    have hA1 : (A' : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := by
      have := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hdet'
      simpa using this
    have hinner : conjAut 3 (ZMod 3) A' ∈ inner L33P := by
      let g : SL(3, ZMod 3) := ⟨(A' : Matrix (Fin 3) (Fin 3) (ZMod 3)), hA1⟩
      refine ⟨proj 3 (ZMod 3) g, ?_⟩
      rw [← CFSG.GH74.KGroups.L3Eps.conjAut_toGL g]
      exact congrArg (conjAut 3 (ZMod 3)) (Units.ext rfl)
    convert hinner using 1
    dsimp [A']
    rw [map_mul, conjAut_scalar, one_mul]

theorem l33Kap_mem_inner (N : GL (Fin 2) (ZMod 3)) : l33Kap N ∈ inner L33P :=
  l33_conjAut_mem_inner _

theorem l33Kap_neg_one : l33Kap (-1) = MulAut.conj (tInv : L33P) := by
  have h : l33Blk (-1) = Matrix.SpecialLinearGroup.toGL (dNeg : SL(3, ZMod 3)) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [l33Blk, bM, coe_dNeg, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  change conjAut 3 (ZMod 3) (l33Blk (-1)) = MulAut.conj (tInv : L33P)
  rw [h, CFSG.GH74.KGroups.L3Eps.conjAut_toGL]
  rfl

theorem l33Kap_dual (N : GL (Fin 2) (ZMod 3)) :
    dualAut 3 (ZMod 3) * l33Kap N * dualAut 3 (ZMod 3) =
      l33Kap (GeneralLinearGroup.inverseTranspose N) := by
  have hkey : GeneralLinearGroup.inverseTranspose (l33Blk N) =
      l33Blk (GeneralLinearGroup.inverseTranspose N) := by
    apply Units.ext
    simp [l33Blk, GeneralLinearGroup.coe_inverseTranspose, bM_transpose]
  have htrans := (standard_automorphism_transport (K := ZMod 3) (n := 3)).2.2.2.2.1
  show dualAut 3 (ZMod 3) * conjAut 3 (ZMod 3) (l33Blk N) * dualAut 3 (ZMod 3) =
    conjAut 3 (ZMod 3) (l33Blk (GeneralLinearGroup.inverseTranspose N))
  rw [htrans (l33Blk N), hkey]

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
