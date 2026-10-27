module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofCore
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Matrix

namespace Item211Lie3Proof

open Item211Lie2Proof

variable {p f : ℕ} {K : Type} [Field K]

theorem neg_one_mem_unitarySU_two (h : UnitaryFieldData p f K) :
    (-1 : GL (Fin 2) K) ∈ unitarySU p f K 2 :=
  CFSG.RankThree.PartTwo.Census.neg_one_mem_unitarySU h

@[expose] noncomputable def negOneSU (h : UnitaryFieldData p f K) : unitarySU p f K 2 :=
  ⟨-1, neg_one_mem_unitarySU_two h⟩

theorem coe_negOneSU (h : UnitaryFieldData p f K) :
    ((negOneSU h : unitarySU p f K 2) : GL (Fin 2) K) = -1 :=
  rfl

theorem exists_su2Equiv (h : UnitaryFieldData p f K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : SL(2, F) ≃* unitarySU p f K 2),
      Nat.card F = p ^ f ∧ e (-1) = negOneSU h := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 2
  refine ⟨CFSG.LieType.Steinberg.fixedSubfield K p f, inferInstance, inferInstance,
    (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
      ((CFSG.LieType.Universal.Unitary.conjEquiv P hP).trans
        (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 2))),
    CFSG.LieType.Steinberg.card_fixedSubfield hK, ?_⟩
  apply Subtype.ext
  change ((CFSG.LieType.Universal.Unitary.conjEquiv P hP
    (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ (-1)) : GL (Fin 2) K)) = -1
  rw [CFSG.LieType.Universal.Unitary.coe_conjEquiv]
  have h1 : ((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ (-1) : GL (Fin 2) K)) = -1 := by
    apply Units.ext
    rw [CFSG.LieType.Steinberg.hypEquiv_apply, CFSG.LieType.Steinberg.coe_hypHom]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.Steinberg.hypMat, Matrix.SpecialLinearGroup.coe_neg]
  rw [h1, mul_neg, mul_one, neg_mul, mul_inv_cancel]

theorem sl2Like_unitarySU_two (h : UnitaryFieldData p f K) (hq : 4 ≤ p ^ f) :
    SL2Like (unitarySU p f K 2) (negOneSU h) := by
  obtain ⟨F, _, _, e, hF, he⟩ := exists_su2Equiv h
  have := (sl2Like_specialLinear (F := F) (by rw [hF]; exact hq)).of_mulEquiv e
  rwa [he] at this

theorem blockMat_map (φ : K →+* K) (A : Matrix (Fin 2) (Fin 2) K) :
    (blockMat A).map φ = blockMat (A.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem blockMat_transpose (A : Matrix (Fin 2) (Fin 2) K) :
    (blockMat A)ᵀ = blockMat Aᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

@[expose] def blockGL : GL (Fin 2) K →* GL (Fin 3) K where
  toFun A := ⟨blockMat A, blockMat ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
    by rw [← blockMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockMat_one],
    by rw [← blockMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockMat_one]⟩
  map_one' := Units.ext blockMat_one
  map_mul' A B := Units.ext (blockMat_mul _ _)

theorem coe_blockGL (A : GL (Fin 2) K) :
    ((blockGL A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = blockMat A :=
  rfl

theorem coe_blockGL_neg_one :
    ((blockGL (-1 : GL (Fin 2) K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![-1, -1, 1] := by
  rw [coe_blockGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat]

theorem blockGL_mem (h : UnitaryFieldData p f K) {A : GL (Fin 2) K}
    (hA : A ∈ unitarySU p f K 2) : blockGL A ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h] at hA ⊢
  refine ⟨by rw [coe_blockGL, det_blockMat, hA.1], ?_⟩
  rw [coe_blockGL, blockMat_map, blockMat_transpose, ← blockMat_mul, hA.2, blockMat_one]

@[expose] def blockEmbU (h : UnitaryFieldData p f K) :
    unitarySU p f K 2 →* unitarySU p f K 3 where
  toFun A := ⟨blockGL A, blockGL_mem h A.2⟩
  map_one' := Subtype.ext (map_one blockGL)
  map_mul' _ _ := Subtype.ext (map_mul blockGL _ _)

theorem coe_blockEmbU (h : UnitaryFieldData p f K) (A : unitarySU p f K 2) :
    ((blockEmbU h A : unitarySU p f K 3) : GL (Fin 3) K) = blockGL A :=
  rfl

theorem exists_blockGL_eq (h : UnitaryFieldData p f K) {C : GL (Fin 3) K}
    (hC : C ∈ unitarySU p f K 3) (hb : Item211Lie2Proof.IsBlock (C : Matrix (Fin 3) (Fin 3) K))
    (h22 : (C : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) :
    ∃ A : unitarySU p f K 2, blockGL (A : GL (Fin 2) K) = C := by
  set N : Matrix (Fin 3) (Fin 3) K := (C : Matrix (Fin 3) (Fin 3) K) with hN
  obtain ⟨hdet, hiso⟩ := (mem_unitarySU_iff h).mp hC
  set B : Matrix (Fin 2) (Fin 2) K := !![N 0 0, N 0 1; N 1 0, N 1 1] with hB
  have hNB : N = blockMat B := by
    obtain ⟨h02, h12, h20, h21⟩ := hb
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockMat, hB, h02, h12, h20, h21, h22]
  have hBdet : B.det = 1 := by rw [← det_blockMat, ← hNB]; exact hdet
  have hBu : (B.map h.bar)ᵀ * B = 1 := by
    have h1 : blockMat ((B.map h.bar)ᵀ * B) = blockMat 1 := by
      rw [blockMat_mul, ← blockMat_transpose, ← blockMat_map, ← hNB, hiso, blockMat_one]
    ext i j
    have := congrFun (congrFun h1 (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;> simpa [blockMat] using this
  have hBunit : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det, hBdet]
    exact isUnit_one
  refine ⟨⟨hBunit.unit, (mem_unitarySU_iff h).mpr ⟨by rw [IsUnit.unit_spec]; exact hBdet,
    by rw [IsUnit.unit_spec]; exact hBu⟩⟩, Units.ext ?_⟩
  rw [coe_blockGL]
  change blockMat ((hBunit.unit : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = N
  rw [IsUnit.unit_spec, hNB]

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
