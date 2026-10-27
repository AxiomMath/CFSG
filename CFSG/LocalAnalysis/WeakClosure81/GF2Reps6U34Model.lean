module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGenModel
public import Certificates.Certificate745101
import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
import CFSG.Certificates.OrbitChain

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.U34

open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups CFSG.LieType.SeitzGeneration.HeisSmall
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Certificates CFSG.LocalAnalysis.ComponentInitial

@[expose] def toM3 (g : unitarySU 2 2 GF16 3) : M3 GF16 :=
  ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16)

theorem toM3_one : toM3 1 = 1 := by
  change ofMat (1 : Matrix (Fin 3) (Fin 3) GF16) = 1
  ext <;> decide

theorem toM3_mul (a b : unitarySU 2 2 GF16 3) : toM3 (a * b) = toM3 a * toM3 b := by
  apply toMat_injective (ι := RingHom.id GF16) (RingHom.id GF16).injective
  change toMat (RingHom.id GF16)
      (ofMat (((a * b : unitarySU 2 2 GF16 3) : GL (Fin 3) GF16) :
        Matrix (Fin 3) (Fin 3) GF16)) =
    toMat (RingHom.id GF16)
      (ofMat ((a : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) *
        ofMat ((b : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16))
  rw [toMat_id_ofMat, toMat_mul, toMat_id_ofMat, toMat_id_ofMat]
  rfl

theorem toM3_injective : Function.Injective toM3 := by
  intro a b hab
  apply Subtype.ext
  apply Units.ext
  have h := congrArg (fun A : M3 GF16 => toMat (RingHom.id GF16) A) hab
  simpa [toM3, toMat_id_ofMat] using h

theorem mem_unitarySU_of_m3 (A B : M3 GF16) (hAB : A * B = 1) (hBA : B * A = 1)
    (hdet : A.det = 1) (hu : (A.map (· ^ (2 ^ 2))).transpose * A = 1) :
    (Units.mk (toMat (RingHom.id GF16) A) (toMat (RingHom.id GF16) B)
      (by rw [← toMat_mul, hAB, toMat_one]) (by rw [← toMat_mul, hBA, toMat_one]) :
        GL (Fin 3) GF16) ∈ unitarySU 2 2 GF16 3 := by
  rw [mem_unitarySU_iff unitaryFieldData_GF16]
  constructor
  · change (toMat (RingHom.id GF16) A).det = 1
    rw [toMat_det, hdet]
    rfl
  · change Matrix.transpose ((toMat (RingHom.id GF16) A).map unitaryFieldData_GF16.bar) *
        toMat (RingHom.id GF16) A = 1
    rw [← toMat_transpose_map unitaryFieldData_GF16 (RingHom.id GF16) A, ← toMat_mul, hu,
      toMat_one]

def mk (A B : M3 GF16) (hAB : A * B = 1) (hBA : B * A = 1) (hdet : A.det = 1)
    (hu : (A.map (· ^ (2 ^ 2))).transpose * A = 1) : unitarySU 2 2 GF16 3 :=
  ⟨_, mem_unitarySU_of_m3 A B hAB hBA hdet hu⟩

theorem toM3_mk (A B : M3 GF16) (hAB : A * B = 1) (hBA : B * A = 1) (hdet : A.det = 1)
    (hu : (A.map (· ^ (2 ^ 2))).transpose * A = 1) : toM3 (mk A B hAB hBA hdet hu) = A := by
  change ofMat (toMat (RingHom.id GF16) A) = A
  ext <;> rfl

theorem toM3_mk_inv (A B : M3 GF16) (hAB : A * B = 1) (hBA : B * A = 1) (hdet : A.det = 1)
    (hu : (A.map (· ^ (2 ^ 2))).transpose * A = 1) : toM3 (mk A B hAB hBA hdet hu)⁻¹ = B := by
  change ofMat (toMat (RingHom.id GF16) B) = B
  ext <;> rfl

theorem toM3_suField (g : unitarySU 2 2 GF16 3) :
    toM3 (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv g) =
      (toM3 g).map (· ^ 4) := by
  change ofMat (((suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv g :
    unitarySU 2 2 GF16 3) : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) =
    (toM3 g).map (· ^ 4)
  rw [coe_suField, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
  change ofMat ((((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16).map
      unitaryFieldData_GF16.barEquiv)) =
    M3.map (fun x : GF16 => x ^ 4)
      (ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16))
  ext <;> simp [ofMat, M3.map, Matrix.map_apply, UnitaryFieldData.barEquiv_apply,
    UnitaryFieldData.bar_apply, show (2 : ℕ) ^ 2 = 4 by norm_num]

theorem suField_mul_self :
    suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv *
      suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv = 1 := by
  rw [← map_mul]
  have hbar2 : unitaryFieldData_GF16.barEquiv * unitaryFieldData_GF16.barEquiv = 1 := by
    ext c
    simp [UnitaryFieldData.barEquiv_apply, UnitaryFieldData.bar_bar]
  rw [hbar2, map_one]

theorem suField_not_mem_range :
    suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv ∉
      (MulAut.conj : unitarySU 2 2 GF16 3 →* MulAut (unitarySU 2 2 GF16 3)).range := by
  rintro ⟨s, hs⟩
  have hbar1 : unitaryFieldData_GF16.barEquiv ≠ 1 := by
    obtain ⟨c, hc⟩ := unitaryFieldData_GF16.exists_bar_ne
    intro h
    apply hc
    have h' := congrArg (fun σ : GF16 ≃+* GF16 => σ c) h
    simpa [UnitaryFieldData.barEquiv_apply] using h'
  have hdesc : psuField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv =
      psuConj unitaryFieldData_GF16 ⟨s, unitarySU_le_unitaryIsom3 s.2⟩ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [psuField_mk, psuConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_suField, coe_suConj]
      have h1 : suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y =
          s * y * s⁻¹ := by
        rw [← hs]
        rfl
      simpa [coe_suField] using
        congrArg (fun z : unitarySU 2 2 GF16 3 => (z : GL (Fin 3) GF16)) h1
  exact (CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.psuField_not_mem_psuConj_range
    (h := unitaryFieldData_GF16) hbar1) ⟨⟨s, unitarySU_le_unitaryIsom3 s.2⟩, hdesc.symm⟩

theorem center_eq_bot : Subgroup.center (unitarySU 2 2 GF16 3) = ⊥ := by
  have hcard : Nat.card (unitaryScalars unitaryFieldData_GF16 3) = 1 := by
    rw [card_unitaryScalars unitaryFieldData_GF16 (by norm_num)]
    norm_num
  rw [center_unitarySU_three (h := unitaryFieldData_GF16) (by norm_num)]
  exact Subgroup.eq_bot_of_card_eq _ hcard

theorem eq_top_of_toM3 {H : Subgroup (unitarySU 2 2 GF16 3)}
    (h₁ : ∃ g ∈ H, toM3 g = d1Mat) (h₂ : ∃ g ∈ H, toM3 g = d2Mat) : H = ⊤ :=
  Certificates.certificate745101.1 H h₁ h₂

end CFSG.LocalAnalysis.WeakClosure81.Asch6.U34

end
