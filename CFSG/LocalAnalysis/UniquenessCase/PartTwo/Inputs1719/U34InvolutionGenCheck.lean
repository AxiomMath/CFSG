module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGenModel
public import Certificates.Certificate745101
import CFSG.Certificates.OrbitChain

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Certificates CFSG.GH74.KGroups CFSG.LieType.SeitzGeneration.HeisSmall
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts

private def mkGL (A B : M3 GF16) (hAB : A * B = 1) (hBA : B * A = 1) : GL (Fin 3) GF16 :=
  Units.mk (toMat (RingHom.id GF16) A) (toMat (RingHom.id GF16) B)
    (by rw [← toMat_mul, hAB, toMat_one])
    (by rw [← toMat_mul, hBA, toMat_one])

private theorem t_sq : tMat * tMat = 1 := by ext <;> decide
private theorem t_det : tMat.det = 1 := by decide
private theorem t_uni : (tMat.map (· ^ (2 ^ 2))).transpose * tMat = 1 := by ext <;> decide

private theorem x1_mul : x1Mat * x1InvMat = 1 := by ext <;> decide
private theorem x1_inv_mul : x1InvMat * x1Mat = 1 := by ext <;> decide
private theorem x1_det : x1Mat.det = 1 := by decide
private theorem x1_uni : (x1Mat.map (· ^ (2 ^ 2))).transpose * x1Mat = 1 := by ext <;> decide

private theorem x2_mul : x2Mat * x2InvMat = 1 := by ext <;> decide
private theorem x2_inv_mul : x2InvMat * x2Mat = 1 := by ext <;> decide
private theorem x2_det : x2Mat.det = 1 := by decide
private theorem x2_uni : (x2Mat.map (· ^ (2 ^ 2))).transpose * x2Mat = 1 := by ext <;> decide

private theorem y1_mul : y1Mat * y1InvMat = 1 := by ext <;> decide
private theorem y1_inv_mul : y1InvMat * y1Mat = 1 := by ext <;> decide
private theorem y1_det : y1Mat.det = 1 := by decide
private theorem y1_uni : (y1Mat.map (· ^ (2 ^ 2))).transpose * y1Mat = 1 := by ext <;> decide

private theorem y2_mul : y2Mat * y2InvMat = 1 := by ext <;> decide
private theorem y2_inv_mul : y2InvMat * y2Mat = 1 := by ext <;> decide
private theorem y2_det : y2Mat.det = 1 := by decide
private theorem y2_uni : (y2Mat.map (· ^ (2 ^ 2))).transpose * y2Mat = 1 := by ext <;> decide

private theorem mem_unitarySU_mkGL (A B : M3 GF16) (hAB : A * B = 1) (hBA : B * A = 1)
    (hdet : A.det = 1) (hu : (A.map (· ^ (2 ^ 2))).transpose * A = 1) :
    mkGL A B hAB hBA ∈ unitarySU 2 2 GF16 3 := by
  rw [mem_unitarySU_iff unitaryFieldData_GF16]
  constructor
  · rw [show ((mkGL A B hAB hBA : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) =
      toMat (RingHom.id GF16) A from rfl, toMat_det, hdet]
    rfl
  · rw [show ((mkGL A B hAB hBA : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) =
      toMat (RingHom.id GF16) A from rfl,
      ← toMat_transpose_map unitaryFieldData_GF16 (RingHom.id GF16) A, ← toMat_mul, hu,
      toMat_one]

private def unitOf (A B : M3 GF16) (hAB : A * B = 1) (hBA : B * A = 1) (hdet : A.det = 1)
    (hu : (A.map (· ^ (2 ^ 2))).transpose * A = 1) : unitarySU 2 2 GF16 3 :=
  ⟨mkGL A B hAB hBA, mem_unitarySU_mkGL A B hAB hBA hdet hu⟩

private def tU : unitarySU 2 2 GF16 3 := unitOf tMat tMat t_sq t_sq t_det t_uni
private def x1U : unitarySU 2 2 GF16 3 :=
  unitOf x1Mat x1InvMat x1_mul x1_inv_mul x1_det x1_uni
private def x2U : unitarySU 2 2 GF16 3 :=
  unitOf x2Mat x2InvMat x2_mul x2_inv_mul x2_det x2_uni
private def y1U : unitarySU 2 2 GF16 3 :=
  unitOf y1Mat y1InvMat y1_mul y1_inv_mul y1_det y1_uni
private def y2U : unitarySU 2 2 GF16 3 :=
  unitOf y2Mat y2InvMat y2_mul y2_inv_mul y2_det y2_uni

private def rho (g : unitarySU 2 2 GF16 3) : M3 GF16 :=
  ofMat ((g : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16)

private theorem rho_one : rho 1 = 1 := by
  change ofMat (1 : Matrix (Fin 3) (Fin 3) GF16) = 1
  ext <;> decide

private theorem rho_mul (a b : unitarySU 2 2 GF16 3) : rho (a * b) = rho a * rho b := by
  apply toMat_injective (ι := RingHom.id GF16) (RingHom.id GF16).injective
  change toMat (RingHom.id GF16)
      (ofMat (((a * b : unitarySU 2 2 GF16 3) : GL (Fin 3) GF16) :
        Matrix (Fin 3) (Fin 3) GF16)) =
    toMat (RingHom.id GF16)
      (ofMat ((a : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) *
        ofMat ((b : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16))
  rw [toMat_id_ofMat, toMat_mul, toMat_id_ofMat, toMat_id_ofMat]
  rfl

private theorem rho_t : rho tU = tMat := by
  change ofMat (toMat (RingHom.id GF16) tMat) = tMat
  ext <;> decide

private theorem rho_x1 : rho x1U = x1Mat := by
  change ofMat (toMat (RingHom.id GF16) x1Mat) = x1Mat
  ext <;> decide

private theorem rho_x1_inv : rho (x1U⁻¹) = x1InvMat := by
  change ofMat (toMat (RingHom.id GF16) x1InvMat) = x1InvMat
  ext <;> decide

private theorem rho_x2 : rho x2U = x2Mat := by
  change ofMat (toMat (RingHom.id GF16) x2Mat) = x2Mat
  ext <;> decide

private theorem rho_x2_inv : rho (x2U⁻¹) = x2InvMat := by
  change ofMat (toMat (RingHom.id GF16) x2InvMat) = x2InvMat
  ext <;> decide

private theorem rho_y1 : rho y1U = y1Mat := by
  change ofMat (toMat (RingHom.id GF16) y1Mat) = y1Mat
  ext <;> decide

private theorem rho_y2 : rho y2U = y2Mat := by
  change ofMat (toMat (RingHom.id GF16) y2Mat) = y2Mat
  ext <;> decide

private theorem rho_d1 : rho (tU * x1U⁻¹ * tU * x1U) = d1Mat := by
  simp only [rho_mul, rho_t, rho_x1_inv, rho_x1]
  ext <;> decide

private theorem rho_d2 : rho (tU * x2U⁻¹ * tU * x2U) = d2Mat := by
  simp only [rho_mul, rho_t, rho_x2_inv, rho_x2]
  ext <;> decide

private theorem rho_suField (σ : GF16 ≃+* GF16) (y : unitarySU 2 2 GF16 3) :
    rho (suField unitaryFieldData_GF16 σ y) =
      ofMat (((y : GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16).map σ) := by
  change ofMat (((suField unitaryFieldData_GF16 σ y : unitarySU 2 2 GF16 3) :
    GL (Fin 3) GF16) : Matrix (Fin 3) (Fin 3) GF16) = _
  rw [coe_suField, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]

private theorem rho_suField_inv (σ : GF16 ≃+* GF16) (y : unitarySU 2 2 GF16 3) :
    rho ((suField unitaryFieldData_GF16 σ y)⁻¹) =
      ofMat ((((y : GL (Fin 3) GF16)⁻¹ : GL (Fin 3) GF16) :
        Matrix (Fin 3) (Fin 3) GF16).map σ) := by
  rw [← map_inv]
  rw [rho_suField]
  rfl

private theorem rho_suField_inv_bar (y : unitarySU 2 2 GF16 3) :
    rho ((suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y)⁻¹) =
      ofMat ((((y : GL (Fin 3) GF16)⁻¹ : GL (Fin 3) GF16) :
        Matrix (Fin 3) (Fin 3) GF16).map (· ^ 4)) := by
  rw [rho_suField_inv]
  congr 1

private theorem y1_GL_inv :
    (((y1U : GL (Fin 3) GF16)⁻¹ : GL (Fin 3) GF16) :
      Matrix (Fin 3) (Fin 3) GF16) = toMat (RingHom.id GF16) y1InvMat := by
  rw [show (y1U : GL (Fin 3) GF16) = mkGL y1Mat y1InvMat y1_mul y1_inv_mul from rfl]
  rw [Units.inv_mk]
  rfl

private theorem y2_GL_inv :
    (((y2U : GL (Fin 3) GF16)⁻¹ : GL (Fin 3) GF16) :
      Matrix (Fin 3) (Fin 3) GF16) = toMat (RingHom.id GF16) y2InvMat := by
  rw [show (y2U : GL (Fin 3) GF16) = mkGL y2Mat y2InvMat y2_mul y2_inv_mul from rfl]
  rw [Units.inv_mk]
  rfl

private theorem rho_suField_inv_y1 :
    rho ((suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y1U)⁻¹) =
      ofMat ((toMat (RingHom.id GF16) y1InvMat).map (· ^ 4)) := by
  rw [rho_suField_inv_bar, y1_GL_inv]

private theorem rho_suField_inv_y2 :
    rho ((suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y2U)⁻¹) =
      ofMat ((toMat (RingHom.id GF16) y2InvMat).map (· ^ 4)) := by
  rw [rho_suField_inv_bar, y2_GL_inv]

private theorem rho_e1 :
    rho ((suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y1U)⁻¹ * y1U) =
      e1Mat := by
  rw [rho_mul, rho_suField_inv_y1, rho_y1]
  ext <;> decide

private theorem rho_e2 :
    rho ((suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y2U)⁻¹ * y2U) =
      e2Mat := by
  rw [rho_mul, rho_suField_inv_y2, rho_y2]
  ext <;> decide

private theorem tU_sq : tU * tU = 1 := by
  apply Subtype.ext
  apply Units.ext
  change toMat (RingHom.id GF16) tMat * toMat (RingHom.id GF16) tMat = 1
  rw [← toMat_mul, t_sq, toMat_one]

private theorem tMat_ne_one : tMat ≠ 1 := by
  intro h
  have h1 : tMat.a01 = (1 : M3 GF16).a01 := congrArg (fun A : M3 GF16 => A.a01) h
  exact absurd h1 (by decide)

private theorem tU_ne_one : tU ≠ 1 := by
  intro h
  have h' : rho tU = rho 1 := congrArg rho h
  have : tMat = 1 := by rw [← rho_t, h', rho_one]
  exact tMat_ne_one this

public section

theorem u34InvGenInner_holds : U34InvGenInner := by
  have htop := Certificates.certificate745101.1
    (Subgroup.closure {tU * x1U⁻¹ * tU * x1U, tU * x2U⁻¹ * tU * x2U})
    ⟨_, Subgroup.subset_closure (by simp), rho_d1⟩ ⟨_, Subgroup.subset_closure (by simp), rho_d2⟩
  exact ⟨tU, x1U, x2U, tU_sq, tU_ne_one, htop⟩

theorem u34InvGenOuter_holds : U34InvGenOuter := by
  have htop := Certificates.certificate745101.2
    (Subgroup.closure
      {(suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y1U)⁻¹ * y1U,
        (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y2U)⁻¹ * y2U})
    ⟨_, Subgroup.subset_closure (by simp), rho_e1⟩ ⟨_, Subgroup.subset_closure (by simp), rho_e2⟩
  exact ⟨y1U, y2U, htop⟩

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
