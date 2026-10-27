module

public import CFSG.Quasithin.H13.U3G2Mdl

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

@[expose] def u5mask : ℕ := 17179869729

theorem conj_g1_codes : ∀ k < 64, g1mask.testBit k = true → ∃ k' < 64,
    a1mask.testBit k' = true ∧ mul6 (mul6 (u6c 4) (s0m k)) (u6ci 4) = s0m k' := by
  decide +kernel

theorem conj_g3_codes : ∀ k < 64, g3mask.testBit k = true → ∃ k' < 64,
    a1mask.testBit k' = true ∧
      mul6 (mul6 (mul6 (u6c 4) (u6c 0)) (s0m k)) (mul6 (u6ci 0) (u6ci 4)) = s0m k' := by
  decide +kernel

theorem card_g13_codes : (ofMask g1mask).card = 8 ∧ (ofMask g3mask).card = 8 := by
  decide +kernel

theorem v5_codes : ∀ k < 64, a1mask.testBit k = true → k ≠ 0 → ∀ c < 64, vapp (s0m k) c = c →
    v5mask.testBit c = true := by
  decide +kernel

theorem u5_codes : ∀ k < 64, a1mask.testBit k = true → ∀ c < 64, v3mask.testBit c = false →
    vapp (s0m k) c = c → u5mask.testBit k = true := by
  decide +kernel

theorem v1_codes : ∀ k < 64, u5mask.testBit k = true → ∀ c < 64, v5mask.testBit c = true →
    v1mask.testBit (vapp (s0m k) c ^^^ c) = true := by
  decide +kernel

theorem z_codes : a1mask.testBit 5 = true ∧ a1mask.testBit 34 = true ∧ vapp (s0m 34) 3 = 3 ∧
    vapp (s0m 5) 7 = 7 ∧ v3mask.testBit 7 = false ∧ vapp (s0m 5) 3 ^^^ 3 = 15 := by
  decide +kernel

noncomputable abbrev yaGL : GL (Fin 6) (ZMod 2) := rho6 (wordElem [4, 0])

theorem yaGL_mem : yaGL ∈ J6 := ⟨_, rfl⟩

theorem ya_codes : wordMat [4, 0] = mul6 (u6c 4) (u6c 0) ∧
    mul6 (mul6 (u6ci 0) (u6ci 4)) (mul6 (u6c 4) (u6c 0)) = id6 := by
  decide +kernel

theorem coe_yaGL : (yaGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (mul6 (u6c 4) (u6c 0)) := by
  rw [coe_rho6_wordElem, ya_codes.1]

theorem coe_yaGL_inv : ((yaGL⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    colMat (mul6 (u6ci 0) (u6ci 4)) :=
  coe_inv_of_code coe_yaGL ya_codes.2

theorem coe_yGL_inv : ((yGL⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    colMat (u6ci 4) :=
  coe_inv_of_code coe_yGL (u6c_mul_inv 4).2

end CFSG.Quasithin.H13.U3
