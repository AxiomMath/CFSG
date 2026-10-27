module

public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

namespace G2Dat

open CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

@[expose] def matTau : List ℕ := [128, 16, 32, 64, 2, 4, 8, 1]

theorem matCode_zTau : matCode (zTau : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _) = matTau := by
  decide +kernel

@[expose] def bCode : List ℕ := [1, 6, 2, 8, 32, 48, 64, 128]

@[expose] def xCode : List ℕ := [3, 2, 68, 40, 147, 32, 64, 130]

theorem code_facts :
    mmul matT10 matT10 = idMat ∧ mmul matTau matTau = idMat ∧
      mmul (mmul (mmul matT10 matTau) matT10) matTau = bCode ∧
      mmul (mmul matTau matX) matTau = xCode ∧
      mmul (mmul (sM 45) (sM 2)) xCode = mmul xCode (sM 2) ∧
      mmul (mmul (sM 44) (sM 18)) (sM 9) = mmul (sM 9) (sM 18) ∧
      mmul (mmul (sM 30) matT10) (sM 36) = mmul (sM 36) matT10 := by
  decide +kernel

@[expose] def zT10G : ↥(quasithinG2 (ZMod 2)) := ⟨zT10, mem_quasithinG2 zT10_mul⟩

@[expose] def zTauG : ↥(quasithinG2 (ZMod 2)) := ⟨zTau, mem_quasithinG2 zTau_mul⟩

@[expose] def zXG : ↥(quasithinG2 (ZMod 2)) := ⟨zX, mem_quasithinG2 zX_mul⟩

theorem eq_of_code {g h : ↥(quasithinG2 (ZMod 2))} (e : matCode g.1 = matCode h.1) : g = h :=
  Subtype.ext (linearEquiv_eq_of_matCode e)

theorem matCode_mulG (g h : ↥(quasithinG2 (ZMod 2))) :
    matCode (g * h).1 = mmul (matCode g.1) (matCode h.1) :=
  matCode_mul g.1 h.1

theorem zT10G_inv : zT10G⁻¹ = zT10G := by
  refine inv_eq_of_mul_eq_one_right (eq_of_code ?_)
  rw [matCode_mulG]
  show mmul (matCode zT10) (matCode zT10) = matCode (1 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _)
  rw [matCode_zT10, matCode_one]
  exact code_facts.1

theorem zTauG_inv : zTauG⁻¹ = zTauG := by
  refine inv_eq_of_mul_eq_one_right (eq_of_code ?_)
  rw [matCode_mulG]
  show mmul (matCode zTau) (matCode zTau) = matCode (1 : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _)
  rw [matCode_zTau, matCode_one]
  exact code_facts.2.1

@[expose] def b₀ : ↥(quasithinG2 (ZMod 2)) := ⁅zT10G, zTauG⁆

theorem matCode_b₀ : matCode b₀.1 = bCode := by
  rw [b₀, commutatorElement_def, zT10G_inv, zTauG_inv, matCode_mulG, matCode_mulG, matCode_mulG]
  show mmul (mmul (mmul (matCode zT10) (matCode zTau)) (matCode zT10)) (matCode zTau) = _
  rw [matCode_zT10, matCode_zTau]
  exact code_facts.2.2.1

@[expose] def xG : ↥(quasithinG2 (ZMod 2)) := zTauG * zXG * zTauG

theorem matCode_xG : matCode xG.1 = xCode := by
  rw [xG, matCode_mulG, matCode_mulG]
  show mmul (mmul (matCode zTau) (matCode zX)) (matCode zTau) = _
  rw [matCode_zTau, matCode_zX]
  exact code_facts.2.2.2.1

theorem commutator_eq_of {Γ : Type*} [Group Γ] {x y c : Γ} (h : c * y * x = x * y) :
    ⁅x, y⁆ = c := by
  rw [commutatorElement_def]
  calc x * y * x⁻¹ * y⁻¹ = (c * y * x) * x⁻¹ * y⁻¹ := by rw [h]
    _ = c := by group

theorem a₀_eq : ⁅xG, sEltG 2⁆ = sEltG 45 := by
  apply commutator_eq_of
  apply eq_of_code
  rw [matCode_mulG, matCode_mulG, matCode_mulG, matCode_sEltG (by norm_num),
    matCode_sEltG (by norm_num), matCode_xG]
  exact code_facts.2.2.2.2.1

theorem c₁_eq : ⁅sEltG 9, sEltG 18⁆ = sEltG 44 := by
  apply commutator_eq_of
  apply eq_of_code
  rw [matCode_mulG, matCode_mulG, matCode_mulG, matCode_sEltG (by norm_num),
    matCode_sEltG (by norm_num), matCode_sEltG (by norm_num)]
  exact code_facts.2.2.2.2.2.1

theorem c₂_eq : ⁅sEltG 36, zT10G⁆ = sEltG 30 := by
  apply commutator_eq_of
  apply eq_of_code
  rw [matCode_mulG, matCode_mulG, matCode_mulG, matCode_sEltG (by norm_num),
    matCode_sEltG (by norm_num)]
  show mmul (mmul (sM 30) (matCode zT10)) (sM 36) = mmul (sM 36) (matCode zT10)
  rw [matCode_zT10]
  exact code_facts.2.2.2.2.2.2

theorem commutator_mem_g2Derived (x y : ↥(quasithinG2 (ZMod 2))) :
    ⁅x, y⁆ ∈ g2Derived (ZMod 2) := by
  rw [g2Derived_eq_commutator]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

theorem fix_c₁₂ : ∀ c ∈ o0Codes, fixQB (sM 44) c = true → fixQB (sM 30) c = true →
    c = 0 ∨ c = 129 ∨ c = 8 ∨ c = 137 := by
  decide +kernel

theorem fix_w₀ : (∀ i < 64, fixQB (sM i) 8 = true) ∧ fixQB bCode 8 = true := by
  decide +kernel

theorem r₀_checks :
    (∀ k < 32, ∀ l < 32, ∃ m < 32, mmul (sM (2 * k)) (sM (2 * l)) = sM (2 * m)) ∧
    (∀ k < 32, ∃ l < 32, mmul (sM (2 * k)) (sM (2 * l)) = idMat) ∧
    (∀ i < 64, ∀ k < 32, ∃ l < 32, mmul (sM i) (sM (2 * k)) = mmul (sM (2 * l)) (sM i)) ∧
    (∀ k < 32, ∃ l < 32, mmul bCode (sM (2 * k)) = mmul (sM (2 * l)) bCode) := by
  decide +kernel

theorem b₀_checks :
    mmul bCode (mmul bCode bCode) = idMat ∧ bCode ≠ idMat ∧
      ∀ k < 32, mmul (sM 45) bCode ≠ mmul (mmul bCode (sM 45)) (sM (2 * k)) := by
  decide +kernel

@[expose] def b1Code : List ℕ := [57, 62, 147, 8, 40, 48, 215, 184]

theorem b₁_checks :
    mmul (sM 16) (sM 16) = idMat ∧ mmul (mmul (sM 16) bCode) (sM 16) = b1Code ∧
      mmul b1Code (mmul b1Code b1Code) = idMat ∧
      ∀ i < 64, mmul (sM i) bCode = mmul bCode (sM i) →
        mmul (sM i) b1Code = mmul b1Code (sM i) → i = 0 := by
  decide +kernel

end G2Dat

end CFSG.Quasithin.H13
