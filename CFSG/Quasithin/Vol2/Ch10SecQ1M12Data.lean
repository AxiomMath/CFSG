module

public import CFSG.Quasithin.Background.HMathieuNorm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM23DataInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

open CFSG.Monster.Code

@[expose] def dodecadMask : ℕ := 1802942

@[expose] def dodecadW : Fin 24 → ZMod 2 := bvec 24 dodecadMask

@[expose] def m12A : Equiv.Perm (Fin 24) where
  toFun := ![22, 9, 7, 3, 4, 20, 11, 2, 21, 1, 10, 6, 12, 18, 14, 15, 16, 19, 13, 17, 5, 8, 0, 23]
  invFun := ![22, 9, 7, 3, 4, 20, 11, 2, 21, 1, 10, 6, 12, 18, 14, 15, 16, 19, 13, 17, 5, 8, 0, 23]
  left_inv := by decide
  right_inv := by decide

@[expose] def m12B : Equiv.Perm (Fin 24) where
  toFun := ![10, 17, 20, 19, 5, 16, 12, 3, 23, 1, 11, 0, 14, 18, 6, 2, 4, 9, 21, 7, 15, 13, 8, 22]
  invFun := ![11, 9, 15, 7, 16, 4, 14, 19, 22, 17, 0, 10, 6, 21, 12, 20, 5, 1, 13, 3, 2, 18, 23, 8]
  left_inv := by decide
  right_inv := by decide

@[expose] def j12 : Fin 12 → Fin 24 := ![5, 15, 2, 20, 1, 19, 3, 16, 4, 7, 9, 17]

@[expose] def k12 : Fin 24 → Fin 12 :=
  ![0, 4, 2, 6, 8, 0, 0, 9, 0, 10, 0, 0, 0, 0, 0, 1, 7, 11, 0, 5, 3, 0, 0, 0]

theorem dodecadW_mem_C : dodecadW ∈ C := by decide

theorem hammingNorm_dodecadW : hammingNorm dodecadW = 12 := by decide

theorem dodecadW_cases : ∀ y : Fin 24, dodecadW y = 0 ∨ dodecadW y = 1 := by decide

theorem dodecadW_zero : dodecadW 0 = 0 := by decide

theorem card_compl_dodecad : (Finset.univ.filter fun y : Fin 24 => dodecadW y = 0).card = 12 := by
  decide

theorem m12A_mem : m12A ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem m12B_mem : m12B ∈ AutPerm := mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem m12A_fix : ∀ y, dodecadW (m12A⁻¹ y) = dodecadW y := by decide

theorem m12B_fix : ∀ y, dodecadW (m12B⁻¹ y) = dodecadW y := by decide

theorem k12_j12 : ∀ i, k12 (j12 i) = i := by decide

theorem j12_k12 : ∀ y, dodecadW y = 1 → j12 (k12 y) = y := by decide

theorem dodecadW_j12 : ∀ i, dodecadW (j12 i) = 1 := by decide

theorem res_m12A : ∀ i, k12 (m12A (j12 i)) = CFSG.Sporadic.Mathieu.m12gA i := by decide

theorem res_m12B : ∀ i, k12 (m12B (j12 i)) = CFSG.Sporadic.Mathieu.m12gB i := by decide

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Vol2Native.L239.Covers in
theorem dodecadW_j23 : ∀ i : Fin 23, dodecadW (j23 i) = 1 ↔ i ∈ D23 := by decide

open CFSG.Quasithin.H.Mathieu in
theorem j23Split_j23 : ∀ i : Fin 23, j23Split (j23 i) = some i := by decide

end CFSG.Quasithin.Vol2.Ch10.SecA.C10P01
