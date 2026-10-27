module

public import CFSG.Quasithin.Background.HSU3Torus

public section

namespace CFSG.Quasithin.H13.L32A.C.SU3

open CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H.SU3
open CFSG.Quasithin.H

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def eW : Fin 3 → K := (wittMat : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1

theorem fix_uiSub (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {v : Fin 3 → K}
    (hv : ∀ u ∈ uiSub n K, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) : ∃ c : K, v = c • eW := by
  set w := (wittInv : Matrix (Fin 3) (Fin 3) K) *ᵥ v with hw
  have hvw : v = (wittMat : Matrix (Fin 3) (Fin 3) K) *ᵥ w := by
    rw [hw, mulVec_mulVec, wittMat_mul_wittInv, one_mulVec]
  have hfix : ∀ u ∈ ujSub n K, (u : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := by
    intro u hu
    have hmem : (wittGL : GL (Fin 3) K) * u * wittGL⁻¹ ∈ uiSub n K := by
      rw [mem_uiSub_iff]
      have e : (wittGL : GL (Fin 3) K)⁻¹ * (wittGL * u * wittGL⁻¹) * wittGL = u := by group
      rw [e]
      exact hu
    have h1 := hv _ hmem
    rw [Units.val_mul, Units.val_mul, coe_wittGL, coe_wittGL_inv] at h1
    have h2 := congrArg (fun x => (wittInv : Matrix (Fin 3) (Fin 3) K) *ᵥ x) h1
    simp only [mulVec_mulVec] at h2
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wittInv_mul_wittMat, Matrix.one_mul,
      ← mulVec_mulVec] at h2
    exact h2
  have hw2 : w 2 = 0 := by
    obtain ⟨u, hu, hu12⟩ := exists_ujSub_one_two hn hK 1
    obtain ⟨hlow, hdiag⟩ := Tri.uni3_entries (ujSub_le_uni3 hu)
    have h := congrFun (hfix u hu) 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
    rw [hlow 1 0 (by decide), hdiag 1, hu12] at h
    simpa using h
  have hw1 : w 1 = 0 := by
    obtain ⟨u, hu, hu01⟩ := exists_ujSub_zero_one hn hK 1
    obtain ⟨hlow, hdiag⟩ := Tri.uni3_entries (ujSub_le_uni3 hu)
    have h := congrFun (hfix u hu) 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
    rw [hdiag 0, hu01, hw2] at h
    simpa using h
  refine ⟨w 0, ?_⟩
  have hwe : w = w 0 • (Pi.single 0 1 : Fin 3 → K) := by
    ext i
    fin_cases i <;> simp [hw1, hw2]
  calc v = (wittMat : Matrix (Fin 3) (Fin 3) K) *ᵥ w := hvw
    _ = (wittMat : Matrix (Fin 3) (Fin 3) K) *ᵥ (w 0 • (Pi.single 0 1 : Fin 3 → K)) := by
        rw [← hwe]
    _ = w 0 • eW := by rw [mulVec_smul, eW]

theorem torI_mulVec_e (hK : Nat.card K = (2 ^ n) ^ 2) (α : Kˣ) (c : K) :
    (((torI hK α : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (c • eW) = ((α : K) * c) • eW := by
  have e1 : (((torI hK α : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = wittMat * torJMat n (α : K) * wittInv := by
    show ((wittGL * torJ n α * wittGL⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [Units.val_mul, Units.val_mul, coe_wittGL, coe_torJ, coe_wittGL_inv]
  have e2 : torJMat n (α : K) *ᵥ (Pi.single 0 1 : Fin 3 → K) =
      (α : K) • (Pi.single 0 1 : Fin 3 → K) := by
    ext i
    fin_cases i <;> simp [torJMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [e1, eW, mulVec_smul, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, wittInv_mul_wittMat,
    Matrix.mul_one, ← mulVec_mulVec, e2, mulVec_smul, smul_smul, mul_comm]

theorem torI_conj_mem_uiSub (hK : Nat.card K = (2 ^ n) ^ 2) (α : Kˣ) {x : GL (Fin 3) K}
    (hx : x ∈ uiSub n K) :
    ((torI hK α : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K) * x *
      ((torI hK α : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K)⁻¹ ∈ uiSub n K := by
  rw [mem_uiSub_iff] at hx ⊢
  have e : (wittGL : GL (Fin 3) K)⁻¹ *
      (((torI hK α : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K) * x *
        ((torI hK α : ↥(StatedSU 3 (2 ^ n) K)) : GL (Fin 3) K)⁻¹) * wittGL =
      torJ n α * (wittGL⁻¹ * x * wittGL) * (torJ n α)⁻¹ := by
    simp only [torI, MonoidHom.coe_mk, OneHom.coe_mk]
    group
  rw [e]
  exact torJ_conj_mem_ujSub hK α hx

end CFSG.Quasithin.H13.L32A.C.SU3
