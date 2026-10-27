module

public import CFSG.Quasithin.Background.HSp4A6DataInputs
public import CFSG.Quasithin.Background.HSp4Model
public import CFSG.Quasithin.Background.G6Natural
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauAlg

public section

namespace CertificateChecks.KernelDirect.C7067

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Sp4A6 CFSG.Assembly.LowTwoRank Matrix
open Equiv
open CFSG.QuasithinUnique.Lin2.Five (tauMat)
open scoped Matrix
local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem decomp_0 :
    ∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 →
      ∃ t : ZMod 2, y = ∑ c, coord y c • bas c + t • ones := by
  decide +kernel

theorem perm6_mul (σ τ : Perm (Fin 6)) (y : Fin 6 → ZMod 2) :
    perm6 (σ * τ) y = perm6 σ (perm6 τ y) := by
  funext i
  simp [perm6, _root_.mul_inv_rev, Perm.mul_apply]

theorem coord_sum_add (σ : Perm (Fin 6)) (f : Fin 2 ⊕ Fin 2 → ZMod 2) (t : ZMod 2) (r : Fin 2 ⊕ Fin 2) :
    coord (perm6 σ (∑ c, f c • bas c + t • ones)) r = ∑ c, f c * coord (perm6 σ (bas c)) r := by
  have h1 : perm6 σ (∑ c, f c • bas c + t • ones) = ∑ c, f c • perm6 σ (bas c) + t • ones := by
    funext i
    simp [perm6, ones]
  have h2 : ∀ r, ones ⬝ᵥ dualBas r = 0 := by decide
  rw [h1]
  simp only [coord, add_dotProduct, smul_dotProduct, h2, smul_zero, add_zero, smul_eq_mul]
  rw [sum_dotProduct]
  simp [smul_dotProduct]

theorem psiMat_mul (σ τ : Perm (Fin 6)) : psiMat (σ * τ) = psiMat σ * psiMat τ := by
  ext r c
  have hs : ∑ i, perm6 τ (bas c) i = 0 := by
    have h : ∀ c, ∑ i, bas c i = 0 := by decide
    rw [← h c]
    exact Equiv.sum_comp τ⁻¹ (bas c)
  obtain ⟨t, ht⟩ := decomp_0 _ hs
  rw [psiMat, Matrix.of_apply, perm6_mul, ht, coord_sum_add, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun c' _ => mul_comm _ _

set_option maxRecDepth 100000 in
theorem psiMat_symplectic_one :
    (psiMat 1)ᵀ * fromBlocks 0 1 (-1) 0 * psiMat 1 = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem psiMat_symplectic_swap : ∀ x y : Fin 6,
    (psiMat (swap x y))ᵀ * fromBlocks 0 1 (-1) 0 * psiMat (swap x y) = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem psiMat_symplectic_1 :
    ∀ σ : Perm (Fin 6),
      (psiMat σ)ᵀ * fromBlocks 0 1 (-1) 0 * psiMat σ = fromBlocks 0 1 (-1) 0 := by
  intro σ
  refine Equiv.Perm.swap_induction_on σ ?_ fun f x y _ ih => ?_
  · exact psiMat_symplectic_one
  · rw [psiMat_mul, Matrix.transpose_mul]
    calc (psiMat f)ᵀ * (psiMat (swap x y))ᵀ * fromBlocks 0 1 (-1) 0 * (psiMat (swap x y) * psiMat f)
        = (psiMat f)ᵀ * ((psiMat (swap x y))ᵀ * fromBlocks 0 1 (-1) 0 * psiMat (swap x y)) *
            psiMat f := by simp only [Matrix.mul_assoc]
      _ = fromBlocks 0 1 (-1) 0 := by rw [psiMat_symplectic_swap, ih]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem psiMat_eq_one_2 :
    ∀ σ : Perm (Fin 6), psiMat σ = 1 → σ = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem stab_fix_3 :
    ∀ w : Fin 2 ⊕ Fin 2 → ZMod 2,
      (∀ σ : Perm (Fin 6), Perm.sign σ = 1 → psiMat σ *ᵥ Pi.single ι₀ 1 = Pi.single ι₀ 1 →
        psiMat σ *ᵥ w = w) → w = 0 ∨ w = Pi.single ι₀ 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem transitive_psiMat_4 :
    ∀ v w : Fin 2 ⊕ Fin 2 → ZMod 2, v ≠ 0 → w ≠ 0 →
      ∃ σ : Perm (Fin 6), Perm.sign σ = 1 ∧ psiMat σ *ᵥ v = w := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem card_fix_cyc345_5 :
    Fintype.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 // psiMat cyc345 *ᵥ v = v} = 4 ∧
      Fintype.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 // tauMat (psiMat cyc345) *ᵥ v = v} = 1 := by
  decide +kernel

end CertificateChecks.KernelDirect.C7067
