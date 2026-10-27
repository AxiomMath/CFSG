module

public import CFSG.Quasithin.Background.HSp4Model
public import CFSG.Quasithin.Background.G6Natural
public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.GroupTheory.Nilpotent
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.Data.Matrix.Block
public meta import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Data.Fin.VecNotation
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauAlg
public import CFSG.Quasithin.Background.HSp4A6DataInputs
public import Certificates.Certificate7067

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4A6

open CFSG.Assembly.LowTwoRank Matrix Equiv
open CFSG.QuasithinUnique.Lin2.Five (tauMat)
open scoped Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

theorem coord_add (y z : Fin 6 → ZMod 2) : coord (y + z) = coord y + coord z := by
  funext r
  simp [coord, add_dotProduct]

theorem coord_smul (t : ZMod 2) (y : Fin 6 → ZMod 2) : coord (t • y) = t • coord y := by
  funext r
  simp [coord, smul_dotProduct]

theorem coord_sum {s : Finset (Fin 2 ⊕ Fin 2)} (f : Fin 2 ⊕ Fin 2 → Fin 6 → ZMod 2) :
    coord (∑ c ∈ s, f c) = ∑ c ∈ s, coord (f c) := by
  funext r
  simp [coord, sum_dotProduct]

theorem perm6_add (σ : Perm (Fin 6)) (y z : Fin 6 → ZMod 2) :
    perm6 σ (y + z) = perm6 σ y + perm6 σ z := rfl

theorem perm6_smul (σ : Perm (Fin 6)) (t : ZMod 2) (y : Fin 6 → ZMod 2) :
    perm6 σ (t • y) = t • perm6 σ y := rfl

theorem perm6_sum (σ : Perm (Fin 6)) {s : Finset (Fin 2 ⊕ Fin 2)}
    (f : Fin 2 ⊕ Fin 2 → Fin 6 → ZMod 2) : perm6 σ (∑ c ∈ s, f c) = ∑ c ∈ s, perm6 σ (f c) := by
  funext i
  simp [perm6, Finset.sum_apply]

theorem perm6_ones (σ : Perm (Fin 6)) : perm6 σ ones = ones := rfl

theorem perm6_mul (σ τ : Perm (Fin 6)) (y : Fin 6 → ZMod 2) :
    perm6 (σ * τ) y = perm6 σ (perm6 τ y) := by
  funext i
  simp [perm6, _root_.mul_inv_rev]

theorem coord_ones : coord ones = 0 := by
  funext r
  rcases r with r | r <;> fin_cases r <;>
    simp [coord, ones, dualBas, dotProduct, Fin.sum_univ_six] <;> decide

theorem coord_bas (c : Fin 2 ⊕ Fin 2) : coord (bas c) = Pi.single c 1 := by
  funext r
  rcases c with c | c <;> fin_cases c <;> rcases r with r | r <;> fin_cases r <;>
    simp [coord, bas, dualBas, dotProduct, Fin.sum_univ_six] <;> decide

theorem decomp : ∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 →
    ∃ t : ZMod 2, y = ∑ c, coord y c • bas c + t • ones :=
  Certificates.certificate7067.1

theorem sum_perm6 (σ : Perm (Fin 6)) (y : Fin 6 → ZMod 2) : ∑ i, perm6 σ y i = ∑ i, y i :=
  Equiv.sum_comp σ⁻¹ y

theorem sum_bas (c : Fin 2 ⊕ Fin 2) : ∑ i, bas c i = 0 := by
  rcases c with c | c <;> fin_cases c <;> simp [bas, Fin.sum_univ_six] <;> decide

theorem coord_perm6 (σ : Perm (Fin 6)) {y : Fin 6 → ZMod 2}
    (hy : ∑ i, y i = 0) :
    coord (perm6 σ y) = psiMat σ *ᵥ coord y := by
  obtain ⟨t, ht⟩ := decomp y hy
  conv_lhs => rw [ht]
  rw [perm6_add, perm6_smul, perm6_ones, coord_add, coord_smul, coord_ones, smul_zero, add_zero,
    perm6_sum, coord_sum]
  funext r
  simp only [perm6_smul, coord_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, psiMat, Matrix.of_apply]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem psiMat_one : psiMat 1 = 1 := by
  ext r c
  rw [psiMat, Matrix.of_apply, show perm6 1 (bas c) = bas c from rfl, coord_bas]
  simp [Matrix.one_apply, Pi.single_apply]

theorem psiMat_mul (σ τ : Perm (Fin 6)) :
    psiMat (σ * τ) = psiMat σ * psiMat τ := by
  ext r c
  rw [psiMat, Matrix.of_apply, perm6_mul, coord_perm6 σ (by rw [sum_perm6]; exact sum_bas c)]
  rfl

@[expose] def psiHom :
    Perm (Fin 6) →* GL (Fin 2 ⊕ Fin 2) (ZMod 2) where
  toFun σ :=
    { val := psiMat σ
      inv := psiMat σ⁻¹
      val_inv := by rw [← psiMat_mul, mul_inv_cancel, psiMat_one]
      inv_val := by rw [← psiMat_mul, inv_mul_cancel, psiMat_one] }
  map_one' := Units.ext psiMat_one
  map_mul' σ τ := Units.ext (psiMat_mul σ τ)

theorem coe_psiHom (σ : Perm (Fin 6)) :
    ((psiHom σ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      psiMat σ := rfl

theorem psiMat_symplectic : ∀ σ : Perm (Fin 6),
    (psiMat σ)ᵀ * fromBlocks 0 1 (-1) 0 * psiMat σ = fromBlocks 0 1 (-1) 0 :=
  Certificates.certificate7067.2.1

theorem psiMat_eq_one : ∀ σ : Perm (Fin 6), psiMat σ = 1 → σ = 1 :=
  Certificates.certificate7067.2.2.1

theorem stab_fix : ∀ w : Fin 2 ⊕ Fin 2 → ZMod 2,
    (∀ σ : Perm (Fin 6), Perm.sign σ = 1 → psiMat σ *ᵥ Pi.single ι₀ 1 = Pi.single ι₀ 1 →
      psiMat σ *ᵥ w = w) → w = 0 ∨ w = Pi.single ι₀ 1 :=
  Certificates.certificate7067.2.2.2.1

theorem transitive_psiMat :
    ∀ v w : Fin 2 ⊕ Fin 2 → ZMod 2, v ≠ 0 → w ≠ 0 →
    ∃ σ : Perm (Fin 6), Perm.sign σ = 1 ∧ psiMat σ *ᵥ v = w :=
  Certificates.certificate7067.2.2.2.2.1

theorem sign_cyc345 : Perm.sign cyc345 = 1 := by
  rw [cyc345, map_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  rfl

theorem card_fix_cyc345 :
    Fintype.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 // psiMat cyc345 *ᵥ v = v} = 4 ∧
      Fintype.card {v : Fin 2 ⊕ Fin 2 → ZMod 2 // tauMat (psiMat cyc345) *ᵥ v = v} = 1 :=
  Certificates.certificate7067.2.2.2.2.2

end Sp4A6

end H

end CFSG.Quasithin
