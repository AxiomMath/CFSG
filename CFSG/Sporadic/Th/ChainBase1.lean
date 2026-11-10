
module


public import CFSG.Sporadic.Th.IndexBase1

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Pointwise

noncomputable def xJ : J := wordG (pairLetters a b) xWord

noncomputable def yJ : J := wordG (pairLetters a b) yWord

noncomputable def z0J :
    J := wordG (pairLetters xJ yJ) zWord0

noncomputable def z1J :
    J := wordG (pairLetters xJ yJ) zWord1

noncomputable def H :
    Subgroup J := Subgroup.closure {xJ, yJ}

noncomputable def L :
    Subgroup J := Subgroup.closure {z0J, z1J}

theorem xJ_mem_H :
    xJ ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)

theorem yJ_mem_H :
    yJ ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem z0J_mem_H :
    z0J ∈ H := wordG_mem H (pairLetters_mem H xJ_mem_H yJ_mem_H) _

theorem z1J_mem_H :
    z1J ∈ H := wordG_mem H (pairLetters_mem H xJ_mem_H yJ_mem_H) _

theorem L_le_H : L ≤ H := by
  rw [L, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact z0J_mem_H
  · exact z1J_mem_H

section TreeOrbit

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

section Data

variable {g₁ g₂ : G} {m r : ℕ} {pts lk : ℕ → ℕ} {pl : Table}

end Data

end TreeOrbit

section Reps

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem rep_a : Rep nX alphaT a := rep_alpha hC.orbit

theorem rep_b : Rep nX betaT b := rep_beta hC.orbit

theorem rep_a_inv :
    Rep nX alphaT a⁻¹ := (rep_a hC).inv_of_invoOK hC.aInvo

theorem rep_b_inv :
    Rep nX betaInvT b⁻¹ := (rep_b hC).inv_of_invOK hC.bInv

theorem rep_x : Rep nX mxT xJ :=
  Rep.wordT (nX_lt hC) xWord (rep_wordLetters (rep_a hC) (rep_a_inv hC) (rep_b hC)
    (rep_b_inv hC) xWord_ok)

theorem rep_y : Rep nX myT yJ :=
  Rep.wordT (nX_lt hC) yWord (rep_wordLetters (rep_a hC) (rep_a_inv hC) (rep_b hC)
    (rep_b_inv hC) yWord_ok)

theorem rep_x_inv :
    Rep nX mxT xJ⁻¹ := (rep_x hC).inv_of_invoOK hC.tables.xInvo

theorem rep_y_inv :
    Rep nX myiT yJ⁻¹ := (rep_y hC).inv_of_invOK hC.tables.yInv

theorem rep_z0 : Rep nX mz0T z0J :=
  Rep.wordT (nX_lt hC) zWord0 (rep_wordLetters (rep_x hC) (rep_x_inv hC) (rep_y hC)
    (rep_y_inv hC) zWord0_ok)

theorem rep_z1 : Rep nX mz1T z1J :=
  Rep.wordT (nX_lt hC) zWord1 (rep_wordLetters (rep_x hC) (rep_x_inv hC) (rep_y hC)
    (rep_y_inv hC) zWord1_ok)

theorem rep_z0_inv :
    Rep nX mz0iT z0J⁻¹ := (rep_z0 hC).inv_of_invOK hC.tables.z0Inv

theorem rep_z1_inv :
    Rep nX mz1iT z1J⁻¹ := (rep_z1 hC).inv_of_invOK hC.tables.z1Inv

theorem rep_chain_inv0 :
    ∀ s, Rep nX (chainT.inv0 s) (lettersG xJ yJ s)⁻¹ :=
  rep_letters_inv (rep_x_inv hC) (rep_y_inv hC)

theorem rep_chain_inv1 :
    ∀ s, Rep nX (chainT.inv1 s) (lettersG z0J z1J s)⁻¹ :=
  rep_letters_inv (rep_z0_inv hC) (rep_z1_inv hC)

theorem rep_xy_letters :
    ∀ s, Rep nX (letters mxT myT s) (lettersG xJ yJ s) :=
  Rep.letters (rep_x hC) (rep_y hC)

theorem rep_z_letters :
    ∀ s, Rep nX (letters mz0T mz1T s) (lettersG z0J z1J s) :=
  Rep.letters (rep_z0 hC) (rep_z1 hC)

end Reps

end CFSG.Sporadic.Th
