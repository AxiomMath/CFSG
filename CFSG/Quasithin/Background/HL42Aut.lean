module

public import CFSG.Quasithin.Background.HL42Data
public import CFSG.Quasithin.Background.HA7Rec

public section

namespace CFSG.Quasithin

namespace H

namespace L4

open Matrix Equiv
open scoped Matrix

@[expose] def dual4 : GL (Fin 4) (ZMod 2) ≃* GL (Fin 4) (ZMod 2) where
  toFun g := ⟨((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ,
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩
  invFun g := ⟨((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ,
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩
  left_inv g := Units.ext (Matrix.transpose_transpose _)
  right_inv g := Units.ext (Matrix.transpose_transpose _)
  map_mul' g h := Units.ext (by
    change (((g * h)⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ =
      ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *
        ((h⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

theorem coe_dual4 (g : GL (Fin 4) (ZMod 2)) :
    ((dual4 g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ :=
  rfl

theorem dual4_not_inner
    : ¬ ∃ c : GL (Fin 4) (ZMod 2), ∀ g, dual4 g = c * g * c⁻¹ := by
  rintro ⟨c, hc⟩
  set w : Fin 4 → ZMod 2 := (c : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1 with hw
  have hcc : ∀ v, ((c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      ((c : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hw0 : w ≠ 0 := by
    intro h
    have h1 := hcc (Pi.single 0 1)
    rw [← hw, h, Matrix.mulVec_zero] at h1
    have h2 := congrFun h1 0
    simp at h2
  apply hw0
  refine eq_zero_of_fix_single w fun i j hj hij => ?_
  let t : GL (Fin 4) (ZMod 2) := ⟨1 + Matrix.single i j 1, 1 + Matrix.single i j 1,
    single_mul_self i j hij, single_mul_self i j hij⟩
  have ht : ((dual4 t : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      1 + Matrix.single j i 1 := single_transpose i j
  have h2 := congrArg (fun g : GL (Fin 4) (ZMod 2) =>
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w) (hc t)
  rw [ht] at h2
  rw [h2, hw, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hcc]
  change (c : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ ((1 + Matrix.single i j 1) *ᵥ Pi.single 0 1) = _
  rw [single_mulVec_e0 i j hj]

@[expose] noncomputable def alpha8 : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2) :=
  MulEquiv.ofBijective B5FinS8.alphaHom B5FinS8.alphaHom_bijective

theorem exists_aut4
    (β : MulAut (GL (Fin 4) (ZMod 2))) : ∃ c : GL (Fin 4) (ZMod 2),
    (∀ g, β g = c * g * c⁻¹) ∨ ∀ g, β g = c * dual4 g * c⁻¹ := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
    (by norm_num)
  obtain ⟨π, hπ⟩ := hb.2 (alpha8.trans (β.trans alpha8.symm))
  obtain ⟨ρ, hρ⟩ := hb.2 (alpha8.trans (dual4.trans alpha8.symm))
  have hβ : ∀ σ, β (alpha8 σ) =
      alpha8 (MulAut.conjNormal (H := alternatingGroup (Fin 8)) π σ) := by
    intro σ
    have h := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) => alpha8 (f σ)) hπ
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hd : ∀ σ, dual4 (alpha8 σ) =
      alpha8 (MulAut.conjNormal (H := alternatingGroup (Fin 8)) ρ σ) := by
    intro σ
    have h := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) => alpha8 (f σ)) hρ
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hρodd : Perm.sign ρ = -1 := by
    rcases Int.units_eq_one_or (Perm.sign ρ) with h | h
    · exfalso
      apply dual4_not_inner
      refine ⟨alpha8 ⟨ρ, Equiv.Perm.mem_alternatingGroup.mpr h⟩, fun g => ?_⟩
      obtain ⟨σ, rfl⟩ := alpha8.surjective g
      rw [hd, ← map_inv, ← map_mul, ← map_mul]
      congr 1
    · exact h
  rcases Int.units_eq_one_or (Perm.sign π) with hs | hs
  · refine ⟨alpha8 ⟨π, Equiv.Perm.mem_alternatingGroup.mpr hs⟩, Or.inl fun g => ?_⟩
    obtain ⟨σ, rfl⟩ := alpha8.surjective g
    rw [hβ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  · have hs' : Perm.sign (π * ρ⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, hρodd]
      rfl
    refine ⟨alpha8 ⟨π * ρ⁻¹, Equiv.Perm.mem_alternatingGroup.mpr hs'⟩, Or.inr fun g => ?_⟩
    obtain ⟨σ, rfl⟩ := alpha8.surjective g
    rw [hβ, hd, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    group

theorem card_mulAut_GL_four : Nat.card (MulAut (GL (Fin 4) (ZMod 2))) = 40320 := by
  rw [← Nat.card_congr (MulAut.congr alpha8).toEquiv,
    ← Nat.card_congr (Equiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
        (by norm_num))),
    Nat.card_perm, Nat.card_fin]
  rfl

@[expose] noncomputable def slEquivGL :
    Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ≃* GL (Fin 4) (ZMod 2) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).trans B5FinS8.slEquiv

theorem card_mulAut_SL_four : Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) ≤
    2 * Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rw [Nat.card_congr (MulAut.congr slEquivGL).toEquiv, Nat.card_congr slEquivGL.toEquiv,
    card_mulAut_GL_four, A7.card_GL_four]

end L4

end H

end CFSG.Quasithin
