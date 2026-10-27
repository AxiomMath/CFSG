module

public import CFSG.RankThree.PartOne.MB3.LnSevenTwo

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Subgroup

@[expose] def cSL : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨cM, cM_det⟩

@[expose] def fSL : SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨fM, fM_det⟩

theorem coe_cSL_pow (i : ℕ) :
    ((cSL ^ i : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      cM ^ i := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  rfl

theorem orderOf_cSL : orderOf cSL = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine orderOf_eq_prime (Subtype.ext ?_) (fun h => cM_ne_one (congrArg Subtype.val h))
  rw [coe_cSL_pow]
  exact cM_pow_seven

theorem cSL_pow_seven : cSL ^ 7 = 1 := by
  rw [← orderOf_cSL]
  exact pow_orderOf_eq_one cSL

theorem fSL_mul_cSL : fSL * cSL = cSL ^ 2 * fSL := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_cSL_pow]
  exact fM_mul_cM

variable {κ : Type} [Fintype κ] [DecidableEq κ]

@[expose] def D2 : (SpecialLinearGroup (Fin 3) (ZMod 2) × SpecialLinearGroup (Fin 3) (ZMod 2)) →*
    SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) where
  toFun p := ⟨bd2 (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0
      (p.2 : Matrix (Fin 3) (Fin 3) (ZMod 2)), by
    rw [bd2_det, det_fromBlocks_zero₂₁, p.1.2, p.2.2]
    simp⟩
  map_one' := Subtype.ext (by
    show bd2 (↑(1 : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0
      (↑(1 : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1
    simp [bd2])
  map_mul' p q := by
    refine Subtype.ext ?_
    show bd2 (↑(p.1 * q.1) : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0
      (↑(p.2 * q.2) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      bd2 (↑p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 ↑p.2 * bd2 ↑q.1 0 0 ↑q.2
    rw [bd2_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    simp

theorem coe_D2 (p : SpecialLinearGroup (Fin 3) (ZMod 2) × SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((D2 p : SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) :
      Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) =
        bd2 (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 (p.2 : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  rfl

theorem D2_injective : Function.Injective
    (D2 : (SpecialLinearGroup (Fin 3) (ZMod 2) × SpecialLinearGroup (Fin 3) (ZMod 2)) →*
      SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) := by
  intro p q h
  obtain ⟨h1, -, -, h2⟩ := bd2_inj (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

section Reindex

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

@[expose] def slRe (e : X ≃ Y) :
    SpecialLinearGroup X (ZMod 2) →* SpecialLinearGroup Y (ZMod 2) where
  toFun g := ⟨Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e (g : Matrix X X (ZMod 2)), by
    rw [Matrix.det_reindexAlgEquiv]; exact g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := by
    refine Subtype.ext ?_
    show Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e (↑(g * h) : Matrix X X (ZMod 2)) =
      Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e ↑g * Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e ↑h
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul]

theorem coe_slRe (e : X ≃ Y) (g : SpecialLinearGroup X (ZMod 2)) :
    ((slRe e g : SpecialLinearGroup Y (ZMod 2)) : Matrix Y Y (ZMod 2)) =
      Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e (g : Matrix X X (ZMod 2)) := rfl

theorem slRe_trans_symm (e : X ≃ Y) (g : SpecialLinearGroup X (ZMod 2)) :
    slRe e.symm (slRe e g) = g := by
  refine Subtype.ext ?_
  rw [coe_slRe, coe_slRe]
  ext i j
  simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem slRe_symm_trans (e : X ≃ Y) (g : SpecialLinearGroup Y (ZMod 2)) :
    slRe e (slRe e.symm g) = g := by
  refine Subtype.ext ?_
  rw [coe_slRe, coe_slRe]
  ext i j
  simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

@[expose] def slReEquiv (e : X ≃ Y) :
    SpecialLinearGroup X (ZMod 2) ≃* SpecialLinearGroup Y (ZMod 2) :=
  { slRe e with
    invFun := slRe e.symm
    left_inv := slRe_trans_symm e
    right_inv := slRe_symm_trans e }

theorem coe_slReEquiv (e : X ≃ Y) (g : SpecialLinearGroup X (ZMod 2)) :
    ((slReEquiv e g : SpecialLinearGroup Y (ZMod 2)) : Matrix Y Y (ZMod 2)) =
      Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e (g : Matrix X X (ZMod 2)) := rfl

end Reindex

end CFSG.RankThree.PartOne.MB3
