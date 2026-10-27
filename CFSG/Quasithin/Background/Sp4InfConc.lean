module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public meta import Mathlib.Algebra.Field.ZMod
public import CFSG.Quasithin.Background.Sp4InfConcInputs
public import Certificates.Certificate8068

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H Matrix
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp)

@[expose] def aMinv : Matrix I4 I4 (ZMod 2) := mk4 ![![1, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1]]

@[expose] def bMinv : Matrix I4 I4 (ZMod 2) := mk4 ![![0, 1, 1, 0], ![1, 1, 1, 1], ![0, 1, 0, 1], ![0, 0, 1, 0]]

theorem aM_mul_inv : aM * aMinv = 1 := by decide

theorem aMinv_mul : aMinv * aM = 1 := by decide

theorem bM_mul_inv : bM * bMinv = 1 := by decide

theorem bMinv_mul : bMinv * bM = 1 := by decide

@[expose] def aGL : GL I4 (ZMod 2) := ⟨aM, aMinv, aM_mul_inv, aMinv_mul⟩

@[expose] def bGL : GL I4 (ZMod 2) := ⟨bM, bMinv, bM_mul_inv, bMinv_mul⟩

theorem aGL_mem : aGL ∈ StatedSp 2 (ZMod 2) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  change aMᵀ * Matrix.fromBlocks 0 1 (-1) 0 * aM = Matrix.fromBlocks 0 1 (-1) 0
  decide

theorem bGL_mem : bGL ∈ StatedSp 2 (ZMod 2) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  change bMᵀ * Matrix.fromBlocks 0 1 (-1) 0 * bM = Matrix.fromBlocks 0 1 (-1) 0
  decide

@[expose] def aSp : StatedSp 2 (ZMod 2) := ⟨aGL, aGL_mem⟩

@[expose] def bSp : StatedSp 2 (ZMod 2) := ⟨bGL, bGL_mem⟩

theorem coe_aSp : (((aSp : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) : Matrix I4 I4 (ZMod 2)) = aM := rfl

theorem coe_bSp : (((bSp : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) : Matrix I4 I4 (ZMod 2)) = bM := rfl

theorem aM_pow_three : aM ^ 3 = 1 := by decide +kernel

theorem bM_pow_five : bM ^ 5 = 1 := by decide +kernel

theorem aSp_pow_three : aSp ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_aSp, aM_pow_three]
  rfl

theorem bSp_pow_five : bSp ^ 5 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_bSp, bM_pow_five]
  rfl

theorem commutant_ab :
    ∀ M : Matrix I4 I4 (ZMod 2), M * aM = aM * M → M * bM = bM * M →
    M = 0 ∨ M = 1 :=
  Certificates.certificate8068

@[expose] def tauAM : Matrix I4 I4 (ZMod 2) :=
  mk4 ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 0, 0, 1]]

theorem coe_tau_aSp : (((tauSp aSp : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) :
    Matrix I4 I4 (ZMod 2)) = tauAM := by
  rw [coe_tauSp, coe_aSp]
  decide

theorem card_fix_eq (g : GL I4 (ZMod 2)) :
    Nat.card {v : StdMod I4 (ZMod 2) // matAut g v = v} =
      Nat.card {w : I4 → ZMod 2 // (g : Matrix I4 I4 (ZMod 2)) *ᵥ w = w} :=
  Nat.card_congr
    { toFun := fun v => ⟨Multiplicative.toAdd v.1, congrArg Multiplicative.toAdd v.2⟩
      invFun := fun w => ⟨Multiplicative.ofAdd w.1, congrArg Multiplicative.ofAdd w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_fix_aM : Nat.card {w : I4 → ZMod 2 // aM *ᵥ w = w} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem card_fix_tauAM : Nat.card {w : I4 → ZMod 2 // tauAM *ᵥ w = w} = 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem card_fix_aSp : Nat.card {v : StdMod I4 (ZMod 2) //
    matAut ((aSp : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) v = v} = 4 := by
  rw [card_fix_eq]
  exact card_fix_aM

theorem card_fix_tau_aSp : Nat.card {v : StdMod I4 (ZMod 2) //
    matAut ((tauSp aSp : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) v = v} = 1 := by
  rw [card_fix_eq, coe_tau_aSp]
  exact card_fix_tauAM

end Sp4Inf

end CFSG.Quasithin
