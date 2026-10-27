module

public import CFSG.Quasithin.Background.G2UTables
public import CFSG.Quasithin.Background.G2UAdjoint

public section

namespace CFSG.Quasithin.G2U

open Matrix

instance : Finite F9 :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm

@[expose] def cU : GL (Fin 14) (ZMod 2) :=
  (gen0 * gen1) ^ 2

@[expose] def dU : GL (Fin 14) (ZMod 2) :=
  (gen2 * gen3) ^ 2

@[expose] def aU : GL (Fin 14) (ZMod 2) :=
  cU ^ 2

@[expose] def bU : GL (Fin 14) (ZMod 2) :=
  cU ^ 3 * dU

theorem coe_cU : (cU : Matrix (Fin 14) (Fin 14) (ZMod 2)) = dec2 cc := by
  simp only [cU, cc, pow_two, Units.val_mul, dec2_mul2]
  rfl

theorem coe_dU : (dU : Matrix (Fin 14) (Fin 14) (ZMod 2)) = dec2 dc := by
  simp only [dU, dc, pow_two, Units.val_mul, dec2_mul2]
  rfl

theorem coe_aU : (aU : Matrix (Fin 14) (Fin 14) (ZMod 2)) = dec2 ac := by
  simp only [aU, ac, pow_two, Units.val_mul, dec2_mul2, coe_cU]

theorem coe_bU : (bU : Matrix (Fin 14) (Fin 14) (ZMod 2)) = dec2 bc := by
  simp only [bU, bc, pow_succ, pow_zero, one_mul, Units.val_mul, dec2_mul2, coe_cU, coe_dU]

@[expose] def unit3 (m mi : List ℕ) (h1 : mul3 m mi = id3) (h2 : mul3 mi m = id3) :
    GL (Fin 3) F9 :=
  ⟨dec3 m, dec3 mi, by rw [← dec3_mul3, h1, dec3_id3], by rw [← dec3_mul3, h2, dec3_id3]⟩

@[expose] def AU : GL (Fin 3) F9 :=
  unit3 Ac Ac (by decide) (by decide)

@[expose] def BU : GL (Fin 3) F9 :=
  unit3 Bc Bic (by decide) (by decide)

@[expose] def derivedJ : Subgroup (GL (Fin 14) (ZMod 2)) :=
  Subgroup.closure {aU, bU}

@[expose] def unitaryS : Subgroup (GL (Fin 3) F9) :=
  Subgroup.closure {AU, BU}

@[expose] def graphD : Subgroup (GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) :=
  Subgroup.closure {(aU, AU), (bU, BU)}

end CFSG.Quasithin.G2U
