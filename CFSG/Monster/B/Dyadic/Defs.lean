module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Certificates.Data.Kernel.BabyMonster.LatText
public import Certificates.Data.Kernel.BabyMonster.LatDecode
public import Certificates.Data.CFSGNative.MonsterB.BinaryFiles

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native CFSG.KC.BM.Lat

@[expose] def basisRowsK (_ : Unit := ()) : Array ByteArray := basisRowsOf CFSG.Monster.B.LatText.text

@[expose] def diagExpK (_ : Unit := ()) : Array Nat := diagExpOf CFSG.Monster.B.LatText.text

@[expose] def Bz (t k : ℕ) : ℤ := ((basisRowsK[t]!.get! k).toNat : ℤ)

@[expose] def Bzq : Matrix (Fin 4371) (Fin 4371) ℚ := fun i j => (Bz i j : ℚ)

@[expose] def numer (g t u : ℕ) : ℤ :=
  ((CFSG.Monster.B.Native.packetRows[selIdx g]!)[t]!).foldl
    (fun s e => if e.1 = u then s + e.2 else s) 0

@[expose] def Mq (g : Fin 26) : Matrix (Fin 4371) (Fin 4371) ℚ := fun t u => (numer g t u : ℚ) / 8

@[expose] noncomputable def Cnum (g : Fin 26) : Matrix (Fin 4371) (Fin 4371) ℚ :=
  Bzq * Mq g * Bzq⁻¹

@[expose] noncomputable def Cmat (g : Fin 26) : Matrix (Fin 4371) (Fin 4371) (ZMod 2) :=
  fun i t => ((Cnum g i t).num : ZMod 2)

@[expose] def fvec : Fin 4371 → ZMod 2 := fun j => if fixedVector.testBit j then 1 else 0

@[expose] def pIdx : Fin 4371 := ⟨1197, by norm_num⟩

@[expose] def Pmap : (Fin 4371 → ZMod 2) →ₗ[ZMod 2] (Fin 4370 → ZMod 2) where
  toFun y j := (y + y pIdx • fvec) (pIdx.succAbove j)
  map_add' y z := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' c y := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[expose] noncomputable def Qmat (g : Fin 26) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  fun k t => Cmat g (pIdx.succAbove k) (pIdx.succAbove t) +
    Cmat g (pIdx.succAbove k) pIdx * fvec (pIdx.succAbove t)

end CFSG.Monster.B.Dyadic

end
