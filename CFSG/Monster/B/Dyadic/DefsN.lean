module

public import CFSG.Monster.B.Dyadic.Defs
public import CFSG.Certificates.Kernel.BabyMonster.PktSound
public import CFSG.Certificates.Kernel.BabyMonster.Dyadic.Gens

public section

namespace CFSG.Monster.B.Dyadic

@[expose] def MqN (N : ℕ → ℕ → ℤ) : Matrix (Fin 4371) (Fin 4371) ℚ := fun t u => (N t u : ℚ) / 8

@[expose] noncomputable def CnumN (N : ℕ → ℕ → ℤ) : Matrix (Fin 4371) (Fin 4371) ℚ :=
  Bzq * MqN N * Bzq⁻¹

@[expose] noncomputable def CmatN (N : ℕ → ℕ → ℤ) : Matrix (Fin 4371) (Fin 4371) (ZMod 2) :=
  fun i t => ((CnumN N i t).num : ZMod 2)

theorem Cnum_eq (g : Fin 26) : Cnum g = CnumN (numer g) := rfl

theorem Cmat_eq (g : Fin 26) : Cmat g = CmatN (numer g) := rfl

@[expose] noncomputable def numer26 (t u : ℕ) : ℤ :=
  CFSG.KC.BM.Pkt.kNumMono (CFSG.KC.BM.nthN CFSG.KC.BM.Dyadic.G26.b0 0) t u

@[expose] noncomputable def Mq26 : Matrix (Fin 4371) (Fin 4371) ℚ := MqN numer26

end CFSG.Monster.B.Dyadic

end
