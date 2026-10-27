module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnSystem
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNRad

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431 Matrix
open scoped commutatorElement

section Elements

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)

@[expose] def zUn (_hF : Nat.card F = (2 ^ f) ^ 2) : SU (unitaryInvolution F 2 f) 4 :=
  longRootHom (unitaryInvolution F 2 f) (i := (0 : Fin 4)) (by decide)
    (Multiplicative.ofAdd
      ⟨1, show (1 : F) + unitaryInvolution F 2 f 1 = 0 by
        rw [map_one]; exact CharTwo.add_self_eq_zero 1⟩)

@[expose] def tUn (hF : Nat.card F = (2 ^ f) ^ 2) : SU (unitaryInvolution F 2 f) 4 :=
  rootHom (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) (i := (0 : Fin 4))
    (j := (2 : Fin 4)) (by decide) (by decide) (by decide) (Multiplicative.ofAdd (1 : F))

theorem coe_zUn : (((zUn hF : SU (unitaryInvolution F 2 f) 4) : GL (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = 1 + single 0 3 1 := rfl

theorem coe_tUn : (((tUn hF : SU (unitaryInvolution F 2 f) 4) : GL (Fin 4) F) :
    Matrix (Fin 4) (Fin 4) F) = 1 + single 0 2 1 + single 1 3 1 := by
  show rootMatrix (unitaryInvolution F 2 f) (0 : Fin 4) 2 1 = _
  rw [rootMatrix, map_one, CharTwo.sub_eq_add]
  rfl

end Elements

section V4

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 f)) [Fact ((ζ : F) ≠ 0)]

@[expose] def v4Un : Subgroup (SU (unitaryInvolution F 2 f) 4) := BN.Uplus (unSystem hF ζ) true

end V4

end CFSG.Quasithin.H13.F431.Un
