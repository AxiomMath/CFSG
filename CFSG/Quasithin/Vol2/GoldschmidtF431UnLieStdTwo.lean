module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieBridgeB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieMapA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un.OL

section Datum

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 f)) [Fact ((ζ : F) ≠ 0)]

theorem stdTwo_datum (hf : 1 ≤ f) :
    Lift.StdTwo (SU (unitaryInvolution F 2 f) 4) (unU hF 4) (unSystem hF ζ).P₂ (unSystem hF ζ).P₁
      (zUn hF) (tUn hF) := by
  have := stdTwo_map (brEps hF hf) (stdTwo_Xg (brFD hF hf))
  rwa [brEps_map_Psy hF hf, brEps_map_Pt hF hf ζ, brEps_map_Ln hF hf ζ, brEps_z1X hF hf,
    brEps_z2X hF hf] at this

end Datum

end CFSG.Quasithin.H13.F431.Un
