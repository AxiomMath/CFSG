module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocH
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieBrA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

section Main

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] (hF : Nat.card F = (2 ^ f) ^ 2)
  (hf : 2 ≤ f)

@[expose] def unVL : Subgroup (SU (unitaryInvolution F 2 f) 4) :=
  (LL.Vx (brFD hF (one_le_two.trans hf))).map (brEps hF (one_le_two.trans hf)).toMonoidHom

@[expose] def unUcL : Subgroup (SU (unitaryInvolution F 2 f) 4) :=
  (LL.Ux (brFD hF (one_le_two.trans hf))).map (brEps hF (one_le_two.trans hf)).toMonoidHom

@[expose] def unRL : Subgroup (SU (unitaryInvolution F 2 f) 4) :=
  (OL.ZX (brFD hF (one_le_two.trans hf))).map (brEps hF (one_le_two.trans hf)).toMonoidHom

@[expose] def unKL : Subgroup (SU (unitaryInvolution F 2 f) 4) :=
  (LL.Kx (brFD hF (one_le_two.trans hf))).map (brEps hF (one_le_two.trans hf)).toMonoidHom

theorem unStdLoc_datum :
    UnStdLoc (SU (unitaryInvolution F 2 f) 4) (unU hF 4) (zUn hF) (tUn hF)
      (unVL hF hf) (unUcL hF hf) (unRL hF hf) (unKL hF hf) := by
  have h1 : 1 ≤ f := one_le_two.trans hf
  have := LL.UnStdLoc.map (brEps hF h1) (LL.unStdLoc_miy (brFD hF h1) hf)
  rwa [brEps_map_Psy hF h1, brEps_z1X hF h1, brEps_z2X hF h1] at this

end Main

end CFSG.Quasithin.H13.F431.Un
