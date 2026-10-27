module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocG
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocB
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocD
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocF
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnStd

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.LL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.Quasithin.H13.F431.Un.OL

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem Vx_ab {a b : Xg h} (ha : a ∈ Vx h) (hb : b ∈ Vx h) : a * b = b * a :=
  Subtype.ext (mul_comm_of_mem_miyamotoA1 h (Subgroup.mem_subgroupOf.1 ha).1
    (Subgroup.mem_subgroupOf.1 hb).1)

theorem Vx_sq {a : Xg h} (ha : a ∈ Vx h) : a ^ 2 = 1 := by
  obtain ⟨b, c, d, hb, hd, hax⟩ := (mem_A1 h).1 (Subgroup.mem_subgroupOf.1 ha).1
  rw [pow_two]
  apply Subtype.ext
  show (a : GL (Fin 4) K) * (a : GL (Fin 4) K) = 1
  rw [hax]
  exact miyamotoXGL_A1_mul_self h hb

theorem Ux_le_Vx : Ux h ≤ Vx h := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (ucGL_le h (Subgroup.mem_subgroupOf.1 hx))

theorem z2X_mem_Ux : z2X h ∈ Ux h :=
  Subgroup.mem_subgroupOf.2 ⟨1, map_one _, coe_z2X h⟩

theorem z1X_comm_z2X : z1X h * z2X h = z2X h * z1X h :=
  Vx_ab h (z1X_mem_Vx h) (Ux_le_Vx h (z2X_mem_Ux h))

theorem unStdLoc_miy (hf : 2 ≤ f) :
    UnStdLoc (Xg h) (Psy h) (z1X h) (z2X h) (Vx h) (Ux h) (ZX h) (Kx h) where
  comm := z1X_comm_z2X h
  sylow_t := isSylowTwoOf_Psy_Cx h hf
  V_le := Vx_le_Cx h
  V_aut := fun _ hφ _ hv => aut_Vx h hφ hv
  V_ab := fun _ ha _ hb => Vx_ab h ha hb
  V_sq := fun _ ha => Vx_sq h ha
  z_V := z1X_mem_Vx h
  U_le := Ux_le_Vx h
  U_aut := fun _ hφ _ hu => aut_Ux h hφ hu
  t_U := z2X_mem_Ux h
  K_le := Kx_le_Cx h
  K_perf := Kx_perfect h hf
  V_K := Vx_le_Kx h
  K_cent := fun _ hk _ hu => Ux_central h (Kx_le_Cx h hk) hu
  coset := fun _ hv hvU => coset_Vx h hv hvU
  nonsolv := ⟨N1Fx h, N1Fx_le_Cx h, not_isSolvable_N1Fx h hf, fun L' hL' hcomm => by
    have : L' = ⊥ := eq_bot_iff.2 fun x hx =>
      (N1Fx_faithful h (hL' hx) (hcomm x hx)) ▸ one_mem _
    subst this
    infer_instance⟩
  R_le := ZX_le_Vx h
  R_two := ZX_two h hf
  R_cls := fun _ hr hr1 => ZX_cls h hr hr1
  R_U := fun _ hr hU => ZX_inf_Ux h hr hU
  z_cent := fun _ hy => Psy_cent_z1 h hy
  P_U := fun _ hy _ hu => Ux_central h hy.2 hu

end CFSG.Quasithin.H13.F431.Un.LL
