module

public import CFSG.Quasithin.EmptyFaithful.S153PDef
public import CFSG.Quasithin.EmptyFaithful.S153PE1
public import CFSG.Quasithin.EmptyFaithful.S153E56A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace S153P

namespace PE

section Abs

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

theorem abs56_of_hypsA (H : HypsA cx N₁ N₂ g s y) {z : G} (hz : S153E56e.ZGen T z) :
    Abs56 (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) Mc z y where
  Z_eq := hz.eq
  z_ne := hz.ne
  z_sq := hz.sq
  Mc_eq := S153E56e.Mc_eq cx
  U_norm := fun _ hh _ hu => S153E.U_conj_mem hh hu
  z_mem := S153E56a.Z_le_U cx hz.mem
  U_comm := fun _ hu _ hv => S153E.commutator_U_mem cx hu hv
  U_sq := fun _ hu => S153E.sq_U_mem cx hu
  U_center := fun _ hu h => S153E56a.orth_nondeg cx H.c.h55.1 hu h
  Z_central := fun _ hu => (S153E56a.Z_comm_U cx hz.mem hu).symm
  zp_mem := zp_mem_U H hz
  zp_ne := zp_ne H hz
  yz := yz_eq H hz

end Abs

end PE

end S153P

end CFSG.Quasithin
