module

public import CFSG.Quasithin.H13.A6S1372SixteenTilde

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Quot

variable {H : Subgroup G} (hH : H ∈ S.Hz)
include hH

theorem UH_le_H : conjClosure S.V3 H ≤ H :=
  conjClosure_le fun _ hh _ hv => H.mul_mem (H.mul_mem hh
    ((((S.V3_le_V).trans (S.V_le_T.trans (le_sup_right.trans hH.1.1))) hv))) (H.inv_mem hh)

theorem normal_V1_subgroupOf : ((fsuV1 T V).subgroupOf H).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (hH.2.1.trans S.G1_le_normalizer_V1)

variable [IsMulCommutative ↥(conjClosure S.V3 H)] [((fsuV1 T V).subgroupOf H).Normal]

@[expose] noncomputable def secEmb :
    Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) →*
      ↥H ⧸ (fsuV1 T V).subgroupOf H :=
  QuotientGroup.lift _ ((QuotientGroup.mk' ((fsuV1 T V).subgroupOf H)).comp
    ((Subgroup.inclusion (UH_le_H hH)).comp (⊤ : Subgroup ↥(conjClosure S.V3 H)).subtype))
    (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
      exact hx)

theorem secEmb_secMk (u : ↥(conjClosure S.V3 H)) :
    secEmb hH (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
      QuotientGroup.mk (⟨u, UH_le_H hH u.2⟩ : ↥H) := rfl

theorem secEmb_injective : Function.Injective (secEmb hH) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ s
  rw [secEmb_secMk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hs
  rw [A6Mod.secMk_eq_one_iff]
  exact hs

theorem secEmb_secAct (h : ↥H)
    (s : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :
    secEmb hH (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) h s) =
      (h : ↥H ⧸ (fsuV1 T V).subgroupOf H) * secEmb hH s *
        (h : ↥H ⧸ (fsuV1 T V).subgroupOf H)⁻¹ := by
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ s
  rw [A6Mod.secAct_secMk, secEmb_secMk, secEmb_secMk, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1

end Quot

end Setting4

end CFSG.Quasithin.H13.A6
