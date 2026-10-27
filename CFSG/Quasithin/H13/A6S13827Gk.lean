module

public import CFSG.Quasithin.H13.A6S13824f
public import CFSG.Quasithin.H13.A6S13827Gi

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom CFSG.Quasithin.B42U33
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem comm_mem_inf_Dγ (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) {X : Subgroup G} (hX : X = S.V3 ∨ X = V)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) {f x : G}
    (hf : f ∈ F8.Uγ S.V3 H (g : G)) (hx : x ∈ conjClosure X H) :
    f * x * f⁻¹ * x⁻¹ ∈ conjClosure X H ⊓ F8.Dγ S.V3 (fsuV1 T V) H (g : G) := by
  have hF := hd.hF
  have h1 : f * x * f⁻¹ * x⁻¹ ∈ conjClosure X H ⊓ F8.Uγ S.V3 H (g : G) := by
    have hc := hF.F913_3 s (X := X) (Y := S.V3) (hX.imp id id) (Or.inl rfl)
    refine hc ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hf hx
  have hXV : conjClosure X H ≤ conjClosure V H := by
    rcases hX with rfl | rfl
    · exact conjClosure_mono S.V3_le_V le_rfl
    · exact le_rfl
  have hVQ := S.VH_le_QH hd.hS.hNS h13315 h1356two hd.hH hF.F911_3
  refine ⟨h1.1, ?_⟩
  rw [hF.Dγ_eq_inf_pCoreOf s]
  exact ⟨h1.2, hVQ (hXV h1.1)⟩

theorem eight_le_card_UH_inf_Dγ (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) [IsMulCommutative ↥(conjClosure S.V3 H)] {W : Subgroup G}
    (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) {γ γ' : F8.Geom T L H}
    {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (h8 : 8 ≤ Nat.card (commV (autSec (autOn (F8.Uγ S.V3 H (g : G)) (conjClosure S.V3 H)) ⊤
      (W.subgroupOf (conjClosure S.V3 H))))) :
    8 ≤ Nat.card ↥(conjClosure S.V3 H ⊓ F8.Dγ S.V3 (fsuV1 T V) H (g : G)) := by
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  have h1 := hsU.card_commV_le (hd.hF.Uγ_le_H s) inf_le_left fun f hf x hx =>
    hd.comm_mem_inf_Dγ h13315 h1356two (Or.inl rfl) s hf hx
  exact h8.trans (h1.trans (Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)))

theorem eight_le_relIndex_VH_u33
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h13314 : Stmt13_3_14)
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) [IsMulCommutative ↥(conjClosure S.V3 H)] {W : Subgroup G}
    (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) (h64 : W.relIndex (conjClosure S.V3 H) = 2 ^ 6)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (h8 : 8 ≤ Nat.card (commV (autSec (autOn (F8.Uγ S.V3 H (g : G)) (conjClosure S.V3 H)) ⊤
      (W.subgroupOf (conjClosure S.V3 H))))) :
    8 ≤ (conjClosure S.V3 H).relIndex (conjClosure V H ⊓ F8.Dγ S.V3 (fsuV1 T V) H (g : G)) := by
  have hF := hd.hF
  have : IsMulCommutative ↥(conjClosure V H) := hF.F911_2.1
  have hVc : ∀ a ∈ conjClosure V H, ∀ b ∈ conjClosure V H, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(conjClosure V H)) ⟨b, hb⟩)
  have hUV : conjClosure S.V3 H ≤ conjClosure V H := conjClosure_mono S.V3_le_V le_rfl
  have hKnt := hd.knt_VH h13315 h1356two h13314
  obtain ⟨W₁, W₂, hUW₁, hW₁W₂, hW₂V, hHW₁, hHW₂, hirr, hKnt₂⟩ :=
    exists_chief_sec hd.hKH (perfect_of_mem_cComp hd.hK) hUV hVc (le_normalizer_conjClosure _ _)
      (le_normalizer_conjClosure _ _) hKnt
  have hs₂ := hd.secV h13315 h1356two h13314 hUW₁ hW₁W₂.le hW₂V hHW₂ hHW₁ hKnt₂
  have : IsMulCommutative ↥W₂ := ⟨⟨fun a b => Subtype.ext (hVc a (hW₂V a.2) b (hW₂V b.2))⟩⟩
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have h8₂ := hs₂.eight_le_card_commV_of_chief hU hirr (hF.Uγ_le_H s) (hd.not_Uγ_le s hDγ)
    (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _) hsU h64 h8
  have h1 := hs₂.card_commV_le (Y := W₂ ⊓ (conjClosure V H ⊓ F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (hF.Uγ_le_H s) inf_le_left fun f hf x hx => by
      refine ⟨?_, hd.comm_mem_inf_Dγ h13315 h1356two (Or.inr rfl) s hf (hW₂V hx)⟩
      have hfx : f * x * f⁻¹ ∈ W₂ :=
        (Subgroup.mem_normalizer_iff.mp (hHW₂ (hF.Uγ_le_H s hf)) x).mp hx
      exact W₂.mul_mem hfx (W₂.inv_mem hx)
  calc 8 ≤ _ := h8₂
    _ ≤ W₁.relIndex (W₂ ⊓ (conjClosure V H ⊓ F8.Dγ S.V3 (fsuV1 T V) H (g : G))) := h1
    _ ≤ (conjClosure S.V3 H).relIndex
          (W₂ ⊓ (conjClosure V H ⊓ F8.Dγ S.V3 (fsuV1 T V) H (g : G))) :=
        Subgroup.relIndex_le_of_le_left hUW₁ (relIndex_ne_zero' _ _)
    _ ≤ (conjClosure S.V3 H).relIndex (conjClosure V H ⊓ F8.Dγ S.V3 (fsuV1 T V) H (g : G)) :=
        Subgroup.relIndex_le_of_le_right inf_le_right (relIndex_ne_zero' _ _)

end DK

end Setting4

end CFSG.Quasithin.H13.A6
