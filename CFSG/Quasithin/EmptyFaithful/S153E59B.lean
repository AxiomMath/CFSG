module

public import CFSG.Quasithin.EmptyFaithful.S153E51A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem card_Z (cx : Ctx15350 T Mc M V₁ V₂ t) : Nat.card (quasithinOmegaOneCenter T) = 2 :=
  cx.hF.card_V₁

theorem Z_le_U (cx : Ctx15350 T Mc M V₁ V₂ t) : quasithinOmegaOneCenter T ≤ UH153 T M V₁ Mc :=
  (S153E.Z_le_ZS cx).trans (S153E.ZS_le_U cx)

theorem Z_central (cx : Ctx15350 T Mc M V₁ V₂ t) {h z : G} (hh : h ∈ Mc)
    (hz : z ∈ quasithinOmegaOneCenter T) : h * z = z * h := by
  have := Subgroup.mem_centralizer_iff.mp (cx.hF.H_le_centralizer hh) z hz
  exact this.symm

theorem centralizer_Z_eq (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = Mc :=
  le_antisymm cx.c.hyp.qtfe.centralizer_le_mc cx.hF.H_le_centralizer

theorem commutator_U {cx : Ctx15350 T Mc M V₁ V₂ t} {a b : G} (ha : a ∈ UH153 T M V₁ Mc)
    (hb : b ∈ UH153 T M V₁ Mc) : a * b * a⁻¹ * b⁻¹ ∈ quasithinOmegaOneCenter T :=
  S153E.commutator_U_mem cx ha hb

end Basic

section Inclusions

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem U_le_Mc (cx : Ctx15350 T Mc M V₁ V₂ t) : UH153 T M V₁ Mc ≤ Mc :=
  (S153E.U_le_T cx).trans (S153E.T_le_Mc cx)

theorem VZ_le_Mc (cx : Ctx15350 T Mc M V₁ V₂ t) : VZ T M ≤ Mc :=
  (cx.c.hyp.VZ_le_T).trans (S153E.T_le_Mc cx)

end Inclusions

end S153E59

end CFSG.Quasithin
