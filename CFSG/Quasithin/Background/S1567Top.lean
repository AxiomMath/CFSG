module

public import CFSG.Quasithin.Background.S1567Q
public import CFSG.Quasithin.Background.S1567BYE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace S1567

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

theorem res15367Rest_of_index (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hY : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (YE153 Mc M E : Set G))
    (hidx : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3) :
    Res15367Rest T Mc M E where
  R_eq := R_eq_of_index k hidx
  M_eq := M_eq_of_index h113 k hidx
  GE_eq := GE_eq_153 k hidx
  XE_not_le := XE_not_le_153 k hidx
  XE_quot := XE_quot_153 k hidx
  YE_quot := YE_quot h113 k.c k.L k.r66
  YE_normal := hY
  XE_normal := XE_normal_153 E
  quot_S3S3 := quot_S3S3_153 h113 k hidx
  XE_comm := XE_comm_153 h113 k hidx

end S1567

theorem stage15367Rest_of_steps (h113 : StageLemma14113) (hY : Step67Normal)
    (hI : Step67Index) : Stage15367Rest := by
  intro G _ _ T Mc M V₁ V₂ E t c r45 r46 r49 r50 L r66 r2
  have k : Ctx67 G T Mc M V₁ V₂ E t := ⟨c, r45, r46, r49, r50, L, r66, r2⟩
  exact S1567.res15367Rest_of_index h113 k (hY G T Mc M V₁ V₂ E t k) (hI G T Mc M V₁ V₂ E t k)

end CFSG.Quasithin
