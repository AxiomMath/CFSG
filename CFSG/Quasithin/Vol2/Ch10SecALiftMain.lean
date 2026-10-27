module

public import CFSG.Quasithin.Vol2.Ch10SecABasicAut

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem isPGroup_autOn {K W : Subgroup G} (hK : IsPGroup 2 K) : IsPGroup 2 ↥(autOn K W) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hK

noncomputable def autOnHomOf {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    ↥L →* ↥(autOn L W) :=
  ((conjAct W).comp (Subgroup.inclusion hLW)).codRestrict _
    fun l => ⟨Subgroup.inclusion hLW l, l.2, rfl⟩

theorem autOnHomOf_apply {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (l : ↥L) (w : ↥W) :
    (((autOnHomOf hLW l : ↥(autOn L W)) : MulAut ↥W) w : G) = l * w * (l : G)⁻¹ :=
  coe_conjAct_apply' _ w

theorem autOnHomOf_surjective {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    Function.Surjective (autOnHomOf hLW) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem autOn_subgroupOf_eq_map {K L W : Subgroup G} (hKL : K ≤ L)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    (autOn K W).subgroupOf (autOn L W) = (K.subgroupOf L).map (autOnHomOf hLW) := by
  ext φ
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro h
    obtain ⟨g, hgK, hg⟩ := mem_autOn_iff'.mp h
    refine ⟨⟨g, hKL hgK⟩, Subgroup.mem_subgroupOf.mpr hgK, Subtype.ext ?_⟩
    rw [← hg]
    rfl
  · rintro ⟨l, hl, rfl⟩
    exact mem_autOn_iff'.mpr ⟨Subgroup.inclusion hLW l, Subgroup.mem_subgroupOf.mp hl, rfl⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
