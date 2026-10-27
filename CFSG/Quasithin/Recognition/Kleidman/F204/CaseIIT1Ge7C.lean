module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.EmptyFaithful.S152XA5
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin
public import CFSG.Quasithin.MS93.S46I469Grp
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Transv

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_ne_one_centralizer {p : ℕ} [Fact p.Prime] {P R : Subgroup G} (hP : IsPGroup p P)
    (hRP : R ≤ P) (hRn : P ≤ Subgroup.normalizer (R : Set G)) (hR : R ≠ ⊥) :
    ∃ r ∈ R, r ≠ 1 ∧ r ∈ Subgroup.centralizer (P : Set G) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have : (R.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mpr hRn
  have hR' : R.subgroupOf P ≠ ⊥ := by
    intro h
    apply hR
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRP hr⟩ : P) ∈ R.subgroupOf P := Subgroup.mem_subgroupOf.mpr hr
    rw [h, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hR'
  obtain ⟨⟨x, hxR, hxZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hxR, fun h1 => hx1 (Subtype.ext (Subtype.ext h1)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have := Subgroup.mem_center_iff.mp hxZ ⟨g, hg⟩
  exact congrArg Subtype.val this

@[expose] def commMap {Z : Subgroup G} (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {k : G}
    (hk : k ∈ Subgroup.normalizer (Z : Set G)) : ↥Z →* ↥Z where
  toFun z := ⟨k * z * k⁻¹ * (z : G)⁻¹,
    Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hk z).mp z.2) (Z.inv_mem z.2)⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    have ha := (Subgroup.mem_normalizer_iff.mp hk a).mp a.2
    have hb := (Subgroup.mem_normalizer_iff.mp hk b).mp b.2
    show k * ((a : G) * b) * k⁻¹ * ((a : G) * b)⁻¹ =
      (k * a * k⁻¹ * (a : G)⁻¹) * (k * b * k⁻¹ * (b : G)⁻¹)
    have e1 := hZ _ ha _ (Z.inv_mem b.2)
    have e2 := hZ _ (Z.inv_mem a.2) _ (Z.mul_mem hb (Z.inv_mem b.2))
    calc k * ((a : G) * b) * k⁻¹ * ((a : G) * b)⁻¹
        = (k * a * k⁻¹) * ((k * b * k⁻¹) * (b : G)⁻¹) * (a : G)⁻¹ := by group
      _ = (k * a * k⁻¹) * ((a : G)⁻¹ * ((k * b * k⁻¹) * (b : G)⁻¹)) := by rw [mul_assoc, e2]
      _ = _ := by group

theorem commMap_apply {Z : Subgroup G} (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {k : G}
    (hk : k ∈ Subgroup.normalizer (Z : Set G)) (z : ↥Z) :
    ((commMap hZ hk z : ↥Z) : G) = k * z * k⁻¹ * (z : G)⁻¹ := rfl

end CFSG.Quasithin.Kleidman.F204
