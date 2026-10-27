module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBGroupAbs
public import CFSG.Quasithin.Background.RonanD33

public section

namespace CFSG.Quasithin.H13.L827X.LBCaseAGBase

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L827X.LBDefs
  CFSG.Quasithin.H13.L827X.LBGroupAbs
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjXEquiv (X : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    ↥X ≃* ↥X where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2⟩
  invFun x := ⟨g⁻¹ * x * g⁻¹⁻¹,
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) (x : G)).mp x.2⟩
  left_inv x := Subtype.ext (by
    show g⁻¹ * (g * (x : G) * g⁻¹) * g⁻¹⁻¹ = (x : G)
    group)
  right_inv x := Subtype.ext (by
    show g * (g⁻¹ * (x : G) * g⁻¹⁻¹) * g⁻¹ = (x : G)
    group)
  map_mul' x y := Subtype.ext (by
    show g * ((x : G) * (y : G)) * g⁻¹ = (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
    group)

theorem conjXEquiv_coe (X : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (x : ↥X) : ((conjXEquiv X hg x : ↥X) : G) = g * (x : G) * g⁻¹ :=
  rfl

theorem conj_mem_pCoreOf_of_mem_normalizer {X : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ pCoreOf 2 X) :
    g * x * g⁻¹ ∈ pCoreOf 2 X := by
  obtain ⟨hxX, hxp⟩ := CFSG.Quasithin.RonanD33.mem_pCoreOf.mp hx
  have hchar : (CFSG.pCore 2 ↥X).Characteristic := inferInstance
  have hmap := Subgroup.characteristic_iff_map_eq.mp hchar (conjXEquiv X hg)
  have h1 : conjXEquiv X hg ⟨x, hxX⟩ ∈
      (CFSG.pCore 2 ↥X).map (conjXEquiv X hg).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hxp
  rw [hmap] at h1
  exact CFSG.Quasithin.RonanD33.mem_pCoreOf.mpr ⟨(conjXEquiv X hg ⟨x, hxX⟩).2, h1⟩

theorem pCoreOf_subgroupOf_eq (X : Subgroup G) :
    (pCoreOf 2 X).subgroupOf X = CFSG.pCore 2 ↥X := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  unfold pCoreOf
  exact Subgroup.mem_map_iff_mem Subtype.val_injective

instance pCoreOf_subgroupOf_normal (X : Subgroup G) : ((pCoreOf 2 X).subgroupOf X).Normal := by
  rw [pCoreOf_subgroupOf_eq]
  infer_instance

theorem map_conj_le_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    X.map (MulAut.conj g).toMonoidHom ≤ X := by
  rintro _ ⟨y, hy, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy

theorem commutator_map_conj_le {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    ⁅X, X⁆.map (MulAut.conj g).toMonoidHom ≤ ⁅X, X⁆ := by
  rw [Subgroup.map_commutator]
  exact Subgroup.commutator_mono (map_conj_le_of_mem_normalizer hg)
    (map_conj_le_of_mem_normalizer hg)

theorem conj_mem_XiY {X : Subgroup G} {g y : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hy : y ∈ XiY X) : g * y * g⁻¹ ∈ XiY X := by
  have hO : (pCoreOf 2 X).map (MulAut.conj g).toMonoidHom ≤ pCoreOf 2 X := by
    rintro _ ⟨z, hz, rfl⟩
    exact conj_mem_pCoreOf_of_mem_normalizer hg hz
  have hle : (XiY X).map (MulAut.conj g).toMonoidHom ≤ XiY X := by
    unfold XiY
    rw [Subgroup.map_sup]
    exact sup_le ((commutator_map_conj_le hg).trans le_sup_left)
      (hO.trans le_sup_right)
  exact hle (Subgroup.mem_map_of_mem _ hy)

theorem map_subtype_Yof (X : Subgroup G) :
    (Yof ((pCoreOf 2 X).subgroupOf X)).map X.subtype = XiY X := by
  unfold Yof XiY
  rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left (CFSG.Quasithin.RonanD33.pCoreOf_le X)]
  congr 1
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem mem_Yof_iff (X : Subgroup G) (x : ↥X) :
    x ∈ Yof ((pCoreOf 2 X).subgroupOf X) ↔ (x : G) ∈ XiY X := by
  rw [← map_subtype_Yof X]
  exact (Subgroup.mem_map_iff_mem Subtype.val_injective).symm

instance Yof_subgroupOf_normal (X : Subgroup G) :
    (Yof ((pCoreOf 2 X).subgroupOf X)).Normal := by
  constructor
  intro n hn g
  rw [mem_Yof_iff] at hn ⊢
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact conj_mem_XiY (Subgroup.le_normalizer g.2) hn

theorem commutator_top_le_subgroupOf_iff (X : Subgroup G) :
    ⁅(⊤ : Subgroup ↥X), ⊤⁆ ≤ (pCoreOf 2 X).subgroupOf X ↔ ⁅X, X⁆ ≤ pCoreOf 2 X := by
  have hmap : (⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ : Subgroup ↥X).map X.subtype = ⁅X, X⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap, Subgroup.map_le_iff_le_comap]
  rfl

end CFSG.Quasithin.H13.L827X.LBCaseAGBase

end
