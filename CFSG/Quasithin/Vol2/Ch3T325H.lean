module

public import CFSG.Quasithin.Vol2.Ch3T325G
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch3T325A
public import CFSG.Quasithin.Vol2.Ch3T325F

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

section Compat

variable {G : Type} [Group G] {A B X : Subgroup G} [IsMulCommutative ↥A] [IsMulCommutative ↥B]

theorem actCompat_inclusion_onA (hAB : A ≤ B) (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) :
    ActCompat (Subgroup.inclusion hAB) (onA A X) (onA B X) := by
  refine ⟨fun b hb => ⟨⟨b, hXB (Subgroup.mem_subgroupOf.mp hb)⟩, hb, fun p => rfl⟩,
    fun a ha => ⟨⟨a, hXA (Subgroup.mem_subgroupOf.mp ha)⟩, ha, fun p => rfl⟩⟩

theorem actCompat_inclusion_autOn (hAB : A ≤ B) (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) :
    ActCompat (Subgroup.inclusion hAB) (onA A X) (autOn X B) := by
  refine ⟨fun b hb => ⟨conjAct B ⟨b, hXB (Subgroup.mem_subgroupOf.mp hb)⟩,
    Setup.mem_autOn_iff.mpr ⟨_, Subgroup.mem_subgroupOf.mp hb, rfl⟩, fun p => ?_⟩,
    fun a ha => ?_⟩
  · apply Subtype.ext
    show (b : G) * (p : G) * (b : G)⁻¹ = _
    rw [MulAut.smul_def, InternalSec.coe_conjAct_apply]
    rfl
  · obtain ⟨g, hgX, rfl⟩ := Setup.mem_autOn_iff.mp ha
    refine ⟨⟨g, hXA hgX⟩, Subgroup.mem_subgroupOf.mpr hgX, fun p => ?_⟩
    apply Subtype.ext
    show (g : G) * (p : G) * (g : G)⁻¹ = _
    rw [MulAut.smul_def, InternalSec.coe_conjAct_apply]
    rfl

omit [IsMulCommutative ↥A] [IsMulCommutative ↥B] in
theorem onA_le_normalizer {Y : Subgroup G} (hYX : Y ≤ Subgroup.normalizer (X : Set G)) :
    onA A Y ≤ Subgroup.normalizer ((onA A X : Subgroup _) : Set _) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro n
  exact Subgroup.mem_normalizer_iff.1 (hYX (Subgroup.mem_subgroupOf.1 ht)) (n : G)

end Compat

section Reduced

variable {G : Type} [Group G] [Finite G] (L T : Subgroup G)

theorem sup_le_NR : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) :=
  Lem3228.le_normalizer_reducedAggregate' (L ⊔ T)

theorem isMulCommutative_R : IsMulCommutative ↥(reducedAggregate (L ⊔ T)) :=
  ⟨⟨fun a b => Subtype.ext ((reducedAggregate_props (L ⊔ T)).2.1 _ a.2 _ b.2)⟩⟩

end Reduced

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem V_le_R : conjClosure V₀ T ≤ reducedAggregate (L ⊔ T) :=
  conjClosure_le fun _ ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (sup_le_NR L T ((le_sup_right : T ≤ L ⊔ T) ht)) v).mp
      (c.irr.1 hv)

theorem irr_V [IsMulCommutative ↥(conjClosure V₀ T)] : V₀.subgroupOf (conjClosure V₀ T) ∈
    IrrPlusOn (onA (conjClosure V₀ T) L)
      (⨆ y ∈ onA (conjClosure V₀ T) T, y • V₀.subgroupOf (conjClosure V₀ T))
      (onA (conjClosure V₀ T) T) := by
  have : IsMulCommutative ↥(reducedAggregate (L ⊔ T)) := isMulCommutative_R L T
  have hLR := le_sup_left.trans (sup_le_NR L T)
  have hTR := le_sup_right.trans (sup_le_NR L T)
  have hR := mem_irrPlusOn_of_isIrrPlusIn hLR hTR c.irr
  have hmap : (V₀.subgroupOf (conjClosure V₀ T)).map (Subgroup.inclusion c.V_le_R) =
      V₀.subgroupOf (reducedAggregate (L ⊔ T)) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, V₀_le_V T V₀ hx⟩, hx, rfl⟩
  refine (actCompat_inclusion_onA c.V_le_R c.L_le_NV hLR).mem_irrPlusOn_of_map
    (Subgroup.inclusion_injective _) (actCompat_inclusion_onA c.V_le_R (T_le_NV T V₀) hTR)
    (onA_le_normalizer c.T_le_M) (onA_le_normalizer c.T_le_M) (Wq := ⊤)
    (fun _ _ _ _ => trivial) ?_
  rw [hmap]
  exact hR

theorem irrT [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))] :
    V₀.subgroupOf (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) ∈
      IrrPlusOn (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
        (orbSup (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
          (V₀.subgroupOf (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))))
        (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))) := by
  set V := conjClosure V₀ T with hV
  set VM := conjClosure V (Subgroup.normalizer (L : Set G)) with hVM
  have hVVM : V ≤ VM := V_le_VM T L V₀
  have hLVM : L ≤ Subgroup.normalizer (VM : Set G) :=
    Subgroup.le_normalizer.trans (M_le_NVM T L V₀)
  have hTVM : T ≤ Subgroup.normalizer (VM : Set G) := c.T_le_M.trans (M_le_NVM T L V₀)
  have h1 := c.irr_V
  set W := ⨆ y ∈ onA V T, y • V₀.subgroupOf V with hW
  have hTX₁ : onA V T ≤ Subgroup.normalizer ((onA V L : Subgroup _) : Set _) :=
    onA_le_normalizer c.T_le_M
  have hTX₂ : autOn T VM ≤ Subgroup.normalizer (autOn L VM : Set (MulAut ↥VM)) :=
    autOn_le_normalizer hLVM hTVM c.T_le_M
  have hWT : ∀ t ∈ onA V T, ∀ w ∈ W, t • w ∈ W := fun t ht w hw => smul_mem_biSup_smul ht hw
  have hWinv : IsModInv (onA V L) W :=
    XMod.isInv_iSup fun y => XMod.isInv_iSup fun hy => isModInv_smul (hTX₁ hy) h1.1.2.1
  have h2 := map_mem_irrPlusOn (Subgroup.inclusion_injective hVVM)
    (actCompat_inclusion_autOn hVVM c.L_le_NV hLVM)
    (actCompat_inclusion_autOn hVVM (T_le_NV T V₀) hTVM) hTX₁ hTX₂ hWT hWinv h1
  have hI : (V₀.subgroupOf V).map (Subgroup.inclusion hVVM) = V₀.subgroupOf VM := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, V₀_le_V T V₀ hx⟩, hx, rfl⟩
  have hWtop : W = ⊤ := by
    apply Subgroup.map_injective V.subtype_injective
    rw [map_biSup_smul (T_le_NV T V₀), Subgroup.map_subgroupOf_eq_of_le (V₀_le_V T V₀),
      map_subtype_top]
  have hVT : orbSup (autOn T VM) (V₀.subgroupOf VM) = V.subgroupOf VM := by
    rw [orbSup_eq_biSup_smul, biSup_smul_eq_of_actCompat (actCompat_autOn_onA T)]
    apply Subgroup.map_injective VM.subtype_injective
    rw [map_biSup_smul hTVM, Subgroup.map_subgroupOf_eq_of_le ((V₀_le_V T V₀).trans hVVM),
      Subgroup.map_subgroupOf_eq_of_le hVVM]
  have hWmap : W.map (Subgroup.inclusion hVVM) = orbSup (autOn T VM) (V₀.subgroupOf VM) := by
    rw [hVT, hWtop]
    ext x
    constructor
    · rintro ⟨v, -, rfl⟩
      exact v.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  rw [hI, hWmap] at h2
  exact h2

end Ctx

end CFSG.Quasithin.H13.T325
