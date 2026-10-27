module

public import CFSG.Quasithin.Vol2.Ch3T326A
public import CFSG.Quasithin.Vol2.Ch3T325H

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise
open T325 (V₀_le_V V_le_VM T_le_NV M_le_NVM sup_le_NR isMulCommutative_R
  mem_irrPlusOn_of_isIrrPlusIn actCompat_inclusion_onA actCompat_inclusion_autOn onA_le_normalizer
  map_mem_irrPlusOn biSup_smul_eq_of_actCompat actCompat_autOn_onA)

section AutOn

variable {G : Type} [Group G] {U : Subgroup G}

theorem autOn_conjClosure {Z H : Subgroup G} (hZ : Z ≤ Subgroup.normalizer (U : Set G))
    (hH : H ≤ Subgroup.normalizer (U : Set G)) :
    autOn (conjClosure Z H) U = conjClosure (autOn Z U) (autOn H U) := by
  apply le_antisymm
  · obtain ⟨R, hR⟩ : ∃ R, R = conjClosure (autOn Z U) (autOn H U) := ⟨_, rfl⟩
    have hZH : conjClosure Z H ≤
        (R.comap (conjAct U)).map (Subgroup.normalizer (U : Set G)).subtype := by
      refine conjClosure_le fun h hh z hz => ?_
      refine ⟨⟨h, hH hh⟩ * ⟨z, hZ hz⟩ * (⟨h, hH hh⟩)⁻¹, ?_, rfl⟩
      show conjAct U _ ∈ R
      rw [map_mul, map_mul, map_inv, hR]
      exact mem_conjClosure ⟨⟨h, hH hh⟩, hh, rfl⟩ ⟨⟨z, hZ hz⟩, hz, rfl⟩
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    obtain ⟨g', hg', hgg⟩ := hZH hg
    have e : g' = g := Subtype.ext hgg
    rw [← hR, ← e]
    exact hg'
  · refine conjClosure_le fun φ hφ ψ hψ => ?_
    obtain ⟨h, hh, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    obtain ⟨z, hz, rfl⟩ := Setup.mem_autOn_iff.1 hψ
    refine Setup.mem_autOn_iff.2 ⟨h * z * h⁻¹, mem_conjClosure hh hz, ?_⟩
    rw [map_mul, map_mul, map_inv]

theorem autOn_conjugate {L : Subgroup G} (hL : L ≤ Subgroup.normalizer (U : Set G)) {s : G}
    (hs : s⁻¹ ∈ Subgroup.normalizer (U : Set G)) :
    autOn (CFSG.conjugate L s) U =
      (autOn L U).map (MulAut.conj (conjAct U ⟨s⁻¹, hs⟩)).toMonoidHom := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hφ
    obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.1 hg
    refine ⟨conjAct U ⟨l, hL hl⟩, Setup.mem_autOn_iff.2 ⟨⟨l, hL hl⟩, hl, rfl⟩, ?_⟩
    have e : g = ⟨s⁻¹, hs⟩ * ⟨l, hL hl⟩ * (⟨s⁻¹, hs⟩)⁻¹ := by
      apply Subtype.ext
      rw [← hlg]
      simp
    rw [e, map_mul, map_mul, map_inv]
    rfl
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨l, hl, rfl⟩ := Setup.mem_autOn_iff.1 ha
    refine Setup.mem_autOn_iff.2 ⟨⟨s⁻¹, hs⟩ * l * (⟨s⁻¹, hs⟩)⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_map.2 ⟨(l : G), hl, ?_⟩
      simp
    · rw [map_mul, map_mul, map_inv]
      rfl

end AutOn

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem V_le_R : conjClosure V₀ T ≤ reducedAggregate (L ⊔ T) :=
  conjClosure_le fun _ ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (sup_le_NR L T ((le_sup_right : T ≤ L ⊔ T) ht)) v).mp
      (c.irr.1 hv)

omit c in
theorem L₀_le_NR (_c : Ctx T L V₀) :
    conjClosure L T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) :=
  (conjClosure_le_sup T L).trans (sup_le_NR L T)

theorem irr_V [IsMulCommutative ↥(conjClosure V₀ T)] : V₀.subgroupOf (conjClosure V₀ T) ∈
    IrrPlusOn (onA (conjClosure V₀ T) (conjClosure L T))
      (⨆ y ∈ onA (conjClosure V₀ T) T, y • V₀.subgroupOf (conjClosure V₀ T))
      (onA (conjClosure V₀ T) T) := by
  have : IsMulCommutative ↥(reducedAggregate (L ⊔ T)) := isMulCommutative_R L T
  have hTR := le_sup_right.trans (sup_le_NR L T)
  have hR := mem_irrPlusOn_of_isIrrPlusIn c.L₀_le_NR hTR c.irr
  have hmap : (V₀.subgroupOf (conjClosure V₀ T)).map (Subgroup.inclusion c.V_le_R) =
      V₀.subgroupOf (reducedAggregate (L ⊔ T)) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨⟨x, V₀_le_V T V₀ hx⟩, hx, rfl⟩
  refine (actCompat_inclusion_onA c.V_le_R c.L₀_le_NV c.L₀_le_NR).mem_irrPlusOn_of_map
    (Subgroup.inclusion_injective _) (actCompat_inclusion_onA c.V_le_R (T_le_NV T V₀) hTR)
    (onA_le_normalizer c.T_le_M) (onA_le_normalizer c.T_le_M) (Wq := ⊤)
    (fun _ _ _ _ => trivial) ?_
  rw [hmap]
  exact hR

theorem irrT [IsMulCommutative ↥(conjClosure V₀ T)] [IsMulCommutative ↥(conjClosure
      (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))] :
    V₀.subgroupOf (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
      ∈ IrrPlusOn (autOn (conjClosure L T) (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))))
        (orbSup (autOn T (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))))
          (V₀.subgroupOf (conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))))
        (autOn T (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  set L₀ := conjClosure L T with hL₀
  set V := conjClosure V₀ T with hV
  set VM := conjClosure V (Subgroup.normalizer (L₀ : Set G)) with hVM
  have hVVM : V ≤ VM := V_le_VM T L₀ V₀
  have hLVM : L₀ ≤ Subgroup.normalizer (VM : Set G) :=
    Subgroup.le_normalizer.trans (M_le_NVM T L₀ V₀)
  have hTVM : T ≤ Subgroup.normalizer (VM : Set G) := c.T_le_M.trans (M_le_NVM T L₀ V₀)
  have h1 := c.irr_V
  set W := ⨆ y ∈ onA V T, y • V₀.subgroupOf V with hW
  have hTX₁ : onA V T ≤ Subgroup.normalizer ((onA V L₀ : Subgroup _) : Set _) :=
    onA_le_normalizer c.T_le_M
  have hTX₂ : autOn T VM ≤ Subgroup.normalizer (autOn L₀ VM : Set (MulAut ↥VM)) :=
    H13.autOn_le_normalizer hLVM hTVM c.T_le_M
  have hWT : ∀ t ∈ onA V T, ∀ w ∈ W, t • w ∈ W := fun t ht w hw => smul_mem_biSup_smul ht hw
  have hWinv : IsModInv (onA V L₀) W :=
    XMod.isInv_iSup fun y => XMod.isInv_iSup fun hy => isModInv_smul (hTX₁ hy) h1.1.2.1
  have h2 := map_mem_irrPlusOn (Subgroup.inclusion_injective hVVM)
    (actCompat_inclusion_autOn hVVM c.L₀_le_NV hLVM)
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

theorem orbSup_eq [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] :
    orbSup (autOn T (conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
        (V₀.subgroupOf (conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) =
      (conjClosure V₀ T).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) := by
  have hVVM := V_le_VM T (conjClosure L T) V₀
  have hTVM := c.T_le_M.trans (M_le_NVM T (conjClosure L T) V₀)
  rw [orbSup_eq_biSup_smul, biSup_smul_eq_of_actCompat (actCompat_autOn_onA T)]
  apply Subgroup.map_injective (conjClosure (conjClosure V₀ T)
    (Subgroup.normalizer (conjClosure L T : Set G))).subtype_injective
  rw [map_biSup_smul hTVM, Subgroup.map_subgroupOf_eq_of_le ((V₀_le_V T V₀).trans hVVM),
    Subgroup.map_subgroupOf_eq_of_le hVVM]

end Ctx

end CFSG.Quasithin.H13.T326
