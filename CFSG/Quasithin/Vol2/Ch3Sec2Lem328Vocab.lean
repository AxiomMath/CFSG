module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Vol2.Ch3Sec2Conj
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped IsMulCommutative

variable {G : Type} [Group G] {L V : Subgroup G}

theorem exists_eq_conj_of_mem_autOn (hL : L ≤ Subgroup.normalizer (V : Set G))
    {a : MulAut ↥V} (ha : a ∈ autOn L V) :
    ∃ l ∈ L, ∀ v : ↥V, ((a v : ↥V) : G) = l * v * l⁻¹ := by
  obtain ⟨h, rfl⟩ := (A4.mem_autOn_iff hL).1 ha
  exact ⟨h, h.2, fun v => A4.actionOn_apply_coe hL h v⟩

theorem exists_mem_autOn_of_mem (hL : L ≤ Subgroup.normalizer (V : Set G)) {l : G} (hl : l ∈ L) :
    ∃ a ∈ autOn L V, ∀ v : ↥V, ((a v : ↥V) : G) = l * v * l⁻¹ :=
  ⟨A4.actionOn V L hL ⟨l, hl⟩, (A4.mem_autOn_iff hL).2 ⟨⟨l, hl⟩, rfl⟩,
    fun v => A4.actionOn_apply_coe hL ⟨l, hl⟩ v⟩

variable [IsMulCommutative ↥V]

theorem fixV_autOn (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autOn L V) = (Subgroup.centralizer (L : Set G)).subgroupOf V :=
  CFSG.Quasithin.AutOn.fixV_autOn_eq hL

theorem map_commV_autOn (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    (commV (autOn L V)).map V.subtype = ⁅V, L⁆ :=
  CFSG.Quasithin.AutOn.map_commV_autOn_eq hL

theorem isModInv_autOn_iff (hL : L ≤ Subgroup.normalizer (V : Set G)) (W : Subgroup ↥V) :
    XMod.IsInv ↥(autOn L V) W ↔
      L ≤ Subgroup.normalizer ((W.map V.subtype : Subgroup G) : Set G) := by
  constructor
  · intro h l hl
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨a, ha, hav⟩ := exists_mem_autOn_of_mem hL hl
      exact Subgroup.mem_map.2 ⟨_, h ⟨a, ha⟩ w hw, hav w⟩
    · intro hg
      obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.1 hg
      obtain ⟨a, ha, hav⟩ := exists_mem_autOn_of_mem hL (L.inv_mem hl)
      refine Subgroup.mem_map.2 ⟨_, h ⟨a, ha⟩ w hw, ?_⟩
      change ((a w : ↥V) : G) = g
      rw [hav w]
      have hwe' : (w : G) = l * g * l⁻¹ := hwe
      rw [hwe']
      group
  · intro h a w hw
    obtain ⟨l, hl, hav⟩ := exists_eq_conj_of_mem_autOn hL a.2
    have h1 : l * (w : G) * l⁻¹ ∈ W.map V.subtype :=
      (Subgroup.mem_normalizer_iff.1 (h hl) w).1 (Subgroup.mem_map.2 ⟨w, hw, rfl⟩)
    obtain ⟨w', hw', hwe⟩ := Subgroup.mem_map.1 h1
    have : w' = (a : MulAut ↥V) w := Subtype.ext (by rw [hav w]; exact hwe)
    change (a : MulAut ↥V) w ∈ W
    rw [← this]
    exact hw'

theorem top_mem_irrPlus_autOn (hL : L ≤ Subgroup.normalizer (V : Set G))
    (h : IsIrrPlusBase L V V) :
    commV (autOn L V) = ⊤ ∧ (⊤ : Subgroup ↥V) ∈ IrrPlus (autOn L V) ⊤ := by
  obtain ⟨-, -, -, hcomm, hlt, hirr⟩ := h
  have hfix := fixV_autOn hL
  have hcomm' : commV (autOn L V) = ⊤ := by
    rw [← Subgroup.map_subtype_inj, map_commV_autOn hL, map_subtype_top]
    exact hcomm
  have hcommOf : XMod.commOf ↥(autOn L V) (⊤ : Subgroup ↥V) = commV (autOn L V) := by
    unfold XMod.commOf commV
    congr 1
    ext c
    constructor
    · rintro ⟨a, l, -, rfl⟩
      exact ⟨a, a.2, l, rfl⟩
    · rintro ⟨a, ha, v, rfl⟩
      exact ⟨⟨a, ha⟩, v, trivial, rfl⟩
  have hfixed : XMod.fixed ↥(autOn L V) (⊤ : Subgroup ↥V) = fixV (autOn L V) := by
    ext v
    rw [XMod.mem_fixed, mem_fixV]
    exact ⟨fun h a ha => h.2 ⟨a, ha⟩, fun h => ⟨trivial, fun a => h a a.2⟩⟩
  refine ⟨hcomm', le_rfl, XMod.isInv_top, ?_, ?_, ?_⟩
  · rw [hcommOf, hcomm']
  · rw [hfixed, hfix, lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hlt.ne (inf_eq_left.2 h)
  · intro J hJ hfJ _
    have hJL := (isModInv_autOn_iff hL J).1 hJ
    rw [hfixed, hfix] at hfJ ⊢
    have hJ' : V ⊓ Subgroup.centralizer (L : Set G) ≤ J.map V.subtype := by
      intro g hg
      exact Subgroup.mem_map.2 ⟨⟨g, hg.1⟩, hfJ hg.2, rfl⟩
    rcases hirr _ hJ' (Subgroup.map_subtype_le J) hJL with h1 | h1
    · left
      rw [← Subgroup.map_subtype_inj, h1, Subgroup.subgroupOf_map_subtype, inf_comm]
    · right
      rw [← Subgroup.map_subtype_inj, h1, map_subtype_top]

end CFSG.Quasithin.H13
