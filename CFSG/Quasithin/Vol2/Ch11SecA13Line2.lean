module

public import CFSG.Quasithin.Vol2.Ch11SecA13Line

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem lOf_le_normalizer_fsuV (h : Hyp11 G T L I n) (U : Subgroup G) :
    LOf L U ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  (lOf_le L U).trans (L_le_normalizer_fsuV h)

theorem pCoreOf_lOf_le_centralizer (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {U₂ : Subgroup G} (hU₂ : IsVi T L I n 2 U₂) :
    pCoreOf 2 (LOf L U₂) ≤ Subgroup.centralizer (U₂ : Set G) := by
  have hUV := IsVi.le_fsuV hU₂
  have ha := (lineFacts hL3 hLp hLg h1102 h hU₂).1
  rw [pCoreOf_perfectCore_eq h1102 h hUV] at ha
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hyV : y ∈ Subgroup.normalizer (fsuV T I : Set G) :=
    ((Subgroup.map_subtype_le _).trans (lOf_le_normalizer_fsuV h U₂)) hy
  have e := congrArg Subtype.val (ha (conjV (fsuV T I) y hyV) (conjV_mem_autOn hy hyV)
    ⟨u, hUV hu⟩ hu)
  rw [conjV_apply_coe] at e
  calc u * y = (y * u * y⁻¹) * y := by rw [e]
    _ = y * u := by group

theorem not_lOf_le_centralizer (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {U₂ : Subgroup G} (hU₂ : IsVi T L I n 2 U₂) :
    ¬ LOf L U₂ ≤ Subgroup.centralizer (U₂ : Set G) := by
  have hUV := IsVi.le_fsuV hU₂
  obtain ⟨s, hs, u, hu, hsu⟩ := (lineFacts hL3 hLp hLg h1102 h hU₂).2.1
  rw [perfectCore_eq_autOn_lOf h hUV] at hs
  obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hs
  intro hle
  apply hsu
  apply Subtype.ext
  rw [conjV_apply_coe]
  have := Subgroup.mem_centralizer_iff.mp (hle hl) (u : G) hu
  calc l * (u : G) * l⁻¹ = (u : G) * l * l⁻¹ := by rw [this]
    _ = u := by group

theorem fixed_lOf_iff (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {U₂ : Subgroup G} (hU₂ : IsVi T L I n 2 U₂)
    {v : G} (hv : v ∈ U₂) :
    (∀ l ∈ LOf L U₂, l * v * l⁻¹ = v) ↔ v ∈ Subgroup.centralizer (L : Set G) := by
  have hUV := IsVi.le_fsuV hU₂
  have hc := (lineFacts hL3 hLp hLg h1102 h hU₂).2.2.1 ⟨v, hUV hv⟩ hv
  rw [perfectCore_eq_autOn_lOf h hUV, Subgroup.mem_subgroupOf] at hc
  rw [← hc]
  constructor
  · intro hl s hs
    obtain ⟨l, hl', hlV, rfl⟩ := mem_autOn_iff.mp hs
    apply Subtype.ext
    rw [conjV_apply_coe]
    exact hl l hl'
  · intro hs l hl
    have e := congrArg Subtype.val
      (hs (conjV (fsuV T I) l (lOf_le_normalizer_fsuV h U₂ hl)) (conjV_mem_autOn hl _))
    rwa [conjV_apply_coe] at e

end CFSG.Quasithin.Vol2.Ch11.SecA
