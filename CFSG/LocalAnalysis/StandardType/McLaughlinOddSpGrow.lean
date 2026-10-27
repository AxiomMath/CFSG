module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddSL
public import CFSG.LocalAnalysis.StandardType.McLaughlinOddSpBasic
public import CFSG.RankThree.PartOne.LIT.McSpShape
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {H : Subgroup (V ≃ₗ[ZMod p] V)}

namespace IsSpBlock

variable {W L : Submodule (ZMod p) V} {β : LinearMap.BilinForm (ZMod p) V}
  (hB : IsSpBlock H W L β)
include hB

theorem reciprocal (hua : HasUniqueAxes H) {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) {x : V}
    {h : Module.Dual (ZMod p) V} (hx0 : x ≠ 0) (hh0 : h ≠ 0) (hxh : TrIn H x h) :
    β (pW hB.compl x) w = 0 ↔ h w = 0 := by
  have := hua.reciprocal hw0 hx0 (hB.flip_ne_zero hw hw0) hh0 (hB.trIn w hw) hxh
  rwa [LinearMap.BilinForm.flip_apply, hB.apply_pW] at this

theorem shape (hua : HasUniqueAxes H) {x : V} {h : Module.Dual (ZMod p) V} (hx0 : x ≠ 0)
    (hh0 : h ≠ 0) (hxh : TrIn H x h) (hW : ∃ w ∈ W, h w ≠ 0) :
    pW hB.compl x ≠ 0 ∧ ∃ ν : ZMod p, ν ≠ 0 ∧ ∀ w ∈ W, h w = ν * β w (pW hB.compl x) := by
  obtain ⟨w₀, hw₀, hhw₀⟩ := hW
  have hw₀0 : w₀ ≠ 0 := fun h0 => hhw₀ (by rw [h0, map_zero])
  have hβw₀ : β (pW hB.compl x) w₀ ≠ 0 := fun h0 =>
    hhw₀ ((hB.reciprocal hua hw₀ hw₀0 hx0 hh0 hxh).mp h0)
  have hxW : pW hB.compl x ≠ 0 := fun h0 => hβw₀ (by rw [h0, map_zero, LinearMap.zero_apply])
  have hβw₀' : β w₀ (pW hB.compl x) ≠ 0 := by
    rw [← hB.alt.neg_eq]
    exact neg_ne_zero.mpr hβw₀
  refine ⟨hxW, h w₀ / β w₀ (pW hB.compl x), div_ne_zero hhw₀ hβw₀', fun w hw => ?_⟩
  obtain ⟨w', hw'⟩ : ∃ w', w' = w - (β w (pW hB.compl x) / β w₀ (pW hB.compl x)) • w₀ :=
    ⟨_, rfl⟩
  have hw'W : w' ∈ W := hw' ▸ W.sub_mem hw (W.smul_mem _ hw₀)
  have hβw'' : β w' (pW hB.compl x) = 0 := by
    rw [hw', LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul, div_mul_cancel₀ _ hβw₀',
      sub_self]
  have hβw' : β (pW hB.compl x) w' = 0 := by
    rw [← hB.alt.neg_eq, hβw'', neg_zero]
  have hhw' : h w' = 0 := by
    by_cases hz : w' = 0
    · rw [hz, map_zero]
    · exact (hB.reciprocal hua hw'W hz hx0 hh0 hxh).mp hβw'
  rw [hw', map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hhw'
  rw [hhw']
  ring

theorem moving_data (hp : p ≠ 2) (hua : HasUniqueAxes H) {x : V} {h : Module.Dual (ZMod p) V}
    (hx0 : x ≠ 0) (hh0 : h ≠ 0) (hxh : TrIn H x h) (hxW : x ∉ W) (hW : ∃ w ∈ W, h w ≠ 0) :
    ∃ ν : ZMod p, ν ≠ 0 ∧ (∀ w ∈ W, (h - ν • β.flip (pW hB.compl x)) w = 0) ∧
      h - ν • β.flip (pW hB.compl x) ≠ 0 ∧
      TrIn H (pL hB.compl x) (h - ν • β.flip (pW hB.compl x)) ∧
      ∀ w ∈ W, w ≠ 0 →
        TrIn H (w + pL hB.compl x) (β.flip w + ν⁻¹ • (h - ν • β.flip (pW hB.compl x))) := by
  obtain ⟨hxW0, ν, hν, hhW⟩ := hB.shape hua hx0 hh0 hxh hW
  obtain ⟨xW, hxWdef⟩ : ∃ xW, xW = pW hB.compl x := ⟨_, rfl⟩
  obtain ⟨xL, hxLdef⟩ : ∃ xL, xL = pL hB.compl x := ⟨_, rfl⟩
  rw [← hxWdef] at hxW0 hhW ⊢
  rw [← hxLdef]
  obtain ⟨h'', hh''⟩ : ∃ h'' : Module.Dual (ZMod p) V, h'' = h - ν • β.flip xW := ⟨_, rfl⟩
  have hxWmem : xW ∈ W := hxWdef ▸ pW_mem hB.compl x
  have hxLmem : xL ∈ L := hxLdef ▸ pL_mem hB.compl x
  have hx : x = xW + xL := by rw [hxWdef, hxLdef, pW_add_pL]
  have hxL0 : xL ≠ 0 := by
    intro h0
    apply hxW
    rw [hx, h0, add_zero]
    exact hxWmem
  have hh''app : ∀ z, h'' z = h z - ν * β z xW := fun z => by
    rw [hh'', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply,
      smul_eq_mul]
  have hvan : ∀ w ∈ W, h'' w = 0 := fun w hw => by rw [hh''app, hhW w hw, sub_self]
  have hh : h = ν • β.flip xW + h'' := by rw [hh'']; abel
  have hhxL : h'' xL = 0 := by
    have h1 := hxh.1
    rw [hx, map_add, hhW xW hxWmem, hB.alt.self_eq_zero, mul_zero, zero_add] at h1
    rw [hh''app, h1, hB.vanish_left hxLmem, mul_zero, sub_zero]
  have hstart : TrIn H (xW + xL) (β.flip xW + ν⁻¹ • h'') := by
    have := hxh.smul ν⁻¹
    rwa [hh, smul_add, smul_smul, inv_mul_cancel₀ hν, one_smul, hx] at this
  have hlink : ∀ w ∈ W, w ≠ 0 → TrIn H (w + xL) (β.flip w + ν⁻¹ • h'') :=
    trIn_transitive hB.alt hB.nondeg hB.trIn (fun u _ => hB.vanish u xL hxLmem)
      (fun u hu => by rw [LinearMap.smul_apply, hvan u hu, smul_zero]) hxWmem hxW0 hstart
  have hneg := hlink (-xW) (W.neg_mem hxWmem) (neg_ne_zero.mpr hxW0)
  have hneg' : TrIn H (xL - xW) (ν⁻¹ • h'' - β.flip xW) := by
    have e1 : -xW + xL = xL - xW := by abel
    have e2 : β.flip (-xW) + ν⁻¹ • h'' = ν⁻¹ • h'' - β.flip xW := by rw [map_neg]; abel
    rwa [e1, e2] at hneg
  have hρ : TrIn H xL (ν⁻¹ • h'') :=
    trIn_pm hp hB.alt hstart hneg' (hB.trIn xW hxWmem)
      (by rw [LinearMap.smul_apply, hvan xW hxWmem, smul_zero])
      (by rw [LinearMap.smul_apply, hhxL, smul_zero]) (hB.vanish_left hxLmem xW)
  have htr : TrIn H xL h'' := trIn_of_smul (inv_ne_zero hν) hρ
  have hne : h'' ≠ 0 := by
    intro h0
    have h2 : TrIn H xL (ν • β.flip xW) := by
      have hxh' : TrIn H x (ν • β.flip xW) := by
        rw [hh, h0, add_zero] at hxh
        exact hxh
      have h3 := trIn_sub_center hxh' ((hB.trIn xW hxWmem).smul ν)
      rwa [hx, add_sub_cancel_left] at h3
    have hf0 : ν • β.flip xW ≠ 0 := smul_ne_zero hν (hB.flip_ne_zero hxWmem hxW0)
    obtain ⟨w', hw', hww'⟩ := hB.nondeg xW hxWmem hxW0
    have hw'0 : w' ≠ 0 := fun h4 => hww' (by rw [h4, map_zero])
    have h5 := (hua.reciprocal hxL0 hw'0 hf0 (hB.flip_ne_zero hw' hw'0) h2 (hB.trIn w' hw')).mpr
      (by rw [LinearMap.BilinForm.flip_apply, hB.vanish_left hxLmem])
    rw [LinearMap.smul_apply, LinearMap.BilinForm.flip_apply, smul_eq_mul] at h5
    apply hww'
    rw [← hB.alt.neg_eq, (mul_eq_zero.mp h5).resolve_left hν, neg_zero]
  refine ⟨ν, hν, ?_⟩
  rw [← hh'']
  exact ⟨hvan, hne, htr, hlink⟩

theorem exists_partner_L (hp : p ≠ 2) (hua : HasUniqueAxes H)
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    {xL : V} (hxL : xL ∈ L) (hxL0 : xL ≠ 0) {h'' : Module.Dual (ZMod p) V} (hh''0 : h'' ≠ 0)
    (hh''W : ∀ w ∈ W, h'' w = 0) (htr : TrIn H xL h'') :
    ∃ (yL : V) (e'' : Module.Dual (ZMod p) V), yL ∈ L ∧ (∀ w ∈ W, e'' w = 0) ∧
      TrIn H yL e'' ∧ h'' yL ≠ 0 ∧ e'' xL ≠ 0 := by
  obtain ⟨b, g, φ, hφ, hg, hφb, hga⟩ := exists_partner H hirr hgen hxL0 hh''0 htr
  obtain ⟨s, hs⟩ := hua xL h'' φ hxL0 htr hφ hh''0
  have hh''b : h'' b ≠ 0 := by
    intro h0
    apply hφb
    rw [hs, LinearMap.smul_apply, h0, smul_zero]
  have hb0 : b ≠ 0 := fun h0 => hh''b (by rw [h0, map_zero])
  have hg0 : g ≠ 0 := fun h0 => hga (by rw [h0, LinearMap.zero_apply])
  have hbW : b ∉ W := fun h => hh''b (hh''W b h)
  by_cases hgW : ∃ w ∈ W, g w ≠ 0
  · obtain ⟨ν, -, hvan, -, htrL, -⟩ := hB.moving_data hp hua hb0 hg0 hg hbW hgW
    refine ⟨pL hB.compl b, g - ν • β.flip (pW hB.compl b), pL_mem hB.compl b, hvan, htrL, ?_, ?_⟩
    · rw [apply_eq_pW_add_pL hB.compl h'' b, hh''W _ (pW_mem hB.compl b), zero_add] at hh''b
      exact hh''b
    · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply,
        hB.vanish_left hxL, smul_zero, sub_zero]
      exact hga
  · push Not at hgW
    have hbW0 : pW hB.compl b = 0 := by
      by_contra hne
      obtain ⟨w, hw, hbw⟩ := hB.nondeg _ (pW_mem hB.compl b) hne
      have hw0 : w ≠ 0 := fun h0 => hbw (by rw [h0, map_zero])
      exact hbw ((hB.reciprocal hua hw hw0 hb0 hg0 hg).mpr (hgW w hw))
    have hbL : b ∈ L := by
      have h1 := pW_add_pL hB.compl b
      rw [hbW0, zero_add] at h1
      rw [← h1]
      exact pL_mem hB.compl b
    exact ⟨b, g, hbL, hgW, hg, hh''b, hga⟩

theorem glue {xL yL : V} (hxL : xL ∈ L) (hyL : yL ∈ L) {h'' e'' : Module.Dual (ZMod p) V}
    (hh''W : ∀ w ∈ W, h'' w = 0) (he''W : ∀ w ∈ W, e'' w = 0)
    (hx : TrIn H xL h'') (hy : TrIn H yL e'') (hhy : h'' yL ≠ 0) (hex : e'' xL ≠ 0)
    {c : ZMod p} (hc : c ≠ 0)
    (hlink : ∀ w ∈ W, w ≠ 0 → TrIn H (w + xL) (β.flip w + (c * e'' xL) • h'')) :
    IsSpBlock H (W ⊔ Submodule.span (ZMod p) {xL, yL})
      (L ⊓ LinearMap.ker h'' ⊓ LinearMap.ker e'')
      (β + c • (h''.smulRight e'' - e''.smulRight h'')) := by
  obtain ⟨γ, hγ⟩ : ∃ γ : LinearMap.BilinForm (ZMod p) V,
      γ = c • (h''.smulRight e'' - e''.smulRight h'') := ⟨_, rfl⟩
  rw [← hγ]
  have hγapp : ∀ z z', γ z z' = c * (h'' z * e'' z' - e'' z * h'' z') := fun z z' => by
    rw [hγ, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
      LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have hhx : h'' xL = 0 := hx.1
  have hey : e'' yL = 0 := hy.1
  have hγalt : γ.IsAlt := fun z => by rw [hγapp]; ring
  obtain ⟨P, hP⟩ : ∃ P : Submodule (ZMod p) V, P = Submodule.span (ZMod p) {xL, yL} :=
    ⟨_, rfl⟩
  rw [← hP]
  have hxP : xL ∈ P := hP ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hyP : yL ∈ P := hP ▸ Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hPL : P ≤ L := by
    rw [hP, Submodule.span_le]
    rintro z (rfl | hz)
    · exact hxL
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hyL
  have hxL0 : xL ≠ 0 := fun h0 => hex (by rw [h0, map_zero])
  have hγx : γ.flip xL = (c * e'' xL) • h'' := by
    ext z
    rw [LinearMap.BilinForm.flip_apply, hγapp, LinearMap.smul_apply, hhx, smul_eq_mul]
    ring
  have hγy : γ.flip yL = (-(c * h'' yL)) • e'' := by
    ext z
    rw [LinearMap.BilinForm.flip_apply, hγapp, LinearMap.smul_apply, hey, smul_eq_mul]
    ring
  have hγW : ∀ w ∈ W, ∀ z, γ z w = 0 := fun w hw z => by
    rw [hγapp, hh''W w hw, he''W w hw]
    ring
  have hPgood : ∀ q ∈ P, TrIn H q (γ.flip q) := by
    have hxg : TrIn H xL (γ.flip xL) := by rw [hγx]; exact hx.smul _
    have hyg : TrIn H yL (γ.flip yL) := by rw [hγy]; exact hy.smul _
    have hxy : γ xL yL ≠ 0 := by
      rw [hγapp, hhx, hey]
      have : c * (0 * 0 - e'' xL * h'' yL) = -(c * (e'' xL * h'' yL)) := by ring
      rw [this, neg_ne_zero]
      exact mul_ne_zero hc (mul_ne_zero hex hhy)
    intro q hq
    exact trIn_span_pair hγalt hxg hyg hxy q (hP ▸ hq)
  have hγnd : ∀ q ∈ P, q ≠ 0 → ∃ q' ∈ P, γ q q' ≠ 0 := by
    intro q hq hq0
    rw [hP] at hq
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hq
    have e1 : γ (s • xL + t • yL) xL = c * t * h'' yL * e'' xL := by
      rw [hγapp]
      simp only [map_add, map_smul, smul_eq_mul, hhx, hey]
      ring
    have e2 : γ (s • xL + t • yL) yL = -(c * s * e'' xL * h'' yL) := by
      rw [hγapp]
      simp only [map_add, map_smul, smul_eq_mul, hhx, hey]
      ring
    by_cases ht : t = 0
    · have hs : s ≠ 0 := by
        rintro rfl
        apply hq0
        rw [ht, zero_smul, zero_smul, add_zero]
      refine ⟨yL, hyP, ?_⟩
      rw [e2, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc hs) hex) hhy
    · refine ⟨xL, hxP, ?_⟩
      rw [e1]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc ht) hhy) hex
  have hβP : ∀ q ∈ P, β.flip q = 0 := fun q hq => by
    ext z
    rw [LinearMap.BilinForm.flip_apply, hB.vanish z q (hPL hq), LinearMap.zero_apply]
  have hflip : ∀ w q : V, w ∈ W → q ∈ P → (β + γ).flip (w + q) = β.flip w + γ.flip q := by
    intro w q hw hq
    ext z
    have h1 := LinearMap.congr_fun (hβP q hq) z
    rw [LinearMap.BilinForm.flip_apply, LinearMap.zero_apply] at h1
    simp only [LinearMap.BilinForm.flip_apply, LinearMap.add_apply, map_add, h1, hγW w hw z]
    abel
  refine ⟨?_, hB.alt.add hγalt, ?_, ?_, ?_⟩
  ·
    refine ⟨Submodule.disjoint_def.mpr fun z hz1 hz2 => ?_,
      codisjoint_iff.mpr (eq_top_iff.mpr fun z _ => ?_)⟩
    · obtain ⟨w, hw, q, hq, rfl⟩ := Submodule.mem_sup.mp hz1
      obtain ⟨hzL', hze⟩ := Submodule.mem_inf.mp hz2
      obtain ⟨hzL, hzh⟩ := Submodule.mem_inf.mp hzL'
      have hwL : w ∈ L := by
        have := L.sub_mem hzL (hPL hq)
        rwa [add_sub_cancel_right] at this
      have hw0 : w = 0 := Submodule.disjoint_def.mp hB.compl.disjoint w hw hwL
      rw [hw0, zero_add] at hzh hze ⊢
      rw [hP] at hq
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hq
      rw [LinearMap.mem_ker, map_add, map_smul, map_smul, hhx, smul_eq_mul, smul_eq_mul,
        mul_zero, zero_add] at hzh
      rw [LinearMap.mem_ker, map_add, map_smul, map_smul, hey, smul_eq_mul, smul_eq_mul,
        mul_zero, add_zero] at hze
      have ht : t = 0 := (mul_eq_zero.mp hzh).resolve_right hhy
      have hs : s = 0 := (mul_eq_zero.mp hze).resolve_right hex
      rw [hs, ht, zero_smul, zero_smul, add_zero]
    · obtain ⟨zW, hzW⟩ : ∃ zW, zW = pW hB.compl z := ⟨_, rfl⟩
      obtain ⟨zL, hzL⟩ : ∃ zL, zL = pL hB.compl z := ⟨_, rfl⟩
      have hz : z = zW + zL := by rw [hzW, hzL, pW_add_pL]
      have hzWmem : zW ∈ W := hzW ▸ pW_mem hB.compl z
      have hzLmem : zL ∈ L := hzL ▸ pL_mem hB.compl z
      have hdec : z = (zW + ((e'' zL / e'' xL) • xL + (h'' zL / h'' yL) • yL)) +
          (zL - (e'' zL / e'' xL) • xL - (h'' zL / h'' yL) • yL) := by
        rw [hz]
        abel
      rw [hdec]
      refine Submodule.add_mem_sup (Submodule.add_mem_sup hzWmem
        (P.add_mem (P.smul_mem _ hxP) (P.smul_mem _ hyP))) ?_
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact L.sub_mem (L.sub_mem hzLmem (L.smul_mem _ hxL)) (L.smul_mem _ hyL)
      · rw [LinearMap.mem_ker]
        simp only [map_sub, map_smul, smul_eq_mul, hhx, mul_zero, sub_zero]
        rw [div_mul_cancel₀ _ hhy, sub_self]
      · rw [LinearMap.mem_ker]
        simp only [map_sub, map_smul, smul_eq_mul, hey, mul_zero, sub_zero]
        rw [div_mul_cancel₀ _ hex, sub_self]
  ·
    intro z l hl
    obtain ⟨hlL', hle⟩ := Submodule.mem_inf.mp hl
    obtain ⟨hlL, hlh⟩ := Submodule.mem_inf.mp hlL'
    rw [LinearMap.add_apply, LinearMap.add_apply, hB.vanish z l hlL, hγapp,
      LinearMap.mem_ker.mp hlh, LinearMap.mem_ker.mp hle]
    ring
  ·
    intro v hv hv0
    obtain ⟨w, hw, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
    by_cases hw0 : w = 0
    · rw [hw0, zero_add] at hv0 ⊢
      obtain ⟨q', hq', hqq'⟩ := hγnd q hq hv0
      refine ⟨q', Submodule.mem_sup_right hq', ?_⟩
      rw [LinearMap.add_apply, LinearMap.add_apply, hB.vanish q q' (hPL hq'), zero_add]
      exact hqq'
    · obtain ⟨w', hw', hww'⟩ := hB.nondeg w hw hw0
      refine ⟨w', Submodule.mem_sup_left hw', ?_⟩
      rw [LinearMap.add_apply, LinearMap.add_apply, hγW w' hw', add_zero, LinearMap.map_add₂,
        hB.vanish_left (hPL hq), add_zero]
      exact hww'
  ·
    intro v hv
    obtain ⟨w, hw, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hflip w q hw hq]
    by_cases hq0 : q = 0
    · rw [hq0, add_zero]
      have := hB.trIn w hw
      have h0 : γ.flip 0 = 0 := map_zero _
      rwa [h0, add_zero]
    by_cases hw0 : w = 0
    · rw [hw0, zero_add, map_zero, zero_add]
      exact hPgood q hq
    have h₀ : TrIn H (xL + w) (γ.flip xL + β.flip w) := by
      have := hlink w hw hw0
      rwa [add_comm w, add_comm (β.flip w), ← hγx] at this
    have := trIn_transitive hγalt hγnd hPgood (fun q' _ => hγW w hw q')
      (fun q' hq' => by rw [LinearMap.BilinForm.flip_apply, hB.vanish_left (hPL hq')])
      hxP hxL0 h₀ q hq hq0
    rwa [add_comm q, add_comm (γ.flip q)] at this

theorem grow (hp : p ≠ 2) (hua : HasUniqueAxes H)
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hT : ∃ (a : V) (f : Module.Dual (ZMod p) V), a ≠ 0 ∧ f ≠ 0 ∧ TrIn H a f) (hL : L ≠ ⊥) :
    ∃ (W' L' : Submodule (ZMod p) V) (β' : LinearMap.BilinForm (ZMod p) V),
      IsSpBlock H W' L' β' ∧ L' < L := by
  by_cases hW : W = ⊥
  · have hLt : L = ⊤ := by
      have := hB.compl.sup_eq_top
      rwa [hW, bot_sup_eq] at this
    obtain ⟨a, f, ha, hf, haf⟩ := hT
    obtain ⟨b, g, φ, hφ, hg, hφb, hga⟩ := exists_partner H hirr hgen ha hf haf
    have hvanW : ∀ χ : Module.Dual (ZMod p) V, ∀ w ∈ W, χ w = 0 := fun χ w hw => by
      rw [hW] at hw
      rw [(Submodule.mem_bot (ZMod p)).mp hw, map_zero]
    have hglue := hB.glue (xL := a) (yL := b) (hLt ▸ Submodule.mem_top)
      (hLt ▸ Submodule.mem_top) (hvanW φ) (hvanW g) hφ hg hφb hga one_ne_zero
      (fun w hw hw0 => absurd ((Submodule.mem_bot (ZMod p)).mp (hW ▸ hw)) hw0)
    refine ⟨_, _, _, hglue, lt_of_le_of_ne (le_trans inf_le_left inf_le_left) fun h => hga ?_⟩
    have : a ∈ L ⊓ LinearMap.ker φ ⊓ LinearMap.ker g := by
      rw [h, hLt]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2
  · have hWt : W ≠ ⊤ := fun h => hL (by
      have := hB.compl.inf_eq_bot
      rwa [h, top_inf_eq] at this)
    obtain ⟨S, hS, hHS⟩ := hgen
    obtain ⟨t, htS, x, h, hth, hxW, w₀, hw₀, hhw₀⟩ :=
      exists_generator_moving hirr hS hHS hW hWt
    have hTr : TrIn H x h := TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure htS) hth
    obtain ⟨ν, hν, hvan, hne, htrL, hlink⟩ :=
      hB.moving_data hp hua hth.1 hth.2.1 hTr hxW ⟨w₀, hw₀, hhw₀⟩
    have hxL0 : pL hB.compl x ≠ 0 := by
      intro h0
      apply hxW
      have := pW_add_pL hB.compl x
      rw [h0, add_zero] at this
      rw [← this]
      exact pW_mem hB.compl x
    obtain ⟨yL, e'', hyL, he''W, hy, hhy, hex⟩ :=
      hB.exists_partner_L hp hua hirr ⟨S, hS, hHS⟩ (pL_mem hB.compl x) hxL0 hne hvan htrL
    have hc : (ν * e'' (pL hB.compl x))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hν hex)
    have hce : (ν * e'' (pL hB.compl x))⁻¹ * e'' (pL hB.compl x) = ν⁻¹ := by
      field_simp
    have hglue := hB.glue (pL_mem hB.compl x) hyL hvan he''W htrL hy hhy hex hc
      (fun w hw hw0 => by rw [hce]; exact hlink w hw hw0)
    refine ⟨_, _, _, hglue,
      lt_of_le_of_ne (le_trans inf_le_left inf_le_left) fun heq => hex ?_⟩
    have : pL hB.compl x ∈
        L ⊓ LinearMap.ker (h - ν • β.flip (pW hB.compl x)) ⊓ LinearMap.ker e'' := by
      rw [heq]
      exact pL_mem hB.compl x
    exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2

end IsSpBlock

theorem exists_isSpBlock_top [Module.Finite (ZMod p) V] (hp : p ≠ 2) (hua : HasUniqueAxes H)
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hT : ∃ (a : V) (f : Module.Dual (ZMod p) V), a ≠ 0 ∧ f ≠ 0 ∧ TrIn H a f) :
    ∃ β : LinearMap.BilinForm (ZMod p) V, IsSpBlock H ⊤ ⊥ β := by
  suffices key : ∀ (n : ℕ) (W L : Submodule (ZMod p) V) (β : LinearMap.BilinForm (ZMod p) V),
      Module.finrank (ZMod p) L = n → IsSpBlock H W L β →
      ∃ β' : LinearMap.BilinForm (ZMod p) V, IsSpBlock H ⊤ ⊥ β' from
    key _ ⊥ ⊤ 0 rfl isSpBlock_bot
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W L β hn hB
  by_cases hL : L = ⊥
  · subst hL
    have hWt : W = ⊤ := by
      have := hB.compl.sup_eq_top
      rwa [sup_bot_eq] at this
    subst hWt
    exact ⟨β, hB⟩
  · obtain ⟨W', L', β', hB', hlt⟩ := hB.grow hp hua hirr hgen hT hL
    exact ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) W' L' β' rfl hB'

end CFSG.StandardType.McLaughlinOdd
