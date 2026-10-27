module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4be_mkTil_bot_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (mkTil (⊥ : Subgroup G) V hV) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hx
    have hx' : x ∈ modNull ⊥ V hV := (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).1 hx
    rw [mem_modNull] at hx'
    exact IntMod.val_injective (by simpa using hx')
  · rintro rfl
    exact map_one _

theorem s16h_sl4be_imgTil_inf {V A B : Subgroup G} (hV : IsElemAbelian 2 V) (hA : A ≤ V)
    (hB : B ≤ V) :
    imgTil ⊥ V hV (A ⊓ B) = imgTil ⊥ V hV A ⊓ imgTil ⊥ V hV B := by
  ext q
  rw [mem_imgTil, Subgroup.mem_inf, mem_imgTil, mem_imgTil]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  · rintro ⟨⟨x, hxA, hxq⟩, ⟨y, hyB, hyq⟩⟩
    have hxy : x = y := s16h_sl4be_mkTil_bot_injective hV (hxq.trans hyq.symm)
    exact ⟨x, ⟨hxA, hxy ▸ hyB⟩, hxq⟩

theorem s16h_sl4be_fixV_map_conj {W : Type*} [CommGroup W] (X : Subgroup (MulAut W))
    (g : MulAut W) :
    fixV (X.map (MulAut.conj g).toMonoidHom) = (fixV X).map g.toMonoidHom := by
  ext v
  constructor
  · intro h
    rw [mem_fixV] at h
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ v, ?_, ?_⟩
    · rw [mem_fixV]
      intro a ha
      have hx : (g * a * g⁻¹) v = v := h _ (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
      rw [MulAut.mul_apply, MulAut.mul_apply] at hx
      calc a (g⁻¹ v) = g⁻¹ (g (a (g⁻¹ v))) := (MulAut.inv_apply_self W g _).symm
        _ = g⁻¹ v := by rw [hx]
    · show g (g⁻¹ v) = v
      exact MulAut.apply_inv_self W g v
  · intro h
    rw [Subgroup.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    rw [mem_fixV] at hw ⊢
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haw : a w = w := hw a ha
    show (g * a * g⁻¹) (g w) = g w
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self W g w, haw]

theorem s16h_sl4be_fixV_barSub {W V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW : W ≤ stabTil ⊥ V) :
    fixV (barSub ⊥ V hV W) = imgTil ⊥ V hV (V ⊓ centralizer (W : Set G)) := by
  ext q
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV q
  rw [mem_fixV, mem_imgTil]
  constructor
  · intro h
    refine ⟨x, ⟨x.val_mem, ?_⟩, rfl⟩
    show ∀ m ∈ (W : Set G), m * x.val = x.val * m
    intro m hm
    have hms : m ∈ stabTil ⊥ V := hW hm
    have hfix := h (actTil ⊥ V hV ⟨m, hms⟩) (actTil_mem_barSub ⊥ V hV hm hms)
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot] at hfix
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hfix)
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := s16h_sl4be_mkTil_bot_injective hV hyx
    rw [hyx'] at hy
    have hyC : x.val ∈ centralizer (W : Set G) := (Subgroup.mem_inf.1 hy).2
    intro φ hφ
    obtain ⟨m, hm, rfl⟩ := (mem_barSub ⊥ V hV W φ).1 hφ
    rw [actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    exact mul_inv_eq_iff_eq_mul.2 ((Subgroup.mem_centralizer_iff.1 hyC) m hm)

theorem s16h_sl4be_preTil_fixV {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hL : L ≤ stabTil ⊥ V) :
    preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) = V ⊓ centralizer (L : Set G) := by
  have hfix := s16h_sl4be_fixV_barSub (W := L) hV hL
  refine le_antisymm ?_ ?_
  · intro g hg
    have hgV : g ∈ V := preTil_le ⊥ V hV _ hg
    rw [Subgroup.mem_inf]
    refine ⟨hgV, ?_⟩
    have hmk : mkTil ⊥ V hV (IntMod.mk hV ⟨g, hgV⟩) ∈ fixV (lBar ⊥ V hV L) :=
      (mem_preTil_iff_of_mem ⊥ V hV _ hgV).1 hg
    change mkTil ⊥ V hV (IntMod.mk hV ⟨g, hgV⟩) ∈ fixV (barSub ⊥ V hV L) at hmk
    rw [hfix] at hmk
    obtain ⟨y, hy, hyx⟩ := (mem_imgTil ⊥ V hV _ _).1 hmk
    have : y = IntMod.mk hV ⟨g, hgV⟩ := s16h_sl4be_mkTil_bot_injective hV hyx
    rw [this] at hy
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 l hl
  · intro g hg
    obtain ⟨hgV, hgC⟩ := Subgroup.mem_inf.1 hg
    rw [mem_preTil_iff_of_mem ⊥ V hV _ hgV,
      show lBar ⊥ V hV L = barSub ⊥ V hV L from rfl, hfix, mem_imgTil]
    exact ⟨IntMod.mk hV ⟨g, hgV⟩, Subgroup.mem_inf.2 ⟨hgV, hgC⟩, rfl⟩

theorem s16h_sl4be_imgTil_wSub_inf_cent {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hL : L ≤ stabTil ⊥ V) :
    imgTil ⊥ V hV (wSub ⊥ V hV L ⊓ centralizer (L : Set G)) =
      wTil ⊥ V hV L ⊓ fixV (lBar ⊥ V hV L) := by
  have hwSub_le : wSub ⊥ V hV L ≤ V := preTil_le ⊥ V hV _
  have hsub : wSub ⊥ V hV L ⊓ centralizer (L : Set G) =
      wSub ⊥ V hV L ⊓ (V ⊓ centralizer (L : Set G)) := by
    rw [← inf_assoc, inf_of_le_left hwSub_le]
  rw [hsub, ← s16h_sl4be_preTil_fixV hV hL, wSub]
  rw [← s16c167_twenty_two_preTil_inf, imgTil_preTil]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
