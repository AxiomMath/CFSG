module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Zc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open S18 (tilOf)
open scoped commutatorElement

section Elementwise

variable {G : Type} [Group G]

private theorem s16t_l4_comm_mul_of_commute {x y w : G} (h : x * ⁅y, w⁆ = ⁅y, w⁆ * x) :
    ⁅x * y, w⁆ = ⁅y, w⁆ * ⁅x, w⁆ := by
  have h1 : ⁅x * y, w⁆ = (x * ⁅y, w⁆ * x⁻¹) * ⁅x, w⁆ := by
    simp only [commutatorElement_def]
    group
  rw [h1, h]
  group

theorem s16t_l4_comm_commutator {Y V₀ : Subgroup G} (hY : ∀ y ∈ Y, ∀ u ∈ V₀, y * u = u * y)
    (hV₀ : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a) {w x y : G} (hx : x ∈ Y) (hy : y ∈ Y)
    (hxw : ⁅x, w⁆ ∈ V₀) (hyw : ⁅y, w⁆ ∈ V₀) : ⁅⁅x, y⁆, w⁆ = 1 := by
  have hmul : ∀ a ∈ Y, ∀ b ∈ Y, ⁅b, w⁆ ∈ V₀ → ⁅a * b, w⁆ = ⁅b, w⁆ * ⁅a, w⁆ :=
    fun a ha b _ hbw => s16t_l4_comm_mul_of_commute (hY a ha _ hbw)
  have hinv : ∀ a ∈ Y, ⁅a, w⁆ ∈ V₀ → ⁅a⁻¹, w⁆ = ⁅a, w⁆⁻¹ := by
    intro a ha haw
    have h1 : ⁅a⁻¹ * a, w⁆ = a⁻¹ * ⁅a, w⁆ * a * ⁅a⁻¹, w⁆ := by
      simp only [commutatorElement_def]
      group
    have h2 : a⁻¹ * ⁅a, w⁆ * a = ⁅a, w⁆ := by
      rw [mul_assoc, ← hY a ha _ haw, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h2, inv_mul_cancel, commutatorElement_one_left] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hxi : ⁅x⁻¹, w⁆ = ⁅x, w⁆⁻¹ := hinv x hx hxw
  have hyi : ⁅y⁻¹, w⁆ = ⁅y, w⁆⁻¹ := hinv y hy hyw
  have hxi_mem : ⁅x⁻¹, w⁆ ∈ V₀ := hxi ▸ V₀.inv_mem hxw
  have hyi_mem : ⁅y⁻¹, w⁆ ∈ V₀ := hyi ▸ V₀.inv_mem hyw
  have hxy : ⁅x * y, w⁆ = ⁅y, w⁆ * ⁅x, w⁆ := hmul x hx y hy hyw
  have hxy_mem : ⁅x * y, w⁆ ∈ V₀ := hxy ▸ V₀.mul_mem hyw hxw
  have h3 : ⁅x * y * x⁻¹, w⁆ = ⁅x⁻¹, w⁆ * ⁅x * y, w⁆ :=
    hmul (x * y) (Y.mul_mem hx hy) x⁻¹ (Y.inv_mem hx) hxi_mem
  have h3_mem : ⁅x * y * x⁻¹, w⁆ ∈ V₀ := h3 ▸ V₀.mul_mem hxi_mem hxy_mem
  have h4 : ⁅x * y * x⁻¹ * y⁻¹, w⁆ = ⁅y⁻¹, w⁆ * ⁅x * y * x⁻¹, w⁆ :=
    hmul (x * y * x⁻¹) (Y.mul_mem (Y.mul_mem hx hy) (Y.inv_mem hx)) y⁻¹ (Y.inv_mem hy) hyi_mem
  have hc : ⁅y, w⁆ * ⁅x, w⁆ = ⁅x, w⁆ * ⁅y, w⁆ := hV₀ _ hyw _ hxw
  rw [commutatorElement_def x y, h4, h3, hxy, hxi, hyi, hc]
  group

theorem s16t_l4_comm_conj {Y V₀ : Subgroup G} (hY : ∀ y ∈ Y, ∀ u ∈ V₀, y * u = u * y)
    {w x z : G} (hx : x ∈ Y) (hz : z ∈ Y) (hxw : ⁅x, w⁆ ∈ V₀) (hzw : ⁅z, w⁆ = 1) :
    ⁅x * z * x⁻¹, w⁆ = 1 := by
  have hmul : ∀ a ∈ Y, ∀ b ∈ Y, ⁅b, w⁆ ∈ V₀ → ⁅a * b, w⁆ = ⁅b, w⁆ * ⁅a, w⁆ :=
    fun a ha b _ hbw => s16t_l4_comm_mul_of_commute (hY a ha _ hbw)
  have hinv : ⁅x⁻¹, w⁆ = ⁅x, w⁆⁻¹ := by
    have h1 : ⁅x⁻¹ * x, w⁆ = x⁻¹ * ⁅x, w⁆ * x * ⁅x⁻¹, w⁆ := by
      simp only [commutatorElement_def]
      group
    have h2 : x⁻¹ * ⁅x, w⁆ * x = ⁅x, w⁆ := by
      rw [mul_assoc, ← hY x hx _ hxw, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h2, inv_mul_cancel, commutatorElement_one_left] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hxz : ⁅x * z, w⁆ = ⁅x, w⁆ := by
    rw [hmul x hx z hz (hzw ▸ V₀.one_mem), hzw, one_mul]
  have hxz_mem : ⁅x * z, w⁆ ∈ V₀ := hxz ▸ hxw
  have hxi_mem : ⁅x⁻¹, w⁆ ∈ V₀ := hinv ▸ V₀.inv_mem hxw
  rw [hmul (x * z) (Y.mul_mem hx hz) x⁻¹ (Y.inv_mem hx) hxi_mem, hxz, hinv, inv_mul_cancel]

end Elementwise

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16t_l4_actTil_tilOf_eq_iff (g : ↥(stabTil V₀ V)) {w : G} (hw : w ∈ V) :
    actTil V₀ V hV g (tilOf V₀ V hV w hw) = tilOf V₀ V hV w hw ↔
      (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ V₀ := by
  unfold tilOf
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
  exact Iff.rfl

theorem s16t_l4_ptStab_perfect {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {w : W} (hpt : Close16PtStab H w) :
    ⁅H ⊓ MulAction.stabilizer (MulAut W) w, H ⊓ MulAction.stabilizer (MulAut W) w⁆ =
      H ⊓ MulAction.stabilizer (MulAut W) w := by
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  obtain ⟨f, hfs, hf2, -⟩ := hpt.quot
  haveI := GoldS146P.sl_simple 3 le_rfl
  have hq : Close16Quot3 (H ⊓ MulAction.stabilizer (MulAut W) w)
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) f := by
    refine ⟨hfs, GoldS146P.sl_simple 3 le_rfl, ?_, ?_, hf2⟩
    · rintro ⟨⟨h⟩⟩
      obtain ⟨a, b, hab⟩ := GoldS146P.sl_nonabelian 3 le_rfl
      exact hab (h a b)
    · rw [close16_card_sl_three_two]
      norm_num
  have h := hq.opp_perfect
  rwa [hpt.opp] at h

theorem s16t_l4_barSub_cent_eq (hS : S16tL4Setting D V₀ V L hV) {Y : Subgroup G}
    (hY : S16tL4Pack D V₀ V L hV Y) {w : G} (hw : w ∈ V)
    (hpt : Close16PtStab (lBar V₀ V hV L) (tilOf V₀ V hV w hw)) :
    barSub V₀ V hV (Y ⊓ centralizer ({w} : Set G)) =
      lBar V₀ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV)) (tilOf V₀ V hV w hw) := by
  have hbar : barSub V₀ V hV Y = lBar V₀ V hV L := hY.bar_eq
  have hY0 := s16t_l4_le_centralizer_v0 hS hY
  have hYc : ∀ y ∈ Y, ∀ u ∈ V₀, y * u = u * y := fun y hy u hu =>
    (Subgroup.mem_centralizer_iff.1 (hY0 hy) u hu).symm
  have hV₀ : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    IsElemAbelian.comm hV (hS.counterex.setting.hyp151.hyp125.pairFacts.le ha)
      (hS.counterex.setting.hyp151.hyp125.pairFacts.le hb)
  haveI : Finite (Vtil V₀ V hV) := inferInstance
  apply le_antisymm
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV _ φ).1 hφ
    have hgY := (Subgroup.mem_inf.1 hg).1
    have hgw := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← hbar]
      exact (mem_barSub V₀ V hV Y _).2 ⟨g, hgY, rfl⟩
    · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      refine (s16t_l4_actTil_tilOf_eq_iff g hw).2 ?_
      have h1 : (g : G) * w * (g : G)⁻¹ * w⁻¹ = 1 := by
        rw [hgw]
        group
      rw [h1]
      exact V₀.one_mem
  · calc lBar V₀ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV)) (tilOf V₀ V hV w hw)
        = ⁅lBar V₀ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV)) (tilOf V₀ V hV w hw),
            lBar V₀ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV))
              (tilOf V₀ V hV w hw)⁆ := (s16t_l4_ptStab_perfect hpt).symm
      _ ≤ barSub V₀ V hV (Y ⊓ centralizer ({w} : Set G)) := by
        rw [Subgroup.commutator_le]
        intro φ₁ hφ₁ φ₂ hφ₂
        have hfix : ∀ φ ∈ lBar V₀ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV))
            (tilOf V₀ V hV w hw), ∃ g : ↥(stabTil V₀ V), (g : G) ∈ Y ∧ actTil V₀ V hV g = φ ∧
              ⁅(g : G), w⁆ ∈ V₀ := by
          intro φ hφ
          obtain ⟨g, hgY, rfl⟩ := (mem_barSub V₀ V hV Y φ).1 (hbar ▸ (Subgroup.mem_inf.1 hφ).1)
          have h2 := (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hφ).2)
          rw [MulAut.smul_def] at h2
          exact ⟨g, hgY, rfl, (s16t_l4_actTil_tilOf_eq_iff g hw).1 h2⟩
        obtain ⟨g₁, hg₁Y, rfl, hg₁w⟩ := hfix φ₁ hφ₁
        obtain ⟨g₂, hg₂Y, rfl, hg₂w⟩ := hfix φ₂ hφ₂
        refine (mem_barSub V₀ V hV _ _).2 ⟨⁅g₁, g₂⁆, ?_, map_commutatorElement _ g₁ g₂⟩
        have hcoe : ((⁅g₁, g₂⁆ : ↥(stabTil V₀ V)) : G) = ⁅(g₁ : G), (g₂ : G)⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hcoe]
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have : ⁅(g₁ : G), (g₂ : G)⁆ = (g₁ : G) * (g₂ : G) * (g₁ : G)⁻¹ * (g₂ : G)⁻¹ := rfl
          rw [this]
          exact Y.mul_mem (Y.mul_mem (Y.mul_mem hg₁Y hg₂Y) (Y.inv_mem hg₁Y)) (Y.inv_mem hg₂Y)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (commutatorElement_eq_one_iff_mul_comm.1
            (s16t_l4_comm_commutator hYc hV₀ hg₁Y hg₂Y hg₁w hg₂w))

theorem s16t_l4_ptStab_of_fix (hS : S16tL4Setting D V₀ V L hV) {w : G} (hw : w ∈ V)
    (hw0 : w ∉ V₀) {τ : MulAut (Vtil V₀ V hV)} (hτK : τ ∈ kBar D.M V₀ V hV L) (hτ1 : τ ≠ 1)
    (hτw : τ (tilOf V₀ V hV w hw) = tilOf V₀ V hV w hw) :
    Close16PtStab (lBar V₀ V hV L) (tilOf V₀ V hV w hw) := by
  obtain ⟨-, ⟨L₀, -, -, -, hsum⟩, -⟩ := hS.shape
  obtain ⟨I, hnat, h01, hsup⟩ := s16c167_seventeen_sumOfNat_two hsum
  have hw1 : tilOf V₀ V hV w hw ≠ 1 := by
    intro h1
    rw [tilOf, ← map_one (mkTil V₀ V hV), mkTil_eq_iff] at h1
    have h2 : (IntMod.mk hV ⟨w, hw⟩).val ∈ V₀ := by simpa using h1
    exact hw0 h2
  refine close16_pt_stab_of_two_summands (s16t_l4_card_lbar hS) hnat h01 hsup hτ1 ?_ hw1 hτw
  intro h hh
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hτK).2 h hh).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
