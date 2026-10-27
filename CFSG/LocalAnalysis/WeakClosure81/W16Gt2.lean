module

public import CFSG.LocalAnalysis.WeakClosure81.W16Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2Gt2
public import CFSG.LocalAnalysis.WeakClosure81.W162FiveMain
public import CFSG.LocalAnalysis.WeakClosure81.W16Closing

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def W16ClosingGt2 (G : Type) [Group G] [Finite G] : Prop :=
  Std15 G → ∀ ⦃M V₀ V U S R H : Subgroup G⦄ ⦃g : G⦄ ⦃B : Subgroup G⦄
    (c : Cfg1620 M V₀ V U S R H g B), 2 < mBar M V₀ V c.cex.hyp.h6.elemAbelian →
      B ⊓ pCoreOf 2 (B ⊔ conjClosure V H) ≠ ⊥ ∧
        B ⊓ pCoreOf 2 (B ⊔ conjClosure V H) ≤
          normalizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G)

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem exists_cfg1620_of_fields (h1 : W16One G) (h15 : W16Fifteen G) (h16 : W16SixteenQ G)
    (h5 : W16Five G) (hS : Std15 G) (h152 : Thm152 G) (h : Cex16 M V₀ V U S) :
    ∃ (R H : Subgroup G) (g : G) (B : Subgroup G), Cfg1620 M V₀ V U S R H g B := by
  obtain ⟨R, hR, hSR⟩ := exists_isSylowIn_ge 2 h.S_le_cTilde h.sylow.isPGroup
  obtain ⟨H, hHQ, hHmin⟩ := exists_minimal_fam16Q (h16 hS h hR hSR)
  obtain ⟨g, hgmem, hgM⟩ := SetLike.not_le_iff_exists.1 hHQ.2.1
  have hgH : g ∈ H := hgmem.1
  have hgC : g ∈ centralizer (U : Set G) := hgmem.2
  have hV₀gS : conjSubgroup V₀ g ≤ S :=
    (conjSubgroup_le_conjClosure_of_mem hgH (le_sup_right : V₀ ≤ U ⊔ V₀)).trans
      (h.conjClosure_le_S h1 hS hSR hHQ)
  have hV₀gR : conjSubgroup V₀ g ≤ R := hV₀gS.trans hSR
  have hV₀gC : conjSubgroup V₀ g ≤ F11.CTilde M V₀ V := hV₀gR.trans hR.le
  have hcen : ∀ x ∈ conjSubgroup V₀ g, x ≠ 1 → V ⊓ centralizer ({x} : Set G) = U ⊔ V₀ :=
    fun x hx hx1 => h.inf_centralizer_eq h1 h5 h15 hS hgC hgM hV₀gC hx hx1
  have hL := h.inf_centralizer_sup_conj_eq h15 hS hgC hgM
  obtain ⟨B, hBR, hBconj, hnot, hcenB⟩ := h.exists_B h152 hR hV₀gR hcen
  exact ⟨R, H, g, B, ⟨h, hR, hSR, hHQ, hHmin, hgmem, hgM, hcen, hL, hBR, hBconj, hnot, hcenB,
    h.sup_ne_conjClosure hR hHQ hgC hL hBR hnot⟩⟩

end Cex16

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem false_of_inf_pCoreOf (c : Cfg1620 M V₀ V U S R H g B)
    (hne : B ⊓ pCoreOf 2 (B ⊔ conjClosure V H) ≠ ⊥)
    (hle : B ⊓ pCoreOf 2 (B ⊔ conjClosure V H) ≤
      normalizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G)) : False := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hxB : (x : G) ∈ B := x.2.1
  have hxN : (x : G) ∈ normalizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) := hle x.2
  have hxC : (x : G) ∈ F11.CTilde M V₀ V := c.sylow.le (c.B_le hxB)
  have hxV : (x : G) ∈ normalizer (V : Set G) := by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact cTilde_le_M M V₀ V hxC
  have hxU : (x : G) ∈ normalizer (U : Set G) := by
    have := mem_normalizer_inf_centralizer_wc16 hxV hxN
    rwa [c.centralizer_L] at this
  have hxcU := c.cex.mem_centralizer_of_mem_normalizer hxC hxU
  have hx1' : (x : G) ≠ 1 := fun e => hx1 (Subtype.ext e)
  apply c.not_comm
  intro u hu
  have hu' : u ∈ V ⊓ centralizer ({(x : G)} : Set G) := by
    refine Subgroup.mem_inf.2 ⟨c.cex.le hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    exact (Subgroup.mem_centralizer_iff.1 hxcU u hu).symm
  rw [c.centralizer_B _ hxB hx1'] at hu'
  exact hu'.2

end Cfg1620

namespace Cex16

variable {M V₀ V U S : Subgroup G}

theorem false_of_gt2 (h1 : W16One G) (h15 : W16Fifteen G) (h16 : W16SixteenQ G)
    (hC : W16ClosingGt2 G) (h5 : W16Five G) (hS : Std15 G) (h152 : Thm152 G)
    (h : Cex16 M V₀ V U S) (hm : 2 < mBar M V₀ V h.hyp.h6.elemAbelian) : False := by
  obtain ⟨R, H, g, B, c⟩ := h.exists_cfg1620_of_fields h1 h15 h16 h5 hS h152
  obtain ⟨hne, hle⟩ := hC hS c hm
  exact c.false_of_inf_pCoreOf hne hle

end Cex16

section Certified

theorem sixteen_two_gt2_of_inputs {M V₀ V : Subgroup G} (hI : Inputs15Two G) (h1 : W16One G)
    (h15 : W16Fifteen G) (h16 : W16SixteenQ G) (hC : W16ClosingGt2 G) (hS : Std15 G)
    (hyp : Hyp15 M V₀ V) (hm : 2 < mBar M V₀ V hyp.h6.elemAbelian) :
    ((mBar M V₀ V hyp.h6.elemAbelian + mSub V₀ : ℕ) : ℕ∞) ≤ rMV M V := by
  by_contra hcon
  obtain ⟨U, S, h⟩ := exists_cex16 hyp (by omega) (not_le.1 hcon)
  exact h.false_of_gt2 h1 h15 h16 hC (w16Five_of_one h1 (thm152_of_inputs hI hS)) hS
    (thm152_of_inputs hI hS) hm

theorem w3Thm162Gt2_holds (hI : Inputs15Two G) (h1 : W16One G) (h15 : W16Fifteen G)
    (h16 : W16SixteenQ G) (hC : W16ClosingGt2 G) : W3Thm162Gt2 G := by
  intro D V₀ V h hV₀ hm
  exact sixteen_two_gt2_of_inputs hI h1 h15 h16 hC (Std15.of_data D) (Hyp15.of_setting h hV₀) hm

end Certified

end CFSG.LocalAnalysis.WeakClosure81
