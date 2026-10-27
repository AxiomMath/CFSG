module

import CFSG.Quasithin.Background.F9Basic

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveF
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveM
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveThirteenC
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteenY
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveFourteenLa

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

section Certified


theorem Hyp167.comm_conj_eSub_of_one_lt (hI : NamedInputs15 G)
    (hS : Std15 G) (h152 : Thm152 G) (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) (hm : 1 < mSub V₀) :
    eSub V₀ X T ≤ centralizer (conjSubgroup V₀ g : Set G) := by
  by_contra hne
  have hV₀ : V₀ ≤ pCoreOf 2 H := hX.cex.hyp.h6.le.trans hVO
  have hEab : IsElemAbelian 2 (eSub V₀ X T) := Hyp167.isElemAbelian_eSub h1 hS hV₀ hX
  have hEcent : eSub V₀ X T ≤ centralizer (eSub V₀ X T : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm hEab hy hx
  have hBC : conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) = ⊥ := by
    by_contra hc
    have hF : conjClosure V₀ X ≤ centralizer (conjSubgroup V₀ g : Set G) :=
      Hyp167.closure_le_centralizer_of_ne_bot h1 hS hX hVO hc
    refine hne ?_
    show conjClosure (V₀ ⊓ centralizer (T : Set G)) X ≤
      centralizer (conjSubgroup V₀ g : Set G)
    exact (conjClosure_mono inf_le_left le_rfl).trans hF
  have hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥ := by
    refine le_bot_iff.mp ?_
    calc conjSubgroup V₀ g ⊓ eSub V₀ X T
        ≤ conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) :=
          inf_le_inf_left _ hEcent
      _ = ⊥ := hBC
  have hK : kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) :=
    Hyp167.kerMOf_le_centralizer_of_inf_eq_bot hI hS h152 h1 hV₀ hX hBE
  have hBbot : conjSubgroup V₀ g ⊓ kerMOf M X = ⊥ := by
    refine le_bot_iff.mp ?_
    calc conjSubgroup V₀ g ⊓ kerMOf M X
        ≤ conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) :=
          inf_le_inf_left _ hK
      _ = ⊥ := hBC
  have hcardB : Nat.card (conjSubgroup V₀ g) = 2 ^ mSub V₀ := by
    rw [card_conjSubgroup' g V₀, card_eq_two_pow_mSub hX.cex.hyp.elemAbelian₀.isPGroup]
  have hD2 : 2 < (conjSubgroup V₀ g ⊓ kerMOf M X).relIndex (conjSubgroup V₀ g) := by
    rw [hBbot, Subgroup.relIndex_bot_left, hcardB]
    have h : 2 ^ 1 < 2 ^ mSub V₀ :=
      (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).2 hm
    simpa using h
  have hBX : conjSubgroup V₀ g ≤ X :=
    (E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le).trans hX.mem.2.2.A_le
  have hXM : ¬ X ≤ M := by
    intro hXM
    have hN : (X.subgroupOf X).Normal := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    have hle : X ≤ kerMOf M X := le_kerMOf_of_normal le_rfl hN hXM
    exact hX.mem.2.2.not_le_ker (hX.mem.2.2.A_le.trans hle)
  obtain ⟨Y, hYX, hY⟩ :=
    exists_isMinimalNotLE (B := M) (A := conjSubgroup V₀ g) (L₀ := X) hBX hXM
  have hDab : IsElemAbelian 2 (conjSubgroup V₀ g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.elemAbelian₀ g
  have hBA : conjSubgroup V₀ g ≤ conjSubgroup V g :=
    E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le
  obtain ⟨-, k, hmk, h12⟩ :=
    Hyp167.setting12Two_of_min hI.thmB hS hX hDab hBA hD2 hY hYX
  have hmq : E3.mQuot (conjSubgroup V₀ g) (conjSubgroup V₀ g ⊓ kerMOf M X) = mSub V₀ := by
    change padicValNat 2
      ((conjSubgroup V₀ g ⊓ kerMOf M X).relIndex (conjSubgroup V₀ g)) = mSub V₀
    rw [hBbot, Subgroup.relIndex_bot_left, hcardB, padicValNat.prime_pow]
  have hk_le_n : k ≤ E3.mQuot V (U ⊔ V₀) :=
    Hyp167.le_n_of_quad hI.mult hS h152 h1 hX hVO hDab hBA hY.1 hYX hY.2.1 h12
      (Hyp167.quad_of_inf_centralizer_eq_bot h1 hS hX hVO hBC)
  have hn_lt := Hyp167.lt_mSub_of_inf_centralizer_eq_bot hI hS h152 h1 hX hVO hm hBC
  have hm_le_k : mSub V₀ ≤ k := by
    rw [← hmq]
    exact hmk
  omega

theorem Hyp167.comm_conj_eSub_of_le_one (hI : NamedInputs15 G)
    (hS : Std15 G) (h152 : Thm152 G) (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) (hm : mSub V₀ ≤ 1) :
    eSub V₀ X T ≤ centralizer (conjSubgroup V₀ g : Set G) := by
  have hV₀ : V₀ ≤ pCoreOf 2 H := hX.cex.hyp.h6.le.trans hVO
  have hne : conjSubgroup V₀ g ⊓ eSub V₀ X T ≠ ⊥ :=
    Hyp167.inf_eSub_ne_bot_of_mSub_le_one hI hS h152 h1 hX hVO hm
  have hcardV₀ : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub hX.cex.hyp.elemAbelian₀.isPGroup
  have hm1 : mSub V₀ = 1 := by
    have h1 : 1 < Nat.card V₀ := (Subgroup.one_lt_card_iff_ne_bot V₀).mpr hX.cex.hyp.ne_bot
    rw [hcardV₀] at h1
    have h0 : 1 ≤ mSub V₀ := by
      by_contra hlt
      have hz : mSub V₀ = 0 := by omega
      rw [hz, pow_zero] at h1
      exact lt_irrefl 1 h1
    omega
  have hcardB : Nat.card (conjSubgroup V₀ g) = 2 := by
    rw [card_conjSubgroup' g V₀, hcardV₀, hm1, pow_one]
  have hBE : conjSubgroup V₀ g ≤ eSub V₀ X T := le_of_card_eq_two_of_inf_ne_bot hcardB hne
  have hEab : IsElemAbelian 2 (eSub V₀ X T) := Hyp167.isElemAbelian_eSub h1 hS hV₀ hX
  have hEcent : eSub V₀ X T ≤ centralizer (eSub V₀ X T : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm hEab hy hx
  exact hEcent.trans (Subgroup.centralizer_le hBE)

theorem Hyp167.comm_conj_eSub (hI : NamedInputs15 G)
    (hS : Std15 G) (h152 : Thm152 G) (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T)
    (hVO : V ≤ pCoreOf 2 H) :
    eSub V₀ X T ≤ centralizer (conjSubgroup V₀ g : Set G) := by
  rcases lt_or_ge 1 (mSub V₀) with hm | hm
  · exact Hyp167.comm_conj_eSub_of_one_lt hI hS h152 h1 hX hVO hm
  · exact Hyp167.comm_conj_eSub_of_le_one hI hS h152 h1 hX hVO hm

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
