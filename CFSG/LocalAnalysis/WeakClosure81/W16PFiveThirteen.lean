module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

private theorem inf_conj_eSub_ne_bot_of_conj_eq_self (hX : Hyp167 M V₀ V U S H g X T)
    (hB : conjSubgroup V₀ g = V₀) : conjSubgroup V₀ g ⊓ eSub V₀ X T ≠ ⊥ := by
  have hTnorm : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hX.cex.hyp.normalizer₀]
    exact hX.sylow.le.trans inf_le_right
  have hZ : V₀ ⊓ centralizer (T : Set G) ≠ ⊥ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
      hX.sylow.isPGroup hX.cex.hyp.elemAbelian₀.isPGroup hX.cex.hyp.ne_bot hTnorm
  have hle : V₀ ⊓ centralizer (T : Set G) ≤ eSub V₀ X T := le_conjClosure _ _
  intro hbot
  rw [hB] at hbot
  exact hZ (le_bot_iff.1 ((le_inf inf_le_left hle).trans hbot.le))

section Certified


theorem Hyp167.inf_conj_eSub_ne_bot_of_conj_ne_self (hI : NamedInputs15 G) (hS : Std15 G)
    (h152 : Thm152 G) (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hB : conjSubgroup V₀ g ≠ V₀) : conjSubgroup V₀ g ⊓ eSub V₀ X T ≠ ⊥ := by
  intro hBE
  have hAab : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hA_le_X : conjSubgroup V g ≤ X := hX.mem.2.2.A_le
  have hKX : X ≤ M → kerMOf M X = X := by
    intro hXM
    exact le_antisymm (kerMOf_le_group M X)
      (le_kerMOf_of_normal le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance) hXM)
  have hXM : ¬ X ≤ M := by
    intro hXM
    exact hX.mem.2.2.not_le_ker (by rw [hKX hXM]; exact hA_le_X)
  obtain ⟨Y, hYX, hYmin⟩ := exists_isMinimalNotLE (B := M) hA_le_X hXM
  have hn : 1 ≤ E3.mQuot V (U ⊔ V₀) := Cex16.one_le_n h152 hX.cex
  have hmV₀ : 1 ≤ mSub V₀ := by
    have hP : IsPGroup 2 V₀ := hX.cex.hyp.elemAbelian₀.isPGroup
    haveI : Nontrivial ↥V₀ := (Subgroup.nontrivial_iff_ne_bot V₀).2 hX.cex.hyp.ne_bot
    have h2 : 1 < Nat.card ↥V₀ := Finite.one_lt_card_iff_nontrivial.2 inferInstance
    rw [card_eq_two_pow_mSub hP] at h2
    by_contra hlt
    have h0 : mSub V₀ = 0 := by omega
    rw [h0, pow_zero] at h2
    omega
  have hmBar : 2 ≤ mBar M V₀ V hX.cex.hyp.h6.elemAbelian := by
    have := hX.cex.n_lt_mBar
    omega
  have hmin := Hyp167.min_le_mQuot_A hI hS h152 h1 hX hVO hBE
  have h2mA : 2 ≤ E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) :=
    le_trans (le_min (by omega) hmBar) hmin
  have hD2 : 2 < ((conjSubgroup V g) ⊓ kerMOf M X).relIndex (conjSubgroup V g) := by
    have hpow := E3.relIndex_eq_two_pow hAab.isPGroup
      ((conjSubgroup V g) ⊓ kerMOf M X)
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ kerMOf M X) :=
          Nat.pow_le_pow_right (by norm_num) h2mA
      _ = ((conjSubgroup V g) ⊓ kerMOf M X).relIndex (conjSubgroup V g) := hpow.symm
  obtain ⟨_, k, hmA_le_k, h12⟩ :=
    Hyp167.setting12Two_of_min hI.thmB hS hX hAab le_rfl hD2 hYmin hYX
  have hcomm : eSub V₀ X T ≤ centralizer (conjSubgroup V₀ g : Set G) :=
    Hyp167.comm_conj_eSub hI hS h152 h1 hX hVO
  have hB_le_CE : conjSubgroup V₀ g ≤ centralizer (eSub V₀ X T : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1 (hcomm he)) b hb).symm
  have hBne : conjSubgroup V₀ g ≠ ⊥ := by
    intro hbot
    apply hX.cex.hyp.ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    have hmem : g⁻¹ * v * g ∈ conjSubgroup V₀ g :=
      (mem_conjSubgroup_iff).2 (by simpa [mul_assoc] using hv)
    rw [hbot] at hmem
    have h1 : g⁻¹ * v * g = 1 := Subgroup.mem_bot.1 hmem
    calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [h1]
      _ = 1 := by group
  have hc : conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) ≠ ⊥ := by
    rw [inf_eq_left.2 hB_le_CE]
    exact hBne
  have hF : conjClosure V₀ X ≤ centralizer (conjSubgroup V₀ g : Set G) :=
    Hyp167.closure_le_centralizer_of_ne_bot h1 hS hX hVO hc
  have hNB : Subgroup.normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup M g := by
    rw [← E3.conjSubgroup_normalizer V₀ g, hX.cex.hyp.normalizer₀]
  have hFA : conjClosure V₀ X ≤ conjSubgroup M g :=
    hF.trans ((Subgroup.centralizer_le_normalizer (conjSubgroup V₀ g : Set G)).trans
      (le_of_eq hNB))
  have hk_le_m : k ≤ mSub V₀ :=
    Hyp167.le_mSub_of_F hI.mult hS h152 h1 hX hVO hYmin.1 hYX hYmin.2.1 h12 hFA
  have hmin_le_m : Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
      (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) ≤ mSub V₀ :=
    hmin.trans (hmA_le_k.trans hk_le_m)
  have hsub_lt : mSub V₀ < E3.mQuot V (U ⊔ V₀) + mSub V₀ := by omega
  have hbar : mBar M V₀ V hX.cex.hyp.h6.elemAbelian ≤ mSub V₀ :=
    (min_le_iff.1 hmin_le_m).resolve_left (not_le.2 hsub_lt)
  have hn_lt_m : E3.mQuot V (U ⊔ V₀) < mSub V₀ :=
    lt_of_lt_of_le hX.cex.n_lt_mBar hbar
  have hV₀A : V₀ ≤ conjSubgroup V g :=
    Hyp167.V₀_le_A hI.mult hS h152 h1 hX hVO hYmin.1 hYX hYmin.2.1 h12 hFA
  have hcv : ∀ x ∈ X, conjSubgroup V x ≤ centralizer (conjSubgroup V₀ g : Set G) :=
    Hyp167.conj_V_le_centralizer_B hS h152 h1 hX hVO hn_lt_m hV₀A hF
  have hI_le_CB : conjClosure V X ≤ centralizer (conjSubgroup V₀ g : Set G) := by
    refine conjClosure_le fun x hx v hv => ?_
    refine hcv x⁻¹ (X.inv_mem hx) ((mem_conjSubgroup_iff).2 ?_)
    have hxv : x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v := by group
    rw [hxv]
    exact hv
  have hIA : conjClosure V X ≤ conjSubgroup M g :=
    hI_le_CB.trans ((Subgroup.centralizer_le_normalizer (conjSubgroup V₀ g : Set G)).trans
      (le_of_eq hNB))
  have hquad := Hyp167.quad_of_le_conjSubgroup_M hX hIA
  have hkn : k ≤ E3.mQuot V (U ⊔ V₀) :=
    Hyp167.le_n_of_quad hI.mult hS h152 h1 hX hVO hAab le_rfl hYmin.1 hYX hYmin.2.1 h12
      hquad
  have hbar_le_min : mBar M V₀ V hX.cex.hyp.h6.elemAbelian ≤
      Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
        (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) :=
    le_min (hbar.trans (Nat.le_add_left (mSub V₀) (E3.mQuot V (U ⊔ V₀)))) le_rfl
  have hn_lt_k : E3.mQuot V (U ⊔ V₀) < k :=
    lt_of_lt_of_le (lt_of_lt_of_le hX.cex.n_lt_mBar hbar_le_min) (hmin.trans hmA_le_k)
  exact absurd (lt_of_le_of_lt hkn hn_lt_k) (lt_irrefl k)

theorem Hyp167.inf_conj_eSub_ne_bot (hI : NamedInputs15 G) (hS : Std15 G) (h152 : Thm152 G)
    (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H) :
    conjSubgroup V₀ g ⊓ eSub V₀ X T ≠ ⊥ := by
  by_cases hB : conjSubgroup V₀ g = V₀
  · exact inf_conj_eSub_ne_bot_of_conj_eq_self hX hB
  · exact Hyp167.inf_conj_eSub_ne_bot_of_conj_ne_self hI hS h152 h1 hX hVO hB

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
