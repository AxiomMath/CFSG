module

public import CFSG.LocalAnalysis.WeakClosure81.W19SixSeven
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenNine
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenConj
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem lt_rMV (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) :
    ((mSub V₀ + 1 : ℕ) : ℕ∞) < rMV D.M V := by
  have h1 : 2 < mBar D.M V₀ V c.setting.isElemAbelian := by have := c.two_lt_mBar; omega
  have h2 := h162 D V₀ V c.setting c.ne_bot h1
  refine lt_of_lt_of_le ?_ h2
  have h3 := c.two_lt_mBar
  exact_mod_cast (by omega : mSub V₀ + 1 < mBar D.M V₀ V c.setting.isElemAbelian + mSub V₀)

theorem exists_hyp65 (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) {g : G} {K : Subgroup G}
    (hc : Conf196 D V X g K) :
    ∃ k ∈ K, Hyp65 1 (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) k := by
  have hVg := hc.isElemAbelian_A c
  have hSyl : IsSylowIn 2 (D.T ⊓ K) K := hc.isE.2.2.1
  have hAS : conjSubgroup V g ≤ D.T ⊓ K := le_inf hc.le_T (hc.A_le_K c)
  have hkV : 1 < rk ↥(conjSubgroup V g) := by
    rw [E3.rk_conjSubgroup]
    have := c.three_le_rk
    omega
  have hr : ((1 : ℕ) : ℕ∞) < E3.rParam (conjSubgroup V g) := by
    rw [E3.rParam_conj]
    exact_mod_cast c.one_lt_rParam h162
  have hA : conjSubgroup V g ∈ E3.gammaSet (conjSubgroup V g) 0 (D.T ⊓ K) :=
    ⟨hAS, 1, by rw [conjSubgroup_one], by rw [conjSubgroup_one, E3.mQuot_self]⟩
  have hK : E1.IsE 1 K (D.T ⊓ K) (conjSubgroup V g) K := hc.isE_self c
  have hne : ⁅twoResidual K, E3.cClos (conjSubgroup V g) 1 (D.T ⊓ K)⁆ ≠ ⊥ := by
    rw [E3.cClos_conjV]
    exact hc.comm_twoResidual_ne_bot c h162
  have hMnormg : normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.setting.normalizer_eq]
  have hN₀g : normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.setting.normalizer₀ c.ne_bot]
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g c.V₀_le_V
  have hmbar : 1 < mBar (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg := by
    rw [mBar_conj D.M V₀ V c.setting.isElemAbelian c.V₀_le_V c.setting.pair.le_normalizer
      c.setting.pair.le_normalizer₀ g]
    have := c.two_lt_mBar
    omega
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := (c.setting.ti₀ c.ne_bot).1
  obtain ⟨-, k, hkK, hk⟩ := six_nine_one_core_of_isE (M := conjSubgroup D.M g)
    (V₀ := conjSubgroup V₀ g) (V := conjSubgroup V g) (H := K) (S := D.T ⊓ K)
    (A := conjSubgroup V g) (K := K) hVg hV₀g hMnormg.ge hN₀g.ge hMnormg hN₀g
    (isTI_form_conj (forall_conjSubgroup_eq_of_isTI hTI) g) hSyl (k := 1) hA le_rfl hK hkV hr
    hmbar hne
  exact ⟨k, hkK, hVg, hV₀g, fun h0 => c.ne_bot (conjSubgroup_eq_bot_iff.1 h0), hMnormg, hN₀g,
    isTI_conj hTI g, hk⟩

section Certified


theorem exists_inCalOStar (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) {g : G}
    {K : Subgroup G} (hc : Conf196 D V X g K) :
    ∃ k ∈ K, ∃ _ : Hyp65 1 (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) k,
      InCalOStar 1 (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) k := by
  obtain ⟨k, hkK, hk⟩ := c.exists_hyp65 h162 hc
  refine ⟨k, hkK, hk, Hyp65.inCalOStar_of_lt_rMV hk ?_⟩
  rw [rMV_conj c.setting.normalizer_eq g]
  have h1 : mSub (conjSubgroup V₀ g) = mSub V₀ := E3.rk_conjSubgroup V₀ g
  rw [h1]
  exact c.lt_rMV h162

end Certified

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
