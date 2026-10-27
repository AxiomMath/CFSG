module

public import CFSG.LocalAnalysis.WeakClosure81.W15NineA
public import CFSG.LocalAnalysis.WeakClosure81.W15NineIdx
public import CFSG.LocalAnalysis.WeakClosure81.W15EightD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem mem_M_of_conj_le (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) {g : G}
    (hle : conjSubgroup V₀ g ≤ M ⊓ centralizer (U : Set G)) : g ∈ M := by
  have hH := h.hyp
  have hp : IsPGroup 2 (conjSubgroup V₀ g) :=
    E3.isPGroup_conjSubgroup (hH.isPGroup.to_le hH.h6.le) g
  obtain ⟨c, hc, hcle⟩ := E3.exists_le_conj_of_isSylowIn h.sylow hle hp
  have h1 : conjSubgroup V₀ (g * c⁻¹) ≤ S := by
    have := E3.conjSubgroup_mono_left c⁻¹ hcle
    rwa [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one] at this
  have h2 : conjSubgroup V₀ (g * c⁻¹) ≤ E3.wClos V₀ 0 S :=
    E3.le_wClos ⟨h1, g * c⁻¹, le_rfl, E3.mQuot_self _⟩
  rw [hI.wClos_eq hS h] at h2
  have h3 : conjSubgroup V₀ (g * c⁻¹) = V₀ :=
    Subgroup.eq_of_le_of_card_ge h2 (by rw [E3.card_conjSubgroup])
  have h4 : g * c⁻¹ ∈ normalizer (V₀ : Set G) := conjSubgroup_eq_iff_mem_normalizer.1 h3
  rw [hH.normalizer₀] at h4
  have h5 := M.mul_mem h4 hc.1
  simpa using h5

theorem centralizesMod_of_card_le (h : Cex15 M V₀ V U S) {y : G} (hyM : y ∈ M) (hy2 : y * y = 1)
    (hcard : Nat.card V ≤ 2 * Nat.card (centMod V₀ V y)) : CentralizesMod V₀ V y := by
  by_contra hnot
  have hH := h.hyp
  have hGT := (mBarGT_iff_lt_mBar M V₀ V hH.h6.elemAbelian hH.h6.le hH.h6.normalizer_eq.ge
    hH.h6.le_normalizer₀ 1).2 h.mbar
  have hc2 : CentralizesMod V₀ V (y * y) := by
    rw [hy2]
    intro v _
    simpa using V₀.one_mem
  have h4 : 2 ^ (1 + 1) * Nat.card (centMod V₀ V y) ≤ Nat.card V := hGT.1 y hyM hnot hc2
  have h4' : 4 * Nat.card (centMod V₀ V y) ≤ Nat.card V := by simpa using h4
  have hpos : 0 < Nat.card (centMod V₀ V y) := by
    haveI : Nonempty (centMod V₀ V y) := ⟨⟨1, V.one_mem, by simpa using V₀.one_mem⟩⟩
    exact Nat.card_pos
  omega

end Cex15

namespace Fam15

variable {M V₀ V U S H' : Subgroup G}

theorem inf_le_conj_M (hS : Std15 G) (h : Cex15 M V₀ V U S) (hF : Fam15 V₀ V U S H') {g : G}
    (hg : g ∈ H') : zSub15 V₀ U H' ⊓ V ≤ conjSubgroup M g := by
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (h.v1Sub15_ne_bot hS)
  have hw0' : w₀ ≠ 1 := fun e => hw₀1 (Subtype.ext e)
  have hxZ : g⁻¹ * w₀ * g ∈ zSub15 V₀ U H' := by
    have := mem_conjClosure (H'.inv_mem hg)
      ((le_sup_right : v1Sub15 V₀ U ≤ U ⊔ v1Sub15 V₀ U) hw₀)
    unfold zSub15
    simpa using this
  have hxV₀g : g⁻¹ * w₀ * g ∈ conjSubgroup V₀ g := by
    rw [mem_conjSubgroup_iff, show g * (g⁻¹ * w₀ * g) * g⁻¹ = w₀ by group]
    exact v1Sub15_le_left V₀ U hw₀
  have hx1 : g⁻¹ * w₀ * g ≠ 1 := fun e => hw0' (by
    have : w₀ = g * (g⁻¹ * w₀ * g) * g⁻¹ := by group
    rw [this, e]
    group)
  intro z hz
  have hzx : z * (g⁻¹ * w₀ * g) = (g⁻¹ * w₀ * g) * z := hF.comm z hz.1 _ hxZ
  have hc : z ∈ centralizer ({g⁻¹ * w₀ * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzx
  have hN := centralizer_le_normalizer_conj h.hyp.isTI g hxV₀g hx1 hc
  rwa [← E3.conjSubgroup_normalizer, h.hyp.normalizer₀] at hN

theorem conj_comm (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hF : Fam15 V₀ V U S H') {g : G} (hg : g ∈ H')
    (hle : conjSubgroup V₀ g ≤ M) (hgM : g ∉ M) :
    ∀ y ∈ conjSubgroup V₀ g, ∀ w ∈ zSub15 V₀ U H' ⊓ V, y * w = w * y := by
  intro y hy w hw
  have hH := h.hyp
  have hyM : y ∈ M := hle hy
  have hy2 : y * y = 1 :=
    (isElemAbelian_conjSubgroup' hH.elemAbelian₀ g).mul_self_eq_one hy
  have hΔcard : Nat.card (conjSubgroup V₀ g ⊓ V : Subgroup G) ≤ 2 := by
    have h1 := h.rk_inf_conj_le_one hI hS hgM
    have hp : IsPGroup 2 (conjSubgroup V₀ g ⊓ V : Subgroup G) := hH.isPGroup.to_le inf_le_right
    have h2 : Nat.card (conjSubgroup V₀ g ⊓ V : Subgroup G) = 2 ^ rk ↥(conjSubgroup V₀ g ⊓ V) :=
      card_eq_two_pow_mSub hp
    rw [h2]
    calc 2 ^ rk ↥(conjSubgroup V₀ g ⊓ V) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      _ = 2 := by norm_num
  have hUW : U ≤ zSub15 V₀ U H' ⊓ V := le_inf (le_sup_left.trans (le_conjClosure _ _)) h.le
  have hgen : V ≤ (zSub15 V₀ U H' ⊓ V) ⊔ V₀ :=
    calc V = U ⊔ V₀ := h.sup_eq.symm
      _ ≤ (zSub15 V₀ U H' ⊓ V) ⊔ V₀ := sup_le_sup_right hUW _
  have hcomm : ∀ w ∈ zSub15 V₀ U H' ⊓ V, y * w * y⁻¹ * w⁻¹ ∈ conjSubgroup V₀ g ⊓ V := by
    intro w hw
    have hyN : y ∈ normalizer (V : Set G) := hH.h6.normalizer_eq.ge hyM
    have hwN : w ∈ normalizer (conjSubgroup V₀ g : Set G) := by
      rw [← E3.conjSubgroup_normalizer, hH.normalizer₀]
      exact hF.inf_le_conj_M hS h hg hw
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : w * y⁻¹ * w⁻¹ ∈ conjSubgroup V₀ g :=
        (Subgroup.mem_normalizer_iff.1 hwN y⁻¹).1 ((conjSubgroup V₀ g).inv_mem hy)
      rw [show y * w * y⁻¹ * w⁻¹ = y * (w * y⁻¹ * w⁻¹) by group]
      exact (conjSubgroup V₀ g).mul_mem hy h1
    · have h1 : y * w * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hyN w).1 hw.2
      exact V.mul_mem h1 (V.inv_mem hw.2)
  have hidx := card_le_two_mul_centMod (V₀ := V₀) (V := V) (W' := zSub15 V₀ U H' ⊓ V)
    (Δ := conjSubgroup V₀ g ⊓ V) (y := y)
    (fun a ha b hb => hH.h6.elemAbelian.comm ha hb) hH.h6.le inf_le_right hgen
    (hH.h6.normalizer_eq.ge hyM) (hH.h6.le_normalizer₀ hyM) inf_le_right hΔcard hcomm
  have hcm := h.centralizesMod_of_card_le hyM hy2 hidx
  have h1 : y * w * y⁻¹ * w⁻¹ ∈ V₀ := hcm w hw.2
  have h2 : y * w * y⁻¹ * w⁻¹ ∈ conjSubgroup V₀ g := (hcomm w hw).1
  have h3 : y * w * y⁻¹ * w⁻¹ ∈ conjSubgroup V₀ g ⊓ V₀ := Subgroup.mem_inf.2 ⟨h2, h1⟩
  rw [hH.conj_inf_eq_bot hgM, Subgroup.mem_bot] at h3
  have h4 : (y * w) * (w * y)⁻¹ = 1 := by
    rw [mul_inv_rev]
    simpa [mul_assoc] using h3
  exact mul_inv_eq_one.1 h4

theorem weakly_closed (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) (hF : Fam15 V₀ V U S H') {g : G} (hg : g ∈ H')
    (hle : conjSubgroup V₀ g ≤ M) : g ∈ M := by
  by_contra hgM
  apply hgM
  have hcomm := hF.conj_comm hI hS h hg hle hgM
  have hUW : U ≤ zSub15 V₀ U H' ⊓ V := le_inf (le_sup_left.trans (le_conjClosure _ _)) h.le
  refine h.mem_M_of_conj_le hI hS (le_inf hle fun y hy => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (hcomm y hy u (hUW hu)).symm

end Fam15

end CFSG.LocalAnalysis.WeakClosure81
