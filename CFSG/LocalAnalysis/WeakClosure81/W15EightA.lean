module

public import CFSG.LocalAnalysis.WeakClosure81.W15Bundle

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem not_conj_V₀_le_M (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    ¬ conjSubgroup V₀ g ≤ M := by
  intro hle
  have hH := h.hyp
  have hV₀U : conjSubgroup V₀ g ≤ centralizer (U : Set G) := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hx' : g * x * g⁻¹ ∈ centralizer (U : Set G) := h.V₀_le_centralizer hx
    have hxe : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [hxe]
    exact (centralizer (U : Set G)).mul_mem ((centralizer (U : Set G)).mul_mem
      ((centralizer (U : Set G)).inv_mem hg) hx') hg
  have hp : IsPGroup 2 (conjSubgroup V₀ g) :=
    E3.isPGroup_conjSubgroup (hH.isPGroup.to_le hH.h6.le) g
  obtain ⟨c, hc, hcle⟩ := E3.exists_le_conj_of_isSylowIn h.sylow (le_inf hle hV₀U) hp
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
  apply hgM
  have h5 := M.mul_mem h4 hc.1
  simpa using h5

theorem not_conj_V_le_M (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    ¬ conjSubgroup V g ≤ M :=
  fun hle => h.not_conj_V₀_le_M hI hS hg hgM
    ((E3.conjSubgroup_mono_left g h.hyp.h6.le).trans hle)

theorem not_V_le_conj_M (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) :
    ¬ V ≤ conjSubgroup M g := by
  intro hle
  refine h.not_conj_V_le_M hI hS ((centralizer (U : Set G)).inv_mem hg)
    (fun hm => hgM (by simpa using M.inv_mem hm)) ?_
  have h1 := E3.conjSubgroup_mono_left g⁻¹ hle
  rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h1

theorem U_le_inf_conj (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    U ≤ V ⊓ conjSubgroup M g ∧ U ≤ conjSubgroup V g ⊓ M := by
  have hfix : ∀ x ∈ U, g * x * g⁻¹ = x := by
    intro x hx
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.1 hg x hx).symm
  refine ⟨fun x hx => Subgroup.mem_inf.2 ⟨h.le hx, ?_⟩,
    fun x hx => Subgroup.mem_inf.2 ⟨?_, h.hyp.le_M (h.le hx)⟩⟩
  · rw [mem_conjSubgroup_iff, hfix x hx]
    exact h.hyp.le_M (h.le hx)
  · rw [mem_conjSubgroup_iff, hfix x hx]
    exact h.le hx

theorem mQuot_conj_le (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) :
    E3.mQuot V (conjSubgroup M g) ≤ mSub V - 1 ∧ E3.mQuot (conjSubgroup V g) M ≤ mSub V - 1 := by
  have hH := h.hyp
  obtain ⟨hU1, hU2⟩ := h.U_le_inf_conj hg
  have hq := h.mQuot_eq
  have hkey : mSub V₀ ≤ mSub V - 1 := by
    have h1 := E3.card_eq_two_pow_mul hH.isPGroup h.le
    rw [card_eq_two_pow_mSub hH.isPGroup, card_eq_two_pow_mSub (hH.isPGroup.to_le h.le),
      ← pow_add] at h1
    have h2 : mSub V = E3.mQuot V U + mSub U := Nat.pow_right_injective (le_refl 2) h1
    have h3 : 1 ≤ mSub U := by
      by_contra hlt
      have h0 : mSub U = 0 := by omega
      have hcard : Nat.card U = 1 := by
        rw [card_eq_two_pow_mSub (hH.isPGroup.to_le h.le), h0]
        rfl
      exact h.ne_bot ((Subgroup.eq_bot_iff_card U).2 hcard)
    rw [← hq]
    omega
  refine ⟨?_, ?_⟩
  · calc E3.mQuot V (conjSubgroup M g) ≤ E3.mQuot V U := E3.mQuot_mono (hU1.trans inf_le_right)
      _ = mSub V₀ := hq
      _ ≤ mSub V - 1 := hkey
  · have hUg : conjSubgroup U g = U :=
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.centralizer_le_normalizer (U : Set G) hg)
    calc E3.mQuot (conjSubgroup V g) M ≤ E3.mQuot (conjSubgroup V g) U :=
          E3.mQuot_mono (hU2.trans inf_le_right)
      _ = E3.mQuot (conjSubgroup V g) (conjSubgroup U g) := by rw [hUg]
      _ = E3.mQuot V U := E3.mQuot_conjSubgroup V U g
      _ = mSub V₀ := hq
      _ ≤ mSub V - 1 := hkey

end Cex15

end CFSG.LocalAnalysis.WeakClosure81
