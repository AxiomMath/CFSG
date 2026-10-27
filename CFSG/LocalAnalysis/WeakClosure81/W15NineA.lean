module

public import CFSG.LocalAnalysis.WeakClosure81.W15EightC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cex15

variable {M V₀ V U S : Subgroup G}

theorem conj_v1Sub15_facts (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) {g : G} (hg : g ∈ centralizer (U : Set G)) (hgM : g ∉ M) {x : G}
    (hx : x ∈ conjSubgroup (v1Sub15 V₀ U) g) (hx1 : x ≠ 1) :
    x ∈ F11.CTilde M V₀ V ∧ V ⊓ centralizer ({x} : Set G) = V ⊓ conjSubgroup M g := by
  have hH := h.hyp
  have hw : g * x * g⁻¹ ∈ v1Sub15 V₀ U := mem_conjSubgroup_iff.1 hx
  have hxO : x ∈ pCoreOf 2 (centralizer (U : Set G)) := (conj_mem_pCoreOf_iff hg x).1 hw.2
  have hxS : x ∈ S := h.pCoreOf_le_S hxO
  have hxM : x ∈ M := h.S_le_M hxS
  have hxV₀g : x ∈ conjSubgroup V₀ g := mem_conjSubgroup_iff.2 hw.1
  refine ⟨h.centralizer_le_cTilde (Subgroup.mem_inf.2 ⟨hxM, h.S_le_centralizer hxS⟩), ?_⟩
  have hVΔ : V ⊓ conjSubgroup V₀ g = ⊥ := by
    by_contra hne
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hu1' : u ≠ 1 := fun e => hu1 (Subtype.ext e)
    apply h.not_V_le_conj_M hI hS hg hgM
    intro v hv
    have hvc : v ∈ centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hH.h6.elemAbelian.comm hv (Subgroup.mem_inf.1 hu).1
    have hN := centralizer_le_normalizer_conj hH.isTI g hu.2 hu1' hvc
    rwa [← E3.conjSubgroup_normalizer, hH.normalizer₀] at hN
  refine le_antisymm (fun y hy => Subgroup.mem_inf.2 ⟨hy.1, ?_⟩)
    (fun y hy => Subgroup.mem_inf.2 ⟨hy.1, ?_⟩)
  · have hN := centralizer_le_normalizer_conj hH.isTI g hxV₀g hx1 hy.2
    rwa [← E3.conjSubgroup_normalizer, hH.normalizer₀] at hN
  · have hyN : y ∈ normalizer (conjSubgroup V₀ g : Set G) := by
      rw [← E3.conjSubgroup_normalizer, hH.normalizer₀]
      exact hy.2
    have hxN : x ∈ normalizer (V : Set G) := hH.h6.normalizer_eq.ge hxM
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ V ⊓ conjSubgroup V₀ g := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 hxN y).1 hy.1) (V.inv_mem hy.1)
      · have h2 : y * x⁻¹ * y⁻¹ ∈ conjSubgroup V₀ g :=
          (Subgroup.mem_normalizer_iff.1 hyN x⁻¹).1 ((conjSubgroup V₀ g).inv_mem hxV₀g)
        rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
        exact (conjSubgroup V₀ g).mul_mem hxV₀g h2
    rw [hVΔ, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h4 : (x * y) * (y * x)⁻¹ = 1 := by
      rw [mul_inv_rev]
      simpa [mul_assoc] using h1
    exact (mul_inv_eq_one.1 h4).symm

theorem rk_inf_conj_le_one (hI : NamedInputs15 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) {g : G} (hg : g ∉ M) : rk ↥(conjSubgroup V₀ g ⊓ V) ≤ 1 := by
  have hH := h.hyp
  obtain ⟨h', hh'C, hh'M⟩ := SetLike.not_le_iff_exists.1 h.not_le
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (h.v1Sub15_ne_bot hS)
  have hw0' : w₀ ≠ 1 := fun e => hw₀1 (Subtype.ext e)
  have hx : h'⁻¹ * w₀ * h' ∈ conjSubgroup (v1Sub15 V₀ U) h' := by
    rw [mem_conjSubgroup_iff, show h' * (h'⁻¹ * w₀ * h') * h'⁻¹ = w₀ by group]
    exact hw₀
  have hx1 : h'⁻¹ * w₀ * h' ≠ 1 := fun e => hw0' (by
    have : w₀ = h' * (h'⁻¹ * w₀ * h') * h'⁻¹ := by group
    rw [this, e]
    group)
  obtain ⟨hxC, hCx⟩ := h.conj_v1Sub15_facts hI hS hh'C hh'M hx hx1
  have hxV : ¬ V ≤ centralizer ({h'⁻¹ * w₀ * h'} : Set G) := fun hle =>
    h.not_V_le_conj_M hI hS hh'C hh'M ((le_inf le_rfl hle).trans hCx.le |>.trans inf_le_right)
  have h146 := mQuot_centralizer_ge_rk_conjSubgroup_inf hH.h6.elemAbelian hH.h6.le
    hH.h6.normalizer_eq.ge hH.normalizer₀ hH.isTI (hH.h6.conjGenerated hH.ne_bot) hg hxC hxV
  rw [hCx] at h146
  have h5 : E3.mQuot V (V ⊓ conjSubgroup M h') = 1 := by
    have h6 := (h.fourteen_five_conj hI hS hh'C hh'M).1
    unfold E3.mQuot at h6 ⊢
    rwa [Subgroup.inf_relIndex_left]
  exact h146.trans h5.le

end Cex15

end CFSG.LocalAnalysis.WeakClosure81
