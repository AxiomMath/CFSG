module

public import CFSG.LocalAnalysis.WeakClosure81.W16Cfg
public import CFSG.LocalAnalysis.WeakClosure81.W16Seventeen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cex16

variable {M V₀ V U S R H : Subgroup G}

theorem mem_of_conj_le_centralizer (h15 : W16Fifteen G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) {y : G} (hle : conjSubgroup V y ≤ M ⊓ centralizer (U : Set G)) :
    y ∈ M := by
  have hp : IsPGroup 2 (conjSubgroup V y) := E3.isPGroup_conjSubgroup h.hyp.isPGroup y
  obtain ⟨c, hc, hcle⟩ := E3.exists_le_conj_of_isSylowIn h.sylow hle hp
  have h1 : conjSubgroup V (y * c⁻¹) ≤ S := by
    have := E3.conjSubgroup_mono_left c⁻¹ hcle
    rwa [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one] at this
  have h4 := h.mem_of_conj_le_S h15 hS h1
  have h5 : y * c⁻¹ * c ∈ M := M.mul_mem h4 hc.1
  have e : y * c⁻¹ * c = y := by group
  rwa [e] at h5

theorem centralizer_conjClosure_le_conj (h : Cex16 M V₀ V U S) {x h' : G}
    (hxI : x ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G)) (hh : h' ∈ H) :
    x ∈ conjSubgroup M h' := by
  rw [mem_conjSubgroup_iff]
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.hyp.ne_bot
  have hw1 : (w : G) ≠ 1 := fun e => hw (Subtype.ext e)
  have hwI : (w : G) ∈ conjClosure (U ⊔ V₀) H :=
    le_conjClosure (U ⊔ V₀) H (Subgroup.mem_sup_right w.2)
  have key : ∀ y : G, y ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) → y ∈ M := by
    intro y hy
    refine h.hyp.centralizer_le w.2 hw1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    exact Subgroup.mem_centralizer_iff.1 hy _ hwI
  have hxI' : h' * x * h'⁻¹ ∈ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzI : h'⁻¹ * z * h' ∈ conjClosure (U ⊔ V₀) H := by
      have hnorm : h'⁻¹ ∈ Subgroup.normalizer (conjClosure (U ⊔ V₀) H : Set G) :=
        le_normalizer_conjClosure (U ⊔ V₀) H (H.inv_mem hh)
      simpa using (Subgroup.mem_normalizer_iff.1 hnorm z).1 hz
    have hcomm : (h'⁻¹ * z * h') * x = x * (h'⁻¹ * z * h') :=
      Subgroup.mem_centralizer_iff.1 hxI _ hzI
    have hkey : (h' * x * h'⁻¹) * z = z * (h' * x * h'⁻¹) := by
      calc (h' * x * h'⁻¹) * z = h' * (x * (h'⁻¹ * z * h')) * h'⁻¹ := by group
        _ = h' * ((h'⁻¹ * z * h') * x) * h'⁻¹ := by rw [← hcomm]
        _ = z * (h' * x * h'⁻¹) := by group
    exact hkey.symm
  exact key _ hxI'

theorem inf_centralizer_conjClosure_eq (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hQ : Fam16Q M V₀ U R H) :
    V ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) = U ⊔ V₀ := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxV, hxC⟩
    obtain ⟨g₁, hg₁, hg₁M⟩ := SetLike.not_le_iff_exists.1 hQ.2.1
    have hxM : x ∈ conjSubgroup M g₁ := centralizer_conjClosure_le_conj h hxC hg₁.1
    have hinf := h.inf_conjSubgroup_eq h1 h5 h15 hS hg₁.2 hg₁M
    rw [← hinf]
    exact ⟨hxV, hxM⟩
  · refine le_inf (sup_le h.le h.hyp.h6.le) fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm (hQ.isElemAbelian h) hy (le_conjClosure (U ⊔ V₀) H hx)

theorem inf_conjClosure_eq_sup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (h : Cex16 M V₀ V U S) (hQ : Fam16Q M V₀ U R H) :
    V ⊓ conjClosure (U ⊔ V₀) H = U ⊔ V₀ := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxV, hxI⟩
    have hx' : x ∈ V ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
      Subgroup.mem_inf.2 ⟨hxV, Subgroup.mem_centralizer_iff.2 fun y hy =>
        B2F.isElemAbelian_comm (hQ.isElemAbelian h) hy hxI⟩
    rwa [inf_centralizer_conjClosure_eq h1 h5 h15 hS h hQ] at hx'
  · exact le_inf (sup_le h.le h.hyp.h6.le) (le_conjClosure (U ⊔ V₀) H)

theorem eq_conjClosure_sup_of_min (h15 : W16Fifteen G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hSR : S ≤ R) (hQ : Fam16Q M V₀ U R H)
    (hmin : ∀ H' : Subgroup G, H' ≤ H → Fam16Q M V₀ U R H' → H' = H) {g : G}
    (hg : g ∈ H ⊓ centralizer (U : Set G)) (hgM : g ∉ M) : H = conjClosure V H ⊔ R := by
  have hVH : V ≤ H := h.V_le_S.trans (hSR.trans hQ.1)
  have hConj : conjSubgroup V g ≤ H := fun x hx => by
    rw [mem_conjSubgroup_iff] at hx
    have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hg.1) (hVH hx)) hg.1
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h1
  have hle : R ⊔ V ⊔ conjSubgroup V g ≤ H := sup_le (sup_le hQ.1 hVH) hConj
  have hVg : conjSubgroup V g ≤ R ⊔ V ⊔ conjSubgroup V g := le_sup_right
  have hQ'2 : ¬ (R ⊔ V ⊔ conjSubgroup V g) ⊓ centralizer (U : Set G) ≤ M := fun hle' =>
    h.not_conj_le_M h15 hS hg.2 hgM
      (le_trans (le_inf hVg (h.conj_le_centralizer hg.2)) hle')
  have hQ'3 : ∀ x ∈ conjClosure (U ⊔ V₀) (R ⊔ V ⊔ conjSubgroup V g),
      ∀ y ∈ conjClosure (U ⊔ V₀) (R ⊔ V ⊔ conjSubgroup V g), x * y = y * x :=
    fun x hx y hy => hQ.2.2 x (conjClosure_mono le_rfl hle hx) y
      (conjClosure_mono le_rfl hle hy)
  have hfam : Fam16Q M V₀ U R (R ⊔ V ⊔ conjSubgroup V g) :=
    ⟨le_trans le_sup_left le_sup_left, hQ'2, hQ'3⟩
  have hH' : R ⊔ V ⊔ conjSubgroup V g = H := hmin _ hle hfam
  have h1 : R ⊔ V ⊔ conjSubgroup V g ≤ conjClosure V H ⊔ R :=
    sup_le (sup_le le_sup_right (le_trans (le_conjClosure V H) le_sup_left))
      (le_trans (conjSubgroup_le_conjClosure_of_mem hg.1 le_rfl) le_sup_left)
  have h2 : conjClosure V H ⊔ R ≤ H :=
    sup_le (conjClosure_le fun k hk v hv => H.mul_mem (H.mul_mem hk (hVH hv)) (H.inv_mem hk))
      hQ.1
  exact le_antisymm (hH'.ge.trans h1) h2

end Cex16

end CFSG.LocalAnalysis.WeakClosure81
