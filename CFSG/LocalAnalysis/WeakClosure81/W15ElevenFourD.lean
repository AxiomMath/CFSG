module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenP1
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenX

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X Y : Subgroup G} {p : ℕ} {v : G}

theorem commutator_tSub15_le (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) (hXC : X ⊓ F11.CTilde M V₀ V = ⊥) (hYX : Y ≤ X)
    (hYM : Y ≤ M) : ⁅tSub15 M V₀ V U P, Y⁆ ≤ iHull15 V₀ U H := by
  have hH := c.cex.hyp
  have hMC : M ≤ normalizer (F11.CTilde M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (cTilde_le_M M V₀ V)).1
      (cTilde_subgroupOf_normal hH.h6.elemAbelian hH.h6.normalizer_eq.symm.le
        hH.normalizer₀.symm.le)
  have hXN : X ≤ normalizer (iHull15 V₀ U H : Set G) :=
    (hX.le_H c).trans (Hyp1510.le_normalizer_iHull15 V₀ U H)
  refine Subgroup.commutator_le.2 fun t ht y hy => ?_
  have htC : t ∈ F11.CTilde M V₀ V := tSub15_le_cTilde M V₀ V U P ht
  have hyQ : y ∈ Q₀ := hX.le (hYX hy)
  have h1 : t * y * t⁻¹ ∈ Q₀ :=
    (Subgroup.mem_normalizer_iff.1 (c.odd.normal (c.tSub15_le_H ht)) y).1 hyQ
  have hQ : ⁅t, y⁆ ∈ Q₀ := by
    rw [commutatorElement_def]
    exact Q₀.mul_mem h1 (Q₀.inv_mem hyQ)
  have hC : ⁅t, y⁆ ∈ F11.CTilde M V₀ V := by
    have h2 : y * t⁻¹ * y⁻¹ ∈ F11.CTilde M V₀ V :=
      (Subgroup.mem_normalizer_iff.1 (hMC (hYM hy)) t⁻¹).1 ((F11.CTilde M V₀ V).inv_mem htC)
    have h3 : ⁅t, y⁆ = t * (y * t⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact (F11.CTilde M V₀ V).mul_mem htC h2
  have hQ' : ⁅t, y⁆ ∈ (iHull15 V₀ U H : Set G) * (X : Set G) := by
    have h4 : ⁅t, y⁆ ∈ iHull15 V₀ U H ⊔ X := by
      rw [sup_comm, hX.sup_eq]
      exact hQ
    exact (Subgroup.coe_mul_of_right_le_normalizer_left _ _ hXN) ▸ h4
  obtain ⟨i, hi, x, hx, hix'⟩ := hQ'
  have hix : i * x = ⁅t, y⁆ := hix'
  have hiC : i ∈ F11.CTilde M V₀ V :=
    tSub15_le_cTilde M V₀ V U P (c.iHull15_le_tSub15 hi)
  have hxC : x ∈ F11.CTilde M V₀ V := by
    have h5 : x = i⁻¹ * ⁅t, y⁆ := eq_inv_mul_of_mul_eq hix
    rw [h5]
    exact (F11.CTilde M V₀ V).mul_mem ((F11.CTilde M V₀ V).inv_mem hiC) hC
  have hx1 : x = 1 := by
    have : x ∈ X ⊓ F11.CTilde M V₀ V := ⟨hx, hxC⟩
    rw [hXC] at this
    exact this
  rw [← hix, hx1, mul_one]
  exact hi

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
