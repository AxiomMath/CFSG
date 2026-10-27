module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Z391

variable {W : Type} [CommGroup W]

theorem isFFModule_autQuot_congr {Y : Type} [CommGroup Y] {U₁ U₂ : Subgroup Y} (h : U₁ = U₂)
    (X : Subgroup (MulAut Y)) (hF : IsFFModule (autQuot X U₁)) : IsFFModule (autQuot X U₂) := by
  subst h
  exact hF

theorem isFFModule_autSec_inf {X : Subgroup (MulAut W)} {V Z : Subgroup W}
    (h : IsFFModule (autSec X V (V ⊓ Z))) : IsFFModule (autSec X V Z) := by
  have e : (V ⊓ Z).subgroupOf V = Z.subgroupOf V := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  exact isFFModule_autQuot_congr e (autSub X V) h

theorem commV_eq_top {M L : Subgroup (MulAut W)} {V : Subgroup W}
    (hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hcomm : commSub V L = V)
    (hgen : (⨆ m ∈ M, V.map m.toMonoidHom) = ⊤) : commV L = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun m hm => ?_
  rw [Subgroup.map_le_iff_le_comap]
  conv_lhs => rw [← hcomm]
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  show m (x w * w⁻¹) ∈ commV L
  have e : m (x w * w⁻¹) = (m * x * m⁻¹) (m w) * (m w)⁻¹ := by
    simp [MulAut.mul_apply, map_mul, map_inv]
  rw [e]
  exact Subgroup.subset_closure ⟨m * x * m⁻¹, hMn m hm x hx, m w, rfl⟩

end Z391

end CFSG.Quasithin
