module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Skew

variable {τ : Tag} {S : TcrSys}

theorem tch_sum_single (γ : Fin τ.rank → ℤ) :
    γ = ∑ j : Fin τ.rank, γ j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem tch_map_decomp (φ : AddMonoid.End (Fin τ.rank → ℤ)) (γ : Fin τ.rank → ℤ) :
    φ γ = ∑ j : Fin τ.rank, γ j • φ (Pi.single j 1) := by
  conv_lhs => rw [tch_sum_single γ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]

private theorem tch_iform_neg_left
    (x y : Fin τ.rank → ℤ) : iform (-x) y = - iform x y := by
  simp only [iform, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private theorem tc_iform_skew
    (φ : AddMonoid.End (Fin τ.rank → ℤ)) (hφ : ∀ x y, iform (φ x) (φ y) = iform x y)
    (hφ2 : ∀ x, φ (φ x) = -x) (x y : Fin τ.rank → ℤ) : iform (φ x) y = - iform x (φ y) := by
  have h := hφ (φ x) y
  rw [hφ2 x] at h
  rw [← h]
  exact tch_iform_neg_left x (φ y)

theorem tch_skew_self
    (φ : AddMonoid.End (Fin τ.rank → ℤ)) (hφ : ∀ x y, iform (φ x) (φ y) = iform x y)
    (hφ2 : ∀ x, φ (φ x) = -x) (x : Fin τ.rank → ℤ) : iform (φ x) x = 0 := by
  have h := tc_iform_skew φ hφ hφ2 x x
  rw [iform_comm x (φ x)] at h
  linarith

end Skew

end CFSG.StandardType.TableCRes

end
