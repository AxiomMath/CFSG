module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem hpart_eq_coordF_gamma {Bs L : Subgroup G} {x y : G} (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3))
    {ι : Additive ↥Bs ≃+ Vec6} (hι5 : ι (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 5 1)
    (hιL : ∀ b : ↥Bs, (b : G) ∈ L ↔ ι (Additive.ofMul b) 5 = 0)
    (hιΦ : ∀ b : ↥Bs, ι (Additive.ofMul b) 5 = 0 →
      coordE.mulVec (ι (Additive.ofMul b)) =
        Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict b))) :
    hpart (ι (Additive.ofMul ⟨y, hyBs⟩)) =
      coordF.mulVec (Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict ⟨y, hyBs⟩))) := by
  obtain ⟨l, hlL, k, hy⟩ := hBsL y hyBs
  have hxk : x ^ k ∈ Bs := pow_mem hxBs k
  have hlBs : l ∈ Bs := by
    have h : l = y * (x ^ k)⁻¹ := by rw [hy]; group
    rw [h]
    exact Bs.mul_mem hyBs (Bs.inv_mem hxk)
  let bl : ↥Bs := ⟨l, hlBs⟩
  have hyb : (⟨y, hyBs⟩ : ↥Bs) = bl * ⟨x, hxBs⟩ ^ k := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    show y = l * x ^ k
    exact hy
  have hcoord : ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) =
      ι (Additive.ofMul bl) + k • Pi.single 5 1 := by
    rw [hyb, ofMul_mul, ofMul_pow, map_add, map_nsmul, hι5]
  have hlb5 : (ι (Additive.ofMul bl)) 5 = 0 := (hιL bl).mp hlL
  have hyd5 : (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) 5 = (k : ZMod 3) := by
    rw [hcoord, Pi.add_apply, hlb5, zero_add, Pi.smul_apply, Pi.single_eq_same, nsmul_one]
  have hhpart : hpart (ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) = ι (Additive.ofMul bl) := by
    rw [hpart, hyd5, hcoord, Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
  have hgamma : ggGamma L hBsN (⟨y, hyBs⟩ : ↥Bs) = ggGamma L hBsN bl := by
    apply MulEquiv.ext
    intro m
    apply Subtype.ext
    rw [ggGamma_coe, ggGamma_coe]
    change y * (m : G) * y⁻¹ = l * (m : G) * l⁻¹
    have hmx : (m : G) * x ^ k = x ^ k * (m : G) := by
      have hx_cen : x ∈ Subgroup.centralizer ({(m : G)} : Set G) :=
        Subgroup.mem_centralizer_iff.mpr (fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact (Subgroup.mem_centralizer_iff.mp (hLx m.2) x (by simp)).symm)
      exact Subgroup.mem_centralizer_iff.mp (pow_mem hx_cen k) (m : G) (by simp)
    rw [hy, mul_inv_rev, mul_assoc l (x ^ k) (m : G), ← hmx]
    group
  have hres : (ggGamma L hBsN).rangeRestrict (⟨y, hyBs⟩ : ↥Bs) =
      (ggGamma L hBsN).rangeRestrict bl := by
    apply Subtype.ext
    change ggGamma L hBsN (⟨y, hyBs⟩ : ↥Bs) = ggGamma L hBsN bl
    exact hgamma
  rw [hhpart, hres, ← coordF_coordE (ι (Additive.ofMul bl)) hlb5, hιΦ bl hlb5]
  rfl

end E6Dep

end CFSG.StandardType

end
