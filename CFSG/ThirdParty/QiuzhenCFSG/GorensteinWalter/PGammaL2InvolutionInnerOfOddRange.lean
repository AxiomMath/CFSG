module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involutions in a semilinear subgroup with odd field image

An involution has trivial image in an odd field-automorphism quotient.  The
result is stated directly in the semidirect-product model so downstream
Section-4 arguments can use the projective-linear representative without
repeating the order/divisibility calculation.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem pGammaL2_involution_mem_inner_of_odd_field_range
    {K : Type u} [Field K] [Finite K]
    (A : Subgroup (PGammaL2 K))
    (hodd : Odd (Nat.card (pGammaL2FieldProjection K A).range))
    {x : PGammaL2 K} (hxA : x ∈ A) (hx2 : x ^ 2 = 1) :
    ∃ z : PGL2 K, x = SemidirectProduct.inl z := by
  let xa : A := ⟨x, hxA⟩
  let σ : K ≃+* K := pGammaL2FieldProjection K A xa
  have hxa2 : xa ^ 2 = 1 := Subtype.ext hx2
  have hσ2 : σ ^ 2 = 1 := by
    change (pGammaL2FieldProjection K A xa) ^ 2 = 1
    rw [← map_pow, hxa2]
    simp
  let σr : (pGammaL2FieldProjection K A).range :=
    ⟨σ, ⟨xa, rfl⟩⟩
  have hσrord : orderOf σr ∣ Nat.card (pGammaL2FieldProjection K A).range :=
    orderOf_dvd_natCard σr
  have hσr2pow : σr ^ 2 = 1 := by
    apply Subtype.ext
    simpa [σr, σ] using hσ2
  have hσr2 : orderOf σr ∣ 2 :=
    (orderOf_dvd_iff_pow_eq_one (x := σr) (n := 2)).mpr hσr2pow
  have hgcd : Nat.gcd 2 (Nat.card (pGammaL2FieldProjection K A).range) = 1 :=
    (Nat.coprime_two_left.mpr hodd).gcd_eq_one
  have hσr1 : orderOf σr = 1 := by
    have hd : orderOf σr ∣ Nat.gcd 2
        (Nat.card (pGammaL2FieldProjection K A).range) := Nat.dvd_gcd hσr2 hσrord
    rw [hgcd] at hd
    exact Nat.dvd_one.mp hd
  have hσr_eq : σr = 1 := orderOf_eq_one_iff.mp hσr1
  have hσ_eq : σ = 1 := by
    exact congrArg Subtype.val hσr_eq
  have hxright : x.right = 1 := by
    simpa [σ, xa, pGammaL2FieldProjection] using hσ_eq
  refine ⟨x.left, ?_⟩
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  simp [hxright]

end CFSG.GorensteinWalter
