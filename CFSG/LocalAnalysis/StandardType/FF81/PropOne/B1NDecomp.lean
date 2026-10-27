module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aYFix
import Mathlib.Tactic.Group

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne.B1Normal

theorem oddAbelian_decomp {W : Type*} [Group W] {Y : Subgroup (MulAut W)} {sX tX : MulAut W}
    (hodd : Odd (Nat.card Y))
    (hab : ∀ a ∈ Y, ∀ c ∈ Y, a * c = c * a)
    (hsY : ∀ y ∈ Y, sX * y * sX⁻¹ ∈ Y) (htY : ∀ y ∈ Y, tX * y * tX⁻¹ ∈ Y)
    (hs2 : sX * sX = 1) (ht2 : tX * tX = 1) (hst : sX * tX = tX * sX)
    (hfree : ∀ y ∈ Y, y * sX = sX * y → y = 1) :
    ∀ y ∈ Y, ∃ a ∈ Y, ∃ c ∈ Y,
      a * (sX * tX) = (sX * tX) * a ∧ c * tX = tX * c ∧ y = a * c := by
  intro y hy
  let : CommGroup ↥Y :=
    { (inferInstance : Group ↥Y) with
      mul_comm := fun a c => Subtype.ext (hab (a : MulAut W) a.2 (c : MulAut W) c.2) }
  have : Finite ↥Y := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hsN : sX ∈ Subgroup.normalizer Y := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hsY h
    · intro hh
      have h1 := hsY (sX * h * sX⁻¹) hh
      rwa [show sX * (sX * h * sX⁻¹) * sX⁻¹ = h by
        calc sX * (sX * h * sX⁻¹) * sX⁻¹ = (sX * sX) * h * (sX⁻¹ * sX⁻¹) := by
              group
          _ = h := by rw [hs2, one_mul, ← mul_inv_rev, hs2, inv_one, mul_one]] at h1
  have htN : tX ∈ Subgroup.normalizer Y := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact htY h
    · intro hh
      have h1 := htY (tX * h * tX⁻¹) hh
      rwa [show tX * (tX * h * tX⁻¹) * tX⁻¹ = h by
        calc tX * (tX * h * tX⁻¹) * tX⁻¹ = (tX * tX) * h * (tX⁻¹ * tX⁻¹) := by
              group
          _ = h := by rw [ht2, one_mul, ← mul_inv_rev, ht2, inv_one, mul_one]] at h1
  let sN : Subgroup.normalizer Y := ⟨sX, hsN⟩
  let tN : Subgroup.normalizer Y := ⟨tX, htN⟩
  let τ : MulAut ↥Y := Subgroup.normalizerMonoidHom (H := Y) sN
  let t : MulAut ↥Y := Subgroup.normalizerMonoidHom (H := Y) tN
  have hτ2 : τ * τ = 1 := by
    change Subgroup.normalizerMonoidHom (H := Y) sN * Subgroup.normalizerMonoidHom (H := Y) sN = 1
    rw [← map_mul, show sN * sN = 1 from Subtype.ext (by simpa using hs2), map_one]
  have ht2' : t * t = 1 := by
    change Subgroup.normalizerMonoidHom (H := Y) tN * Subgroup.normalizerMonoidHom (H := Y) tN = 1
    rw [← map_mul, show tN * tN = 1 from Subtype.ext (by simpa using ht2), map_one]
  have hcomm : τ * t = t * τ := by
    change Subgroup.normalizerMonoidHom (H := Y) sN * Subgroup.normalizerMonoidHom (H := Y) tN =
      Subgroup.normalizerMonoidHom (H := Y) tN * Subgroup.normalizerMonoidHom (H := Y) sN
    rw [← map_mul, ← map_mul, show sN * tN = tN * sN from Subtype.ext (by simpa using hst)]
  have hfreeY : ∀ z : ↥Y, τ z = z → z = 1 := by
    intro z hz
    have hz' : sX * (z : MulAut W) * sX⁻¹ = (z : MulAut W) := by
      have h := congrArg (fun w : ↥Y => (w : MulAut W)) hz
      simpa [τ, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    exact Subtype.ext (hfree (z : MulAut W) z.2 (mul_inv_eq_iff_eq_mul.mp hz').symm)
  obtain ⟨a, c, ha, hc, hyac⟩ :=
    CFSG.exists_fixed_mul_fixed_of_fixedPointFree_mul (A := ↥Y) hodd τ t hτ2 ht2'
      hcomm hfreeY ⟨y, hy⟩
  have ha_coe : ((τ * t) a : MulAut W) =
      (sX * tX) * (a : MulAut W) * (sX * tX)⁻¹ := by
    simp only [τ, t, sN, tN, MulAut.mul_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      mul_inv_rev]
    group
  refine ⟨(a : MulAut W), a.2, (c : MulAut W), c.2, ?_, ?_, ?_⟩
  · have h : (sX * tX) * (a : MulAut W) * (sX * tX)⁻¹ = (a : MulAut W) := by
      rw [← ha_coe]
      exact congrArg (fun w : ↥Y => (w : MulAut W)) ha
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · have hc' : tX * (c : MulAut W) * tX⁻¹ = (c : MulAut W) := by
      have h := congrArg (fun w : ↥Y => (w : MulAut W)) hc
      simpa [t, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
    exact (mul_inv_eq_iff_eq_mul.mp hc').symm
  · have h := congrArg (fun w : ↥Y => (w : MulAut W)) hyac
    simpa using h

end CFSG.StandardType.FF81.PropOne.B1Normal

end
