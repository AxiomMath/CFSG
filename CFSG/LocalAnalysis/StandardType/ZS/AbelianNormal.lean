module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.Quasithin.Background.SimsG4OrthUAbel
public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

open CFSG.Quasithin.SimsG4

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U]

omit [Module.Finite (ZMod p) U] in
private theorem zan_isSemisimple_of_not_dvd_orderOf {c : U ≃ₗ[ZMod p] U}
    (hc : ¬ p ∣ orderOf c) :
    Module.End.IsSemisimple (c : Module.End (ZMod p) U) := by
  refine isSemisimple_of_natCast_orderOf_ne_zero ?_
  exact fun h => hc ((ZMod.natCast_eq_zero_iff (orderOf c) p).mp h)

private theorem zan_refl_commute (hn : 3 ≤ Module.finrank (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A)
    {B : Subgroup (U ≃ₗ[ZMod p] U)} (hBn : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBss : ∀ c ∈ B, Module.End.IsSemisimple (c : Module.End (ZMod p) U))
    {b t : U ≃ₗ[ZMod p] U} (hb : b ∈ B) (htA : t ∈ A) (ht : IsRefl p t) :
    t * b = b * t := by
  classical
  let g : U ≃ₗ[ZMod p] U := b⁻¹ * (t * b * t⁻¹)
  have hgB : g ∈ B := by
    dsimp only [g]
    exact B.mul_mem (B.inv_mem hb) (hBn t htA b hb)
  rcases @isImprimitiveOnV_or_injective_of_commute (ZMod p) _ U _ _ _ _ A B hBc hBss hBn
    with himp | hinj
  · exact absurd himp hprim
  have hconj : IsRefl p (b⁻¹ * t * b) := by
    simpa only [inv_inv] using ht.conj b⁻¹
  obtain ⟨v, hv0, htv, hcv⟩ := IsRefl.exists_ne_zero_fixed hn ht hconj
  have htinv : t⁻¹ v = v := by
    simpa only [htv, LinearEquiv.coe_inv] using t.symm_apply_apply v
  have hbv : t (b v) = b v := by
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply] using congrArg b hcv
  have hgv : g v = v := by
    dsimp only [g]
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, htinv, hbv] using
      b.symm_apply_apply v
  have hmem : (g : Module.End (ZMod p) U) - 1 ∈
      Algebra.adjoin (ZMod p)
        ((fun c : U ≃ₗ[ZMod p] U => (c : Module.End (ZMod p) U)) ''
          (B : Set (U ≃ₗ[ZMod p] U))) := by
    refine sub_mem (Algebra.subset_adjoin ⟨g, hgB, rfl⟩) ?_
    simp
  have hzero : (g : Module.End (ZMod p) U) - 1 = 0 := by
    by_contra hne
    exact hv0 (hinj ((g : Module.End (ZMod p) U) - 1) hmem hne (by simp [hgv]))
  have hg1 : g = 1 := by
    ext x
    have h := congrArg (fun f : Module.End (ZMod p) U => f x) hzero
    simpa [sub_eq_zero] using h
  have hgt : t * b * t⁻¹ = b := by
    have h1 : b * g = t * b * t⁻¹ := by
      dsimp only [g]
      group
    rw [hg1, mul_one] at h1
    exact h1.symm
  calc t * b = (t * b * t⁻¹) * t := by group
    _ = b * t := by rw [hgt]

theorem commute_of_mem_of_isMulCommutative (hn : 3 ≤ Module.finrank (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A) {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (_hBA : B ≤ A) (hBn : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBp : ∀ b ∈ B, ¬ p ∣ orderOf b)
    {a b : U ≃ₗ[ZMod p] U} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have hBss : ∀ c ∈ B, Module.End.IsSemisimple (c : Module.End (ZMod p) U) :=
    fun c hc => zan_isSemisimple_of_not_dvd_orderOf (hBp c hc)
  rw [hgen] at ha
  refine Subgroup.closure_induction (p := fun x _ => x * b = b * x) ?_ ?_ ?_ ?_ ha
  · intro s hs
    exact zan_refl_commute hn hprim hBn hBc hBss hb hs.1 hs.2
  · simp
  · intro x y _ _ hx' hy'
    rw [mul_assoc, hy', ← mul_assoc, hx', mul_assoc]
  · intro x _ hx'
    exact (Commute.inv_left ((commute_iff_eq x b).mpr hx')).eq

end CFSG.StandardType.ZS
