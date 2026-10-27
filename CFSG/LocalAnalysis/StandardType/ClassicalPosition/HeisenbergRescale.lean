module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergDefs
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

private lemma heisRes_coe_pow {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (e : V ≃ₗ[F] V) (n : ℕ) :
    ((e ^ n : V ≃ₗ[F] V) : Module.End F V) = (e : Module.End F V) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one]; rfl
  | succ k ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

theorem exists_rescaled_pair {F V : Type} [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    {p : ℕ} (hp : (p : F) ≠ 0) (X Y : V ≃ₗ[F] V) (hX : X ^ p ∈ scalarAut F V)
    (hY : Y ^ p ∈ scalarAut F V) (hc : X * Y * X⁻¹ * Y⁻¹ ∈ scalarAut F V)
    (hnc : X * Y ≠ Y * X) :
    ∃ (x y : Module.End F V) (ζ : F), (∃ c : F, c ≠ 0 ∧ x = c • (X : Module.End F V)) ∧
      (∃ c : F, c ≠ 0 ∧ y = c • (Y : Module.End F V)) ∧ x ^ p = 1 ∧ y ^ p = 1 ∧
      ζ ≠ 1 ∧ ζ ^ p = 1 ∧ x * y = ζ • (y * x) := by
  haveI : Nontrivial V := by
    by_contra h
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp h
    exact hnc (LinearEquiv.ext fun _ => Subsingleton.elim _ _)
  have hp0 : 0 < p := Nat.pos_of_ne_zero fun h => hp (by simp [h])
  have hpne : p ≠ 0 := Nat.pos_iff_ne_zero.mp hp0
  obtain ⟨ζ, hζ⟩ := mem_scalarAut_iff.mp hc
  have hcomm : (X : Module.End F V) * (Y : Module.End F V) =
      ζ • ((Y : Module.End F V) * (X : Module.End F V)) := by
    ext w
    rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply]
    change X (Y w) = ζ • Y (X w)
    have h := hζ (Y (X w))
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h
    exact h
  have hX0 : (X : Module.End F V) ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h
    have hxv : X v = 0 := by
      have := LinearMap.congr_fun h v
      simpa using this
    have hne : X v ≠ 0 := by simpa using X.injective.ne hv
    exact hne hxv
  obtain ⟨c₀, hc₀⟩ := mem_scalarAut_iff.mp hX
  obtain ⟨d₀, hd₀⟩ := mem_scalarAut_iff.mp hY
  have hXpow : (X : Module.End F V) ^ p = c₀ • 1 := by
    rw [← heisRes_coe_pow X p]
    ext v
    rw [LinearMap.smul_apply, Module.End.one_apply]
    exact hc₀ v
  have hYpow : (Y : Module.End F V) ^ p = d₀ • 1 := by
    rw [← heisRes_coe_pow Y p]
    ext v
    rw [LinearMap.smul_apply, Module.End.one_apply]
    exact hd₀ v
  have hc₀ne : c₀ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h0
    have h := hc₀ v
    rw [h0, zero_smul] at h
    have hne : (X ^ p) v ≠ 0 := by simpa using (X ^ p).injective.ne hv
    exact hne h
  have hd₀ne : d₀ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h0
    have h := hd₀ v
    rw [h0, zero_smul] at h
    have hne : (Y ^ p) v ≠ 0 := by simpa using (Y ^ p).injective.ne hv
    exact hne h
  have hζ_ne_one : ζ ≠ 1 := by
    intro h1
    apply hnc
    ext w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have h := LinearMap.congr_fun hcomm w
    rw [h1, one_smul] at h
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    exact h
  have hsc : SemiconjBy (X : Module.End F V) (Y : Module.End F V)
      (ζ • (Y : Module.End F V)) := by
    show (X : Module.End F V) * (Y : Module.End F V) =
      (ζ • (Y : Module.End F V)) * (X : Module.End F V)
    rw [smul_mul_assoc]
    exact hcomm
  have hpow_eq : (X : Module.End F V) * (Y : Module.End F V) ^ p =
      ζ ^ p • ((Y : Module.End F V) ^ p * (X : Module.End F V)) := by
    have h := (hsc.pow_right p).eq
    rw [smul_pow, smul_mul_assoc] at h
    exact h
  have hζpow : ζ ^ p = 1 := by
    have h := hpow_eq
    rw [hYpow, mul_smul_comm, mul_one, smul_mul_assoc, one_mul] at h
    have h2 : (1 - ζ ^ p) • (d₀ • (X : Module.End F V)) = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr h
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact (sub_eq_zero.mp h3).symm
    · exact absurd h3 (smul_ne_zero hd₀ne hX0)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c₀⁻¹ hp0
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq d₀⁻¹ hp0
  have hane : a ≠ 0 := by
    intro ha0
    have : c₀⁻¹ = 0 := by rw [← ha, ha0, zero_pow hpne]
    exact inv_ne_zero hc₀ne this
  have hbne : b ≠ 0 := by
    intro hb0
    have : d₀⁻¹ = 0 := by rw [← hb, hb0, zero_pow hpne]
    exact inv_ne_zero hd₀ne this
  have hxpow : (a • (X : Module.End F V)) ^ p = 1 := by
    rw [smul_pow, hXpow, smul_smul, ha, inv_mul_cancel₀ hc₀ne, one_smul]
  have hypow : (b • (Y : Module.End F V)) ^ p = 1 := by
    rw [smul_pow, hYpow, smul_smul, hb, inv_mul_cancel₀ hd₀ne, one_smul]
  have hxy : (a • (X : Module.End F V)) * (b • (Y : Module.End F V)) =
      ζ • ((b • (Y : Module.End F V)) * (a • (X : Module.End F V))) := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hcomm, smul_smul, smul_smul]
    congr 1
    ring
  exact ⟨a • (X : Module.End F V), b • (Y : Module.End F V), ζ,
    ⟨a, hane, rfl⟩, ⟨b, hbne, rfl⟩, hxpow, hypow, hζ_ne_one, hζpow, hxy⟩

end CFSG.StandardType.ClassicalPosition.HeisRank
