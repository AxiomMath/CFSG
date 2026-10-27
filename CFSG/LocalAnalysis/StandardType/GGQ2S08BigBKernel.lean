module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import Mathlib.LinearAlgebra.Basis.VectorSpace

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggQ2s08tbk_eq_sum_single {n : ℕ} (v : Vn n) :
    v = ∑ i, v i • Pi.single i 1 := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma ggQ2s08tbk_dot_functional {n : ℕ} (φ : Vn n →ₗ[ZMod 3] ZMod 3) (v : Vn n) :
    (fun j => φ (Pi.single j 1)) ⬝ᵥ v = φ v := by
  have hL : (fun j => φ (Pi.single j 1)) ⬝ᵥ v =
      ∑ j, φ (Pi.single j 1) * v j := rfl
  rw [hL]
  conv_rhs => rw [ggQ2s08tbk_eq_sum_single v]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma ggQ2s08tbk_lambda_one {n : ℕ} {H : Submodule (ZMod 3) (Vn n)} {xv u₀ : Vn n}
    (hH : IsCompl H (Submodule.span (ZMod 3) {xv})) (hxvH : xv ∉ H)
    {A : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} (hnt : ∀ g ∈ A, ¬ IsTransv g)
    {k : Vn n ≃ₗ[ZMod 3] Vn n} (hkA : k ∈ A)
    (hkfix : ∀ u ∈ H, k u = u) (hu₀ : u₀ ∈ H) (hkx : k xv = u₀ + xv) :
    u₀ = 0 := by
  by_contra hne
  obtain ⟨φ₀, hφ₀v, hφ₀H⟩ := Submodule.exists_le_ker_of_notMem hxvH
  have hφ₀H' : ∀ u ∈ H, φ₀ u = 0 := by
    intro u hu
    have h := hφ₀H hu
    simpa [LinearMap.mem_ker] using h
  let φ : Vn n →ₗ[ZMod 3] ZMod 3 := (φ₀ xv)⁻¹ • φ₀
  have hφx : φ xv = 1 := by
    change ((φ₀ xv)⁻¹ • φ₀) xv = 1
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀v]
  have hφH : ∀ u ∈ H, φ u = 0 := by
    intro u hu
    change ((φ₀ xv)⁻¹ • φ₀) u = 0
    rw [LinearMap.smul_apply, hφ₀H' u hu, smul_eq_mul, mul_zero]
  let a : Vn n := fun j => φ (Pi.single j 1)
  have ha_dot : ∀ v, a ⬝ᵥ v = φ v := fun v => ggQ2s08tbk_dot_functional φ v
  have hax : a ⬝ᵥ xv = 1 := by rw [ha_dot, hφx]
  have haH : ∀ u ∈ H, a ⬝ᵥ u = 0 := by
    intro u hu
    rw [ha_dot, hφH u hu]
  have hane : a ≠ 0 := by
    intro h0
    have h1 : a ⬝ᵥ xv = 0 := by rw [h0, zero_dotProduct]
    rw [hax] at h1
    exact one_ne_zero h1
  refine (hnt k hkA) ⟨u₀, a, hne, hane, ?_, ?_⟩
  · rw [haH u₀ hu₀]
  · intro v
    have hvsup : v ∈ H ⊔ Submodule.span (ZMod 3) {xv} := by
      rw [hH.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨h, hhH, z, hz, hsum⟩ := Submodule.mem_sup.mp hvsup
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hz
    have hv : v = h + d • xv := by rw [← hsum, ← hd]
    have hav : a ⬝ᵥ v = d := by
      rw [ha_dot, hv, map_add, map_smul, hφH h hhH, zero_add, hφx, smul_eq_mul, mul_one]
    rw [hav, hv, map_add, map_smul, hkfix h hhH, hkx, smul_add]
    abel

theorem ggQ2s08_bigB_kernel {n : ℕ} {W R A : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {xv : Vn n}
    {H : Submodule (ZMod 3) (Vn n)} (hH : IsCompl H (Submodule.span (ZMod 3) {xv}))
    (hWx : ∀ w ∈ W, w xv = xv)
    (hWfix : ∀ v : Vn n, (∀ w ∈ W, w v = v) → v ∈ Submodule.span (ZMod 3) {xv})
    (hWR : W ≤ R) (hRA : R ≤ A) (hnt : ∀ g ∈ A, ¬ IsTransv g)
    (hpres : ∀ g ∈ R, ∀ u ∈ H, g u ∈ H)
    (hres : ∀ g ∈ R, ∃ w ∈ W, ∀ u ∈ H, g u = w u) :
    ∀ g ∈ R, FixesLine xv g := by
  intro g hg
  by_cases hx0 : xv = 0
  · left
    simp [hx0]
  obtain ⟨w, hw, hgw⟩ := hres g hg
  have hwR : w ∈ R := hWR hw
  have hwinvR : w⁻¹ ∈ R := R.inv_mem hwR
  let k : Vn n ≃ₗ[ZMod 3] Vn n := g * w⁻¹
  have hkR : k ∈ R := R.mul_mem hg hwinvR
  have hkA : k ∈ A := hRA hkR
  have hkfix : ∀ u ∈ H, k u = u := by
    intro u hu
    have hwu : w⁻¹ u ∈ H := hpres w⁻¹ hwinvR u hu
    change g (w⁻¹ u) = u
    rw [hgw (w⁻¹ u) hwu]
    simp
  have hwx : w⁻¹ xv = xv := by
    have h1 : w xv = xv := hWx w hw
    calc w⁻¹ xv = w⁻¹ (w xv) := by rw [h1]
      _ = xv := by simp
  have hkx : k xv = g xv := by
    change g (w⁻¹ xv) = g xv
    rw [hwx]
  have hxvH : xv ∉ H := by
    intro hmem
    have hspan : xv ∈ Submodule.span (ZMod 3) {xv} := Submodule.mem_span_singleton_self xv
    have hbot : xv ∈ (⊥ : Submodule (ZMod 3) (Vn n)) := by
      rw [← hH.inf_eq_bot]
      exact Submodule.mem_inf.mpr ⟨hmem, hspan⟩
    exact hx0 (by simpa using hbot)
  have hksup : k xv ∈ H ⊔ Submodule.span (ZMod 3) {xv} := by
    rw [hH.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u₀, hu₀H, z, hz, hsum⟩ := Submodule.mem_sup.mp hksup
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
  have hkx' : k xv = u₀ + c • xv := by rw [← hsum, hc]
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hkx0 : k xv = u₀ := by rw [hkx', hc0, zero_smul, add_zero]
    have hfixpt : k (k xv) = k xv := by
      rw [hkx0]
      exact hkfix u₀ hu₀H
    have hx_eq : xv = k xv := by
      have h1 : k⁻¹ (k (k xv)) = k⁻¹ (k xv) := congrArg (fun x => k⁻¹ x) hfixpt
      simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using h1.symm
    exact hxvH (by rw [hx_eq, hkx0]; exact hu₀H)
  have hc_cases : c = 1 ∨ c = -1 := by
    have hkey : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
    exact hkey c hc_ne
  rcases hc_cases with hc1 | hcneg
  · have hu₀0 : u₀ = 0 :=
      ggQ2s08tbk_lambda_one hH hxvH hnt hkA hkfix hu₀H
        (by rw [hkx', hc1, one_smul])
    left
    rw [← hkx, hkx', hu₀0, hc1, zero_add, one_smul]
  · have hcneg' : c • xv = -xv := by rw [hcneg, neg_smul, one_smul]
    have hkx'' : k xv = u₀ - xv := by rw [hkx', hcneg', sub_eq_add_neg]
    have hWfixu₀ : ∀ w' ∈ W, w' u₀ = u₀ := by
      intro w' hw'
      have hw'R : w' ∈ R := hWR hw'
      have hw'invR : w'⁻¹ ∈ R := R.inv_mem hw'R
      have hw'x : w'⁻¹ xv = xv := by
        have h1 : w' xv = xv := hWx w' hw'
        calc w'⁻¹ xv = w'⁻¹ (w' xv) := by rw [h1]
          _ = xv := by simp
      let k' : Vn n ≃ₗ[ZMod 3] Vn n := w' * k * w'⁻¹
      have hk'R : k' ∈ R := R.mul_mem (R.mul_mem hw'R hkR) hw'invR
      have hk'A : k' ∈ A := hRA hk'R
      have hk'fix : ∀ u ∈ H, k' u = u := by
        intro u hu
        have h1 : w'⁻¹ u ∈ H := hpres w'⁻¹ hw'invR u hu
        change w' (k (w'⁻¹ u)) = u
        rw [hkfix (w'⁻¹ u) h1]
        simp
      have hk'u₀ : k' u₀ = u₀ := by
        have h1 : w'⁻¹ u₀ ∈ H := hpres w'⁻¹ hw'invR u₀ hu₀H
        change w' (k (w'⁻¹ u₀)) = u₀
        rw [hkfix (w'⁻¹ u₀) h1]
        simp
      have hk'x : k' xv = w' u₀ - xv := by
        change w' (k (w'⁻¹ xv)) = w' u₀ - xv
        rw [hw'x, hkx'', map_sub, hWx w' hw']
      have hk'kfix : ∀ u ∈ H, (k' * k) u = u := by
        intro u hu
        change k' (k u) = u
        rw [hkfix u hu]
        exact hk'fix u hu
      have hk'kx : (k' * k) xv = (u₀ - w' u₀) + xv := by
        change k' (k xv) = (u₀ - w' u₀) + xv
        rw [hkx'', map_sub, hk'u₀, hk'x]
        abel
      have hsub : u₀ - w' u₀ = 0 :=
        ggQ2s08tbk_lambda_one hH hxvH hnt (A.mul_mem hk'A hkA) hk'kfix
          (Submodule.sub_mem H hu₀H (hpres w' hw'R u₀ hu₀H)) hk'kx
      exact (sub_eq_zero.mp hsub).symm
    have hu₀span : u₀ ∈ Submodule.span (ZMod 3) {xv} := hWfix u₀ hWfixu₀
    have hu₀bot : u₀ ∈ (⊥ : Submodule (ZMod 3) (Vn n)) := by
      rw [← hH.inf_eq_bot]
      exact Submodule.mem_inf.mpr ⟨hu₀H, hu₀span⟩
    have hu₀0 : u₀ = 0 := by simpa using hu₀bot
    right
    rw [← hkx, hkx', hu₀0, hcneg', zero_add]

end CFSG.StandardType

end
