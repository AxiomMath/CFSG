module

public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Frame
public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Hilbert
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFixed

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128Move

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_u_of_field (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : slPi π 3 (p ^ f) K} (hxZ : x ∉ Subgroup.center (slPi π 3 (p ^ f) K)) (hx3 : x ^ 3 = 1)
    {ζ : MulAut (slPi π 3 (p ^ f) K)} (hζx : ζ x = x) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {H : GL (Fin 3) K} (hH : H ∈ glPi π 3 (p ^ f) K)
    (hζH : ∀ s : slPi π 3 (p ^ f) K,
      ((ζ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = H * frobGL σ (H⁻¹ * s * H) * H⁻¹) :
    ∃ u : slPi π 3 (p ^ f) K, u * x * u⁻¹ * x⁻¹ ∈ Subgroup.center (slPi π 3 (p ^ f) K) ∧
      u * x * u⁻¹ ≠ x ∧ ζ u * u⁻¹ = x := by
  have hxs : (x : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := by
    intro hs
    exact hxZ (Subgroup.mem_center_iff.mpr fun s =>
      Subtype.ext (commute_of_mem_statedScalars hs (s : GL (Fin 3) K)))
  have hx3' : (x : GL (Fin 3) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hx3]
    rfl
  obtain ⟨g, hg, a, ω, hω1, hω3, ha3, hframe⟩ := exists_frame hK hq x.2 hx3' hxs
  have hx : (x : GL (Fin 3) K) = g * diagUnits a (a * ω) (a * ω ^ 2) * g⁻¹ := by
    rw [← hframe]
    group
  obtain ⟨f₀, φ, hf, hφ, hφ3, hψ⟩ := exists_frob_data hK hσ
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringAut_apply_three hσ
  have hψ3 : ∀ A : GL (Fin 3) K, frobGL σ (frobGL σ (frobGL σ A)) = A :=
    frobGL_three' hφ3 hψ
  have hsemi : SemiAct ζ σ (H * frobGL σ H⁻¹) := semiAct_of_conj_frob hζH
  have haω3 : (a * ω) ^ 3 = 1 := by rw [mul_pow, ha3, hω3, one_mul]
  have haω23 : (a * ω ^ 2) ^ 3 = 1 := by
    rw [mul_pow, ha3, one_mul, ← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hfa : unitMap σ a = a := unitMap_eq_of_pow_three hσ3 ha3
  have hfaω : unitMap σ (a * ω) = a * ω := unitMap_eq_of_pow_three hσ3 haω3
  have hfaω2 : unitMap σ (a * ω ^ 2) = a * ω ^ 2 := unitMap_eq_of_pow_three hσ3 haω23
  have hfD : frobGL σ (diagUnits a (a * ω) (a * ω ^ 2)) = diagUnits a (a * ω) (a * ω ^ 2) := by
    rw [frobGL_diagUnits, hfa, hfaω, hfaω2]
  have hcD := commute_of_fixed hsemi hζx hframe hfD
  obtain ⟨hne1, hne2, hne3⟩ := frame_entries_ne (a := a) hω1 hω3
  obtain ⟨c₀, c₁, c₂, hc⟩ := exists_diagUnits_of_commute hne1 hne2 hne3 hcD
  have hcH : g⁻¹ * (H * frobGL σ H⁻¹) * frobGL σ g ∈ glPi π 3 (p ^ f) K :=
    mul_mem (mul_mem (inv_mem hg) (mul_mem hH (frobGL_mem_glPi hK σ (inv_mem hH))))
      (frobGL_mem_glPi hK σ hg)
  rw [hc, diagUnits_mem_glPi_iff hK] at hcH
  obtain ⟨hc0, hc1, hc2⟩ := hcH
  have hN : (g⁻¹ * (H * frobGL σ H⁻¹) * frobGL σ g) *
      frobGL σ (g⁻¹ * (H * frobGL σ H⁻¹) * frobGL σ g) *
      frobGL σ (frobGL σ (g⁻¹ * (H * frobGL σ H⁻¹) * frobGL σ g)) = 1 := by
    simp only [map_mul, map_inv, hψ3]
    group
  rw [hc, frobGL_diagUnits, frobGL_diagUnits, diagUnits_mul, diagUnits_mul, ← diagUnits_one,
    diagUnits_eq_iff] at hN
  obtain ⟨hn0, hn1, hn2⟩ := hN
  have hk0 : kNorm σ c₀ = 1 := hn0
  have hk1 : kNorm σ c₁ = 1 := hn1
  have hk2 : kNorm σ c₂ = 1 := hn2
  have haR : a ∈ rootsOfUnity (qSubPi π (p ^ f)) K := mem_rootsOfUnity_qSubPi_of_pow_three hq ha3
  have haωR : a * ω ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
    mem_rootsOfUnity_qSubPi_of_pow_three hq haω3
  obtain ⟨α₀, hα₀R, hα₀⟩ := exists_frob_mul_eq hK hq hf hφ hφ3 hψ
    (ℓ := a⁻¹ * c₀ * c₂⁻¹) (mul_mem (mul_mem (inv_mem haR) hc0) (inv_mem hc2))
    (kNorm_coe σ (kNorm_ratio σ ha3 hfa hk0 hk2))
  obtain ⟨α₁, hα₁R, hα₁⟩ := exists_frob_mul_eq hK hq hf hφ hφ3 hψ
    (ℓ := (a * ω)⁻¹ * c₁ * c₀⁻¹) (mul_mem (mul_mem (inv_mem haωR) hc1) (inv_mem hc0))
    (kNorm_coe σ (kNorm_ratio σ haω3 hfaω hk1 hk0))
  obtain ⟨u, hu, hcomm, hne⟩ := exists_u_of_frame hK hq hg hω1 hω3 hx hα₀R hα₁R
    (mul_inv_cancel (α₀ * α₁))
  refine ⟨u, hcomm, hne, ?_⟩
  have hcoc := cocycle_in_frame hsemi hu hc
  have e0 : c₀ * unitMap σ α₀ * c₂⁻¹ * α₀⁻¹ = a := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_unitMap] at hα₀ ⊢
    have h0 := c₀.ne_zero
    have h2 := c₂.ne_zero
    have h3 := α₀.ne_zero
    have h4 := a.ne_zero
    field_simp at hα₀ ⊢
    exact hα₀
  have e1 : c₁ * unitMap σ α₁ * c₀⁻¹ * α₁⁻¹ = a * ω := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_unitMap] at hα₁ ⊢
    have h0 := c₀.ne_zero
    have h1 := c₁.ne_zero
    have h3 := α₁.ne_zero
    have h4 := a.ne_zero
    have h5 := ω.ne_zero
    field_simp at hα₁ ⊢
    exact hα₁
  have e2 : c₂ * unitMap σ (α₀ * α₁)⁻¹ * c₁⁻¹ * ((α₀ * α₁)⁻¹)⁻¹ = a * ω ^ 2 := by
    have hX : (σ (α₀ : K)) = a * c₂ * α₀ / c₀ := by
      have h := hα₀
      simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h
      have h0 := c₀.ne_zero
      have h2 := c₂.ne_zero
      have h4 := a.ne_zero
      field_simp at h ⊢
      exact h
    have hY : (σ (α₁ : K)) = a * ω * c₀ * α₁ / c₁ := by
      have h := hα₁
      simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h
      have h0 := c₀.ne_zero
      have h1 := c₁.ne_zero
      have h4 := a.ne_zero
      have h5 := ω.ne_zero
      field_simp at h ⊢
      exact h
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, coe_unitMap, map_mul, map_inv₀, inv_inv,
      Units.val_pow_eq_pow_val]
    rw [hX, hY]
    have h0 := c₀.ne_zero
    have h1 := c₁.ne_zero
    have h2 := c₂.ne_zero
    have h3 := α₀.ne_zero
    have h3' := α₁.ne_zero
    have h4 := a.ne_zero
    have h5 := ω.ne_zero
    field_simp
    have ha3' : (a : K) ^ 3 = 1 := by simpa using congrArg Units.val ha3
    have hω3' : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val hω3
    rw [ha3', hω3']
    norm_num
  rw [e0, e1, e2] at hcoc
  apply Subtype.ext
  rw [hcoc, hx]

end CFSG.RankThree.PartTwo.Sec12.KS128Move
