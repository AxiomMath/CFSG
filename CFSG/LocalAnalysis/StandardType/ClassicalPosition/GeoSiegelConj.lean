module

public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.ClassicalPosition.Geo

open CFSG.LieType.Universal

private theorem gOmR_polar_sum_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {ι : Type} [Fintype ι] (g : ι → K) (w : ι → V) (y : V) :
    QuadraticMap.polar Q (∑ i, g i • w i) y = ∑ i, g i * QuadraticMap.polar Q (w i) y := by
  rw [← QuadraticMap.polarBilin_apply_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    QuadraticMap.polarBilin_apply_apply, smul_eq_mul]

theorem map_conj_range_longRoot_eq_siegelGroup {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {n : ℕ} (F : Spin.HypFrame Q n) {i j : Fin n}
    (hij : i ≠ j) (s t : Bool) (u : spinGroup Q) :
    ((F.longRoot hij s t).range.map (MulAut.conj u).toMonoidHom).map (Spin.spinAction Q) =
      siegelGroup Q (Spin.spinAction Q u (F.vec j t)) (Spin.spinAction Q u (F.vec i s)) := by
  have hgO : Spin.spinAction Q u ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => Spin.map_spinAction Q u v
  have hgen : ∀ c : K, CFSG.ClassicalGroups.Orthogonal.eichler Q
      (Spin.spinAction Q u (F.vec j t)) (c • Spin.spinAction Q u (F.vec i s)) ∈
      ((F.longRoot hij s t).range.map (MulAut.conj u).toMonoidHom).map (Spin.spinAction Q) := by
    intro c
    refine Subgroup.mem_map.mpr ⟨u * F.longRoot hij s t (.ofAdd c) * u⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨F.longRoot hij s t (.ofAdd c), ?_, ?_⟩
      · exact MonoidHom.mem_range.mpr ⟨.ofAdd c, rfl⟩
      · exact MulAut.conj_apply u _
    · simp only [map_mul, map_inv]
      rw [F.spinAction_longRoot_eq_eichler, CFSG.ClassicalGroups.Orthogonal.eichler_conj hgO,
        map_smul]
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [MonoidHom.mem_range] at hz
    obtain ⟨a, rfl⟩ := hz
    change Spin.spinAction Q (u * F.longRoot hij s t a * u⁻¹) ∈
      siegelGroup Q (Spin.spinAction Q u (F.vec j t)) (Spin.spinAction Q u (F.vec i s))
    rw [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from rfl]
    simp only [map_mul, map_inv]
    rw [F.spinAction_longRoot_eq_eichler, CFSG.ClassicalGroups.Orthogonal.eichler_conj hgO,
      map_smul]
    exact Subgroup.subset_closure ⟨Multiplicative.toAdd a, rfl⟩
  · rw [siegelGroup, Subgroup.closure_le]
    intro x hx
    obtain ⟨c, rfl⟩ := hx
    exact hgen c

theorem linearIndependent_quad_of_polar {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {a₁ a₂ b₁ b₂ : V}
    (hQ : Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0)
    (h₁ : QuadraticMap.polar Q a₁ b₁ = 1) (h₂ : QuadraticMap.polar Q a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0) :
    LinearIndependent K ![a₁, a₂, b₁, b₂] := by
  obtain ⟨hQ1, hQ2, hQ3, hQ4⟩ := hQ
  obtain ⟨haa, hbb, hab2, hba2⟩ := h₀
  have ha1a1 : QuadraticMap.polar Q a₁ a₁ = 0 := by
    rw [QuadraticMap.polar_self, hQ1, smul_zero]
  have ha2a2 : QuadraticMap.polar Q a₂ a₂ = 0 := by
    rw [QuadraticMap.polar_self, hQ2, smul_zero]
  have hb1b1 : QuadraticMap.polar Q b₁ b₁ = 0 := by
    rw [QuadraticMap.polar_self, hQ3, smul_zero]
  have hb2b2 : QuadraticMap.polar Q b₂ b₂ = 0 := by
    rw [QuadraticMap.polar_self, hQ4, smul_zero]
  have ha2a1 : QuadraticMap.polar Q a₂ a₁ = 0 := by
    rw [QuadraticMap.polar_comm, haa]
  have hb2b1 : QuadraticMap.polar Q b₂ b₁ = 0 := by
    rw [QuadraticMap.polar_comm, hbb]
  have hb1a2 : QuadraticMap.polar Q b₁ a₂ = 0 := by
    rw [QuadraticMap.polar_comm, hba2]
  have hb2a1 : QuadraticMap.polar Q b₂ a₁ = 0 := by
    rw [QuadraticMap.polar_comm, hab2]
  have hb1a1 : QuadraticMap.polar Q b₁ a₁ = 1 := by
    rw [QuadraticMap.polar_comm, h₁]
  have hb2a2 : QuadraticMap.polar Q b₂ a₂ = 1 := by
    rw [QuadraticMap.polar_comm, h₂]
  have hv0 : ![a₁, a₂, b₁, b₂] 0 = a₁ := rfl
  have hv1 : ![a₁, a₂, b₁, b₂] 1 = a₂ := rfl
  have hv2 : ![a₁, a₂, b₁, b₂] 2 = b₁ := rfl
  have hv3 : ![a₁, a₂, b₁, b₂] 3 = b₂ := rfl
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpair : ∀ y : V, (∑ i, g i * QuadraticMap.polar Q (![a₁, a₂, b₁, b₂] i) y) = 0 := by
    intro y
    rw [← gOmR_polar_sum_smul Q g ![a₁, a₂, b₁, b₂] y, hg, QuadraticMap.polar_zero_left]
  have h0 : g 0 = 0 := by
    have h := hpair b₁
    rw [Fin.sum_univ_four] at h
    simp only [hv0, hv1, hv2, hv3, h₁, hba2, hb1b1, hb2b1, mul_one, mul_zero, add_zero] at h
    exact h
  have h1 : g 1 = 0 := by
    have h := hpair b₂
    rw [Fin.sum_univ_four] at h
    simp only [hv0, hv1, hv2, hv3, hab2, h₂, hbb, hb2b2, mul_one, mul_zero, add_zero, zero_add] at h
    exact h
  have h2 : g 2 = 0 := by
    have h := hpair a₁
    rw [Fin.sum_univ_four] at h
    simp only [hv0, hv1, hv2, hv3, ha1a1, ha2a1, hb1a1, hb2a1, mul_one, mul_zero,
      add_zero, zero_add] at h
    exact h
  have h3 : g 3 = 0 := by
    have h := hpair a₂
    rw [Fin.sum_univ_four] at h
    simp only [hv0, hv1, hv2, hv3, haa, ha2a2, hb1a2, hb2a2, mul_one, mul_zero, add_zero,
      zero_add] at h
    exact h
  intro k
  fin_cases k <;> assumption

end CFSG.StandardType.ClassicalPosition.Geo
