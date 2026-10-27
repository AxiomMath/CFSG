module

public import CFSG.RankThree.GF2n.Stroth80.QuadWitt

public section

namespace CFSG.RankThree.GF2n.Stroth80.Satz5

open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] {P Z : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem exists_hyperbolic_quadruple (M₀ : Tim79.QuadModel P Z K γ)
    {S₁ S₂ : Submodule K M₀.E} (hS : IsCompl S₁ S₂) (hS₁ : ∀ x ∈ S₁, M₀.Qf x = 0)
    (hS₂ : ∀ x ∈ S₂, M₀.Qf x = 0) (hdim : 4 ≤ Module.finrank K M₀.E) :
    ∃ v₁ v₂ w₁ w₂ : M₀.E, M₀.Qf v₁ = 0 ∧ M₀.Qf v₂ = 0 ∧ M₀.Qf w₁ = 0 ∧ M₀.Qf w₂ = 0 ∧
      M₀.B v₁ w₁ = 1 ∧ M₀.B v₂ w₂ = 1 ∧ M₀.B v₁ w₂ = 0 ∧ M₀.B v₂ w₁ = 0 ∧
      M₀.B v₁ v₂ = 0 ∧ M₀.B w₁ w₂ = 0 := by
  classical
  haveI : Module.Finite K M₀.E := M₀.fin
  have hB₁ : ∀ x ∈ S₁, ∀ y ∈ S₁, M₀.B x y = 0 := fun x hx y hy =>
    Tim79.QuadModel.B_eq_zero_of_singular M₀ (U := S₁.toAddSubgroup) hS₁ hx hy
  have hB₂ : ∀ x ∈ S₂, ∀ y ∈ S₂, M₀.B x y = 0 := fun x hx y hy =>
    Tim79.QuadModel.B_eq_zero_of_singular M₀ (U := S₂.toAddSubgroup) hS₂ hx hy
  have hsplit : ∀ e : M₀.E, ∃ a ∈ S₁, ∃ b ∈ S₂, a + b = e := fun e => by
    have : e ∈ S₁ ⊔ S₂ := by rw [hS.sup_eq_top]; trivial
    exact Submodule.mem_sup.mp this
  have hperp₁ : ∀ v ∈ S₁, (∀ w ∈ S₂, M₀.B v w = 0) → v = 0 := by
    intro v hv h
    refine M₀.nondeg v fun f => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit f
    rw [map_add, hB₁ v hv a ha, h b hb, add_zero]
  have hperp₂ : ∀ w ∈ S₂, (∀ v ∈ S₁, M₀.B v w = 0) → w = 0 := by
    intro w hw h
    refine M₀.nondeg w fun f => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hsplit f
    rw [map_add, Tim79.QuadModel.B_comm (M₀ := M₀) w a, h a ha, hB₂ w hw b hb]
    simp
  have hdual : ∀ v ∈ S₁, v ≠ 0 → ∃ w ∈ S₂, M₀.B v w = 1 := by
    intro v hv hv0
    by_contra hcon
    push Not at hcon
    refine hv0 (hperp₁ v hv fun w hw => ?_)
    by_contra hne
    exact hcon ((M₀.B v w)⁻¹ • w) (S₂.smul_mem _ hw)
      (by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne])
  have hdim₁ : 2 ≤ Module.finrank K S₁ := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hS
    let Φ : S₂ →ₗ[K] (S₁ →ₗ[K] K) := (M₀.B.compl₁₂ S₁.subtype S₂.subtype).flip
    have hinj : Function.Injective Φ := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      have h0 : ∀ v ∈ S₁, M₀.B v y = 0 := fun v hv => by
        have := LinearMap.congr_fun hy ⟨v, hv⟩
        simpa [Φ] using this
      exact Subtype.ext (hperp₂ y.1 y.2 h0)
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    have h2 : Module.finrank K (S₁ →ₗ[K] K) = Module.finrank K S₁ := Subspace.dual_finrank_eq
    omega
  obtain ⟨⟨v₁, hv₁⟩, hv₁0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := S₁)).mp (by omega)
  have hv₁0' : v₁ ≠ 0 := fun h => hv₁0 (Subtype.ext h)
  obtain ⟨w₁, hw₁, hbw₁⟩ := hdual v₁ hv₁ hv₁0'
  let ψ : S₁ →ₗ[K] K := (M₀.B.flip w₁).comp S₁.subtype
  have hker : 1 ≤ Module.finrank K (LinearMap.ker ψ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have h2 : Module.finrank K (LinearMap.range ψ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range ψ)
      simpa using this
    omega
  obtain ⟨⟨⟨v₂, hv₂⟩, hv₂ker⟩, hv₂0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := LinearMap.ker ψ)).mp (by omega)
  have hv₂0' : v₂ ≠ 0 := fun h => hv₂0 (Subtype.ext (Subtype.ext h))
  have hb21 : M₀.B v₂ w₁ = 0 := by simpa [ψ] using hv₂ker
  obtain ⟨y, hy, hyB, hyne⟩ : ∃ y ∈ S₂, M₀.B v₁ y = 0 ∧ M₀.B v₂ y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hv₂0' (hperp₁ v₂ hv₂ fun w hw => ?_)
    have h1 := hcon (w - M₀.B v₁ w • w₁) (S₂.sub_mem hw (S₂.smul_mem _ hw₁))
      (by rw [map_sub, map_smul, hbw₁]; simp)
    rw [map_sub, map_smul, hb21] at h1
    simpa using h1
  refine ⟨v₁, v₂, w₁, (M₀.B v₂ y)⁻¹ • y, hS₁ _ hv₁, hS₁ _ hv₂, hS₂ _ hw₁,
    hS₂ _ (S₂.smul_mem _ hy), hbw₁, ?_, ?_, hb21, hB₁ _ hv₁ _ hv₂, ?_⟩
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hyne]
  · rw [map_smul, hyB, smul_zero]
  · rw [map_smul, hB₂ _ hw₁ _ hy, smul_zero]

end CFSG.RankThree.GF2n.Stroth80.Satz5
