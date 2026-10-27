module

public import CFSG.LocalAnalysis.StandardType.GGK2E6D5ActualSimpleDSP

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.HdRo7D

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def DSPSubgroup (p : ℕ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) :
    Subgroup (V ≃ₗ[ZMod p] V) where
  carrier := {a | DSP p b a}
  mul_mem' := by
    intro a q ha hq
    obtain ⟨σ, c, hσ0, hc0, hc, hprod, hact⟩ := ha
    obtain ⟨τ, d, hτ0, hd0, hd, hdprod, hqact⟩ := hq
    refine ⟨σ * τ, fun i => d i * c (τ i), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hτ0, hσ0]
    · show d 0 * c (τ 0) = 1
      rw [hτ0, hd0, hc0, mul_one]
    · intro i
      rcases hd i with h | h <;> rcases hc (τ i) with h' | h' <;> simp [h, h']
    · rw [Finset.prod_mul_distrib, hdprod]
      have hcomp : (∏ i, c (τ i)) = ∏ i, c i := Equiv.prod_comp τ c
      rw [hcomp, hprod, mul_one]
    · intro i
      rw [LinearEquiv.mul_apply, hqact i, map_smul, hact (τ i), smul_smul,
        Equiv.Perm.mul_apply]
  one_mem' := by
    refine ⟨1, fun _ => 1, rfl, rfl, fun i => Or.inl rfl, by simp, ?_⟩
    intro i; simp
  inv_mem' := by
    intro a ha
    obtain ⟨σ, c, hσ0, hc0, hc, hprod, hact⟩ := ha
    refine ⟨σ⁻¹, fun i => c (σ⁻¹ i), ?_, ?_, ?_, ?_, ?_⟩
    · have h0 : σ.symm 0 = 0 := by simpa using (congrArg σ.symm hσ0).symm
      exact h0
    · have h0 : σ.symm 0 = 0 := by simpa using (congrArg σ.symm hσ0).symm
      change c (σ.symm 0) = 1
      rw [h0, hc0]
    · intro i; exact hc _
    · rw [show (∏ i, c (σ⁻¹ i)) = ∏ i, c i from Equiv.prod_comp σ⁻¹ c, hprod]
    · intro i
      have h := congrArg (fun v => a.symm v) (hact (σ.symm i))
      simp only [LinearEquiv.symm_apply_apply] at h
      rcases hc (σ.symm i) with hc1 | hcn
      · rw [hc1] at h
        simpa [hc1] using h.symm
      · rw [hcn] at h
        simpa [hcn, neg_one_smul] using congrArg (fun v => -v) h.symm

theorem d5_actual_AL_le_DSP
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin 6) (ZMod 3) V)
    (AL : Subgroup (MulAut ↥Bs)) (φ : Fin 5 → MulAut ↥Bs)
    (hclos : AL = Subgroup.closure (Set.range φ))
    (hgen : ∀ i : Fin 5, DSP 3 b (ggLin (p := 3) ι (φ i))) :
    ∀ a ∈ AL, DSP 3 b (ggLin (p := 3) ι a) := by
  classical
  let P : Subgroup (V ≃ₗ[ZMod 3] V) := DSPSubgroup 3 b
  have hgenP : Set.range (fun i : Fin 5 => ggLin (p := 3) ι (φ i)) ⊆ P := by
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have hclosure : Subgroup.closure (Set.range (fun i : Fin 5 =>
      ggLin (p := 3) ι (φ i))) ≤ P := (Subgroup.closure_le P).2 hgenP
  intro a ha
  have hmem : ggLin (p := 3) ι a ∈
      (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) := by
    exact ⟨a, by rwa [← hclos], rfl⟩
  rw [MonoidHom.map_closure] at hmem
  have hmem' : ggLin (p := 3) ι a ∈
      Subgroup.closure (Set.range (fun i : Fin 5 =>
        ggLin (p := 3) ι (φ i))) := by
    simpa [Set.range_comp'] using hmem
  exact hclosure hmem'

end CFSG.StandardType

end
