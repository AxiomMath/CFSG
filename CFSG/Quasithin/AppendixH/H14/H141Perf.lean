module

public import CFSG.Quasithin.AppendixH.H14.H142F4

public section

open scoped commutatorElement

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.ASVolI.ChH CFSG.Quasithin

def IsSemilinAutOf {K : Type*} [Field K] {d : ℕ} (σ : K ≃+* K)
    (γ : MulAut (Multiplicative (Fin d → K))) : Prop :=
  ∀ (c : K) (w : Fin d → K), γ (Multiplicative.ofAdd (c • w)) =
    Multiplicative.ofAdd (σ c • Multiplicative.toAdd (γ (Multiplicative.ofAdd w)))

lemma mem_gammaLset_iff_semilin {K : Type*} [Field K] {d : ℕ}
    (γ : MulAut (Multiplicative (Fin d → K))) :
    γ ∈ gammaLset d K ↔ ∃ σ : K ≃+* K, IsSemilinAutOf σ γ := Iff.rfl

lemma IsSemilinAutOf.inv {K : Type*} [Field K] {d : ℕ} {σ : K ≃+* K}
    {γ : MulAut (Multiplicative (Fin d → K))} (h : IsSemilinAutOf σ γ) :
    IsSemilinAutOf σ.symm γ⁻¹ := by
  intro c w
  apply γ.injective
  rw [h (σ.symm c) (Multiplicative.toAdd (γ⁻¹ (Multiplicative.ofAdd w)))]
  simp

def klinAutSubgroup : Subgroup (MulAut (Multiplicative (Fin 3 → GF4))) where
  carrier := {γ | IsKLinearAut γ}
  one_mem' := by
    intro c w
    simp
  mul_mem' := by
    intro γ δ hγ hδ c w
    rw [MulAut.mul_apply, hδ c w, hγ c (Multiplicative.toAdd (δ (Multiplicative.ofAdd w)))]
    simp
  inv_mem' := by
    intro γ hγ c w
    apply γ.injective
    rw [hγ c (Multiplicative.toAdd (γ⁻¹ (Multiplicative.ofAdd w)))]
    simp

@[simp] lemma frobGF4_symm : frobGF4.symm = frobGF4 := by
  ext c
  rfl

lemma frobGF4_invol (c : GF4) : frobGF4 (frobGF4 c) = c := by
  fin_cases c <;> decide

lemma ringAut_gf4_comm (σ τ : GF4 ≃+* GF4) (c : GF4) :
    σ (τ (σ.symm (τ.symm c))) = c := by
  rcases ringEquiv_gf4_cases σ with rfl | rfl <;>
    rcases ringEquiv_gf4_cases τ with rfl | rfl <;>
    simp only [frobGF4_symm, RingEquiv.symm_refl, RingEquiv.refl_apply, frobGF4_invol]

theorem commutator_isKLinearAut {γ δ : MulAut (Multiplicative (Fin 3 → GF4))}
    (hγ : γ ∈ gammaLset 3 GF4) (hδ : δ ∈ gammaLset 3 GF4) : IsKLinearAut ⁅γ, δ⁆ := by
  obtain ⟨σ, hσ⟩ := (mem_gammaLset_iff_semilin γ).mp hγ
  obtain ⟨τ, hτ⟩ := (mem_gammaLset_iff_semilin δ).mp hδ
  have hσi : IsSemilinAutOf σ.symm γ⁻¹ := IsSemilinAutOf.inv hσ
  have hτi : IsSemilinAutOf τ.symm δ⁻¹ := IsSemilinAutOf.inv hτ
  unfold IsKLinearAut
  intro c w
  have step1 : δ⁻¹ (Multiplicative.ofAdd (c • w)) =
      Multiplicative.ofAdd (τ.symm c • Multiplicative.toAdd (δ⁻¹ (Multiplicative.ofAdd w))) :=
    hτi c w
  have step2 : γ⁻¹ (Multiplicative.ofAdd
        (τ.symm c • Multiplicative.toAdd (δ⁻¹ (Multiplicative.ofAdd w)))) =
      Multiplicative.ofAdd (σ.symm (τ.symm c) •
        Multiplicative.toAdd (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd w)))) := by
    simpa using hσi (τ.symm c) (Multiplicative.toAdd (δ⁻¹ (Multiplicative.ofAdd w)))
  have step3 : δ (Multiplicative.ofAdd (σ.symm (τ.symm c) •
        Multiplicative.toAdd (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd w))))) =
      Multiplicative.ofAdd (τ (σ.symm (τ.symm c)) •
        Multiplicative.toAdd (δ (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd w))))) := by
    simpa using hτ (σ.symm (τ.symm c))
      (Multiplicative.toAdd (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd w))))
  have step4 : γ (Multiplicative.ofAdd (τ (σ.symm (τ.symm c)) •
        Multiplicative.toAdd (δ (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd w)))))) =
      Multiplicative.ofAdd (σ (τ (σ.symm (τ.symm c))) •
        Multiplicative.toAdd (γ (δ (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd w)))))) := by
    simpa using hσ (τ (σ.symm (τ.symm c)))
      (Multiplicative.toAdd (δ (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd w)))))
  have hfix := ringAut_gf4_comm σ τ c
  change γ (δ (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd (c • w))))) =
    Multiplicative.ofAdd (c • Multiplicative.toAdd
      (γ (δ (γ⁻¹ (δ⁻¹ (Multiplicative.ofAdd w))))))
  rw [step1, step2, step3, step4, hfix]

theorem perfectCore_isKLinear {M : Subgroup S24}
    (π : ↥M →* MulAut (Multiplicative (Fin 3 → GF4))) (hπ : ∀ g, π g ∈ gammaLset 3 GF4) :
    ∀ g : ↥M, (g : S24) ∈ perfectCore M → IsKLinearAut (π g) := by
  have hcomm : ⁅M, M⁆ ≤ (klinAutSubgroup.comap π).map M.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine Subgroup.mem_map.mpr ⟨⁅(⟨g₁, hg₁⟩ : ↥M), (⟨g₂, hg₂⟩ : ↥M)⁆, ?_, ?_⟩
    · rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutator_isKLinearAut (hπ _) (hπ _)
    · rw [map_commutatorElement]
      rfl
  intro g hg
  have hg' : (g : S24) ∈ (klinAutSubgroup.comap π).map M.subtype :=
    hcomm (perfectCore_le_derivedSeriesOf M 1 hg)
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hg'
  have hxlin : π x ∈ klinAutSubgroup := Subgroup.mem_comap.mp hx
  change IsKLinearAut (π x) at hxlin
  have hxg : x = g := Subtype.ext (by simpa using hxeq)
  rw [← hxg]
  exact hxlin

end CFSG.Quasithin.AppendixH.H14
