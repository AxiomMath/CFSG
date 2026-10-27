module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PF3

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

theorem act_fibre_pair {r w y : Fin 4 → k} (hwy : spBil w y = 0) (hry : spBil r y = 0) (γ : k) :
    natAct (trv w 1 * trv (w + γ • y) 1) r = r + (γ * spBil r w) • y := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hyw : spBil y w = 0 := by rw [bil_symm]; exact hwy
  rw [natAct_mul, act_trv, act_trv, one_mul, one_mul, map_add, map_smul, hry, smul_zero, add_zero]
  simp only [LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, hyw, smul_eq_mul, mul_zero,
    add_zero]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (spBil r w * w i) * h2

theorem prYL_smul_add_smul {r s y : Fin 4 → k} (hc : spBil r s ≠ 0) (hyr : spBil y r = 0)
    (hys : spBil y s = 0) (a l : k) : prYL r s (a • r + l • y) = l • y := by
  rw [map_add, map_smul, map_smul, prYL_of_perp hyr hys]
  have h0 := prYL_smul_add hc 1 0
  rw [one_smul, zero_smul, add_zero] at h0
  rw [h0, smul_zero, zero_add]

theorem exists_smul_mem_YO [Finite k]
    {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) {G₀ : Subgroup (antiSp k)}
    (hone : Refl.OnePerCentre G₀)
    (hL4 : ∀ (G : Subgroup (antiSp k)) (F : Subfield k) (e e' : Fin 4 → k),
      Refl.OnePerCentre G → CaseB G F e e' →
      ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
        Q (eOne k) ≠ 0 ∧ ∀ z ∈ Refl.normC G, z 2 = 0 → proj z ≠ 0 → Q z = 1)
    {r s : Fin 4 → k} (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) (hc : spBil r s ≠ 0)
    {x : Fin 4 → k} (hx : x ∈ Refl.normC G₀) (hxy : prYL r s x ≠ 0) :
    ∃ μ : k, μ ≠ 0 ∧ ∃ x' ∈ Refl.normC G₀, spBil x' r = 0 ∧ prYL r s x' = μ • prYL r s x := by
  have hyr : spBil (prYL r s x) r = 0 := bil_prYL_left hc x
  have hys : spBil (prYL r s x) s = 0 := bil_prYL_right hc x
  have hry : spBil r (prYL r s x) = 0 := by rw [bil_symm]; exact hyr
  have hsy : spBil s (prYL r s x) = 0 := by rw [bil_symm]; exact hys
  have hxy' : spBil x (prYL r s x) = 0 := by
    have h := congrArg (fun v => spBil v (prYL r s x)) (eq_prPL_add r s x)
    rw [h]
    simp only [LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, hry, hsy, smul_eq_mul,
      mul_zero, add_zero]
  by_cases hxn : x ∈ k ∙ prYL r s x
  · refine ⟨1, one_ne_zero, x, hx, ?_, by rw [one_smul]⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxn
    rw [← ha, LinearMap.map_smul₂, hyr, smul_zero]
  rcases split_at hn hk hone hL4 hxy hr hs hry hsy hc with ⟨-, hspan⟩ | ⟨-, ⟨F₁, hF₁, hcov⟩⟩
  · by_cases hfib : ∀ z ∈ Refl.normC G₀, ∀ z' ∈ Refl.normC G₀, spBil z (prYL r s x) = 0 →
        z ∉ k ∙ prYL r s x → z' - z ∈ k ∙ prYL r s x → z' = z
    · exfalso
      obtain ⟨α, β, hαβ⟩ := hspan hfib x hx hxy' hxn
      exact hxy (by rw [hαβ, prYL_smul_add hc])
    simp only [not_forall] at hfib
    obtain ⟨z, hz, z', hz', hzy, hzn, hdiff, hne⟩ := hfib
    obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hdiff
    have hz'e : z' = z + γ • prYL r s x := by rw [hγ, add_sub_cancel]
    have hγ0 : γ ≠ 0 := fun h => hne (by rw [hz'e, h, zero_smul, add_zero])
    obtain ⟨w, hw, hw', hwy, hrw⟩ : ∃ w ∈ Refl.normC G₀, w + γ • prYL r s x ∈ Refl.normC G₀ ∧
        spBil w (prYL r s x) = 0 ∧ spBil r w ≠ 0 := by
      by_cases hrz : spBil r z = 0
      · obtain ⟨a, b, l, hze⟩ := exists_eq_add_smul hc hxy hyr hys hzy
        have hb : b = 0 := by
          have h1 : spBil r z = b * spBil r s := by
            rw [hze]
            simp only [map_add, map_smul, bil_self, hry, smul_eq_mul, mul_zero, zero_add, add_zero]
          rw [h1] at hrz
          exact (mul_eq_zero.mp hrz).resolve_right hc
        have ha : a ≠ 0 := by
          rintro rfl
          apply hzn
          rw [hze, hb, zero_smul, zero_smul, zero_add, zero_add]
          exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        have hst : natAct (trv s 1) (prYL r s x) = prYL r s x :=
          act_trv_of_bil_eq_zero 1 hys
        refine ⟨natAct (trv s 1) z, Refl.act_mem_normC hz hs.2, ?_, ?_, ?_⟩
        · have h1 := Refl.act_mem_normC (hz'e ▸ hz') hs.2
          rwa [act_add, act_smul, hst] at h1
        · rw [act_trv, one_mul, LinearMap.map_add₂, LinearMap.map_smul₂, hzy, hsy, smul_zero,
            add_zero]
        · rw [act_trv, one_mul, map_add, map_smul, hrz, zero_add, smul_eq_mul, hze, hb]
          simp only [LinearMap.map_add₂, LinearMap.map_smul₂, hys, smul_eq_mul, mul_zero,
            add_zero, zero_smul]
          exact mul_ne_zero (mul_ne_zero ha hc) hc
      · exact ⟨z, hz, hz'e ▸ hz', hzy, hrz⟩
    have hmem : natAct (trv w 1 * trv (w + γ • prYL r s x) 1) r ∈ Refl.normC G₀ :=
      Refl.act_mem_normC hr (G₀.mul_mem hw.2 hw'.2)
    rw [act_fibre_pair hwy hry] at hmem
    refine ⟨γ * spBil r w, mul_ne_zero hγ0 hrw, _, hmem, ?_, ?_⟩
    · rw [LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, hyr, smul_zero, add_zero]
    · have h0 := prYL_smul_add_smul hc hyr hys 1 (γ * spBil r w)
      rwa [one_smul] at h0
  · obtain ⟨μ, hμ, hμ0, hμ1⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card F₁) 0 1
    have hrn : r ∉ k ∙ prYL r s x := fun h => by
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
      apply hc
      rw [← ha, LinearMap.map_smul₂, hys, smul_zero]
    obtain ⟨x', hx', hdiff⟩ := hcov r hr hry hrn μ hμ hμ0
    obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp hdiff
    have hx'e : x' = μ • r + ν • prYL r s x := by
      rw [hν, add_sub_cancel]
    have hν0 : ν ≠ 0 := by
      rintro rfl
      rw [zero_smul, add_zero] at hx'e
      exact hμ1 (Refl.eq_one_of_smul_mem hone hr (hx'e ▸ hx'))
    refine ⟨ν, hν0, x', hx', ?_, ?_⟩
    · rw [hx'e, LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂, bil_self, hyr,
        smul_zero, smul_zero, add_zero]
    · rw [hx'e, prYL_smul_add_smul hc hyr hys]

end CFSG.Quasithin.Ch3E213M.G41.Big
