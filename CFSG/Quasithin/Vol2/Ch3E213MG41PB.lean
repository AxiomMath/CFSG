module

public import CFSG.Quasithin.Vol2.Ch3E213MG41S1

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2]

@[expose] def sieg (ρ b : Fin 4 → k) (γ : k) : antiSp k :=
  trv b 1 * trv (b + ρ) 1 * trv ρ (γ + 1)

theorem vec_add_self (w : Fin 4 → k) : w + w = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero (w i)

theorem act_sieg {ρ b : Fin 4 → k} (hb : spBil b ρ = 0) (γ : k) (v : Fin 4 → k) :
    natAct (sieg ρ b γ) v = v + spBil v b • ρ + spBil v ρ • b + (γ * spBil v ρ) • ρ := by
  have hρb : spBil ρ b = 0 := by rw [bil_symm]; exact hb
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [sieg, natAct_mul, natAct_mul, act_trv, act_trv, act_trv]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, bil_self,
    hρb, mul_zero, add_zero, one_mul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (spBil v ρ * ρ i + spBil v b * b i) * h2

theorem sieg_add_smul {ρ b : Fin 4 → k} (hb : spBil b ρ = 0) (a γ : k) :
    sieg ρ (b + a • ρ) γ = sieg ρ b γ := by
  have hb' : spBil (b + a • ρ) ρ = 0 := by
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, hb, smul_zero, add_zero]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply ext_act
  intro v
  rw [act_sieg hb', act_sieg hb]
  simp only [map_add, map_smul, smul_eq_mul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (a * spBil v ρ * ρ i) * h2

theorem sieg_zero (ρ : Fin 4 → k) (γ : k) : sieg ρ 0 γ = trv ρ γ := by
  apply ext_act
  intro v
  rw [act_sieg (by simp) γ v, act_trv]
  simp

theorem sieg_mul {ρ b b' : Fin 4 → k} (hb : spBil b ρ = 0) (hb' : spBil b' ρ = 0) (γ γ' : k) :
    sieg ρ b γ * sieg ρ b' γ' = sieg ρ (b + b') (γ + γ' + spBil b b') := by
  have hbb : spBil (b + b') ρ = 0 := by rw [LinearMap.map_add₂, hb, hb', add_zero]
  have hρb : spBil ρ b = 0 := by rw [bil_symm]; exact hb
  have hsym : spBil b' b = spBil b b' := bil_symm b' b
  apply ext_act
  intro v
  rw [natAct_mul, act_sieg hb', act_sieg hb, act_sieg hbb]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, bil_self,
    hb', hρb, hsym, mul_zero, add_zero]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem conj_sieg (g : antiSp k) {ρ : Fin 4 → k} (hgρ : natAct g ρ = ρ) (b : Fin 4 → k) (γ : k) :
    g * sieg ρ b γ * g⁻¹ = sieg ρ (natAct g b) γ := by
  have e : g * (trv b 1 * trv (b + ρ) 1 * trv ρ (γ + 1)) * g⁻¹ =
      (g * trv b 1 * g⁻¹) * (g * trv (b + ρ) 1 * g⁻¹) * (g * trv ρ (γ + 1) * g⁻¹) := by
    group
  rw [sieg, e, conj_trv, conj_trv, conj_trv, act_add, hgρ, sieg]

theorem trv_mul_trv_eq_sieg {ρ z : Fin 4 → k} (hz : spBil z ρ = 0) (c : k) :
    trv z 1 * trv (z + c • ρ) 1 = sieg ρ (c • z) (c ^ 2) := by
  have hcz : spBil (c • z) ρ = 0 := by rw [LinearMap.map_smul₂, hz, smul_zero]
  have hρz : spBil ρ z = 0 := by rw [bil_symm]; exact hz
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply ext_act
  intro v
  rw [natAct_mul, act_trv, act_trv, act_sieg hcz]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, bil_self,
    hρz, mul_zero, add_zero, one_mul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (spBil v z * z i) * h2

variable {G₀ : Subgroup (antiSp k)}

theorem mem_Lam_of_fibre {ρ z : Fin 4 → k} (hz : spBil z ρ = 0) {c : k} (h₁ : trv z 1 ∈ G₀)
    (h₂ : trv (z + c • ρ) 1 ∈ G₀) {g₁ g₂ g₃ g₄ : antiSp k} (hg₁ : g₁ ∈ G₀) (hg₂ : g₂ ∈ G₀)
    (hg₃ : g₃ ∈ G₀) (hg₄ : g₄ ∈ G₀) (hρ₁ : natAct g₁ ρ = ρ) (hρ₂ : natAct g₂ ρ = ρ)
    (hρ₃ : natAct g₃ ρ = ρ) (hρ₄ : natAct g₄ ρ = ρ) {a : k}
    (hsum : natAct g₁ z + natAct g₂ z = natAct g₃ z + natAct g₄ z + a • ρ) :
    c ^ 2 * (spBil (natAct g₁ z) (natAct g₂ z) + spBil (natAct g₃ z) (natAct g₄ z)) ∈
      Lam G₀ ρ := by
  have hs : sieg ρ (c • z) (c ^ 2) ∈ G₀ := by
    rw [← trv_mul_trv_eq_sieg hz]
    exact G₀.mul_mem h₁ h₂
  have hconj : ∀ g ∈ G₀, natAct g ρ = ρ → sieg ρ (c • natAct g z) (c ^ 2) ∈ G₀ := by
    intro g hg hgρ
    rw [← act_smul, ← conj_sieg g hgρ]
    exact G₀.mul_mem (G₀.mul_mem hg hs) (G₀.inv_mem hg)
  have hperp : ∀ g : antiSp k, natAct g ρ = ρ → spBil (c • natAct g z) ρ = 0 := by
    intro g hgρ
    rw [LinearMap.map_smul₂, ← hgρ, bil_act, hz, smul_zero]
  set x₁ := natAct g₁ z
  set x₂ := natAct g₂ z
  set x₃ := natAct g₃ z
  set x₄ := natAct g₄ z
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hp : ∀ x x' : Fin 4 → k, spBil (c • x) ρ = 0 → spBil (c • x') ρ = 0 →
      sieg ρ (c • x) (c ^ 2) * sieg ρ (c • x') (c ^ 2) =
        sieg ρ (c • (x + x')) (c ^ 2 * spBil x x') := by
    intro x x' hx hx'
    rw [sieg_mul hx hx', smul_add, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul]
    congr 1
    linear_combination c ^ 2 * h2
  have hP₁₂ := G₀.mul_mem (hconj g₁ hg₁ hρ₁) (hconj g₂ hg₂ hρ₂)
  have hP₃₄ := G₀.mul_mem (hconj g₃ hg₃ hρ₃) (hconj g₄ hg₄ hρ₄)
  rw [hp x₁ x₂ (hperp g₁ hρ₁) (hperp g₂ hρ₂)] at hP₁₂
  rw [hp x₃ x₄ (hperp g₃ hρ₃) (hperp g₄ hρ₄)] at hP₃₄
  have h34 : spBil (c • (x₃ + x₄)) ρ = 0 := by
    rw [smul_add, LinearMap.map_add₂, hperp g₃ hρ₃, hperp g₄ hρ₄, add_zero]
  have e12 : sieg ρ (c • (x₁ + x₂)) (c ^ 2 * spBil x₁ x₂) =
      sieg ρ (c • (x₃ + x₄)) (c ^ 2 * spBil x₁ x₂) := by
    rw [hsum, smul_add, smul_smul, sieg_add_smul h34]
  rw [e12] at hP₁₂
  have hprod := G₀.mul_mem hP₁₂ hP₃₄
  rw [sieg_mul h34 h34, vec_add_self, bil_self, add_zero, sieg_zero] at hprod
  rw [mem_Lam, mul_add]
  exact hprod

theorem eq_of_mem_Lam (hone : Refl.OnePerCentre G₀) {ρ : Fin 4 → k} (hρ : ρ ≠ 0) {γ γ' : k}
    (hγ : γ ∈ Lam G₀ ρ) (hγ' : γ' ∈ Lam G₀ ρ) (h0 : γ ≠ 0) (h0' : γ' ≠ 0) : γ = γ' := by
  have h := hone _ (trv_mem_transvSet hρ h0 hγ) _ (trv_mem_transvSet hρ h0' hγ')
    (by rw [commSpace_trv hρ h0, commSpace_trv hρ h0'])
  exact trv_param_inj hρ h

end CFSG.Quasithin.Ch3E213M.G41.Big
