module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD5
public import CFSG.Quasithin.Vol2.Ch3E213MG41PD8

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

theorem eq_frame_add {v w x : Fin 4 → k} (hv : v 2 = 0) (hw : w 2 = 0) (hx : x 2 = 0)
    (hvw : spBil v w = 1) :
    x = spBil w x • v + spBil v x • w + (x 1 - spBil w x * v 1 - spBil v x * w 1) • eOne k := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [bil_apply, hv, hw] at hvw
  funext i
  fin_cases i
  · simp [bil_apply, hv, hw, hx, eOne]
    linear_combination (-x 0) * hvw - (v 0 * w 0 * x 3) * h2
  · simp [eOne]
  · simp [hv, hw, hx, eOne]
  · simp [bil_apply, hv, hw, hx, eOne]
    linear_combination (-x 3) * hvw - (v 3 * w 3 * x 0) * h2

theorem sub_mem_span (z₁ z₂ v : Fin 4 → k) :
    natAct (trv z₁ 1 * trv z₂ 1) v - v =
      (spBil v z₁ + spBil v z₂ * spBil z₂ z₁) • z₁ + spBil v z₂ • z₂ := by
  rw [natAct_mul, act_trv, act_trv, LinearMap.map_add₂, LinearMap.map_smul₂, one_mul, one_mul,
    smul_eq_mul]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_sub_eq {z₁ z₂ : Fin 4 → k} (hc : spBil z₁ z₂ ≠ 0) (α β : k) :
    ∃ a b : k, α • z₁ + β • z₂ =
      natAct (trv z₁ 1 * trv z₂ 1) (a • z₁ + b • z₂) - (a • z₁ + b • z₂) := by
  refine ⟨β / spBil z₁ z₂, α / spBil z₁ z₂ - β, ?_⟩
  rw [sub_mem_span]
  have e1 : spBil ((β / spBil z₁ z₂) • z₁ + (α / spBil z₁ z₂ - β) • z₂) z₁ =
      (α / spBil z₁ z₂ - β) * spBil z₁ z₂ := by
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂, bil_self, bil_symm z₂ z₁]
    simp
  have e2 : spBil ((β / spBil z₁ z₂) • z₁ + (α / spBil z₁ z₂ - β) • z₂) z₂ = β := by
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂, bil_self]
    simp only [smul_eq_mul, mul_zero, add_zero]
    exact div_mul_cancel₀ β hc
  rw [e1, e2, bil_symm z₂ z₁]
  congr 2
  rw [sub_mul, div_mul_cancel₀ α hc]
  ring

omit [CharP k 2] in
theorem act_sub_vec (g : antiSp k) (x y : Fin 4 → k) :
    natAct g (x - y) = natAct g x - natAct g y :=
  Matrix.mulVec_sub _ _ _

theorem act_trv_trv (u x : Fin 4 → k) : natAct (trv u 1) (natAct (trv u 1) x) = x := by
  rw [← natAct_mul, trv_mul_self, natAct_one]

variable {G₀ : Subgroup (antiSp k)}

theorem CaseA.act_fix [Finite k] (hA : CaseA G₀) {z₁ z₂ z : Fin 4 → k} (hz₁ : z₁ ∈ cenT G₀)
    (hz₂ : z₂ ∈ cenT G₀) (hz : z ∈ cenT G₀) (hc : spBil (proj z₁) (proj z₂) ≠ 0)
    (hpz : proj z ≠ 0)
    (hfib : ∀ x ∈ cenT G₀, ∀ x' ∈ cenT G₀, proj x ≠ 0 → proj x = proj x' → x = x')
    {v : Fin 4 → k} (hv : v 2 = 0) :
    natAct (trv z 1 * (trv z₁ 1 * trv z₂ 1) * trv z 1 * (trv z₁ 1 * trv z₂ 1)) v = v := by
  have h₁2 : z₁ 2 = 0 := hz₁.2
  have h₂2 : z₂ 2 = 0 := hz₂.2
  have h2 : z 2 = 0 := hz.2
  set N : stabE k := ⟨trv z 1, trv_mem_stabE h2 1⟩ *
      (⟨trv z₁ 1, trv_mem_stabE h₁2 1⟩ * ⟨trv z₂ 1, trv_mem_stabE h₂2 1⟩) *
      ⟨trv z 1, trv_mem_stabE h2 1⟩ *
      (⟨trv z₁ 1, trv_mem_stabE h₁2 1⟩ * ⟨trv z₂ 1, trv_mem_stabE h₂2 1⟩) with hN
  have hNn : (N : antiSp k) = trv z 1 * (trv z₁ 1 * trv z₂ 1) * trv z 1 *
      (trv z₁ 1 * trv z₂ 1) := rfl
  rw [← hNn]
  have hNG : (N : antiSp k) ∈ G₀ := by
    rw [hNn]
    have h₁ := hz₁.1.2
    have h₂ := hz₂.1.2
    have h := hz.1.2
    exact G₀.mul_mem (G₀.mul_mem (G₀.mul_mem h (G₀.mul_mem h₁ h₂)) h) (G₀.mul_mem h₁ h₂)
  have hsec : secHom N = 1 := by
    simp only [hN, map_mul]
    rw [secHom_trv h2, secHom_trv h₁2, secHom_trv h₂2, CaseA.conj_inv hA hz₁ hz₂ hz hc hpz,
      inv_mul_cancel]
  have hfix : ∀ x ∈ cenT G₀, proj x ≠ 0 → natAct (N : antiSp k) x = x := by
    intro x hx hpx
    have hmem : natAct (N : antiSp k) x ∈ cenT G₀ :=
      ⟨Refl.act_mem_normC hx.1 hNG, by rw [act_two N.2]; exact hx.2⟩
    have hproj : proj (natAct (N : antiSp k) x) = proj x := by
      rw [proj_act N hx.2, hsec, natAct_one]
    exact (hfib x hx _ hmem hpx hproj.symm).symm
  have hcc : spBil z₁ z₂ ≠ 0 := by rwa [← bil_proj_of_two h₁2 h₂2]
  have hu₁ : proj z₁ ≠ 0 := fun h => hc (by rw [h]; simp)
  have hu₂ : proj z₂ ≠ 0 := fun h => hc (by rw [h, map_zero])
  have hw2 : ((spBil z₁ z₂)⁻¹ • z₂) 2 = 0 := by simp [h₂2]
  have hvw : spBil z₁ ((spBil z₁ z₂)⁻¹ • z₂) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hcc]
  rw [eq_frame_add h₁2 hw2 hv hvw, act_add, act_add, act_smul, act_smul, act_smul, act_smul,
    hfix z₁ hz₁ hu₁, hfix z₂ hz₂ hu₂, show natAct (N : antiSp k) (eOne k) = eOne k from N.2]

theorem CaseA.act_sub [Finite k] (hA : CaseA G₀) {z₁ z₂ z : Fin 4 → k} (hz₁ : z₁ ∈ cenT G₀)
    (hz₂ : z₂ ∈ cenT G₀) (hz : z ∈ cenT G₀) (hc : spBil (proj z₁) (proj z₂) ≠ 0)
    (hpz : proj z ≠ 0)
    (hfib : ∀ x ∈ cenT G₀, ∀ x' ∈ cenT G₀, proj x ≠ 0 → proj x = proj x' → x = x')
    {y : Fin 4 → k} (hy : y 2 = 0) :
    ∃ y' : Fin 4 → k, y' 2 = 0 ∧ natAct (trv z 1) (natAct (trv z₁ 1 * trv z₂ 1) y - y) =
      natAct (trv z₁ 1 * trv z₂ 1) y' - y' := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hE : ∀ u : Fin 4 → k, u ∈ cenT G₀ → ∀ x : Fin 4 → k, x 2 = 0 →
      natAct (trv u 1) x 2 = 0 := fun u hu x hx => by
    rw [act_two (trv_mem_stabE hu.2 1), hx]
  set y' := natAct (trv z₂ 1) (natAct (trv z₁ 1) (natAct (trv z 1) y)) with hy'
  have hy'2 : y' 2 = 0 := hE _ hz₂ _ (hE _ hz₁ _ (hE _ hz _ hy))
  refine ⟨y', hy'2, ?_⟩
  have e1 : natAct (trv z₁ 1 * trv z₂ 1) y' = natAct (trv z 1) y := by
    rw [hy', natAct_mul, act_trv_trv, act_trv_trv]
  have key := CaseA.act_fix hA hz₁ hz₂ hz hc hpz hfib hy'2
  rw [natAct_mul, natAct_mul, natAct_mul, e1, act_trv_trv] at key
  rw [act_sub_vec, key, e1]
  funext i
  simp only [Pi.sub_apply]
  linear_combination (y' i - natAct (trv z 1) y i) * h2

theorem CaseA.mem_span [Finite k] (hA : CaseA G₀) {z₁ z₂ z : Fin 4 → k} (hz₁ : z₁ ∈ cenT G₀)
    (hz₂ : z₂ ∈ cenT G₀) (hz : z ∈ cenT G₀) (hc : spBil (proj z₁) (proj z₂) ≠ 0)
    (hpz : proj z ≠ 0)
    (hfib : ∀ x ∈ cenT G₀, ∀ x' ∈ cenT G₀, proj x ≠ 0 → proj x = proj x' → x = x') :
    ∃ α β : k, z = α • z₁ + β • z₂ := by
  have hcc : spBil z₁ z₂ ≠ 0 := by rwa [← bil_proj_of_two hz₁.2 hz₂.2]
  have hx : ∃ α₀ β₀ : k, spBil (α₀ • z₁ + β₀ • z₂) z ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have e1 : spBil (proj z₁) (proj z) = 0 := by
      rw [bil_proj_of_two hz₁.2 hz.2]
      simpa using hcon 1 0
    have e2 : spBil (proj z₂) (proj z) = 0 := by
      rw [bil_proj_of_two hz₂.2 hz.2]
      simpa using hcon 0 1
    apply hpz
    have hvw : spBil (proj z₁) ((spBil (proj z₁) (proj z₂))⁻¹ • proj z₂) = 1 := by
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]
    rw [eq_bil_smul_add (p := proj z) (by simp [proj]) (by simp [proj]) (by simp [proj]) hvw,
      LinearMap.map_smul₂, e2, e1]
    simp
  obtain ⟨α₀, β₀, hne⟩ := hx
  obtain ⟨a, b, hab⟩ := exists_sub_eq hcc α₀ β₀
  have hy2 : (a • z₁ + b • z₂) 2 = 0 := by simp [hz₁.2, hz₂.2]
  obtain ⟨y', -, hy'⟩ := CaseA.act_sub hA hz₁ hz₂ hz hc hpz hfib hy2
  rw [← hab, sub_mem_span, act_trv, one_mul] at hy'
  set μ := spBil (α₀ • z₁ + β₀ • z₂) z with hμ
  have hz' : μ • z = (spBil y' z₁ + spBil y' z₂ * spBil z₂ z₁ - α₀) • z₁ +
      (spBil y' z₂ - β₀) • z₂ := by
    rw [eq_sub_of_add_eq' hy']
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨μ⁻¹ * (spBil y' z₁ + spBil y' z₂ * spBil z₂ z₁ - α₀), μ⁻¹ * (spBil y' z₂ - β₀), ?_⟩
  calc z = μ⁻¹ • (μ • z) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = _ := by rw [hz', smul_add, smul_smul, smul_smul]

end CFSG.Quasithin.Ch3E213M.G41.Big
