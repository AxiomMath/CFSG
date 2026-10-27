module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08A6Stage2
public import Mathlib.LinearAlgebra.StdBasis

public section

namespace CFSG.StandardType.A6

open Matrix

@[expose] def A6ROPrime (M : Subgroup (V6 ≃ₗ[ZMod 3] V6)) (t : V6 ≃ₗ[ZMod 3] V6) : Prop :=
  ∃ f : Fin 6 → V6, LinearIndependent (ZMod 3) f ∧ ∑ i, f i = one6 ∧
    (∀ σ : Equiv.Perm (Fin 6), ∃ τ : Equiv.Perm (Fin 6), ∀ i, perm6 σ (f i) = f (τ i)) ∧
    (∀ g : V6 ≃ₗ[ZMod 3] V6, A6MonoEven f g → g ∈ M) ∧ A6Mono f t

private theorem a6m_mem_map_iff {S : Subgroup (V6 ≃ₗ[ZMod 3] V6)} (κ g : V6 ≃ₗ[ZMod 3] V6) :
    κ * g * κ⁻¹ ∈ S.map (MulAut.conj κ).toMonoidHom ↔ g ∈ S := by
  constructor
  · rintro ⟨g', hg', hgg'⟩
    have : g' = g := by
      have h2 : κ * g' * κ⁻¹ = κ * g * κ⁻¹ := hgg'
      simpa using h2
    exact this ▸ hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

private theorem a6m_conj_isRefl6 {g : V6 ≃ₗ[ZMod 3] V6} (hg : IsRefl6 g) (κ : V6 ≃ₗ[ZMod 3] V6) :
    IsRefl6 (κ * g * κ⁻¹) := by
  obtain ⟨c, a, hac, rfl⟩ := eq_refl6_of_isRefl6 hg
  rw [conj_refl6]
  exact isRefl6_refl6 _ _ _

private theorem a6m_conj_movesLine6 {g : V6 ≃ₗ[ZMod 3] V6} (hg : MovesLine6 g)
    (κ : V6 ≃ₗ[ZMod 3] V6) (hκ1 : κ one6 = one6) : MovesLine6 (κ * g * κ⁻¹) := by
  have hκ1' : κ⁻¹ one6 = one6 := by
    have := κ.symm_apply_apply one6
    rw [hκ1] at this
    exact this
  have hval : (κ * g * κ⁻¹) one6 = κ (g one6) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hκ1']
  refine ⟨fun h => hg.1 ?_, fun h => hg.2 ?_⟩
  · rw [hval] at h
    exact κ.injective (h.trans hκ1.symm)
  · rw [hval] at h
    exact κ.injective (h.trans (by rw [map_neg, hκ1]))

theorem a6_main {A M : Subgroup (V6 ≃ₗ[ZMod 3] V6)} (h : A6Hyp A M) {r : V6 ≃ₗ[ZMod 3] V6}
    (hr : r ∈ M) (hrR : IsRefl6 r) (hrx : MovesLine6 r) {t : V6 ≃ₗ[ZMod 3] V6} (ht : t ∈ A)
    (htR : IsRefl6 t) (htx : MovesLine6 t) :
    t ∈ M ∨ A6ROPrime M t := by
  obtain ⟨σ, c, a, hac, hsurv, hσ⟩ := a6_stage1 h (h.le hr) hrR hrx
  obtain ⟨b, τ, hstd⟩ := a6_surv_transport hsurv hac
  set κ : V6 ≃ₗ[ZMod 3] V6 := phi6 b * perm6 τ * perm6 σ with hκ
  have hcomm : ∀ ρ₀, phi6 b * perm6 ρ₀ * (phi6 b)⁻¹ = perm6 ρ₀ := fun ρ₀ => by
    rw [phi6_perm6, mul_inv_cancel_right]
  have hcomm' : ∀ ρ₀, (phi6 b)⁻¹ * perm6 ρ₀ * phi6 b = perm6 ρ₀ := fun ρ₀ => by
    rw [mul_assoc, ← phi6_perm6, inv_mul_cancel_left]
  have hκW : ∀ ρ, ∃ ρ', κ * perm6 ρ * κ⁻¹ = perm6 ρ' := by
    intro ρ
    refine ⟨τ * σ * ρ * σ⁻¹ * τ⁻¹, ?_⟩
    have hperm : perm6 τ * perm6 σ * perm6 ρ * (perm6 σ)⁻¹ * (perm6 τ)⁻¹ =
        perm6 (τ * σ * ρ * σ⁻¹ * τ⁻¹) := by
      simp only [perm6_mul, perm6_inv]
    calc κ * perm6 ρ * κ⁻¹
        = phi6 b * (perm6 τ * perm6 σ * perm6 ρ * (perm6 σ)⁻¹ * (perm6 τ)⁻¹) * (phi6 b)⁻¹ := by
          rw [hκ]; group
      _ = phi6 b * perm6 (τ * σ * ρ * σ⁻¹ * τ⁻¹) * (phi6 b)⁻¹ := by rw [hperm]
      _ = perm6 (τ * σ * ρ * σ⁻¹ * τ⁻¹) := hcomm _
  have hκW' : ∀ ρ, ∃ ρ', κ⁻¹ * perm6 ρ * κ = perm6 ρ' := by
    intro ρ
    refine ⟨σ⁻¹ * τ⁻¹ * ρ * τ * σ, ?_⟩
    have hperm : (perm6 σ)⁻¹ * (perm6 τ)⁻¹ * perm6 ρ * perm6 τ * perm6 σ =
        perm6 (σ⁻¹ * τ⁻¹ * ρ * τ * σ) := by
      simp only [perm6_mul, perm6_inv]
    calc κ⁻¹ * perm6 ρ * κ
        = (perm6 σ)⁻¹ * (perm6 τ)⁻¹ * ((phi6 b)⁻¹ * perm6 ρ * phi6 b) * perm6 τ * perm6 σ := by
          rw [hκ]; group
      _ = perm6 (σ⁻¹ * τ⁻¹ * ρ * τ * σ) := by rw [hcomm', hperm]
  have hκ1 : κ one6 = one6 := by
    rw [hκ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, perm6_one6, perm6_one6, phi6_one6]
  have hA' := h.map κ hκW hκW' hκ1
  have hr' : κ * r * κ⁻¹ = phi6 b * perm6 τ * refl6 c a hac * (phi6 b * perm6 τ)⁻¹ := by
    rw [← hσ, hκ]; group
  have hrstd : κ * r * κ⁻¹ = rB ∨ κ * r * κ⁻¹ = rD ∨ κ * r * κ⁻¹ = rS := by
    rw [hr']; exact hstd
  have hrM : κ * r * κ⁻¹ ∈ M.map (MulAut.conj κ).toMonoidHom := (a6m_mem_map_iff κ r).mpr hr
  have htA : κ * t * κ⁻¹ ∈ A.map (MulAut.conj κ).toMonoidHom := (a6m_mem_map_iff κ t).mpr ht
  rcases a6_stage2 hA' hrM hrstd htA (a6m_conj_isRefl6 htR κ)
      (a6m_conj_movesLine6 htx κ hκ1) with hin | ⟨hD, i, hti⟩
  · exact Or.inl ((a6m_mem_map_iff κ t).mp hin)
  · right
    have hsymm : ∀ v, κ⁻¹ v = κ.symm v := fun v => rfl
    refine ⟨fun j => κ.symm (e6 j), ?_, ?_, ?_, ?_, ?_⟩
    · have hb := ((Pi.basisFun (ZMod 3) (Fin 6)).map κ.symm).linearIndependent
      convert hb using 1
      funext j
      rw [Module.Basis.map_apply, Pi.basisFun_apply]
      rfl
    · have hsum : ∑ j, e6 j = one6 := by
        funext k
        simp [e6, one6, Finset.sum_apply, Pi.single_apply]
      rw [← map_sum, hsum]
      have := κ.symm_apply_apply one6
      rw [hκ1] at this
      exact this
    · intro ρ
      obtain ⟨ρ', hρ'⟩ := hκW ρ
      refine ⟨ρ', fun j => ?_⟩
      have h2 : perm6 ρ * κ⁻¹ = κ⁻¹ * perm6 ρ' := by
        rw [← hρ']
        simp only [hκ]
        group
      have h3 := congrArg (fun g : V6 ≃ₗ[ZMod 3] V6 => g (e6 j)) h2
      simp only [LinearEquiv.mul_apply, perm6_e6, hsymm] at h3
      exact h3
    · intro g hg
      have hgM : κ * g * κ⁻¹ ∈ M.map (MulAut.conj κ).toMonoidHom := by
        obtain ⟨π, ε, hε, hprod, hgf⟩ := hg
        refine monoEven_mem (fun ρ => ?_) (hD ▸ hrM) _ π ε hε hprod (fun j => ?_)
        · obtain ⟨ρ', hρ'⟩ := hκW' ρ
          refine ⟨perm6 ρ', h.perm_mem ρ', ?_⟩
          change κ * perm6 ρ' * κ⁻¹ = perm6 ρ
          rw [← hρ']; group
        · simp only [LinearEquiv.mul_apply, hsymm]
          rw [hgf j, map_smul, LinearEquiv.apply_symm_apply]
      exact (a6m_mem_map_iff κ g).mp hgM
    · refine ⟨1, fun j => if j = i then -1 else 1, fun j => by dsimp only; split_ifs <;> decide,
        fun j => ?_⟩
      have hstep : t (κ.symm (e6 j)) = κ.symm ((κ * t * κ⁻¹) (e6 j)) := by
        simp [LinearEquiv.mul_apply, hsymm]
      rw [hstep, hti]
      by_cases hji : j = i
      · subst hji
        simp only [if_true, Equiv.Perm.coe_one, id]
        rw [show sign6 j (e6 j) = -e6 j from ?_, map_neg, neg_one_smul]
        rw [sign6, refl6_apply]
        funext k
        simp only [e6, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        by_cases hk : k = j
        · subst hk; simp [dotProduct_single]; decide
        · simp [hk, dotProduct_single]
      · simp only [hji, if_false, Equiv.Perm.coe_one, id, one_smul]
        congr 1
        rw [sign6, refl6_apply]
        funext k
        simp [e6, Pi.single_apply, dotProduct_single, hji]

end CFSG.StandardType.A6

end
