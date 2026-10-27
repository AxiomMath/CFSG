module

public import CFSG.Quasithin.Vol2.Ch3E213MG41S1
public import CFSG.Quasithin.Vol2.Ch3E213MG41PE3

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)}

namespace IPL

@[expose] def rotP (r s : Fin 4 → k) : antiSp k :=
  trv r 1 * trv s 1

theorem rotP_mem {r s : Fin 4 → k} (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) :
    rotP r s ∈ G₀ :=
  G₀.mul_mem hr.2 hs.2

theorem act_rotP (r s : Fin 4 → k) (v : k × k) :
    natAct (rotP r s) (v.1 • r + v.2 • s) =
      (rotC (spBil r s) v).1 • r + (rotC (spBil r s) v).2 • s := by
  have hsr : spBil s r = spBil r s := bil_symm s r
  simp only [rotP, natAct_mul, act_trv, rotC, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, bil_self, hsr, mul_zero, add_zero, zero_add, one_mul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem act_rotP_pow (r s : Fin 4 → k) (v : k × k) (j : ℕ) :
    natAct (rotP r s ^ j) (v.1 • r + v.2 • s) =
      ((rotC (spBil r s))^[j] v).1 • r + ((rotC (spBil r s))^[j] v).2 • s := by
  induction j generalizing v with
  | zero => simp [natAct_one]
  | succ j ih => rw [pow_succ, natAct_mul, act_rotP, ih, Function.iterate_succ_apply]

theorem act_rotP_pow_of_perp {r s y : Fin 4 → k} (hyr : spBil y r = 0) (hys : spBil y s = 0)
    (j : ℕ) : natAct (rotP r s ^ j) y = y := by
  have hg : natAct (rotP r s) y = y := by
    rw [rotP, natAct_mul, act_trv_of_bil_eq_zero 1 hys, act_trv_of_bil_eq_zero 1 hyr]
  induction j with
  | zero => simp [natAct_one]
  | succ j ih => rw [pow_succ, natAct_mul, hg, ih]

theorem eq_zero_of_perp_four {r s π a u : Fin 4 → k} (hrs : spBil r s ≠ 0)
    (hπa : spBil π a ≠ 0) (hπr : spBil π r = 0) (hπs : spBil π s = 0) (har : spBil a r = 0)
    (has : spBil a s = 0) (hur : spBil u r = 0) (hus : spBil u s = 0) (huπ : spBil u π = 0)
    (hua : spBil u a = 0) : u = 0 := by
  have hsr : spBil s r = spBil r s := bil_symm s r
  have hrπ : spBil r π = 0 := by rw [bil_symm, hπr]
  have hsπ : spBil s π = 0 := by rw [bil_symm, hπs]
  have hra : spBil r a = 0 := by rw [bil_symm, har]
  have hsa : spBil s a = 0 := by rw [bil_symm, has]
  have haπ : spBil a π = spBil π a := bil_symm a π
  have hli : LinearIndependent k ![r, s, π, a] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e : ∀ x, g 0 * spBil r x + g 1 * spBil s x + g 2 * spBil π x + g 3 * spBil a x = 0 := by
      intro x
      have := congrArg (fun v => spBil v x) hg
      simpa [Fin.sum_univ_four, map_add, map_smul] using this
    have e₀ := e s
    have e₁ := e r
    have e₂ := e a
    have e₃ := e π
    simp only [bil_self, hπs, has, hπr, har, hsr, hra, hsa, hrπ, hsπ, haπ, mul_zero,
      add_zero, zero_add] at e₀ e₁ e₂ e₃
    intro i
    fin_cases i
    · exact (mul_eq_zero.mp e₀).resolve_right hrs
    · exact (mul_eq_zero.mp e₁).resolve_right hrs
    · exact (mul_eq_zero.mp e₂).resolve_right hπa
    · exact (mul_eq_zero.mp e₃).resolve_right hπa
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  apply eq_zero_of_bil_eq_zero
  intro x
  have hx : x ∈ Submodule.span k (Set.range ![r, s, π, a]) := hspan ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    fin_cases i
    · simpa [bil_symm r u] using hur
    · simpa [bil_symm s u] using hus
    · simpa [bil_symm π u] using huπ
    · simpa [bil_symm a u] using hua
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul t x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem exists_w [Finite k] (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)))
    {r s π : Fin 4 → k} (hc : spBil r s ≠ 0) (hπ : π ≠ 0) (hπr : spBil π r = 0)
    (hπs : spBil π s = 0) :
    ∃ w ∈ Refl.normC G₀, spBil w π ≠ 0 ∧ (spBil w r ≠ 0 ∨ spBil w s ≠ 0) := by
  by_contra hcon
  simp only [not_exists, not_and, not_or, not_not] at hcon
  have hsr : spBil s r = spBil r s := bil_symm s r
  have hrπ : spBil r π = 0 := by rw [bil_symm, hπr]
  have hsπ : spBil s π = 0 := by rw [bil_symm, hπs]
  by_cases hA : ∃ a ∈ Refl.normC G₀, spBil a π ≠ 0
  · obtain ⟨a, ha, haπ⟩ := hA
    obtain ⟨har, has⟩ := hcon a ha haπ
    have hP : ∀ u ∈ Refl.normC G₀, ¬(spBil u r = 0 ∧ spBil u s = 0) →
        u ∈ Submodule.span k {r, s} := by
      intro u hu huY
      have huπ : spBil u π = 0 := by
        by_contra h
        exact huY (hcon u hu h)
      have hua : spBil u a = 0 := by
        by_contra h
        have h' := Refl.act_mem_normC hu ha.2
        rw [act_trv] at h'
        have hπ' : spBil (u + (1 * spBil u a) • a) π ≠ 0 := by
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            huπ, one_mul, zero_add]
          exact mul_ne_zero h haπ
        obtain ⟨h1, h2⟩ := hcon _ h' hπ'
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          har, has, mul_zero, add_zero] at h1 h2
        exact huY ⟨h1, h2⟩
      have hra : spBil r a = 0 := by rw [bil_symm, har]
      have hsa : spBil s a = 0 := by rw [bil_symm, has]
      have e := eq_zero_of_perp_four (u := u - ((spBil u s / spBil r s) • r +
          (spBil u r / spBil r s) • s)) hc haπ har has hπr hπs
        (by simp [map_sub, bil_self, hsr, div_mul_cancel₀ _ hc])
        (by simp [map_sub, bil_self, div_mul_cancel₀ _ hc])
        (by simp [map_sub, hua, hra, hsa])
        (by simp [map_sub, huπ, hrπ, hsπ])
      rw [sub_eq_zero] at e
      rw [e]
      exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
    have hinv : DInv G₀ (Submodule.span k {r, s}) := by
      intro d hd v hv
      obtain ⟨u, hu, rfl⟩ := Refl.exists_normC_eq hd
      rw [act_trv]
      by_cases huY : spBil u r = 0 ∧ spBil u s = 0
      · obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
        have h0 : spBil (α • r + β • s) u = 0 := by
          simp [map_add, map_smul, bil_symm r u, bil_symm s u, huY.1, huY.2]
        rw [h0, mul_zero, zero_smul, add_zero]
        exact hv
      · exact Submodule.add_mem _ hv (Submodule.smul_mem _ _ (hP u hu huY))
    rcases dInv_of_irr_closure hirr _ hinv with h | h
    · have hr : r ∈ Submodule.span k {r, s} := Submodule.subset_span (by simp)
      rw [h, Submodule.mem_bot] at hr
      exact hc (by rw [hr, map_zero, LinearMap.zero_apply])
    · have hmem : π ∈ Submodule.span k {r, s} := by rw [h]; exact Submodule.mem_top
      obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
      have h1 : spBil π s = α * spBil r s := by
        rw [← hαβ]; simp [map_add, map_smul, bil_self]
      have h2 : spBil π r = β * spBil r s := by
        rw [← hαβ]; simp [map_add, map_smul, bil_self, hsr]
      rw [hπs] at h1
      rw [hπr] at h2
      have hα : α = 0 := (mul_eq_zero.mp h1.symm).resolve_right hc
      have hβ : β = 0 := (mul_eq_zero.mp h2.symm).resolve_right hc
      exact hπ (by rw [← hαβ, hα, hβ, zero_smul, zero_smul, add_zero])
  · simp only [not_exists, not_and, not_not] at hA
    have hinv : DInv G₀ (k ∙ π) := by
      intro d hd v hv
      obtain ⟨u, hu, rfl⟩ := Refl.exists_normC_eq hd
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [act_trv, map_smul, LinearMap.smul_apply, bil_symm π u, hA u hu, smul_zero, mul_zero,
        zero_smul, add_zero]
      exact hv
    rcases dInv_of_irr_closure hirr _ hinv with h | h
    · have hm : π ∈ k ∙ π := Submodule.mem_span_singleton_self π
      rw [h, Submodule.mem_bot] at hm
      exact hπ hm
    · have hm : r ∈ k ∙ π := by rw [h]; exact Submodule.mem_top
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hm
      exact hc (by rw [← ht, map_smul, LinearMap.smul_apply, hπs, smul_zero])

end IPL

end CFSG.Quasithin.Ch3E213M.G41.Big
