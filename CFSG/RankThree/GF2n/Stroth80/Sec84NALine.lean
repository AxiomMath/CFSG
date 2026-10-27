module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Line

variable {Γ : Type} [Group Γ] {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]
  [Module.Finite K E] [DistribMulAction Γ E] [SMulCommClass Γ K E]

theorem line_trivial (V₀ V : Submodule K E) (hV₀V : V₀ ≤ V)
    (hV₀inv : ∀ (ρ : Γ), ∀ x ∈ V₀, ρ • x ∈ V₀) (hVinv : ∀ (ρ : Γ), ∀ x ∈ V, ρ • x ∈ V)
    (hdim : Module.finrank K V = Module.finrank K V₀ + 1)
    (N' : Subgroup Γ) (hN' : ∀ n ∈ N', ∀ x ∈ V, n • x - x ∈ V₀)
    (hperf : ∀ ρ : Γ, ∃ a ∈ commutator Γ, ∃ k ∈ N', ρ = a * k) :
    ∀ (ρ : Γ), ∀ x ∈ V, ρ • x - x ∈ V₀ := by
  classical
  obtain ⟨w, hwV, hwV₀⟩ : ∃ w ∈ V, w ∉ V₀ := by
    by_contra hcon
    push Not at hcon
    have : V ≤ V₀ := fun x hx => hcon x hx
    have := Submodule.finrank_mono this
    omega
  have hw0 : w ≠ 0 := fun h => hwV₀ (h ▸ V₀.zero_mem)
  have hinf : V₀ ⊓ Submodule.span K {w} = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₀, hxs⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · exfalso
      apply hwV₀
      have h' := V₀.smul_mem c⁻¹ hx₀
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
  have hle' : V₀ ⊔ Submodule.span K {w} ≤ V :=
    sup_le hV₀V ((Submodule.span_singleton_le_iff_mem _ _).mpr hwV)
  have hsup : V₀ ⊔ Submodule.span K {w} = V := by
    have hfin := Submodule.finrank_sup_add_finrank_inf_eq V₀ (Submodule.span K {w})
    rw [hinf, finrank_bot, finrank_span_singleton hw0] at hfin
    exact Submodule.eq_of_le_of_finrank_eq hle' (by omega)
  have huniq : ∀ c : K, c • w ∈ V₀ → c = 0 := by
    intro c hc
    by_contra hc0
    apply hwV₀
    have h' := V₀.smul_mem c⁻¹ hc
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h'
  have hscal : ∀ ρ : Γ, ∃ c : K, ∀ x ∈ V, ρ • x - c • x ∈ V₀ := by
    intro ρ
    have hρw : ρ • w ∈ V₀ ⊔ Submodule.span K {w} := by rw [hsup]; exact hVinv ρ w hwV
    obtain ⟨v, hv, z, hz, hsum⟩ := Submodule.mem_sup.mp hρw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨c, fun x hx => ?_⟩
    have hx' : x ∈ V₀ ⊔ Submodule.span K {w} := by rw [hsup]; exact hx
    obtain ⟨v', hv', z', hz', hsum'⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hz'
    subst hsum'
    have h1 : ρ • (v' + d • w) - c • (v' + d • w) =
        ρ • v' - c • v' + d • (ρ • w - c • w) := by
      rw [smul_add, smul_add, smul_comm ρ d w, smul_sub]
      simp only [smul_comm c d w]
      abel
    rw [h1]
    refine V₀.add_mem (V₀.sub_mem (hV₀inv ρ v' hv') (V₀.smul_mem c hv')) (V₀.smul_mem d ?_)
    have : ρ • w - c • w = v := by rw [← hsum]; abel
    rw [this]
    exact hv
  choose cf hcf using hscal
  have hcf_unique : ∀ ρ : Γ, ∀ c : K, (∀ x ∈ V, ρ • x - c • x ∈ V₀) → c = cf ρ := by
    intro ρ c hc
    have h1 := hc w hwV
    have h2 := hcf ρ w hwV
    have : (c - cf ρ) • w ∈ V₀ := by
      have e : (c - cf ρ) • w = (ρ • w - cf ρ • w) - (ρ • w - c • w) := by
        rw [sub_smul]; abel
      rw [e]
      exact V₀.sub_mem h2 h1
    exact sub_eq_zero.mp (huniq _ this)
  have hmul : ∀ ρ ρ' : Γ, cf (ρ * ρ') = cf ρ * cf ρ' := by
    intro ρ ρ'
    symm
    apply hcf_unique
    intro x hx
    have e : (ρ * ρ') • x - (cf ρ * cf ρ') • x =
        ρ • (ρ' • x - cf ρ' • x) + cf ρ' • (ρ • x - cf ρ • x) := by
      rw [mul_smul, smul_sub, mul_smul, smul_sub, smul_comm ρ (cf ρ') x]
      simp only [mul_comm (cf ρ) (cf ρ'), mul_smul, smul_comm (cf ρ') (cf ρ) x]
      abel
    rw [e]
    exact V₀.add_mem (hV₀inv ρ _ (hcf ρ' x hx)) (V₀.smul_mem _ (hcf ρ x hx))
  have hone : cf 1 = 1 := by
    symm
    apply hcf_unique
    intro x hx
    simp
  have hunit : ∀ ρ : Γ, cf ρ * cf ρ⁻¹ = 1 := fun ρ => by
    rw [← hmul, mul_inv_cancel, hone]
  let χ : Γ →* Kˣ :=
    { toFun := fun ρ => ⟨cf ρ, cf ρ⁻¹, hunit ρ, by rw [mul_comm]; exact hunit ρ⟩
      map_one' := Units.ext hone
      map_mul' := fun ρ ρ' => Units.ext (hmul ρ ρ') }
  have hcomm_ker : commutator Γ ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have hNker : N' ≤ χ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    show cf n = 1
    symm
    apply hcf_unique
    intro x hx
    simpa using hN' n hn x hx
  intro ρ x hx
  obtain ⟨a, ha, k, hk, rfl⟩ := hperf ρ
  have h1 : χ (a * k) = 1 := by
    rw [map_mul, MonoidHom.mem_ker.mp (hcomm_ker ha), MonoidHom.mem_ker.mp (hNker hk), one_mul]
  have h2 : cf (a * k) = 1 := congrArg Units.val h1
  have := hcf (a * k) x hx
  rwa [h2, one_smul] at this

end Line

end CFSG.RankThree.GF2n.Stroth80
