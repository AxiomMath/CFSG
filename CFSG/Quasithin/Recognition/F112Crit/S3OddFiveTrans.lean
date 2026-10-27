module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open
open CosetGeom (graph stab ballStab nbrs)

variable {G : Type} [Group G] {G₀ G₁ G₂ : Subgroup G}

theorem APrime.S3Point.exists_stab_smul_pair {δ : CosetGeom G₀ G₁ G₂}
    (h : APrime.S3Point G₀ G₁ G₂ δ) {μ μ' ν ν' : CosetGeom G₀ G₁ G₂} (hμ : μ ∈ nbrs δ)
    (hμ' : μ' ∈ nbrs δ) (hne : μ ≠ μ') (hν : ν ∈ nbrs δ) (hν' : ν' ∈ nbrs δ) (hne' : ν ≠ ν') :
    ∃ g : ↥G₀, (g : G) ∈ stab δ ∧ g • μ = ν ∧ g • μ' = ν' := by
  obtain ⟨g, hgδ, hgμ⟩ := CosetGeom.stab_transitive_on_nbrs hμ hν
  have hgμ' : g • μ' ∈ nbrs δ := by
    have h' := (CosetGeom.smul_adj g).mpr (show (graph G₀ G₁ G₂).Adj δ μ' from hμ')
    rwa [CosetGeom.smul_eq_of_mem_stab hgδ] at h'
  have hne'' : g • μ' ≠ ν := by
    rw [← hgμ]
    exact fun h' => hne (smul_left_cancel g h').symm
  by_cases heq : g • μ' = ν'
  · exact ⟨g, hgδ, hgμ, heq⟩
  · obtain ⟨s, hsδ, hsν, hs, -⟩ :=
      h.exists_swap_fix ν hν (g • μ') hgμ' ν' hν' hne'' hne'.symm heq
    exact ⟨s * g, (stab δ).mul_mem hsδ hgδ, by rw [mul_smul, hgμ, hsν], by rw [mul_smul, hs]⟩

theorem pCoreOf_inf_le_ballStab_smul (g : ↥G₀) {δ μ μ' : CosetGeom G₀ G₁ G₂}
    (h : pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ) ≤ ballStab 1 μ') :
    pCoreOf 2 (stab (g • δ)) ⊓ pCoreOf 2 (stab (g • μ)) ≤ ballStab 1 (g • μ') := by
  rw [CosetGeom.stab_smul, CosetGeom.stab_smul, CosetGeom.ballStab_smul, pCoreOf_conjSub,
    pCoreOf_conjSub, ← conjSub_inf]
  exact conjSub_mono _ h

theorem pCoreOf_inf_trans_smul (g : ↥G₀) {δ μ μ' : CosetGeom G₀ G₁ G₂}
    (h : ∀ ε ∈ nbrs μ', ∀ ε' ∈ nbrs μ', ε ≠ δ → ε' ≠ δ →
      ∃ r : ↥G₀, (r : G) ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ) ∧ r • ε = ε') :
    ∀ ε ∈ nbrs (g • μ'), ∀ ε' ∈ nbrs (g • μ'), ε ≠ g • δ → ε' ≠ g • δ →
      ∃ r : ↥G₀, (r : G) ∈ pCoreOf 2 (stab (g • δ)) ⊓ pCoreOf 2 (stab (g • μ)) ∧ r • ε = ε' := by
  intro ε hε ε' hε' hne hne'
  have hmem : ∀ {x : CosetGeom G₀ G₁ G₂}, x ∈ nbrs (g • μ') → g⁻¹ • x ∈ nbrs μ' := fun {x} hx => by
    have h' := (CosetGeom.smul_adj g⁻¹).mpr (show (graph G₀ G₁ G₂).Adj (g • μ') x from hx)
    rwa [inv_smul_smul] at h'
  obtain ⟨r, hr, hrε⟩ := h _ (hmem hε) _ (hmem hε')
    (fun h' => hne (by rw [← h', smul_inv_smul])) (fun h' => hne' (by rw [← h', smul_inv_smul]))
  refine ⟨g * r * g⁻¹, ?_, by rw [mul_smul, mul_smul, hrε, smul_inv_smul]⟩
  rw [CosetGeom.stab_smul, CosetGeom.stab_smul, pCoreOf_conjSub, pCoreOf_conjSub, ← conjSub_inf]
  exact mul_mem_conjSub hr

private theorem centerConds_conjSub (g : G) {A K B : Subgroup G}
    (h : (∀ k ∈ K, ∀ x ∈ A, k * x * k⁻¹ * x⁻¹ ∈ B) ∧
      (∀ a ∈ A, ∀ b ∈ A, ∃ k ∈ K, k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ B) ∧
      (∀ k ∈ K, k * k ∈ B) ∧ ∃ a ∈ A, ∃ b ∈ A, a * b * a⁻¹ * b⁻¹ ∉ B) :
    (∀ k ∈ conjSub g K, ∀ x ∈ conjSub g A, k * x * k⁻¹ * x⁻¹ ∈ conjSub g B) ∧
      (∀ a ∈ conjSub g A, ∀ b ∈ conjSub g A,
        ∃ k ∈ conjSub g K, k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ conjSub g B) ∧
      (∀ k ∈ conjSub g K, k * k ∈ conjSub g B) ∧
      ∃ a ∈ conjSub g A, ∃ b ∈ conjSub g A, a * b * a⁻¹ * b⁻¹ ∉ conjSub g B := by
  obtain ⟨h1, h2, h3, a, ha, b, hb, hab⟩ := h
  refine ⟨fun k hk x hx => ?_, fun a' ha' b' hb' => ?_, fun k hk => ?_,
    g * a * g⁻¹, mul_mem_conjSub ha, g * b * g⁻¹, mul_mem_conjSub hb, ?_⟩
  · rw [mem_conjSub] at hk hx ⊢
    convert h1 _ hk _ hx using 1
    group
  · rw [mem_conjSub] at ha' hb'
    obtain ⟨k, hk, hkB⟩ := h2 _ ha' _ hb'
    refine ⟨g * k * g⁻¹, mul_mem_conjSub hk, ?_⟩
    rw [mem_conjSub]
    convert hkB using 1
    group
  · rw [mem_conjSub] at hk ⊢
    convert h3 _ hk using 1
    group
  · rw [mem_conjSub]
    convert hab using 2
    group

theorem pCoreOf_inf_center_smul (g : ↥G₀) {δ μ μ' : CosetGeom G₀ G₁ G₂}
    (h : (∀ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ), ∀ x ∈ pCoreOf 2 (stab δ),
        k * x * k⁻¹ * x⁻¹ ∈ ballStab 1 μ') ∧
      (∀ a ∈ pCoreOf 2 (stab δ), ∀ b ∈ pCoreOf 2 (stab δ),
        ∃ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ), k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ') ∧
      (∀ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ), k * k ∈ ballStab 1 μ') ∧
      ∃ a ∈ pCoreOf 2 (stab δ), ∃ b ∈ pCoreOf 2 (stab δ), a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ') :
    (∀ k ∈ pCoreOf 2 (stab (g • δ)) ⊓ pCoreOf 2 (stab (g • μ)), ∀ x ∈ pCoreOf 2 (stab (g • δ)),
        k * x * k⁻¹ * x⁻¹ ∈ ballStab 1 (g • μ')) ∧
      (∀ a ∈ pCoreOf 2 (stab (g • δ)), ∀ b ∈ pCoreOf 2 (stab (g • δ)),
        ∃ k ∈ pCoreOf 2 (stab (g • δ)) ⊓ pCoreOf 2 (stab (g • μ)),
          k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 (g • μ')) ∧
      (∀ k ∈ pCoreOf 2 (stab (g • δ)) ⊓ pCoreOf 2 (stab (g • μ)), k * k ∈ ballStab 1 (g • μ')) ∧
      ∃ a ∈ pCoreOf 2 (stab (g • δ)), ∃ b ∈ pCoreOf 2 (stab (g • δ)),
        a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 (g • μ') := by
  have eK : pCoreOf 2 (stab (g • δ)) ⊓ pCoreOf 2 (stab (g • μ)) =
      conjSub (g : G) (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ)) := by
    rw [CosetGeom.stab_smul, CosetGeom.stab_smul, pCoreOf_conjSub, pCoreOf_conjSub, conjSub_inf]
  have eA : pCoreOf 2 (stab (g • δ)) = conjSub (g : G) (pCoreOf 2 (stab δ)) := by
    rw [CosetGeom.stab_smul, pCoreOf_conjSub]
  rw [eK, eA, CosetGeom.ballStab_smul]
  exact centerConds_conjSub (g : G) h

end CFSG.Quasithin.F112Crit

end
