module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalReg
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPU

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem exists_edge_conj_false {δ u : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = false)
    (hu : u ∈ nbrs δ) :
    ∃ g : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), g • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) = δ ∧
      g • γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) = u := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hδ
  have hadj : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj
      (γ₀ _ _ _) (g⁻¹ • u) := by
    have := (smul_adj g⁻¹).mpr hu
    rwa [inv_smul_smul] at this
  obtain ⟨q, hq0, hq1⟩ := exists_stab_smul_eq adj_γ₀_γ₁ hadj
  refine ⟨g * q, ?_, ?_⟩
  · rw [mul_smul, hq0]
  · rw [mul_smul, hq1, smul_inv_smul]

omit [Finite G] in
theorem exists_edge_conj_true {δ u : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = true)
    (hu : u ∈ nbrs δ) :
    ∃ g : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), g • γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) = δ ∧
      g • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) = u := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hδ
  have hadj : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj
      (γ₁ _ _ _) (g⁻¹ • u) := by
    have := (smul_adj g⁻¹).mpr hu
    rwa [inv_smul_smul] at this
  obtain ⟨q, hq1, hq0⟩ := exists_stab_smul_eq adj_γ₀_γ₁.symm hadj
  refine ⟨g * q, ?_, ?_⟩
  · rw [mul_smul, hq1]
  · rw [mul_smul, hq0, smul_inv_smul]

theorem Qv_le_sup_of_not_normal (F : Frame L1 L2 S D X)
    (hPU : ¬ P1 L1 L2 S ≤ Subgroup.normalizer ((Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) : Set G))
    {δ u u' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = false) (hu : u ∈ nbrs δ)
    (hu' : u' ∈ nbrs δ) (huu : u ≠ u') :
    Qv δ ≤ (Qv δ ⊓ Qv u) ⊔ (Qv δ ⊓ Qv u') := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨g, hg0, hg1⟩ := exists_edge_conj_false hδ hu
  have hadj : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj
      (γ₀ _ _ _) (g⁻¹ • u') := by
    have := (smul_adj g⁻¹).mpr hu'
    rwa [← hg0, inv_smul_smul] at this
  obtain ⟨q, hq0, hq1⟩ := exists_stab_smul_eq adj_γ₀_γ₁ hadj
  have hqP : (q : G) ∈ P1 L1 L2 S := by
    have := mem_stab_of_smul_eq hq0
    rwa [stab_γ₀ h₁] at this
  have hqB : (q : G) ∉ bigB L1 L2 S := by
    intro hB
    apply huu
    have hfix : q • γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) =
        γ₁ _ _ _ := by
      apply smul_eq_of_mem_stab
      rw [stab_γ₁ h₂]
      exact (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hB
    rw [hfix] at hq1
    rw [← hg1, hq1, smul_inv_smul]
  have hu'eq : u' = (g * q) • γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) := by
    rw [mul_smul, hq1, smul_inv_smul]
  have hQδ : Qv δ = conjSub (g : G) (Q1 L1 L2 S) := by
    rw [← hg0, Qv_smul]; unfold Qv; rw [stab_γ₀ h₁]
  have hQu : Qv u = conjSub (g : G) (Q2 L1 L2 S) := by
    rw [← hg1, Qv_smul]; unfold Qv; rw [stab_γ₁ h₂]
  have hQu' : Qv u' = conjSub (g : G) (conjSub (q : G) (Q2 L1 L2 S)) := by
    rw [hu'eq, Qv_smul, Subgroup.coe_mul, conjSub_mul]
    unfold Qv; rw [stab_γ₁ h₂]
  have hqQ1 : conjSub (q : G) (Q1 L1 L2 S) = Q1 L1 L2 S :=
    conjSub_eq_of_mem_normalizer (P1_le_normalizer_Q1 L1 L2 S hqP)
  have hmain := Q1_eq_sup_of_not_normal F hPU hqP hqB
  have hmain' : (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ (Q1 L1 L2 S ⊓ conjSub (q : G) (Q2 L1 L2 S)) =
      Q1 L1 L2 S := by
    have := hmain
    rw [conjSub_inf, hqQ1] at this
    exact this
  rw [hQδ, hQu, hQu', ← conjSub_inf, ← conjSub_inf, ← conjSub_sup, hmain']

theorem exists_Qv_smul_nbr (F : Frame L1 L2 S D X) {δ μ w w' : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = true) (hμ : μ ∈ nbrs δ) (hw : w ∈ nbrs δ) (hw' : w' ∈ nbrs δ)
    (hwμ : w ≠ μ) (hw'μ : w' ≠ μ) :
    ∃ q : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), (q : G) ∈ Qv μ ∧ q • w = w' := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨g, hg1, hg0⟩ := exists_edge_conj_true hδ hμ
  have adjOf : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), x ∈ nbrs δ →
      (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj (γ₁ _ _ _) (g⁻¹ • x) := by
    intro x hx
    have := (smul_adj g⁻¹).mpr hx
    rwa [← hg1, inv_smul_smul] at this
  obtain ⟨p, hp1, hp0⟩ := exists_stab_smul_eq adj_γ₀_γ₁.symm (adjOf w hw)
  obtain ⟨p', hp1', hp0'⟩ := exists_stab_smul_eq adj_γ₀_γ₁.symm (adjOf w' hw')
  have hpP : (p : G) ∈ P2 L1 L2 S := by
    have := mem_stab_of_smul_eq hp1; rwa [stab_γ₁ h₂] at this
  have hp'P : (p' : G) ∈ P2 L1 L2 S := by
    have := mem_stab_of_smul_eq hp1'; rwa [stab_γ₁ h₂] at this
  have notB : ∀ r : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S),
      r • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) = g⁻¹ • x → x ≠ μ →
      (r : G) ∉ bigB L1 L2 S := by
    intro r x hr hxμ hB
    apply hxμ
    have hfix : r • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) = γ₀ _ _ _ := by
      apply smul_eq_of_mem_stab
      rw [stab_γ₀ h₁]
      exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hB
    rw [hfix] at hr
    rw [← hg0, hr, smul_inv_smul]
  obtain ⟨q, hq, hqB⟩ := Q1_trans_P2 F hpP hp'P (notB p w hp0 hwμ) (notB p' w' hp0' hw'μ)
  have hqP1 : q ∈ P1 L1 L2 S := (pCoreOf_le 2 (P1 L1 L2 S)) hq
  set qq : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨q, h₁ hqP1⟩ with hqq
  refine ⟨g * qq * g⁻¹, ?_, ?_⟩
  · have hQμ : Qv μ = conjSub (g : G) (Q1 L1 L2 S) := by
      rw [← hg0, Qv_smul]; unfold Qv; rw [stab_γ₀ h₁]
    rw [hQμ]
    have := mem_conjSub_of_mem' (h := (g : G)) hq
    simpa using this
  · have hkey : (p'⁻¹ * qq * p) • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) = γ₀ _ _ _ := by
      apply smul_eq_of_mem_stab
      rw [stab_γ₀ h₁]
      have : (((p'⁻¹ * qq * p : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G)) = (p' : G)⁻¹ * q * p := by
        simp [hqq]
      rw [this]
      exact (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hqB
    have hw1 : w = g • (p • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) := by
      rw [hp0, smul_inv_smul]
    have hw1' : w' = g • (p' • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) := by
      rw [hp0', smul_inv_smul]
    have hqp : qq • (p • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) =
        p' • γ₀ _ _ _ := by
      rw [← inv_smul_eq_iff, ← mul_smul, ← mul_smul]
      exact hkey
    rw [hw1, hw1']
    simp only [mul_smul, inv_smul_smul, hqp]

end CFSG.Quasithin.Kleidman.F204
