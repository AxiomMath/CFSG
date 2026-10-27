module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalTwo
public import CFSG.Quasithin.EmptyFaithful.SzF53BasA
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalThree

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem mem_stab_smul_γ₀ {H M : Subgroup G} (h₁ : H ≤ H ⊔ M) (g : ↥(H ⊔ M)) {x : G} :
    x ∈ stab (g • γ₀ (H ⊔ M) H M) ↔ (g : G)⁻¹ * x * g ∈ H := by
  rw [stab_smul, stab_γ₀ h₁, mem_conjSub]

omit [Finite G] in
theorem mem_stab_smul_γ₁ {H M : Subgroup G} (h₂ : M ≤ H ⊔ M) (g : ↥(H ⊔ M)) {x : G} :
    x ∈ stab (g • γ₁ (H ⊔ M) H M) ↔ (g : G)⁻¹ * x * g ∈ M := by
  rw [stab_smul, stab_γ₁ h₂, mem_conjSub]

theorem three_mem_stab_nbr (F : Frame L1 L2 S D X) {δ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ) {t : G} (ht : t ∈ stab δ) (ht3 : t ^ 3 = 1) :
    t ∈ stab μ := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hδ
  rw [mem_stab_smul_γ₀ h₁] at ht
  have hadj : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj
      (γ₀ _ _ _) (g⁻¹ • μ) := by
    have := (smul_adj g⁻¹).mpr hμ
    rwa [inv_smul_smul] at this
  obtain ⟨q, hq0, hq1⟩ := exists_stab_smul_eq adj_γ₀_γ₁ hadj
  have hμeq : μ = (g * q) • γ₁ _ _ _ := by
    rw [mul_smul, hq1, smul_inv_smul]
  rw [hμeq, mem_stab_smul_γ₁ h₂]
  have hqP : (q : G) ∈ P1 L1 L2 S := by
    have := mem_stab_of_smul_eq hq0
    rwa [stab_γ₀ h₁] at this
  have ht0 : (g : G)⁻¹ * t * g ∈ P1 L1 L2 S := ht
  have ht03 : ((g : G)⁻¹ * t * g) ^ 3 = 1 := by
    have hcp := conj_pow (a := (g : G)⁻¹) (b := t) (i := 3)
    simp only [inv_inv] at hcp
    rw [hcp, ht3]; group
  have hB := three_conj_mem_B F ht0 ht03 hqP
  have e : ((g * q : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G)⁻¹ * t * ((g * q : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G)
      = (q : G)⁻¹ * ((g : G)⁻¹ * t * g) * q := by
    simp [mul_assoc]
  rw [e]
  exact (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hB

theorem exists_three_stab_two_nbrs (F : Frame L1 L2 S D X)
    {μ u v : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hμ : vtype μ = true) (hu : u ∈ nbrs μ)
    (hv : v ∈ nbrs μ) (huv : u ≠ v) :
    ∃ t ∈ stab μ, t ≠ 1 ∧ t ^ 3 = 1 ∧ t ∈ stab u ∧ t ∈ stab v := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hμ
  have hu' : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj
      (γ₁ _ _ _) (g⁻¹ • u) := by
    have := (smul_adj g⁻¹).mpr hu
    rwa [inv_smul_smul] at this
  have hv' : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj
      (γ₁ _ _ _) (g⁻¹ • v) := by
    have := (smul_adj g⁻¹).mpr hv
    rwa [inv_smul_smul] at this
  obtain ⟨q₁, hq₁0, hq₁1⟩ := exists_stab_smul_eq adj_γ₀_γ₁.symm hu'
  obtain ⟨q₂, hq₂0, hq₂1⟩ := exists_stab_smul_eq adj_γ₀_γ₁.symm hv'
  have hueq : u = (g * q₁) • γ₀ _ _ _ := by rw [mul_smul, hq₁1, smul_inv_smul]
  have hveq : v = (g * q₂) • γ₀ _ _ _ := by rw [mul_smul, hq₂1, smul_inv_smul]
  have hq₁P : (q₁ : G) ∈ P2 L1 L2 S := by
    have := mem_stab_of_smul_eq hq₁0
    rwa [stab_γ₁ h₂] at this
  have hq₂P : (q₂ : G) ∈ P2 L1 L2 S := by
    have := mem_stab_of_smul_eq hq₂0
    rwa [stab_γ₁ h₂] at this
  have hgg : (q₁ : G)⁻¹ * q₂ ∈ P2 L1 L2 S :=
    (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hq₁P) hq₂P
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hggB : (q₁ : G)⁻¹ * q₂ ∉ bigB L1 L2 S := by
    intro hB
    apply huv
    have hfix : (q₁⁻¹ * q₂) • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) =
        γ₀ _ _ _ := by
      apply smul_eq_of_mem_stab
      rw [stab_γ₀ h₁]
      exact hBP1 hB
    have h2 : q₂ • γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) =
        q₁ • γ₀ _ _ _ := by
      rw [← inv_smul_eq_iff, ← mul_smul]
      exact hfix
    rw [hueq, hveq, mul_smul, mul_smul, h2]
  obtain ⟨t, htB, ht1, ht3, htg⟩ := exists_three_conj_mem_B F hgg hggB
  set t'' : G := (g : G) * (q₁ : G) * t * ((g : G) * (q₁ : G))⁻¹ with ht''
  have hback : ((g : G) * (q₁ : G))⁻¹ * t'' * ((g : G) * (q₁ : G)) = t := by
    rw [ht'']; group
  refine ⟨t'', ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_stab_smul_γ₁ h₂]
    have : (g : G)⁻¹ * t'' * g = (q₁ : G) * t * (q₁ : G)⁻¹ := by rw [ht'']; group
    rw [this]
    exact (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).mul_mem hq₁P ((le_sup_right : bigB L1 L2 S ≤
      P2 L1 L2 S) htB)) ((P2 L1 L2 S).inv_mem hq₁P)
  · intro h
    apply ht1
    rw [h] at hback
    simpa using hback.symm
  · rw [ht'', conj_pow, ht3]; group
  · rw [hueq, mem_stab_smul_γ₀ h₁]
    have e : (((g * q₁ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G))⁻¹ * t'' *
        ((g * q₁ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) = t := by
      rw [← hback]; simp [mul_assoc]
    rw [e]
    exact hBP1 htB
  · rw [hveq, mem_stab_smul_γ₀ h₁]
    have e : (((g * q₂ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G))⁻¹ * t'' *
        ((g * q₂ : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) =
        ((q₁ : G)⁻¹ * q₂)⁻¹ * t * ((q₁ : G)⁻¹ * q₂) := by
      rw [ht'']; simp [mul_assoc]
    rw [e]
    exact hBP1 htg

end CFSG.Quasithin.Kleidman.F204
