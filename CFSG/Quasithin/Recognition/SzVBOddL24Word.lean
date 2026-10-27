module

public import CFSG.Quasithin.Recognition.F112J2Ctx

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem exists_L2_smul_γ₁ (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {ε : CosetGeom (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)}
    (hε : (graph (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)).Adj
      (γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) ε) :
    ∃ (y : ↥(K1 ⊔ L2 ⊔ S)) (l : G), l ∈ L2 ∧ (y : G) = l ∧
      y • γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) = ε := by
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  obtain ⟨g, hg1, hg2⟩ := exists_stab_smul_eq
    (adj_γ₀_γ₁ (G₀ := K1 ⊔ L2 ⊔ S) (G₁ := L2 ⊔ S) (G₂ := K1 ⊔ S)) hε
  have hg : (g : G) ∈ L2 ⊔ S := by
    have := mem_stab_of_smul_eq hg1
    rwa [stab_γ₀ hyp.le₁] at this
  obtain ⟨l, hl, s, hs, hls⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes h.hyp.h2.normalizes).mp hg
  have hl₀ : l ∈ K1 ⊔ L2 ⊔ S := hyp.le₁ (Subgroup.mem_sup_left hl)
  have hs₂ : s ∈ K1 ⊔ S := Subgroup.mem_sup_right hs
  have hs₀ : s ∈ K1 ⊔ L2 ⊔ S := hyp.le₂ hs₂
  refine ⟨⟨l, hl₀⟩, l, hl, rfl, ?_⟩
  have e : g = ⟨l, hl₀⟩ * ⟨s, hs₀⟩ := Subtype.ext hls
  rw [← hg2, e, mul_smul, smul_γ₁_of_mem hyp.le₂ hs₂]

theorem exists_word_step (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {δ : CosetGeom (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)} {d : ℕ}
    (hd : dist (γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) δ = d + 2) :
    ∃ (x : ↥(K1 ⊔ L2 ⊔ S)) (l k : G), l ∈ L2 ∧ k ∈ K1 ⊔ S ∧ (x : G) = l * k ∧
      dist (γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) (x⁻¹ • δ) = d := by
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hd' : dist δ (γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) = d + 1 + 1 := by
    rw [CosetGeom.dist_comm, hd]
  obtain ⟨β₁, hβ₁, hdβ₁⟩ := exists_adj_dist_eq hyp.gen hd'
  obtain ⟨β₂, hβ₂, hdβ₂⟩ := exists_adj_dist_eq hyp.gen hdβ₁
  obtain ⟨y, l, hl, hyl, hy⟩ := exists_L2_smul_γ₁ hRO h hβ₁
  have hadj : (graph (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)).Adj
      (γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) (y⁻¹ • β₂) := by
    have := (smul_adj y⁻¹).mpr hβ₂
    rwa [← hy, inv_smul_smul] at this
  obtain ⟨κ, hκ1, hκ2⟩ := exists_stab_smul_eq
    (adj_γ₀_γ₁ (G₀ := K1 ⊔ L2 ⊔ S) (G₁ := L2 ⊔ S) (G₂ := K1 ⊔ S)).symm hadj
  have hκ : (κ : G) ∈ K1 ⊔ S := by
    have := mem_stab_of_smul_eq hκ1
    rwa [stab_γ₁ hyp.le₂] at this
  have hx : (y * κ) • γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) = β₂ := by
    rw [mul_smul, hκ2, smul_inv_smul]
  refine ⟨y * κ, l, κ, hl, hκ, by rw [Subgroup.coe_mul, hyl], ?_⟩
  calc dist (γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) ((y * κ)⁻¹ • δ)
      = dist ((y * κ) • γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) ((y * κ) • (y * κ)⁻¹ • δ) :=
        (CosetGeom.dist_smul _ _ _).symm
    _ = dist β₂ δ := by rw [hx, smul_inv_smul]
    _ = d := by rw [CosetGeom.dist_comm]; exact hdβ₂

theorem exists_word_five (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {δ : CosetGeom (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)}
    (hd : dist (γ₀ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S)) δ = 3) :
    ∃ (x : ↥(K1 ⊔ L2 ⊔ S)) (l₁ l₂ k : G), l₁ ∈ L2 ∧ l₂ ∈ L2 ∧ k ∈ K1 ⊔ S ∧
      (x : G) = l₁ * k * l₂ ∧ x • γ₁ (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) = δ := by
  obtain ⟨x, l₁, k, hl₁, hk, hx, hdx⟩ := exists_word_step hRO h (δ := δ) (d := 1) (by omega)
  obtain ⟨y, l₂, hl₂, hyl, hy⟩ :=
    exists_L2_smul_γ₁ hRO h (CosetGeom.dist_eq_one_iff_adj.mp hdx)
  refine ⟨x * y, l₁, l₂, k, hl₁, hl₂, hk, ?_, ?_⟩
  · rw [Subgroup.coe_mul, hx, hyl]
  · rw [mul_smul, hy, smul_inv_smul]

end CFSG.Quasithin.SzVB
