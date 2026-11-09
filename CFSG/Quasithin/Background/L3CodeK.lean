module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.LinearAlgebra.F2SL3Code

public section

namespace CFSG.Quasithin.L3.CodeK

open CFSG.F2NatMat CFSG.Quasithin.L3

@[expose] def actc (x : SL3c) (v : Vec) : Vec := (dec 3 x.1.1).mulVec v

theorem act_toSL (x : SL3c) (v : Vec) : act (SL3c.toSL x) v = actc x v := rfl

theorem a4_gen_c : ∀ c : Vec, c ≠ 0 → ∀ δ : SL3c, actc δ c = c → δ * δ * δ = 1 → δ ≠ 1 →
    ∀ γ : SL3c, actc γ c = c → (∀ v, actc (γ * γ * γ) v - v ∈ ({0, c} : Finset Vec)) →
      γ * γ = 1 ∨ (δ⁻¹ * γ) * (δ⁻¹ * γ) = 1 ∨ (δ⁻¹ * δ⁻¹ * γ) * (δ⁻¹ * δ⁻¹ * γ) = 1 := by
  decide +kernel

theorem a4_gen_k : ∀ c : Vec, c ≠ 0 → ∀ δ γ : Γ, act δ c = c → δ * δ * δ = 1 → δ ≠ 1 →
    act γ c = c → γ * γ * γ ∈ AS {0, c} →
      γ * γ = 1 ∨ (δ⁻¹ * γ) * (δ⁻¹ * γ) = 1 ∨ (δ⁻¹ * δ⁻¹ * γ) * (δ⁻¹ * δ⁻¹ * γ) = 1 := by
  intro c hc δ γ h1 h2 h3 h4 h5
  obtain ⟨d, rfl⟩ := SL3c.toSL_surjective δ
  obtain ⟨g, rfl⟩ := SL3c.toSL_surjective γ
  simp only [AS, Finset.mem_filter, Finset.mem_univ, true_and] at h5
  simp only [← SL3c.toSL_mul, ← SL3c.toSL_inv, ← SL3c.toSL_one, SL3c.toSL_injective.eq_iff,
    act_toSL, Ne] at h1 h2 h3 h4 h5 ⊢
  exact a4_gen_c c hc d h1 h2 h3 g h4 h5

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem l3_stab_two_c : ∀ p : Vec, p ≠ 0 → ∀ x : SL3c, actc x p = p → x ^ 8 = 1 →
    ∀ g : SL3c, g ^ 3 = 1 → g ≠ 1 → actc g p = p → (x * (g * x * g⁻¹)) ^ 8 = 1 →
      (x * (g⁻¹ * x * g)) ^ 8 = 1 → ∀ v, actc x v - v ∈ ({0, p} : Finset Vec) := by
  decide +kernel

theorem l3_stab_two_k : ∀ p : Vec, p ≠ 0 → ∀ x : Γ, act x p = p → x ^ 8 = 1 →
    ∀ g : Γ, g ^ 3 = 1 → g ≠ 1 → act g p = p → (x * (g * x * g⁻¹)) ^ 8 = 1 →
      (x * (g⁻¹ * x * g)) ^ 8 = 1 → x ∈ AS {0, p} := by
  intro p hp x h1 h2 g h3 h4 h5 h6 h7
  obtain ⟨x, rfl⟩ := SL3c.toSL_surjective x
  obtain ⟨g, rfl⟩ := SL3c.toSL_surjective g
  simp only [AS, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [← SL3c.toSL_mul, ← SL3c.toSL_inv, ← SL3c.toSL_one, ← SL3c.toSL_npow,
    SL3c.toSL_injective.eq_iff, act_toSL, Ne] at h1 h2 h3 h4 h5 h6 h7 ⊢
  exact l3_stab_two_c p hp x h1 h2 g h3 h4 h5 h6 h7

@[expose] def uniC : List SL3c :=
  [⟨⟨273, by norm_num⟩, by decide⟩, ⟨⟨305, by norm_num⟩, by decide⟩,
    ⟨⟨277, by norm_num⟩, by decide⟩, ⟨⟨309, by norm_num⟩, by decide⟩,
    ⟨⟨275, by norm_num⟩, by decide⟩, ⟨⟨307, by norm_num⟩, by decide⟩,
    ⟨⟨279, by norm_num⟩, by decide⟩, ⟨⟨311, by norm_num⟩, by decide⟩]

end CFSG.Quasithin.L3.CodeK
