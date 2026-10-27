module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3CovTools
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowGroup

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3Sylow

open CFSG.Quasithin

structure J3CoverFacts {J : Type} [Group J] (T R : Subgroup J) (s : J) : Prop where
  card_T : Nat.card T = 243
  mem_R : ∀ x, x ∈ R ↔ x ∈ T ∧ ∀ y ∈ T, y * x = x * y
  s_norm : s ∈ Subgroup.normalizer (T : Set J)
  s_pow : s ^ 8 = 1
  R_elem : CFSG.Open.IsElemAbelian 3 R
  R_card : Nat.card R = 9
  R_fix : ∀ x ∈ R, s * x * s⁻¹ = x → x = 1
  R_inv : ∀ x ∈ R, s ^ 4 * x * (s ^ 4)⁻¹ = x⁻¹
  nonab : ∃ x ∈ T, ∃ y ∈ T, x * y * x⁻¹ * y⁻¹ ∉ R
  singer : ∀ W : Subgroup J, W ≤ T → W.relIndex T = 3 → s ^ 2 ∉ Subgroup.normalizer (W : Set J)

theorem LocalData.coverFacts {X : Type} [Group X] [Finite X] {H : Subgroup X} {t₁ t₂ s : X}
    {Z : Fin 9 → X} {w₁ w₂ : List Bool} (D : LocalData H t₁ t₂ s Z w₁ w₂) :
    J3CoverFacts (Subgroup.closure ({t₁, t₂} : Set X))
      (centerOf (Subgroup.closure ({t₁, t₂} : Set X))) s where
  card_T := D.card_P
  mem_R := fun _ => mem_centerOf
  s_norm := D.mem_normalizer
  s_pow := D.s_pow_eight
  R_elem := D.center_elem.1
  R_card := D.card_center
  R_fix := fun x hx hfix => by
    by_contra hne
    obtain ⟨i, rfl⟩ := (D.Z_mem x).1 hx
    exact (D.Z_irred i hne).2.1 hfix
  R_inv := by
    have hirr : ∀ x ∈ centerOf (Subgroup.closure ({t₁, t₂} : Set X)), x ≠ 1 →
        s * x * s⁻¹ ≠ 1 ∧ s * x * s⁻¹ ≠ x ∧ s * x * s⁻¹ ≠ x ^ 2 := fun x hx hne => by
      obtain ⟨i, rfl⟩ := (D.Z_mem x).1 hx
      exact D.Z_irred i hne
    have hc4 : ∃ x ∈ centerOf (Subgroup.closure ({t₁, t₂} : Set X)),
        s ^ 4 * x ≠ x * s ^ 4 := by
      obtain ⟨i, hi⟩ := D.Z_cent 4 (by norm_num) (by norm_num)
      exact ⟨Z i, (D.Z_mem _).2 ⟨i, rfl⟩, hi⟩
    exact pow_four_inv_of_irred D.center_elem.1 D.card_center D.mem_normalizer_center
      D.s_pow_eight hirr hc4
  nonab := by
    by_contra h
    have h' : ∀ x ∈ Subgroup.closure ({t₁, t₂} : Set X),
        ∀ y ∈ Subgroup.closure ({t₁, t₂} : Set X),
        x * y * x⁻¹ * y⁻¹ ∈ centerOf (Subgroup.closure ({t₁, t₂} : Set X)) := fun x hx y hy =>
      Classical.byContradiction fun hn => h ⟨x, hx, y, hy, hn⟩
    have hc : ∀ x ∈ Subgroup.closure ({t₁, t₂} : Set X),
        ∀ y ∈ Subgroup.closure ({t₁, t₂} : Set X),
        ∀ g ∈ Subgroup.closure ({t₁, t₂} : Set X),
        (x * y * x⁻¹ * y⁻¹) * g = g * (x * y * x⁻¹ * y⁻¹) := fun x hx y hy g hg =>
      ((mem_centerOf.1 (h' x hx y hy)).2 g hg).symm
    have hcomm := commutator_mem_zpowers_of_class_two hc
    have hzc : t₁ * t₂ * t₁⁻¹ * t₂⁻¹ ∈ centerOf (Subgroup.closure ({t₁, t₂} : Set X)) :=
      h' t₁ (Subgroup.subset_closure (by simp)) t₂ (Subgroup.subset_closure (by simp))
    obtain ⟨i, hi⟩ := (D.Z_mem _).1 hzc
    have hne : Z i ≠ 1 := by
      rw [← hi]
      intro h1
      apply D.noncomm
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hcomm' := hcomm (s * t₁ * s⁻¹) D.conj₁ (s * t₂ * s⁻¹) D.conj₂
    have e : (s * t₁ * s⁻¹) * (s * t₂ * s⁻¹) * (s * t₁ * s⁻¹)⁻¹ * (s * t₂ * s⁻¹)⁻¹ =
        s * (t₁ * t₂ * t₁⁻¹ * t₂⁻¹) * s⁻¹ := by group
    rw [e, hi] at hcomm'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hcomm'
    have ho : orderOf (Z i) = 3 := orderOf_eq_prime (D.Z_cube i) hne
    rw [← zpow_mod_orderOf, ho] at hn
    obtain ⟨h1, h2, h3⟩ := D.Z_irred i hne
    have h0 : 0 ≤ n % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h3' : n % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    generalize n % ((3 : ℕ) : ℤ) = r at hn h0 h3'
    interval_cases r
    · exact h1 (by simpa using hn.symm)
    · exact h2 (by simpa using hn.symm)
    · exact h3 (by simpa using hn.symm)
  singer := fun _ _ hW => D.sq_not_mem_normalizer hW

end CFSG.AGLEmbedding.KFactProofs.J3Sylow
