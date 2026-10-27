module

public import CFSG.Quasithin.Vol2.KGFactC31NoM22Ord
public import CFSG.Quasithin.Vol2.KGFactC31NoM22FusSection
public import CFSG.Quasithin.Vol2.KGFactC31NoM22FusM22

public section

namespace CFSG.Quasithin.KGC31

@[expose] def SylowAutBound (ℓ m : ℕ) (S : Type) [Group S] [Finite S] : Prop :=
  ∃ P : Sylow ℓ S, (∀ x ∈ (P : Subgroup S), ∀ y ∈ (P : Subgroup S), x * y = y * x) ∧
    ∀ u ∈ Subgroup.normalizer ((P : Subgroup S) : Set S),
      u ^ m ∈ Subgroup.centralizer ((P : Subgroup S) : Set S)

@[expose] def LieSylow11Exc : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (f : ℕ),
    (IsG2 2 f S ∨ Is3D4 2 f S ∨ Is2F4 f S) → SylowAutBound 11 1152 S

theorem no_m22_surj_of_sylowAutBound {G : Type} [Group G] [Finite G] {ℓ m : ℕ}
    (h : SylowAutBound ℓ m G) (hℓ : (ℓ = 11 ∧ ¬ 5 ∣ m) ∨ (ℓ = 5 ∧ ¬ 4 ∣ m))
    (A : Subgroup G) (φ : A →* CFSG.Blueprint.NativeSporadic.Carrier .M22) :
    ¬ Function.Surjective φ := by
  obtain ⟨P, hP, hm⟩ := h
  intro hsurj
  rcases hℓ with ⟨rfl, hm5⟩ | ⟨rfl, hm4⟩
  · haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨α, β, hα, hβ⟩ := m22_exists_eleven
    obtain ⟨a', ha'⟩ := hsurj α
    obtain ⟨b', hb'⟩ := hsurj β
    have hk : φ b' * φ a' * (φ b')⁻¹ = φ a' ^ 3 := by
      rw [ha', hb']
      exact hβ
    have hfus := section_fusion P hP hm φ a' b' ⟨1, by rw [pow_one, ha', hα]⟩ hk
    rw [ha'] at hfus
    have h1 : 3 ^ m ≡ 1 [MOD orderOf α] :=
      pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact hfus)
    rw [hα] at h1
    exact hm5 (five_dvd_of_three_pow_modEq_eleven h1)
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨c, d, hc, hd⟩ := m22_exists_five
    obtain ⟨c', hc'⟩ := hsurj c
    obtain ⟨d', hd'⟩ := hsurj d
    have hk : φ d' * φ c' * (φ d')⁻¹ = φ c' ^ 3 := by
      rw [hc', hd']
      exact hd
    have hfus := section_fusion P hP hm φ c' d' ⟨1, by rw [pow_one, hc', hc]⟩ hk
    rw [hc'] at hfus
    have h1 : 3 ^ m ≡ 1 [MOD orderOf c] :=
      pow_eq_pow_iff_modEq.1 (by rw [pow_one]; exact hfus)
    rw [hc] at h1
    exact hm4 (four_dvd_of_three_pow_modEq_five h1)

theorem noM22SectionLieExcRes_of_lieSylow11 (h : LieSylow11Exc) : NoM22SectionLieExcRes := by
  unfold NoM22SectionLieExcRes
  intro S _ _ hS Y φ
  obtain ⟨f, hf⟩ := hS
  have hsyl : SylowAutBound 11 1152 S := by
    rcases hf with ⟨_, _, hG⟩ | ⟨_, _, hD⟩ | ⟨_, _, _, hF⟩
    · exact h S f (Or.inl hG)
    · exact h S f (Or.inr (Or.inl hD))
    · exact h S f (Or.inr (Or.inr hF))
  exact no_m22_surj_of_sylowAutBound hsyl (Or.inl ⟨rfl, by norm_num⟩) Y φ

end CFSG.Quasithin.KGC31

end
