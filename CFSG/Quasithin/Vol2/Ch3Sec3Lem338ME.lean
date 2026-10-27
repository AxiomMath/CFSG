module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338MD

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.M338

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch3Sec3

variable {V : Type} [CommGroup V]

@[expose] def InCore (K A : Subgroup (MulAut V)) : Prop :=
  K ≤ A ∧ ∀ N ≤ A, Group.IsPerfect ↥N → N ≤ K

section Assign

variable {J K₁ K₂ G₁ G₂ : Subgroup (MulAut V)}
  (hq₁ : CFSG.IsQuasisimple ↥K₁) (hs₁ : IsSimpleGroup ↥K₁) (hq₂ : CFSG.IsQuasisimple ↥K₂)
  (hs₂ : IsSimpleGroup ↥K₂) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : K₁ ⊓ K₂ = ⊥)
  (hK₁J : K₁ ≤ J) (hK₂J : K₂ ≤ J)
  (hJK : J ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)))

theorem exists_noncomm {K : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥K) :
    ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := InternalSec.exists_noncomm_of_isQuasisimple hq
  exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩

theorem ne_bot_of_quasisimple {K : Subgroup (MulAut V)} (hq : CFSG.IsQuasisimple ↥K) : K ≠ ⊥ := by
  intro hb
  obtain ⟨a, ha, b, -, hab⟩ := exists_noncomm hq
  rw [hb, Subgroup.mem_bot] at ha
  exact hab (by rw [ha, one_mul, mul_one])

include hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK in
theorem assign (hsup : G₁ ⊔ G₂ = J) (hinf₁₂ : G₁ ⊓ G₂ = ⊥)
    (hc₁₂ : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hf₁ : B56FactorList ↥G₁)
    (hf₂ : B56FactorList ↥G₂) :
    (InCore K₁ G₁ ∧ InCore K₂ G₂) ∨ (InCore K₁ G₂ ∧ InCore K₂ G₁) := by
  have hperf₁ : ⁅K₁, K₁⁆ = K₁ := commutator_self_of_isPerfect hq₁.1
  have hperf₂ : ⁅K₂, K₂⁆ = K₂ := commutator_self_of_isPerfect hq₂.1
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut V)) := le_normalizer_of_commute hc
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set (MulAut V)) :=
    le_normalizer_of_commute fun a ha b hb => (hc b hb a ha).symm
  have hKN₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hK₂N
  have hKN₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set (MulAut V)) :=
    sup_le hK₁N Subgroup.le_normalizer
  have hc₂₁ : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc₁₂ b hb a ha).symm
  have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
  have hG₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
  have hJG₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_commute hc₁₂)
  have hJG₂ : J ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
    rw [← hsup]
    exact sup_le (le_normalizer_of_commute hc₂₁) Subgroup.le_normalizer
  have hdich : ∀ N : Subgroup (MulAut V), N ≤ J → J ≤ Subgroup.normalizer (N : Set (MulAut V)) →
      (K₁ ≤ N ∨ ∀ a ∈ K₁, ∀ b ∈ N, a * b = b * a) ∧
        (K₂ ≤ N ∨ ∀ a ∈ K₂, ∀ b ∈ N, a * b = b * a) := by
    intro N hNJ hJN
    have hCK : ∀ {K : Subgroup (MulAut V)}, K ≤ K₁ ⊔ K₂ → ⁅K, N⁆ ≤ K₁ ⊔ K₂ := fun hK =>
      (Subgroup.commutator_mono hK hNJ).trans (commutator_le_left_of_le_normalizer hJK)
    exact ⟨le_or_commute_of_isSimpleGroup hs₁ hperf₁ (hK₁J.trans hJN)
        ((hCK le_sup_left).trans hKN₁),
      le_or_commute_of_isSimpleGroup hs₂ hperf₂ (hK₂J.trans hJN) ((hCK le_sup_right).trans hKN₂)⟩
  have hcore : ∀ {A B : Subgroup (MulAut V)} {K K' : Subgroup (MulAut V)}, A ⊓ B = ⊥ →
      B56FactorList ↥A → A ≤ J → J ≤ Subgroup.normalizer (A : Set (MulAut V)) →
      CFSG.IsQuasisimple ↥K → K ≤ A → K' ≤ B → (K = K₁ ∧ K' = K₂ ∨ K = K₂ ∧ K' = K₁) →
      InCore K A := by
    intro A B K K' hAB hfA hAJ hJA hq hKA hK'B hKK'
    rcases factorList_core hfA with h0 | ⟨Q, hQA, hQ, hQp, -⟩
    · exact absurd (h0 K hKA hq.1) (ne_bot_of_quasisimple hq)
    have hKQ : K ≤ Q := hQp K hKA hq.1
    have hKs : K ⊔ K' = K₁ ⊔ K₂ := by
      rcases hKK' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact sup_comm _ _
    have hKN : K' ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
      rcases hKK' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hK₂N
      · exact hK₁N
    have hKA' : ∀ x ∈ K ⊔ K', x ∈ A → x ∈ K := by
      intro x hx hxA
      obtain ⟨k, hk, k', hk', rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hKN).mp hx
      have hk'A : k' ∈ A := by
        have : k' = k⁻¹ * (k * k') := by group
        rw [this]
        exact A.mul_mem (A.inv_mem (hKA hk)) hxA
      have hk'1 : k' = 1 := by
        have : k' ∈ A ⊓ B := ⟨hk'A, hK'B hk'⟩
        rwa [hAB, Subgroup.mem_bot] at this
      rw [hk'1, mul_one]
      exact hk
    have hAN : A ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
      refine le_normalizer_of_conj fun x hx k hk => hKA' _ ?_ ?_
      · rw [hKs]
        exact (Subgroup.mem_normalizer_iff.mp (hJK (hAJ hx)) k).mp
          (hKs ▸ Subgroup.mem_sup_left hk)
      · exact A.mul_mem (A.mul_mem hx (hKA hk)) (A.inv_mem hx)
    have hKQ' : K = Q := hQ K hKQ (hQA.trans hAN) (exists_noncomm hq)
    exact ⟨hKA, fun N hN hp => hKQ' ▸ hQp N hN hp⟩
  have hK₁s : K₁ ≤ G₁ ⊔ G₂ := by rw [hsup]; exact hK₁J
  have hK₂s : K₂ ≤ G₁ ⊔ G₂ := by rw [hsup]; exact hK₂J
  have hinf₂₁ : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf₁₂
  obtain ⟨d₁₁, d₂₁⟩ := hdich G₁ hG₁J hJG₁
  obtain ⟨d₁₂, d₂₂⟩ := hdich G₂ hG₂J hJG₂
  have hK₁in : K₁ ≤ G₁ ∨ K₁ ≤ G₂ := by
    rcases d₁₁ with h | c₁
    · exact Or.inl h
    rcases d₁₂ with h | c₂
    · exact Or.inr h
    exact (false_of_commute_sup hK₁s (exists_noncomm hq₁) c₁ c₂).elim
  have hK₂in : K₂ ≤ G₁ ∨ K₂ ≤ G₂ := by
    rcases d₂₁ with h | c₁
    · exact Or.inl h
    rcases d₂₂ with h | c₂
    · exact Or.inr h
    exact (false_of_commute_sup hK₂s (exists_noncomm hq₂) c₁ c₂).elim
  have hsame : ∀ {A : Subgroup (MulAut V)}, B56FactorList ↥A → A ≤ J → K₁ ≤ A → K₂ ≤ A →
      False := by
    intro A hfA hAJ h₁ h₂
    rcases factorList_core hfA with h0 | ⟨Q, hQA, hQ, hQp, -⟩
    · exact ne_bot_of_quasisimple hq₁ (h0 K₁ h₁ hq₁.1)
    exact false_of_isNormalRigid hQ (hQp K₁ h₁ hq₁.1) (hQp K₂ h₂ hq₂.1)
      (hQA.trans (hAJ.trans hJK)) hKN₁ (exists_noncomm hq₁) (ne_bot_of_quasisimple hq₂) hinf
  rcases hK₁in with h₁ | h₁ <;> rcases hK₂in with h₂ | h₂
  · exact (hsame hf₁ hG₁J h₁ h₂).elim
  · exact Or.inl ⟨hcore hinf₁₂ hf₁ hG₁J hJG₁ hq₁ h₁ h₂ (Or.inl ⟨rfl, rfl⟩),
      hcore hinf₂₁ hf₂ hG₂J hJG₂ hq₂ h₂ h₁ (Or.inr ⟨rfl, rfl⟩)⟩
  · exact Or.inr ⟨hcore hinf₂₁ hf₂ hG₂J hJG₂ hq₁ h₁ h₂ (Or.inl ⟨rfl, rfl⟩),
      hcore hinf₁₂ hf₁ hG₁J hJG₁ hq₂ h₂ h₁ (Or.inr ⟨rfl, rfl⟩)⟩
  · exact (hsame hf₂ hG₂J h₁ h₂).elim

end Assign

end CFSG.Quasithin.H13.M338
