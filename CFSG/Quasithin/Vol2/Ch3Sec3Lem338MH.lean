module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338MG

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.M338

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch3Sec3

variable {V : Type} [CommGroup V] [Finite V] {J K₁ K₂ : Subgroup (MulAut V)}
  (hq₁ : CFSG.IsQuasisimple ↥K₁) (hs₁ : IsSimpleGroup ↥K₁) (hq₂ : CFSG.IsQuasisimple ↥K₂)
  (hs₂ : IsSimpleGroup ↥K₂) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : K₁ ⊓ K₂ = ⊥)
  (hK₁J : K₁ ≤ J) (hK₂J : K₂ ≤ J)
  (hJK : J ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)))

include hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK in
theorem not_case124 (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case4 J) : False := by
  have hperf₁ : ⁅K₁, K₁⁆ = K₁ := commutator_self_of_isPerfect hq₁.1
  have hperf₂ : ⁅K₂, K₂⁆ = K₂ := commutator_self_of_isPerfect hq₂.1
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut V)) := le_normalizer_of_commute hc
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set (MulAut V)) :=
    le_normalizer_of_commute fun a ha b hb => (hc b hb a ha).symm
  have hKN₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut V)) :=
    sup_le Subgroup.le_normalizer hK₂N
  have hKN₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set (MulAut V)) :=
    sup_le hK₁N Subgroup.le_normalizer
  have hKJ : K₁ ⊔ K₂ ≤ J := sup_le hK₁J hK₂J
  have habs : ∀ Q : Subgroup (MulAut V), IsNormalRigid Q → K₁ ≤ Q → K₂ ≤ Q →
      Q ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)) → False :=
    fun Q hQ h₁ h₂ hQK => false_of_isNormalRigid hQ h₁ h₂ hQK hKN₁ (exists_noncomm hq₁)
      (ne_bot_of_quasisimple hq₂) hinf
  have hdich : ∀ N : Subgroup (MulAut V), N ≤ J → J ≤ Subgroup.normalizer (N : Set (MulAut V)) →
      (K₁ ≤ N ∨ ∀ a ∈ K₁, ∀ b ∈ N, a * b = b * a) ∧
        (K₂ ≤ N ∨ ∀ a ∈ K₂, ∀ b ∈ N, a * b = b * a) := by
    intro N hNJ hJN
    have hCK : ∀ {K : Subgroup (MulAut V)}, K ≤ K₁ ⊔ K₂ → ⁅K, N⁆ ≤ K₁ ⊔ K₂ := fun hK =>
      (Subgroup.commutator_mono hK hNJ).trans (commutator_le_left_of_le_normalizer hJK)
    exact ⟨le_or_commute_of_isSimpleGroup hs₁ hperf₁ (hK₁J.trans hJN)
        ((hCK le_sup_left).trans hKN₁),
      le_or_commute_of_isSimpleGroup hs₂ hperf₂ (hK₂J.trans hJN) ((hCK le_sup_right).trans hKN₂)⟩
  rcases hcases with ⟨hE, -, -⟩ | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc₁₂, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩
  · have hcomp : ∀ {K : Subgroup (MulAut V)}, CFSG.IsQuasisimple ↥K → K ≤ K₁ ⊔ K₂ →
        K₁ ⊔ K₂ ≤ Subgroup.normalizer (K : Set (MulAut V)) →
          K ≤ CFSG.Open.quasithinGenFitting J := by
      intro K hq hK hKn
      refine le_sup_of_le_right (le_sSup ⟨hK.trans hKJ, ?_, B1Red.isQuasisimple_to_open hq⟩)
      exact CFSG.Open.IsSubnormal.step hK
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hK).mpr hKn)
        (CFSG.Open.IsSubnormal.step hKJ
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mpr hJK)
          (CFSG.Open.IsSubnormal.refl J))
    exact habs _ (isNormalRigid_of_isQuasisimple hE) (hcomp hq₁ le_sup_left hKN₁)
      (hcomp hq₂ le_sup_right hKN₂) ((quasithinGenFitting_le J).trans hJK)
  · exact InternalSec.not_le_perm_three hq₁ hK₁J e
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc₂₁ : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc₁₂ b hb a ha).symm
    have htN : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
      InternalSec.mem_normalizer_sup ht₁ ht₂
    have hsub : ∀ {K : Subgroup (MulAut V)}, K ≤ J → Group.IsPerfect ↥K → K ≤ G₁ ⊔ G₂ := by
      intro K hK hp
      rw [hJt] at hK
      exact (InternalSec.le_commutator_of_perfect hK hp).trans
        (InternalSec.commutator_le_of_zpowers htN)
    have hG₁J : G₁ ≤ J := by rw [hJt]; exact le_sup_left.trans le_sup_left
    have hG₂J : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    have hJG₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut V)) := by
      rw [hJt]
      exact sup_le (sup_le Subgroup.le_normalizer (le_normalizer_of_commute hc₁₂))
        (Subgroup.zpowers_le.mpr ht₁)
    have hJG₂ : J ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
      rw [hJt]
      exact sup_le (sup_le (le_normalizer_of_commute hc₂₁) Subgroup.le_normalizer)
        (Subgroup.zpowers_le.mpr ht₂)
    obtain ⟨d₁₁, d₂₁⟩ := hdich G₁ hG₁J hJG₁
    obtain ⟨d₁₂, d₂₂⟩ := hdich G₂ hG₂J hJG₂
    have hin : ∀ {K : Subgroup (MulAut V)}, CFSG.IsQuasisimple ↥K → K ≤ J →
        (K ≤ G₁ ∨ ∀ a ∈ K, ∀ b ∈ G₁, a * b = b * a) →
        (K ≤ G₂ ∨ ∀ a ∈ K, ∀ b ∈ G₂, a * b = b * a) → K ≤ G₁ := by
      intro K hq hKJ' d₁ d₂
      rcases d₁ with h | c₁
      · exact h
      rcases d₂ with h | c₂
      · exact (InternalSec.not_le_of_card_prime hq h hc₂).elim
      · exact (false_of_commute_sup (hsub hKJ' hq.1) (exists_noncomm hq) c₁ c₂).elim
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact habs G₁ (isNormalRigid_of_isSimpleGroup e₁.isSimpleGroup) (hin hq₁ hK₁J d₁₁ d₁₂)
      (hin hq₂ hK₂J d₂₁ d₂₂) (hG₁J.trans hJK)

include hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK in
theorem module_of_b56 (hV2 : ∀ v : V, v ^ 2 = 1)
    (hA₁ : A38Types ↥K₁) (hA₂ : A38Types ↥K₂) (hSL3 : A38TypesSLThree) {s : MulAut V}
    (hs₁₂ : conjSub s K₂ = K₁) (hs₂₁ : conjSub s K₁ = K₂)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    (commV K₁ ⊔ fixV (K₁ ⊔ K₂)) ⊓ (commV K₂ ⊔ fixV (K₁ ⊔ K₂)) = fixV (K₁ ⊔ K₂) ∧
      ModType K₁ (commV K₁ ⊔ fixV (K₁ ⊔ K₂)) (fixV (K₁ ⊔ K₂)) := by
  have hKJ : K₁ ⊔ K₂ ≤ J := sup_le hK₁J hK₂J
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exact (not_case124 hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK (Or.inl h1)).elim
  · exact (not_case124 hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK (Or.inr (Or.inl h2))).elim
  · obtain ⟨G₁, G₂, hsup, hinf₁₂, hc₁₂, hf₁, hf₂, W₁, W₂, hCW₁, hCW₂, hinv₁, hinv₂, hWW, hWiW,
      hp₁, hp₂⟩ := h3
    have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
    have hG₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
    have hi₁ : ∀ j ∈ J, ∀ w ∈ W₁, j w ∈ W₁ := fun j hj w hw => hinv₁ ⟨j, hj⟩ w hw
    have hi₂ : ∀ j ∈ J, ∀ w ∈ W₂, j w ∈ W₂ := fun j hj w hw => hinv₂ ⟨j, hj⟩ w hw
    rcases assign hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK hsup hinf₁₂ hc₁₂ hf₁ hf₂ with
      ⟨h11, h22⟩ | ⟨h12, h21⟩
    · exact case3_core hV2 hq₁ hq₂ hA₁ hA₂ hSL3 hKJ hG₁J hG₂J hi₁ hi₂ hCW₁ hCW₂ hWW hWiW hp₁ hp₂
        h11 h22
    · exact case3_core hV2 hq₁ hq₂ hA₁ hA₂ hSL3 hKJ hG₂J hG₁J hi₂ hi₁ hCW₂ hCW₁
        (by rw [sup_comm]; exact hWW) (by rw [inf_comm]; exact hWiW) hp₂ hp₁ h12 h21
  · exact (not_case124 hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK (Or.inr (Or.inr h4))).elim
  · exact case5_core hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK hs₁₂ hs₂₁ h5

end CFSG.Quasithin.H13.M338
