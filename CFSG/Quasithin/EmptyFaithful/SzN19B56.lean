module

public import CFSG.Quasithin.EmptyFaithful.S153LComp
public import CFSG.Quasithin.EmptyFaithful.SzN19Swap

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace SzN19

section Pair

variable {Ω : Type} [Group Ω]

theorem false_of_mem_cComp_of_solvable [Finite Ω] {J K : Subgroup Ω} (hK : K ∈ cComp J)
    (hJ : Group.IsSolvable ↥J) : False := by
  have hKJ : K ≤ J := le_of_mem_cComp hK
  have hKs : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKJ)
      (Subgroup.inclusion_injective hKJ)
  have h1 := (isSolvable_iff_perfectCore_eq_bot K).mp hKs
  rw [perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK)] at h1
  exact ne_bot_of_mem_cComp hK h1

theorem pair_of_two {J N₁ N₂ : Subgroup Ω} (hinf : N₁ ⊓ N₂ = ⊥)
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hall : ∀ K ∈ cComp J, K = N₁ ∨ K = N₂)
    {K₁ K₂ : Subgroup Ω} (h₁ : K₁ ∈ cComp J) (h₂ : K₂ ∈ cComp J) (hne : K₁ ≠ K₂) :
    K₁ ⊓ K₂ = ⊥ ∧ (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧ ∀ K ∈ cComp J, K = K₁ ∨ K = K₂ := by
  rcases hall K₁ h₁ with h1 | h1 <;> rcases hall K₂ h₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · subst h1
    subst h2
    exact ⟨hinf, hc, fun K hK => hall K hK⟩
  · subst h1
    subst h2
    exact ⟨by rw [inf_comm]; exact hinf, fun a ha b hb => (hc b hb a ha).symm,
      fun K hK => (hall K hK).symm⟩
  · exact absurd (h1.trans h2.symm) hne

end Pair

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem pair_of_factors {J G₁ G₂ N₁ N₂ : Subgroup (MulAut V)} (hG₁J : G₁ ≤ J) (hG₂J : G₂ ≤ J)
    (f₁ : S153L.FactorN G₁ N₁) (f₂ : S153L.FactorN G₂ N₂) (hinf : G₁ ⊓ G₂ = ⊥)
    (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (hn₁ : ∀ x ∈ J, ∀ n ∈ N₁, x * n * x⁻¹ ∈ N₁) (hn₂ : ∀ x ∈ J, ∀ n ∈ N₂, x * n * x⁻¹ ∈ N₂)
    (hKP : ∀ K ∈ cComp J, K ≤ G₁ ⊔ G₂)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J)
    {K₁ K₂ : Subgroup (MulAut V)} (h₁ : K₁ ∈ cComp J) (h₂ : K₂ ∈ cComp J) (hne : K₁ ≠ K₂) :
    K₁ ⊓ K₂ = ⊥ ∧ (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧ ∀ K ∈ cComp J, K = K₁ ∨ K = K₂ := by
  obtain ⟨-, -, -, -, -, -, hall⟩ :=
    S153L.components_of_factors hG₁J hG₂J f₁ f₂ hc hn₁ hn₂ hKP hcases
  exact pair_of_two (le_bot_iff.mp ((inf_le_inf f₁.1 f₂.1).trans hinf.le))
    (fun a ha b hb => hc a (f₁.1 ha) b (f₂.1 hb)) hall h₁ h₂ hne

theorem b56_pair {J : Subgroup (MulAut V)}
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J)
    {K₁ K₂ : Subgroup (MulAut V)} (h₁ : K₁ ∈ cComp J) (h₂ : K₂ ∈ cComp J) (hne : K₁ ≠ K₂) :
    K₁ ⊓ K₂ = ⊥ ∧ (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧ ∀ K ∈ cComp J, K = K₁ ∨ K = K₂ := by
  have hcases' := hcases
  have hbotn : ∀ x ∈ J, ∀ n ∈ (⊥ : Subgroup (MulAut V)), x * n * x⁻¹ ∈ (⊥ : Subgroup (MulAut V)) :=
    fun x _ n hn => by rw [Subgroup.mem_bot] at hn ⊢; simp [hn]
  have hcbot : ∀ (G : Subgroup (MulAut V)), ∀ a ∈ G, ∀ b ∈ (⊥ : Subgroup (MulAut V)),
      a * b = b * a := fun G a _ b hb => by rw [Subgroup.mem_bot] at hb; simp [hb]
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, hinf, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, hG₂⟩
  ·
    obtain ⟨hq, -, hlist⟩ := h1
    have hFJ : quasithinGenFitting J ≤ J := quasithinGenFitting_le J
    have hFn : ∀ x ∈ J, ∀ n ∈ quasithinGenFitting J, x * n * x⁻¹ ∈ quasithinGenFitting J :=
      fun x hx n hn =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_quasithinGenFitting J hx) n).mp hn
    have hall : ∀ K ∈ cComp J, K = quasithinGenFitting J ∨ K = ⊥ := by
      intro K hK
      left
      rcases S153L.comp_dichotomy hK hFJ hFn (Or.inr hq) with h | hc
      · exact h
      · have hKc : K ≤ Subgroup.centralizer (quasithinGenFitting J : Set (MulAut V)) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            (by rw [Subgroup.commutator_comm]; exact hc)
        have hKF : K ≤ quasithinGenFitting J := fun x hx =>
          centralizer_quasithinGenFitting_le J ⟨le_of_mem_cComp hK hx, hKc hx⟩
        rcases S153L.comp_cq hK (by rwa [sup_bot_eq]) hFJ hFn (Or.inr hq) bot_le hbotn
          (Or.inl rfl) with h | h
        · exact h
        · exact absurd h (ne_bot_of_mem_cComp hK)
    exact pair_of_two (inf_bot_eq _) (hcbot _) hall h₁ h₂ hne
  ·
    exfalso
    have hcard : Nat.card ↥J = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    exact false_of_mem_cComp_of_solvable h₁ (S153L.comp_solvable_of_card_six hcard)
  ·
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    have hsup' : G₂ ⊔ G₁ = J := by rw [sup_comm]; exact hsup
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hKP : ∀ K ∈ cComp J, K ≤ G₁ ⊔ G₂ := fun K hK => by
      rw [hsup]; exact le_of_mem_cComp hK
    have go : ∀ N₁ N₂ : Subgroup (MulAut V), S153L.FactorN G₁ N₁ → S153L.FactorN G₂ N₂ →
        K₁ ⊓ K₂ = ⊥ ∧ (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧
          ∀ K ∈ cComp J, K = K₁ ∨ K = K₂ := fun N₁ N₂ f₁ f₂ =>
      pair_of_factors hG₁J hG₂J f₁ f₂ hinf hc (S153L.comp_normal_in_join hsup hc f₁.1 f₁.2.1)
        (S153L.comp_normal_in_join hsup' hc' f₂.1 f₂.2.1) hKP hcases' h₁ h₂ hne
    rcases S153L.factor_of_list hf₁ with ⟨h6₁, nc₁, hN₁⟩ | ⟨N₁, hN₁ne, hN₁⟩ <;>
      rcases S153L.factor_of_list hf₂ with ⟨h6₂, nc₂, hN₂⟩ | ⟨N₂, hN₂ne, hN₂⟩
    · exfalso
      have hs : Group.IsSolvable ↥(G₁ ⊔ G₂) :=
        F1.isSolvable_sup_of_le_normalizer (S153L.comp_solvable_of_card_six h6₁)
          (S153L.comp_solvable_of_card_six h6₂) (le_normalizer_of_commute hc)
      rw [hsup] at hs
      exact false_of_mem_cComp_of_solvable h₁ hs
    · exact go ⊥ N₂ hN₁ hN₂
    · exact go N₁ ⊥ hN₁ hN₂
    · exact go N₁ N₂ hN₁ hN₂
  ·
    have hG₁J : G₁ ≤ J := by rw [hJt]; exact le_sup_left.trans le_sup_left
    have hG₂J : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    obtain ⟨hN₁, -⟩ := S153L.factor_alt6 e₁
    have hN₂ := S153L.factor_card_three hc₂
    have hA : G₁ ⊔ G₂ ≤ J := sup_le hG₁J hG₂J
    have hnorm : J ≤ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
      rw [hJt]
      exact sup_le Subgroup.le_normalizer
        (Subgroup.zpowers_le.2 (InternalSec.mem_normalizer_sup ht₁ ht₂))
    have hAn : ((G₁ ⊔ G₂).subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mpr hnorm
    have hB : Group.IsSolvable ↥(Subgroup.zpowers t) := inferInstance
    have hKP : ∀ K ∈ cComp J, K ≤ G₁ ⊔ G₂ := fun K hK =>
      (le_perfectCore_of_perfect (le_of_mem_cComp hK) (perfect_of_mem_cComp hK)).trans
        (perfectCore_le_of_sup_solvable hA hAn hJt hB)
    have hn₁ : ∀ x ∈ J, ∀ n ∈ G₁, x * n * x⁻¹ ∈ G₁ := fun x hx n hn => by
      rw [hJt] at hx
      exact SBc3.conj_mem_of_mem_sup_zpowers hc ht₁ ht₂ x hx n hn
    exact pair_of_factors hG₁J hG₂J hN₁ hN₂ hinf hc hn₁ hbotn hKP hcases' h₁ h₂ hne
  ·
    have hG₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ J := hsup ▸ le_sup_right
    have hsup' : G₂ ⊔ G₁ = J := by rw [sup_comm]; exact hsup
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hKP : ∀ K ∈ cComp J, K ≤ G₁ ⊔ G₂ := fun K hK => by
      rw [hsup]; exact le_of_mem_cComp hK
    obtain ⟨hN₁, -⟩ := S153L.factor_sl3 (m := 1) (F := ZMod 2) odd_one (by simp) le_rfl e₁
    obtain ⟨N₂, hN₂⟩ : ∃ N₂, S153L.FactorN G₂ N₂ := by
      rcases hG₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hR⟩
      · exact ⟨G₂, (S153L.factor_sl3 (m := 1) (F := ZMod 2) odd_one (by simp) le_rfl e₂).1⟩
      · exact S153L.factor_image_sl2 hF π hR.1
    exact pair_of_factors hG₁J hG₂J hN₁ hN₂ hinf hc (S153L.comp_normal_in_join hsup hc hN₁.1 hN₁.2.1)
      (S153L.comp_normal_in_join hsup' hc' hN₂.1 hN₂.2.1) hKP hcases' h₁ h₂ hne

end Main

end SzN19

end CFSG.Quasithin
