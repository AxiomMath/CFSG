module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5CfgComp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.ComponentClassification (Layer.subgroup)

variable {K : Type} [Group K] [Finite K]

theorem le_centralizer_of_isComponentOf {J J' : Subgroup K} (hJ : IsComponentOf J ⊤)
    (hJ' : IsComponentOf J' ⊤) (hne : J ≠ J') : J' ≤ centralizer (J : Set K) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne J' J hJ' hJ hne.symm)

theorem map_conj_eq_or_swap {J₁ J₂ : Subgroup K} (hJ₁ : IsComponentOf J₁ ⊤)
    (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) (k : K) :
    (J₁.map (MulAut.conj k).toMonoidHom = J₁ ∧ J₂.map (MulAut.conj k).toMonoidHom = J₂) ∨
      (J₁.map (MulAut.conj k).toMonoidHom = J₂ ∧ J₂.map (MulAut.conj k).toMonoidHom = J₁) := by
  have h₁ := isComponentOf_map_conj hJ₁ k
  have h₂ := isComponentOf_map_conj hJ₂ k
  have hdistinct : J₁.map (MulAut.conj k).toMonoidHom ≠ J₂.map (MulAut.conj k).toMonoidHom :=
    fun h => hne (Subgroup.map_injective (f := (MulAut.conj k).toMonoidHom)
      (MulAut.conj k).injective h)
  rcases hJu _ h₁ with h₁₁ | h₁₂ <;> rcases hJu _ h₂ with h₂₁ | h₂₂
  · exact absurd (h₁₁.trans h₂₁.symm) hdistinct
  · exact Or.inl ⟨h₁₁, h₂₂⟩
  · exact Or.inr ⟨h₁₂, h₂₁⟩
  · exact absurd (h₁₂.trans h₂₂.symm) hdistinct

theorem mem_normalizer_of_odd {J₁ J₂ : Subgroup K} (hJ₁ : IsComponentOf J₁ ⊤)
    (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) {k : K}
    (hk : Odd (orderOf k)) : k ∈ normalizer (J₁ : Set K) ⊓ normalizer (J₂ : Set K) := by
  obtain ⟨m, hm⟩ := hk
  rcases map_conj_eq_or_swap hJ₁ hJ₂ hne hJu k with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := J₁) (g := k)).mpr (by simpa using h₁)
    · exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := J₂) (g := k)).mpr (by simpa using h₂)
  · exfalso
    have hk2 : k ^ 2 ∈ normalizer (J₁ : Set K) := by
      have hmap : J₁.map (MulAut.conj (k ^ 2)).toMonoidHom = J₁ := by
        have hcomp : (MulAut.conj (k ^ 2)).toMonoidHom =
            ((MulAut.conj k).toMonoidHom).comp ((MulAut.conj k).toMonoidHom) := by
          rw [pow_two, map_mul]
          ext x
          rfl
        rw [hcomp]
        rw [← Subgroup.map_map (g := (MulAut.conj k).toMonoidHom)
          (f := (MulAut.conj k).toMonoidHom), h₁, h₂]
      exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := J₁) (g := k ^ 2)).mpr
        (by simpa using hmap)
    have hexp : 2 * (m + 1) = orderOf k + 1 := by omega
    have hk_eq : k = (k ^ 2) ^ (m + 1) := by
      calc k = k ^ (orderOf k + 1) := by simp [pow_succ, pow_orderOf_eq_one]
        _ = k ^ (2 * (m + 1)) := by rw [hexp]
        _ = (k ^ 2) ^ (m + 1) := pow_mul k 2 (m + 1)
    have hk_mem : k ∈ normalizer (J₁ : Set K) := by
      have hpow : (k ^ 2) ^ (m + 1) ∈ normalizer (J₁ : Set K) :=
        Subgroup.pow_mem _ hk2 (m + 1)
      simpa [← hk_eq] using hpow
    have hmap : J₁.map (MulAut.conj k) = J₁ :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := J₁) (g := k)).mp hk_mem
    exact hne (hmap.symm.trans (by simpa using h₁))

namespace Cfg145

variable {M X₁ X₂ P : Subgroup K}

theorem card_inf_eq_three (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K} (hJ₁ : IsComponentOf J₁ ⊤)
    (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂) : Nat.card ↥((X₁ ⊔ X₂) ⊓ J₁) = 3 := by
  have hne_bot : (X₁ ⊔ X₂) ⊓ J₁ ≠ ⊥ := c.inf_ne_bot_of_isComponentOf hJ₁
  have hdvd : Nat.card ↥((X₁ ⊔ X₂) ⊓ J₁) ∣ 3 ^ 2 := by
    have h : Nat.card ↥((X₁ ⊔ X₂) ⊓ J₁) ∣ 9 := by
      rw [← c.card_sup]
      exact Subgroup.card_dvd_of_le inf_le_left
    rwa [show (9 : ℕ) = 3 ^ 2 by norm_num] at h
  obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases k
  · simp only [pow_zero] at hk_eq
    exact absurd (Subgroup.card_eq_one.mp hk_eq) hne_bot
  · simpa using hk_eq
  · exfalso
    have hZeq : (X₁ ⊔ X₂) ⊓ J₁ = X₁ ⊔ X₂ := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hk_eq, c.card_sup]
      norm_num
    have hle : X₁ ⊔ X₂ ≤ J₁ := hZeq ▸ inf_le_right
    have hZ₂bot : (X₁ ⊔ X₂) ⊓ J₂ = ⊥ := by
      apply le_antisymm _ bot_le
      calc (X₁ ⊔ X₂) ⊓ J₂ ≤ J₁ ⊓ J₂ := inf_le_inf hle le_rfl
        _ = ⊥ := c.inf_eq_bot_of_isComponentOf hJ₁ hJ₂ hne
    exact c.inf_ne_bot_of_isComponentOf hJ₂ hZ₂bot

theorem inf_sup_inf_eq (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K} (hJ₁ : IsComponentOf J₁ ⊤)
    (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂) :
    (X₁ ⊔ X₂) ⊓ J₁ ⊔ (X₁ ⊔ X₂) ⊓ J₂ = X₁ ⊔ X₂ := by
  have hcard₁ : Nat.card ↥((X₁ ⊔ X₂) ⊓ J₁) = 3 := card_inf_eq_three c hJ₁ hJ₂ hne
  have hcard₂ : Nat.card ↥((X₁ ⊔ X₂) ⊓ J₂) = 3 := card_inf_eq_three c hJ₂ hJ₁ hne.symm
  have hinf : (X₁ ⊔ X₂) ⊓ J₁ ⊓ ((X₁ ⊔ X₂) ⊓ J₂) = ⊥ := by
    apply le_antisymm _ bot_le
    calc (X₁ ⊔ X₂) ⊓ J₁ ⊓ ((X₁ ⊔ X₂) ⊓ J₂) ≤ J₁ ⊓ J₂ :=
          inf_le_inf inf_le_right inf_le_right
      _ = ⊥ := c.inf_eq_bot_of_isComponentOf hJ₁ hJ₂ hne
  have hc : ∀ x ∈ (X₁ ⊔ X₂) ⊓ J₁, ∀ y ∈ (X₁ ⊔ X₂) ⊓ J₂, x * y = y * x := by
    intro x hx y hy
    have hxX : x ∈ X₁ ⊔ X₂ := (Subgroup.mem_inf.mp hx).1
    have hyX : y ∈ X₁ ⊔ X₂ := (Subgroup.mem_inf.mp hy).1
    exact congrArg Subtype.val ((c.isElemAbelian).1.is_comm.comm
      (⟨x, hxX⟩ : ↥(X₁ ⊔ X₂)) ⟨y, hyX⟩)
  have hcardsup := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    ((X₁ ⊔ X₂) ⊓ J₁) ((X₁ ⊔ X₂) ⊓ J₂) hc).1
  have hcard : Nat.card ↥((X₁ ⊔ X₂) ⊓ J₁ ⊔ (X₁ ⊔ X₂) ⊓ J₂) = 9 := by
    rw [hcard₁, hcard₂, hinf, Subgroup.card_bot, Nat.mul_one] at hcardsup
    norm_num at hcardsup
    exact hcardsup
  apply Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
  rw [c.card_sup, hcard]

theorem centralizer_sup_eq_bot (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K}
    (hJ₁ : IsComponentOf J₁ ⊤) (hJ₂ : IsComponentOf J₂ ⊤)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) :
    centralizer ((J₁ ⊔ J₂ : Subgroup K) : Set K) = ⊥ := by
  rw [← layer_eq_sup_of_forall hJ₁ hJ₂ hJu]
  exact c.centralizer_layer_eq_bot

theorem false_of_sup_le (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K} (hJ₁ : IsComponentOf J₁ ⊤)
    (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂) (h₁ : J₁ ≤ M)
    (h₂ : J₂ ≤ M) : False := by
  have hE : (J₁ ⊔ J₂ : Subgroup K).Normal := by
    rw [← layer_eq_sup_of_forall hJ₁ hJ₂ hJu]
    exact CFSG.ComponentClassification.Layer.normal K
  have hXE : X₁ ⊔ X₂ ≤ J₁ ⊔ J₂ := by
    rw [← inf_sup_inf_eq c hJ₁ hJ₂ hne]
    exact sup_le_sup inf_le_right inf_le_right
  exact c.false_of_le hE hXE (sup_le h₁ h₂)

theorem false_of_inf_eq (c : Cfg145 M X₁ X₂ P) {J₁ J₂ : Subgroup K} (hJ₁ : IsComponentOf J₁ ⊤)
    (hJ₂ : IsComponentOf J₂ ⊤) (hne : J₁ ≠ J₂)
    (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J₁ ∨ J' = J₂)
    (hZ₁ : (X₁ ⊔ X₂) ⊓ J₁ = X₁ ∨ (X₁ ⊔ X₂) ⊓ J₁ = X₂)
    (hZ₂ : (X₁ ⊔ X₂) ⊓ J₂ = X₁ ∨ (X₁ ⊔ X₂) ⊓ J₂ = X₂) : False := by
  have hZne : (X₁ ⊔ X₂) ⊓ J₁ ≠ (X₁ ⊔ X₂) ⊓ J₂ := by
    intro heq
    have hbot : (X₁ ⊔ X₂) ⊓ J₁ = ⊥ := by
      apply le_antisymm _ bot_le
      calc (X₁ ⊔ X₂) ⊓ J₁ = (X₁ ⊔ X₂) ⊓ J₁ ⊓ ((X₁ ⊔ X₂) ⊓ J₂) := by rw [← heq, inf_idem]
        _ ≤ J₁ ⊓ J₂ := inf_le_inf inf_le_right inf_le_right
        _ = ⊥ := c.inf_eq_bot_of_isComponentOf hJ₁ hJ₂ hne
    exact c.inf_ne_bot_of_isComponentOf hJ₁ hbot
  rcases hZ₁ with hZ₁ | hZ₁ <;> rcases hZ₂ with hZ₂ | hZ₂
  · exact absurd (hZ₁.trans hZ₂.symm) hZne
  · have hX₁J₁ : X₁ ≤ J₁ := hZ₁ ▸ inf_le_right
    have hX₂J₂ : X₂ ≤ J₂ := hZ₂ ▸ inf_le_right
    have hJ₂M : J₂ ≤ M :=
      (le_centralizer_of_isComponentOf hJ₁ hJ₂ hne).trans
        ((Subgroup.centralizer_le (fun x hx => hX₁J₁ hx)).trans
          ((Subgroup.centralizer_le_normalizer (X₁ : Set K)).trans c.normalizer_left_le))
    have hJ₁M : J₁ ≤ M :=
      (le_centralizer_of_isComponentOf hJ₂ hJ₁ hne.symm).trans
        ((Subgroup.centralizer_le (fun x hx => hX₂J₂ hx)).trans
          ((Subgroup.centralizer_le_normalizer (X₂ : Set K)).trans c.normalizer_right_le))
    exact false_of_sup_le c hJ₁ hJ₂ hne hJu hJ₁M hJ₂M
  · have hX₂J₁ : X₂ ≤ J₁ := hZ₁ ▸ inf_le_right
    have hX₁J₂ : X₁ ≤ J₂ := hZ₂ ▸ inf_le_right
    have hJ₂M : J₂ ≤ M :=
      (le_centralizer_of_isComponentOf hJ₁ hJ₂ hne).trans
        ((Subgroup.centralizer_le (fun x hx => hX₂J₁ hx)).trans
          ((Subgroup.centralizer_le_normalizer (X₂ : Set K)).trans c.normalizer_right_le))
    have hJ₁M : J₁ ≤ M :=
      (le_centralizer_of_isComponentOf hJ₂ hJ₁ hne.symm).trans
        ((Subgroup.centralizer_le (fun x hx => hX₁J₂ hx)).trans
          ((Subgroup.centralizer_le_normalizer (X₁ : Set K)).trans c.normalizer_left_le))
    exact false_of_sup_le c hJ₁ hJ₂ hne hJu hJ₁M hJ₂M
  · exact absurd (hZ₁.trans hZ₂.symm) hZne

end Cfg145

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
