module

public import CFSG.RankThree.PartTwo.Sec3.Item321

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res3

open CFSG CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

structure IsLChain (L : Subgroup G) (f : ℕ → Subgroup G) (n : ℕ) (A B : Subgroup G) : Prop where
  zero : f 0 = A
  last : f n = B
  normalized : ∀ i ≤ n, L ≤ Subgroup.normalizer (f i : Set G)
  lt : ∀ i < n, f i < f (i + 1)
  irreducible : ∀ i < n, ∀ W : Subgroup G, f i ≤ W → W ≤ f (i + 1) →
    L ≤ Subgroup.normalizer (W : Set G) → W = f i ∨ W = f (i + 1)

@[expose] def IsLStep (L A B : Subgroup G) : Prop :=
  L ≤ Subgroup.normalizer (A : Set G) ∧ L ≤ Subgroup.normalizer (B : Set G) ∧ A < B ∧
    ∀ W : Subgroup G, A ≤ W → W ≤ B → L ≤ Subgroup.normalizer (W : Set G) → W = A ∨ W = B

theorem isLChain_refl {L A : Subgroup G} (hA : L ≤ Subgroup.normalizer (A : Set G)) :
    IsLChain L (fun _ => A) 0 A A :=
  ⟨rfl, rfl, fun _ _ => hA, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem isLChain_single {L A B : Subgroup G} (h : IsLStep L A B) :
    IsLChain L (fun i => if i = 0 then A else B) 1 A B := by
  obtain ⟨hA, hB, hlt, hirr⟩ := h
  refine ⟨rfl, rfl, fun i _ => ?_, fun i hi => ?_, fun i hi W h1 h2 hW => ?_⟩
  · by_cases h0 : i = 0
    · simp only [h0, ite_true]
      exact hA
    · simp only [h0, ite_false]
      exact hB
  · have : i = 0 := by omega
    subst this
    simpa using hlt
  · have : i = 0 := by omega
    subst this
    simpa using hirr W h1 h2 hW

theorem IsLChain.append {L A B C : Subgroup G} {f g : ℕ → Subgroup G} {m n : ℕ}
    (hf : IsLChain L f m A B) (hg : IsLChain L g n B C) :
    IsLChain L (fun i => if i ≤ m then f i else g (i - m)) (m + n) A C := by
  obtain ⟨hf0, hfm, hfN, hflt, hfirr⟩ := hf
  obtain ⟨hg0, hgn, hgN, hglt, hgirr⟩ := hg
  have hval : ∀ i, m ≤ i → (if i ≤ m then f i else g (i - m)) = g (i - m) := by
    intro i hi
    by_cases h : i ≤ m
    · have : i = m := le_antisymm h hi
      subst this
      simp [hfm, hg0]
    · simp [h]
  refine ⟨by simp [hf0], ?_, fun i hi => ?_, fun i hi => ?_, fun i hi W h1 h2 hW => ?_⟩
  · rw [hval _ (Nat.le_add_right m n), Nat.add_sub_cancel_left, hgn]
  · by_cases h : i ≤ m
    · simp only [h, ite_true]
      exact hfN i h
    · simp only [h, ite_false]
      exact hgN _ (by omega)
  · by_cases h : i < m
    · have h' : i + 1 ≤ m := h
      simp only [h.le, h', ite_true]
      exact hflt i h
    · rw [hval i (by omega), hval (i + 1) (by omega), show i + 1 - m = (i - m) + 1 by omega]
      exact hglt _ (by omega)
  · by_cases h : i < m
    · have h' : i + 1 ≤ m := h
      simp only [h.le, h', ite_true] at h1 h2 ⊢
      exact hfirr i h W h1 h2 hW
    · have e1 := hval i (by omega)
      have e2 := hval (i + 1) (by omega)
      rw [e1] at h1 ⊢
      rw [e2] at h2 ⊢
      rw [show i + 1 - m = (i - m) + 1 by omega] at h2 ⊢
      exact hgirr _ (by omega) W h1 h2 hW

theorem IsLChain.append' {L A B C : Subgroup G} {f g : ℕ → Subgroup G} {m n : ℕ}
    (hf : IsLChain L f m A B) (hg : IsLChain L g n B C) :
    ∃ h : ℕ → Subgroup G, IsLChain L h (m + n) A C ∧ (∀ i ≤ m, h i = f i) ∧
      ∀ j ≤ n, h (m + j) = g j := by
  refine ⟨_, hf.append hg, fun i hi => by simp [hi], fun j _ => ?_⟩
  by_cases hj : j = 0
  · subst hj
    simp [hf.last, hg.zero]
  · have : ¬ m + j ≤ m := by omega
    simp [this]

theorem exists_lchain [Finite G] {L : Subgroup G} :
    ∀ (n : ℕ) (A B : Subgroup G), Nat.card B - Nat.card A = n → A ≤ B →
      L ≤ Subgroup.normalizer (A : Set G) → L ≤ Subgroup.normalizer (B : Set G) →
      ∃ (f : ℕ → Subgroup G) (k : ℕ), IsLChain L f k A B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B hn hAB hA hB
  by_cases hEq : A = B
  · subst hEq
    exact ⟨_, _, isLChain_refl hA⟩
  have hlt : A < B := lt_of_le_of_ne hAB hEq
  classical
  have hex : ∃ k, ∃ C : Subgroup G, (A < C ∧ C ≤ B ∧ L ≤ Subgroup.normalizer (C : Set G)) ∧
      Nat.card C = k := ⟨_, B, ⟨hlt, le_rfl, hB⟩, rfl⟩
  obtain ⟨C, ⟨hAC, hCB, hC⟩, hmin⟩ := Nat.find_spec hex
  have hle' : ∀ D : Subgroup G, A < D → D ≤ B → L ≤ Subgroup.normalizer (D : Set G) →
      Nat.card C ≤ Nat.card D := fun D h1 h2 h3 =>
    hmin ▸ Nat.find_min' hex ⟨D, ⟨h1, h2, h3⟩, rfl⟩
  have hstep : IsLStep L A C := by
    refine ⟨hA, hC, hAC, fun W h1 h2 hW => ?_⟩
    by_cases hWA : W = A
    · exact Or.inl hWA
    · right
      have hAW : A < W := lt_of_le_of_ne h1 (Ne.symm hWA)
      exact Subgroup.eq_of_le_of_card_ge h2 (hle' W hAW (h2.trans hCB) hW)
  have hdec : Nat.card B - Nat.card C < n := by
    have h1 : Nat.card A < Nat.card C := Subgroup.card_lt_of_lt hAC
    have h2 : Nat.card C ≤ Nat.card B := Subgroup.card_le_of_le hCB
    omega
  obtain ⟨g, m, hg⟩ := ih _ hdec C B rfl hCB hC hB
  exact ⟨_, _, (isLChain_single hstep).append hg⟩

theorem isChiefSeriesUnder_of_lchain {L W : Subgroup G} {f : ℕ → Subgroup G} {r : ℕ}
    (h : IsLChain L f r ⊥ W) :
    Sec3.IsChiefSeriesUnder L W r (fun i => f i) where
  zero := h.zero
  last := h.last
  normalized := fun i => h.normalized i (Nat.lt_succ_iff.mp i.2)
  lt := fun i => h.lt i i.2
  irreducible := fun i W h1 h2 hW => h.irreducible i i.2 W h1 h2 hW

theorem exists_noncentral_step [Finite G] {L A B : Subgroup G} (hAB : A < B)
    (hA : L ≤ Subgroup.normalizer (A : Set G)) (hB : L ≤ Subgroup.normalizer (B : Set G))
    (hper : B ≤ A ⊔ ⁅B, L⁆) :
    ∃ D : Subgroup G, A ≤ D ∧ IsLStep L D B ∧ ¬ ⁅B, L⁆ ≤ D := by
  obtain ⟨D, hAD, hD⟩ := Finite.exists_le_maximal (p := fun D : Subgroup G =>
    A ≤ D ∧ D < B ∧ L ≤ Subgroup.normalizer (D : Set G)) ⟨le_rfl, hAB, hA⟩
  obtain ⟨-, hDB, hDL⟩ := hD.prop
  refine ⟨D, hAD, ⟨hDL, hB, hDB, fun W h1 h2 hW => ?_⟩, fun hle => ?_⟩
  · by_cases hWB : W = B
    · exact Or.inr hWB
    · left
      exact (hD.eq_of_le ⟨hAD.trans h1, lt_of_le_of_ne h2 hWB, hW⟩ h1).symm
  · exact (lt_irrefl B) (lt_of_le_of_lt (hper.trans (sup_le hAD hle)) hDB)

theorem exists_chief_three_noncentral [Finite G] {L W W₁ W₂ W₃ : Subgroup G}
    (h0 : ⊥ < W₁) (h12 : W₁ < W₂) (h23 : W₂ < W₃) (h3 : W₃ ≤ W)
    (hW₁ : L ≤ Subgroup.normalizer (W₁ : Set G)) (hW₂ : L ≤ Subgroup.normalizer (W₂ : Set G))
    (hW₃ : L ≤ Subgroup.normalizer (W₃ : Set G)) (hW : L ≤ Subgroup.normalizer (W : Set G))
    (hp₁ : W₁ ≤ ⁅W₁, L⁆) (hp₂ : W₂ ≤ W₁ ⊔ ⁅W₂, L⁆) (hp₃ : W₃ ≤ W₂ ⊔ ⁅W₃, L⁆) :
    ∃ (r : ℕ) (Vs : Fin (r + 1) → Subgroup G), Sec3.IsChiefSeriesUnder L W r Vs ∧
      ∃ i j k : Fin r, i < j ∧ j < k ∧ ¬ ⁅Vs i.succ, L⁆ ≤ Vs i.castSucc ∧
        ¬ ⁅Vs j.succ, L⁆ ≤ Vs j.castSucc ∧ ¬ ⁅Vs k.succ, L⁆ ≤ Vs k.castSucc := by
  have hbot : L ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun l _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro h
      calc x = l⁻¹ * (l * x * l⁻¹) * l := by group
        _ = 1 := by rw [h]; group
  obtain ⟨D₁, hD₁0, hs₁, hn₁⟩ := exists_noncentral_step h0 hbot hW₁ (by simpa using hp₁)
  obtain ⟨D₂, hD₂0, hs₂, hn₂⟩ := exists_noncentral_step h12 hW₁ hW₂ hp₂
  obtain ⟨D₃, hD₃0, hs₃, hn₃⟩ := exists_noncentral_step h23 hW₂ hW₃ hp₃
  obtain ⟨f₁, a₁, hf₁⟩ := exists_lchain (L := L) _ ⊥ D₁ rfl bot_le hbot hs₁.1
  obtain ⟨f₂, a₂, hf₂⟩ := exists_lchain (L := L) _ W₁ D₂ rfl hD₂0 hW₁ hs₂.1
  obtain ⟨f₃, a₃, hf₃⟩ := exists_lchain (L := L) _ W₂ D₃ rfl hD₃0 hW₂ hs₃.1
  obtain ⟨f₄, a₄, hf₄⟩ := exists_lchain (L := L) _ W₃ W rfl h3 hW₃ hW
  obtain ⟨h₁, c₁, h₁a, h₁b⟩ := hf₁.append' (isLChain_single hs₁)
  obtain ⟨h₂, c₂, h₂a, h₂b⟩ := c₁.append' hf₂
  obtain ⟨h₃, c₃, h₃a, h₃b⟩ := c₂.append' (isLChain_single hs₂)
  obtain ⟨h₄, c₄, h₄a, h₄b⟩ := c₃.append' hf₃
  obtain ⟨h₅, c₅, h₅a, h₅b⟩ := c₄.append' (isLChain_single hs₃)
  obtain ⟨h₆, c₆, h₆a, h₆b⟩ := c₅.append' hf₄
  have hD₁ : h₆ a₁ = D₁ := by
    rw [h₆a _ (by omega), h₅a _ (by omega), h₄a _ (by omega), h₃a _ (by omega), h₂a _ (by omega),
      h₁a _ le_rfl, hf₁.last]
  have hW₁ : h₆ (a₁ + 1) = W₁ := by
    rw [h₆a _ (by omega), h₅a _ (by omega), h₄a _ (by omega), h₃a _ (by omega), h₂a _ (by omega),
      h₁b 1 le_rfl]
    rfl
  have hD₂ : h₆ (a₁ + 1 + a₂) = D₂ := by
    rw [h₆a _ (by omega), h₅a _ (by omega), h₄a _ (by omega), h₃a _ (by omega), h₂b _ le_rfl,
      hf₂.last]
  have hW₂ : h₆ (a₁ + 1 + a₂ + 1) = W₂ := by
    rw [h₆a _ (by omega), h₅a _ (by omega), h₄a _ (by omega), h₃b 1 le_rfl]
    rfl
  have hD₃ : h₆ (a₁ + 1 + a₂ + 1 + a₃) = D₃ := by
    rw [h₆a _ (by omega), h₅a _ (by omega), h₄b _ le_rfl, hf₃.last]
  have hW₃ : h₆ (a₁ + 1 + a₂ + 1 + a₃ + 1) = W₃ := by
    rw [h₆a _ (by omega), h₅b 1 le_rfl]
    rfl
  refine ⟨_, _, isChiefSeriesUnder_of_lchain c₆, ⟨a₁, by omega⟩, ⟨a₁ + 1 + a₂, by omega⟩,
    ⟨a₁ + 1 + a₂ + 1 + a₃, by omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show a₁ < a₁ + 1 + a₂
    omega
  · show a₁ + 1 + a₂ < a₁ + 1 + a₂ + 1 + a₃
    omega
  · show ¬ ⁅h₆ (a₁ + 1), L⁆ ≤ h₆ a₁
    rw [hW₁, hD₁]
    exact hn₁
  · show ¬ ⁅h₆ (a₁ + 1 + a₂ + 1), L⁆ ≤ h₆ (a₁ + 1 + a₂)
    rw [hW₂, hD₂]
    exact hn₂
  · show ¬ ⁅h₆ (a₁ + 1 + a₂ + 1 + a₃ + 1), L⁆ ≤ h₆ (a₁ + 1 + a₂ + 1 + a₃)
    rw [hW₃, hD₃]
    exact hn₃

end CFSG.RankThree.PartTwo.Sec20.Res3
