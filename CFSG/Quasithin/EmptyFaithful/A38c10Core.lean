module

public import CFSG.Quasithin.EmptyFaithful.A38c7Core

public section

namespace CFSG.Quasithin.A38c10

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.FLc CFSG.Quasithin.A38c7

variable {F : Type} [Group F] [Finite F]

omit [Finite F] in
theorem cuts_eq_nodes_erase {Lm B : Subgroup F} (D : BorelIso 4 Lm B) {Q : Subgroup F} {a : ℕ}
    (haQ : a ∉ D.cutsOf Q) (hu : ∀ y, IsNode 4 y → y ∉ D.cutsOf Q → y = a) :
    ∀ y, y ∈ D.cutsOf Q ↔ IsNode 4 y ∧ y ≠ a := by
  intro y
  constructor
  · intro hy
    exact ⟨D.isNode_of_mem_cutsOf hy, fun h => haQ (h ▸ hy)⟩
  · rintro ⟨hyn, hya⟩
    by_contra h
    exact hya (hu y hyn h)

theorem core4 {Lm B W Y₁ Y₂ : Subgroup F} (D : BorelIso 4 Lm B) (hB : IsSylowTwoOf B Lm) (hBW : B ≤ W)
    (hWL : ∀ w ∈ W, ∀ l ∈ Lm, w * l * w⁻¹ ∈ Lm) (hWB : ∀ w ∈ W, ∀ b ∈ B, w * b * w⁻¹ ∈ B)
    (hY₁ : Y₁ ≤ Lm) (hY₁W : ∀ w ∈ W, ∀ y ∈ Y₁, w * y * w⁻¹ ∈ Y₁) (hY₁c : ∃ a, Nat.card Y₁ = 2 ^ a * 3)
    (hY₂ : Y₂ ≤ Lm) (hY₂W : ∀ w ∈ W, ∀ y ∈ Y₂, w * y * w⁻¹ ∈ Y₂) (hY₂c : ∃ a, Nat.card Y₂ = 2 ^ a * 3)
    (h9 : 9 ∣ Nat.card ↥(Y₁ ⊔ Y₂)) (h1344 : ∀ k, (k = 1 ∨ k = 3) → Nat.card ↥(QI 4 {k}) = 1344) :
    ∃ P₁ P₂ P₃ : Subgroup F,
      (B ≤ P₁ ∧ P₁ ≤ Lm ∧ D.cutsOf P₁ = {1}) ∧ (B ≤ P₂ ∧ P₂ ≤ Lm ∧ D.cutsOf P₂ = {2}) ∧
      (B ≤ P₃ ∧ P₃ ≤ Lm ∧ D.cutsOf P₃ = {3}) ∧
      (∀ P : Subgroup F, B ≤ P → P ≤ Lm → ∀ w ∈ W, ∀ p ∈ P, w * p * w⁻¹ ∈ P) ∧
      (∀ X : Subgroup F, B ≤ X → X ≤ Lm → X ≠ Lm → X ≤ P₁ ∨ X ≤ P₂ ∨ X ≤ P₃) ∧
      Y₁ ⊔ Y₂ ≤ P₂ ∧ P₂ = (Y₁ ⊔ B) ⊔ (Y₂ ⊔ B) ∧
      ((Y₁ ≤ P₁ ∧ ¬ Y₁ ≤ P₃ ∧ Y₂ ≤ P₃ ∧ ¬ Y₂ ≤ P₁) ∨ (Y₁ ≤ P₃ ∧ ¬ Y₁ ≤ P₁ ∧ Y₂ ≤ P₁ ∧ ¬ Y₂ ≤ P₃)) := by
  have hBL : B ≤ Lm := hB.1
  have hWN : W ≤ Subgroup.normalizer (Lm : Set F) := le_normalizer_of_conj_mem hWL
  have key : ∀ Y : Subgroup F, Y ≤ Lm → (∀ w ∈ W, ∀ y ∈ Y, w * y * w⁻¹ ∈ Y) →
      (∃ a, Nat.card Y = 2 ^ a * 3) →
      ∃ Q : Subgroup F, B ≤ Q ∧ Q ≤ Lm ∧ Y ≤ Q ∧ (∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) ∧
        Nat.card Q = 3 * Nat.card B ∧ Q = Y ⊔ B ∧
        ∃ x, IsNode 4 x ∧ x ∉ D.cutsOf Q ∧ ∀ y, IsNode 4 y → y ∉ D.cutsOf Q → y = x := by
    intro Y hYL hYW hYc
    have hcard := card_sup_eq_three_mul hB hYL (fun b hb y hy => hYW b (hBW hb) y hy) hYc
    refine ⟨Y ⊔ B, le_sup_right, sup_le hYL hBL, le_sup_left, ?_, hcard, rfl, ?_⟩
    · intro w hw q hq
      have h1 : conjSub w (Y ⊔ B) = Y ⊔ B := by
        have e1 : conjSub w Y = Y := conjSub_eq_of_conj_mem hYW hw
        have e2 : conjSub w B = B := conjSub_eq_of_conj_mem hWB hw
        change Subgroup.map _ (Y ⊔ B) = _
        rw [Subgroup.map_sup]
        exact congrArg₂ (· ⊔ ·) e1 e2
      have h2 : w * q * w⁻¹ ∈ conjSub w (Y ⊔ B) := by
        rw [mem_conjSub]
        have e : w⁻¹ * (w * q * w⁻¹) * w = q := by group
        rw [e]
        exact hq
      rwa [h1] at h2
    · have hmax := isMaxSubgroupIn_of_card (le_sup_right : B ≤ Y ⊔ B) hcard
      exact D.exists_unique_node_of_isMax hBL (sup_le hYL hBL) hmax
  obtain ⟨Q₁, hBQ₁, hQ₁L, hY₁Q₁, hQ₁W, hQ₁c, hQ₁e, a₁, ha₁, ha₁Q, ha₁u⟩ := key Y₁ hY₁ hY₁W hY₁c
  obtain ⟨Q₂, hBQ₂, hQ₂L, hY₂Q₂, hQ₂W, hQ₂c, hQ₂e, a₂, ha₂, ha₂Q, ha₂u⟩ := key Y₂ hY₂ hY₂W hY₂c
  have hc₁ := cuts_eq_nodes_erase D ha₁Q ha₁u
  have hc₂ := cuts_eq_nodes_erase D ha₂Q ha₂u
  have hnine : ∀ k, (k = 1 ∨ k = 3) → ∀ P : Subgroup F, B ≤ P → P ≤ Lm → D.cutsOf P = {k} →
      ¬ 9 ∣ Nat.card P := by
    intro k hk P hBP hPL hPk h9P
    have hUt : Ut 4 ≤ D.model P := (D.Ut_le_model_iff hBL).2 hBP
    have hmodel : D.model P = QI 4 {k} := by
      have h1 : D.model P = QI 4 (cuts (D.model P)) := eq_QI_cuts hUt
      rw [h1]
      show QI 4 (D.cutsOf P) = _
      rw [hPk]
    have hcard : Nat.card P = 1344 := by
      rw [← D.card_model hPL, hmodel]
      exact h1344 k hk
    rw [hcard] at h9P
    omega
  obtain ⟨P₁, hBP₁, hP₁L, hP₁c⟩ := D.exists_cutsOf_eq hBL (I := {1}) (by rintro i rfl; exact ⟨le_rfl, by norm_num⟩)
  obtain ⟨P₂, hBP₂, hP₂L, hP₂c⟩ := D.exists_cutsOf_eq hBL (I := {2}) (by rintro i rfl; exact ⟨by norm_num, by norm_num⟩)
  obtain ⟨P₃, hBP₃, hP₃L, hP₃c⟩ := D.exists_cutsOf_eq hBL (I := {3}) (by rintro i rfl; exact ⟨by norm_num, by norm_num⟩)
  have hY₁₂ : Y₁ ⊔ Y₂ ≤ Lm := sup_le hY₁ hY₂
  have hle : ∀ (Q P : Subgroup F) (k : ℕ), B ≤ Q → Q ≤ Lm → B ≤ P → D.cutsOf P = {k} →
      (Q ≤ P ↔ k ∈ D.cutsOf Q) := by
    intro Q P k hBQ hQL hBP hPk
    rw [D.cutsOf_le_iff hBL hBQ hQL hBP, hPk]
    exact Set.singleton_subset_iff
  have hne : a₁ ≠ a₂ := by
    intro h
    subst h
    have hQeq : Q₁ = Q₂ := D.eq_of_cutsOf_eq hBL hBQ₁ hQ₁L hBQ₂ hQ₂L (by
      ext y
      rw [hc₁ y, hc₂ y])
    have hsup : Y₁ ⊔ Y₂ ≤ Q₁ := sup_le hY₁Q₁ (hQeq ▸ hY₂Q₂)
    have hd : 9 ∣ Nat.card ↥Q₁ := h9.trans (Subgroup.card_dvd_of_le hsup)
    rw [hQ₁c] at hd
    have hBc : ∃ k, Nat.card B = 2 ^ k := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hB.2.1
      exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hBc
    rw [hk] at hd
    have h3 : 3 ∣ 2 ^ k := by omega
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hq : ∀ k, (k = 1 ∨ k = 3) → a₁ ≠ k → a₂ ≠ k → False := by
    intro k hk hk₁ hk₂
    obtain ⟨P, hBP, hPL, hPk⟩ := D.exists_cutsOf_eq hBL (I := {k}) (by
      rintro i rfl
      rcases hk with rfl | rfl
      · exact ⟨le_rfl, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩)
    have hk' : IsNode 4 k := by rcases hk with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
    have hQ₁P : Q₁ ≤ P := (hle Q₁ P k hBQ₁ hQ₁L hBP hPk).2 ((hc₁ k).2 ⟨hk', fun h => hk₁ h.symm⟩)
    have hQ₂P : Q₂ ≤ P := (hle Q₂ P k hBQ₂ hQ₂L hBP hPk).2 ((hc₂ k).2 ⟨hk', fun h => hk₂ h.symm⟩)
    have hsup : Y₁ ⊔ Y₂ ≤ P := sup_le (hY₁Q₁.trans hQ₁P) (hY₂Q₂.trans hQ₂P)
    exact hnine k hk P hBP hPL hPk (h9.trans (Subgroup.card_dvd_of_le hsup))
  have hnodes : (a₁ = 1 ∧ a₂ = 3) ∨ (a₁ = 3 ∧ a₂ = 1) := by
    obtain ⟨h₁a, h₁b⟩ := ha₁
    obtain ⟨h₂a, h₂b⟩ := ha₂
    have h3 : ¬ (a₁ ≠ 3 ∧ a₂ ≠ 3) := fun h => hq 3 (Or.inr rfl) h.1 h.2
    have h1 : ¬ (a₁ ≠ 1 ∧ a₂ ≠ 1) := fun h => hq 1 (Or.inl rfl) h.1 h.2
    omega
  have ha₁n : a₁ = 1 ∨ a₁ = 3 := by omega
  have hinv : ∀ P : Subgroup F, B ≤ P → P ≤ Lm → ∀ w ∈ W, conjSub w P = P := by
    intro P hBP hPL w hw
    have hwN : w ∈ Subgroup.normalizer (Lm : Set F) := hWN hw
    have hBc : conjSub w B = B := conjSub_eq_of_conj_mem hWB hw
    have hφ : (Ut 4).map (D.autOf w hwN).toMonoidHom = Ut 4 := by
      have := D.model_conjSub w hwN B
      rwa [hBc, D.model_B] at this
    rcases aut_dichotomy (by norm_num) (D.autOf w hwN) hφ with ⟨b, hbU, hb⟩ | hswap
    · have hUP : Ut 4 ≤ D.model P := (D.Ut_le_model_iff hBL).2 hBP
      have hmap : (D.model P).map (D.autOf w hwN).toMonoidHom = D.model P := by
        ext g
        constructor
        · rintro ⟨h, hh, rfl⟩
          have : (D.autOf w hwN) h = b * h * b⁻¹ := hb h
          show (D.autOf w hwN) h ∈ D.model P
          rw [this]
          exact (D.model P).mul_mem ((D.model P).mul_mem (hUP hbU) hh) ((D.model P).inv_mem (hUP hbU))
        · intro hg
          refine ⟨b⁻¹ * g * b, (D.model P).mul_mem ((D.model P).mul_mem ((D.model P).inv_mem (hUP hbU)) hg) (hUP hbU), ?_⟩
          show (D.autOf w hwN) (b⁻¹ * g * b) = g
          rw [hb]
          group
      have hmodel : D.model (conjSub w P) = D.model P := by
        rw [← D.model_conjSub w hwN P, hmap]
      have hcL : conjSub w P ≤ Lm := by
        intro x hx
        have h1 : w⁻¹ * x * w ∈ P := mem_conjSub.1 hx
        have h2 := hWL w hw _ (hPL h1)
        simpa [mul_assoc] using h2
      exact le_antisymm ((D.model_le_iff hcL).1 hmodel.le) ((D.model_le_iff hPL).1 hmodel.ge)
    · exfalso
      have h1 := D.cutsOf_conjSub hBL w hwN hswap hBQ₁
      rw [conjSub_eq_of_conj_mem hQ₁W hw] at h1
      have h2 := two_mul_eq_of_flip (fun i hi => D.isNode_of_mem_cutsOf hi) h1 ha₁ ha₁Q ha₁u
      omega
  have hinvar : ∀ P : Subgroup F, B ≤ P → P ≤ Lm → ∀ w ∈ W, ∀ p ∈ P, w * p * w⁻¹ ∈ P := by
    intro P hBP hPL w hw p hp
    have h1 : w * p * w⁻¹ ∈ conjSub w P := by
      rw [mem_conjSub]
      have e : w⁻¹ * (w * p * w⁻¹) * w = p := by group
      rw [e]
      exact hp
    rwa [hinv P hBP hPL w hw] at h1
  have hYpos : ∀ (Y Q : Subgroup F) (a : ℕ), Q = Y ⊔ B → (∀ y, y ∈ D.cutsOf Q ↔ IsNode 4 y ∧ y ≠ a) →
      B ≤ Q → Q ≤ Lm → ∀ (P : Subgroup F) (k : ℕ), IsNode 4 k → B ≤ P → D.cutsOf P = {k} →
        (Y ≤ P ↔ k ≠ a) := by
    intro Y Q a hQ hc hBQ hQL P k hk hBP hPk
    have hYQ : Y ≤ P ↔ Q ≤ P := by
      constructor
      · intro h
        rw [hQ]
        exact sup_le h hBP
      · intro h
        rw [hQ] at h
        exact le_sup_left.trans h
    rw [hYQ, hle Q P k hBQ hQL hBP hPk, hc k]
    exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
  have hn1 : IsNode 4 1 := ⟨le_rfl, by norm_num⟩
  have hn2 : IsNode 4 2 := ⟨by norm_num, by norm_num⟩
  have hn3 : IsNode 4 3 := ⟨by norm_num, by norm_num⟩
  have hQ₁₂ : Q₁ ⊔ Q₂ ≤ Lm := sup_le hQ₁L hQ₂L
  have hBQ₁₂ : B ≤ Q₁ ⊔ Q₂ := hBQ₁.trans le_sup_left
  have hP₂eq : P₂ = Q₁ ⊔ Q₂ := by
    have h1 : Q₁ ≤ P₂ := (hle Q₁ P₂ 2 hBQ₁ hQ₁L hBP₂ hP₂c).2 ((hc₁ 2).2 ⟨hn2, by omega⟩)
    have h2 : Q₂ ≤ P₂ := (hle Q₂ P₂ 2 hBQ₂ hQ₂L hBP₂ hP₂c).2 ((hc₂ 2).2 ⟨hn2, by omega⟩)
    refine le_antisymm ?_ (sup_le h1 h2)
    rw [D.cutsOf_le_iff hBL hBP₂ hP₂L hBQ₁₂, hP₂c]
    intro k hk
    have c1 : k ∈ D.cutsOf Q₁ :=
      (D.cutsOf_le_iff hBL hBQ₁ hQ₁L hBQ₁₂).1 le_sup_left hk
    have c2 : k ∈ D.cutsOf Q₂ :=
      (D.cutsOf_le_iff hBL hBQ₂ hQ₂L hBQ₁₂).1 le_sup_right hk
    have d1 := (hc₁ k).1 c1
    have d2 := (hc₂ k).1 c2
    obtain ⟨⟨hk1, hk2⟩, hka₁⟩ := d1
    obtain ⟨-, hka₂⟩ := d2
    show k = 2
    omega
  refine ⟨P₁, P₂, P₃, ⟨hBP₁, hP₁L, hP₁c⟩, ⟨hBP₂, hP₂L, hP₂c⟩, ⟨hBP₃, hP₃L, hP₃c⟩, hinvar, ?_, ?_, ?_, ?_⟩
  ·
    intro X hBX hXL hXne
    have hne : (D.cutsOf X).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      apply hXne
      exact D.eq_of_cutsOf_eq hBL hBX hXL hBL le_rfl (by rw [hempty, D.cutsOf_L])
    obtain ⟨k, hk⟩ := hne
    obtain ⟨hk1, hk2⟩ := D.isNode_of_mem_cutsOf hk
    have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl ((hle X P₁ 1 hBX hXL hBP₁ hP₁c).2 hk)
    · exact Or.inr (Or.inl ((hle X P₂ 2 hBX hXL hBP₂ hP₂c).2 hk))
    · exact Or.inr (Or.inr ((hle X P₃ 3 hBX hXL hBP₃ hP₃c).2 hk))
  · rw [hP₂eq]
    exact sup_le_sup hY₁Q₁ hY₂Q₂
  · rw [hP₂eq, hQ₁e, hQ₂e]
  · rcases hnodes with ⟨h1, h3⟩ | ⟨h3, h1⟩
    · right
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (hYpos Y₁ Q₁ a₁ hQ₁e hc₁ hBQ₁ hQ₁L P₃ 3 hn3 hBP₃ hP₃c).2 (by omega)
      · exact fun h => ((hYpos Y₁ Q₁ a₁ hQ₁e hc₁ hBQ₁ hQ₁L P₁ 1 hn1 hBP₁ hP₁c).1 h) (by omega)
      · exact (hYpos Y₂ Q₂ a₂ hQ₂e hc₂ hBQ₂ hQ₂L P₁ 1 hn1 hBP₁ hP₁c).2 (by omega)
      · exact fun h => ((hYpos Y₂ Q₂ a₂ hQ₂e hc₂ hBQ₂ hQ₂L P₃ 3 hn3 hBP₃ hP₃c).1 h) (by omega)
    · left
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (hYpos Y₁ Q₁ a₁ hQ₁e hc₁ hBQ₁ hQ₁L P₁ 1 hn1 hBP₁ hP₁c).2 (by omega)
      · exact fun h => ((hYpos Y₁ Q₁ a₁ hQ₁e hc₁ hBQ₁ hQ₁L P₃ 3 hn3 hBP₃ hP₃c).1 h) (by omega)
      · exact (hYpos Y₂ Q₂ a₂ hQ₂e hc₂ hBQ₂ hQ₂L P₃ 3 hn3 hBP₃ hP₃c).2 (by omega)
      · exact fun h => ((hYpos Y₂ Q₂ a₂ hQ₂e hc₂ hBQ₂ hQ₂L P₁ 1 hn1 hBP₁ hP₁c).1 h) (by omega)

end CFSG.Quasithin.A38c10
