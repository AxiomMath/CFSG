module

public import CFSG.Quasithin.Background.FLcLn

public section

namespace CFSG.Quasithin.A38c7

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.FLc

variable {F : Type} [Group F] [Finite F]

theorem card_sup_eq_three_mul {Lm B Y : Subgroup F} (hB : IsSylowTwoOf B Lm) (hYL : Y ≤ Lm)
    (hBY : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hY : ∃ a, Nat.card Y = 2 ^ a * 3) :
    Nat.card ↥(Y ⊔ B) = 3 * Nat.card ↥B := by
  obtain ⟨a, ha⟩ := hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBn : B ≤ Subgroup.normalizer (Y : Set F) := le_normalizer_of_conj_mem' hBY
  have h1 : Y.relIndex (B ⊔ Y) = Y.relIndex B := A4.relIndex_sup_eq_of_le_normalizer' hBn
  have h2 : Y.relIndex (B ⊔ Y) * Nat.card ↥(Y ⊓ (B ⊔ Y)) = Nat.card ↥(B ⊔ Y) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr (le_sup_right : Y ≤ B ⊔ Y), h1, ha] at h2
  obtain ⟨j, hj⟩ := hB.2.1.index (Y.subgroupOf B)
  have h3 : Y.relIndex B = 2 ^ j := hj
  rw [h3] at h2
  have hQL : B ⊔ Y ≤ Lm := sup_le hB.1 hYL
  have hBQ : IsSylowTwoOf B (B ⊔ Y) := A4.isSylowTwoOf_mono hB le_sup_left hQL
  have h4 : Nat.card ↥((B.subgroupOf (B ⊔ Y))) * (B.subgroupOf (B ⊔ Y)).index = Nat.card ↥(B ⊔ Y) :=
    Subgroup.card_mul_index _
  have h5 : Nat.card ↥(B.subgroupOf (B ⊔ Y)) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : B ≤ B ⊔ Y)).toEquiv
  rw [h5] at h4
  have hodd : ¬ 2 ∣ (B.subgroupOf (B ⊔ Y)).index := hBQ.2.2
  have hdvd : (B.subgroupOf (B ⊔ Y)).index ∣ 2 ^ (j + a) * 3 := by
    refine ⟨Nat.card ↥B, ?_⟩
    rw [pow_add, mul_assoc, h2, ← h4]
    ring
  have hcop : Nat.Coprime ((B.subgroupOf (B ⊔ Y)).index) (2 ^ (j + a)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  have h3dvd : (B.subgroupOf (B ⊔ Y)).index ∣ 3 := hcop.dvd_of_dvd_mul_left hdvd
  rcases (Nat.dvd_prime Nat.prime_three).1 h3dvd with h | h
  · exfalso
    rw [h, mul_one] at h4
    have hYd : Nat.card Y ∣ Nat.card ↥B := by
      rw [h4]
      exact Subgroup.card_dvd_of_le le_sup_right
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hB.2.1
    rw [hk, ha] at hYd
    have h3d : 3 ∣ 2 ^ k := (Dvd.intro_left _ rfl).trans hYd
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d)
    omega
  · rw [h] at h4
    rw [sup_comm, ← h4]
    ring

theorem exists_two_nodes_five (a₁ a₂ : ℕ) (h₁ : IsNode 5 a₁) (h₂ : IsNode 5 a₂) :
    ∃ k₁ k₂ : ℕ, IsNode 5 k₁ ∧ IsNode 5 k₂ ∧ k₁ ≠ k₂ ∧ k₁ ≠ a₁ ∧ k₁ ≠ a₂ ∧ k₂ ≠ a₁ ∧ k₂ ≠ a₂ := by
  obtain ⟨h₁a, h₁b⟩ := h₁
  obtain ⟨h₂a, h₂b⟩ := h₂
  interval_cases a₁ <;> interval_cases a₂ <;>
    first
    | exact ⟨1, 2, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨1, 3, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨1, 4, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨2, 3, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨2, 4, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega, by omega, by omega⟩
    | exact ⟨3, 4, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega, by omega, by omega⟩

theorem core5 {Lm B W Y₁ Y₂ : Subgroup F} (e : ↥Lm ≃* SLt 5) (hB : IsSylowTwoOf B Lm) (hBW : B ≤ W)
    (hWL : ∀ w ∈ W, ∀ l ∈ Lm, w * l * w⁻¹ ∈ Lm) (hWB : ∀ w ∈ W, ∀ b ∈ B, w * b * w⁻¹ ∈ B)
    (hY₁ : Y₁ ≤ Lm) (hY₁W : ∀ w ∈ W, ∀ y ∈ Y₁, w * y * w⁻¹ ∈ Y₁) (hY₁c : ∃ a, Nat.card Y₁ = 2 ^ a * 3)
    (hY₂ : Y₂ ≤ Lm) (hY₂W : ∀ w ∈ W, ∀ y ∈ Y₂, w * y * w⁻¹ ∈ Y₂) (hY₂c : ∃ a, Nat.card Y₂ = 2 ^ a * 3) :
    ∃ P₁ P₂ : Subgroup F,
      (B ≤ P₁ ∧ P₁ ≤ Lm ∧ P₁ ≠ Lm ∧ Y₁ ≤ P₁ ∧ Y₂ ≤ P₁ ∧ ∀ w ∈ W, ∀ p ∈ P₁, w * p * w⁻¹ ∈ P₁) ∧
      (B ≤ P₂ ∧ P₂ ≤ Lm ∧ P₂ ≠ Lm ∧ Y₁ ≤ P₂ ∧ Y₂ ≤ P₂ ∧ ∀ w ∈ W, ∀ p ∈ P₂, w * p * w⁻¹ ∈ P₂) ∧
      P₁ ⊔ P₂ = Lm := by
  obtain ⟨D⟩ := exists_borelIso (n := 5) (by norm_num) hB e
  have hBL : B ≤ Lm := hB.1
  have hWN : W ≤ Subgroup.normalizer (Lm : Set F) := le_normalizer_of_conj_mem hWL
  have key : ∀ Y : Subgroup F, Y ≤ Lm → (∀ w ∈ W, ∀ y ∈ Y, w * y * w⁻¹ ∈ Y) →
      (∃ a, Nat.card Y = 2 ^ a * 3) →
      ∃ Q : Subgroup F, B ≤ Q ∧ Q ≤ Lm ∧ Y ≤ Q ∧ (∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) ∧
        ∃ x, IsNode 5 x ∧ x ∉ D.cutsOf Q ∧ ∀ y, IsNode 5 y → y ∉ D.cutsOf Q → y = x := by
    intro Y hYL hYW hYc
    refine ⟨Y ⊔ B, le_sup_right, sup_le hYL hBL, le_sup_left, ?_, ?_⟩
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
    · have hcard := card_sup_eq_three_mul hB hYL (fun b hb y hy => hYW b (hBW hb) y hy) hYc
      have hmax := isMaxSubgroupIn_of_card (le_sup_right : B ≤ Y ⊔ B) hcard
      exact D.exists_unique_node_of_isMax hBL (sup_le hYL hBL) hmax
  obtain ⟨Q₁, hBQ₁, hQ₁L, hY₁Q₁, hQ₁W, a₁, ha₁, ha₁Q, ha₁u⟩ := key Y₁ hY₁ hY₁W hY₁c
  obtain ⟨Q₂, hBQ₂, hQ₂L, hY₂Q₂, hQ₂W, a₂, ha₂, ha₂Q, ha₂u⟩ := key Y₂ hY₂ hY₂W hY₂c
  have hinv : ∀ P : Subgroup F, B ≤ P → P ≤ Lm → ∀ w ∈ W, conjSub w P = P := by
    intro P hBP hPL w hw
    have hwN : w ∈ Subgroup.normalizer (Lm : Set F) := hWN hw
    have hBc : conjSub w B = B := conjSub_eq_of_conj_mem hWB hw
    have hφ : (Ut 5).map (D.autOf w hwN).toMonoidHom = Ut 5 := by
      have := D.model_conjSub w hwN B
      rwa [hBc, D.model_B] at this
    rcases aut_dichotomy (by norm_num) (D.autOf w hwN) hφ with ⟨b, hbU, hb⟩ | hswap
    · have hUP : Ut 5 ≤ D.model P := (D.Ut_le_model_iff hBL).2 hBP
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
  obtain ⟨k₁, k₂, hk₁, hk₂, hk12, hk₁a₁, hk₁a₂, hk₂a₁, hk₂a₂⟩ := exists_two_nodes_five a₁ a₂ ha₁ ha₂
  obtain ⟨P₁, hBP₁, hP₁L, hP₁c⟩ := D.exists_cutsOf_eq hBL (I := {k₁}) (by rintro i rfl; exact hk₁)
  obtain ⟨P₂, hBP₂, hP₂L, hP₂c⟩ := D.exists_cutsOf_eq hBL (I := {k₂}) (by rintro i rfl; exact hk₂)
  have hin₁ : ∀ k, IsNode 5 k → k ≠ a₁ → k ∈ D.cutsOf Q₁ := fun k hk hka => by
    by_contra h
    exact hka (ha₁u k hk h)
  have hin₂ : ∀ k, IsNode 5 k → k ≠ a₂ → k ∈ D.cutsOf Q₂ := fun k hk hka => by
    by_contra h
    exact hka (ha₂u k hk h)
  have hQP : ∀ (Q P : Subgroup F) (k : ℕ), B ≤ Q → Q ≤ Lm → B ≤ P → D.cutsOf P = {k} →
      k ∈ D.cutsOf Q → Q ≤ P := fun Q P k hBQ hQL hBP hPk hk =>
    (D.cutsOf_le_iff hBL hBQ hQL hBP).2 (by rw [hPk]; exact Set.singleton_subset_iff.2 hk)
  have hne : ∀ (P : Subgroup F) (k : ℕ), D.cutsOf P = {k} → P ≠ Lm := fun P k hP h => by
    rw [h, D.cutsOf_L] at hP
    exact Set.singleton_ne_empty k hP.symm
  refine ⟨P₁, P₂, ⟨hBP₁, hP₁L, hne P₁ k₁ hP₁c, ?_, ?_, hinvar P₁ hBP₁ hP₁L⟩,
    ⟨hBP₂, hP₂L, hne P₂ k₂ hP₂c, ?_, ?_, hinvar P₂ hBP₂ hP₂L⟩, ?_⟩
  · exact hY₁Q₁.trans (hQP Q₁ P₁ k₁ hBQ₁ hQ₁L hBP₁ hP₁c (hin₁ k₁ hk₁ hk₁a₁))
  · exact hY₂Q₂.trans (hQP Q₂ P₁ k₁ hBQ₂ hQ₂L hBP₁ hP₁c (hin₂ k₁ hk₁ hk₁a₂))
  · exact hY₁Q₁.trans (hQP Q₁ P₂ k₂ hBQ₁ hQ₁L hBP₂ hP₂c (hin₁ k₂ hk₂ hk₂a₁))
  · exact hY₂Q₂.trans (hQP Q₂ P₂ k₂ hBQ₂ hQ₂L hBP₂ hP₂c (hin₂ k₂ hk₂ hk₂a₂))
  · have hBS : B ≤ P₁ ⊔ P₂ := hBP₁.trans le_sup_left
    have hSL : P₁ ⊔ P₂ ≤ Lm := sup_le hP₁L hP₂L
    have h1 : D.cutsOf (P₁ ⊔ P₂) ⊆ D.cutsOf P₁ := (D.cutsOf_le_iff hBL hBP₁ hP₁L hBS).1 le_sup_left
    have h2 : D.cutsOf (P₁ ⊔ P₂) ⊆ D.cutsOf P₂ := (D.cutsOf_le_iff hBL hBP₂ hP₂L hBS).1 le_sup_right
    have hcut : D.cutsOf (P₁ ⊔ P₂) = D.cutsOf Lm := by
      rw [D.cutsOf_L]
      ext i
      constructor
      · intro hi
        have e1 : i = k₁ := by simpa [hP₁c] using h1 hi
        have e2 : i = k₂ := by simpa [hP₂c] using h2 hi
        exact absurd (e1.symm.trans e2) hk12
      · intro hi
        exact absurd hi (Set.notMem_empty i)
    exact D.eq_of_cutsOf_eq hBL hBS hSL hBL le_rfl hcut

end CFSG.Quasithin.A38c7
