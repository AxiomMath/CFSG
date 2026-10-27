module

public import CFSG.Quasithin.MS93.ASGroup

public section

namespace CFSG.Quasithin.MS93.S52i

open scoped commutatorElement

variable {G : Type} [Group G] {M L : Subgroup G}

theorem commutator_le_of_two_step (hperf : ⁅L, L⁆ = L) {A X B : Subgroup G}
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hBX : ⁅B, L⁆ ≤ X) (hXA : ⁅X, L⁆ ≤ A) : ⁅B, L⁆ ≤ A := by
  have h1 : ⁅⁅B, L⁆, L⁆ ≤ A := (Subgroup.commutator_mono hBX le_rfl).trans hXA
  have h2 : ⁅⁅L, B⁆, L⁆ ≤ A := by rw [Subgroup.commutator_comm L B]; exact h1
  have h3 := three_subgroups_le hLA hLA hBA h2 h1
  rw [hperf] at h3
  rw [Subgroup.commutator_comm]
  exact h3

variable (hLM : L ≤ M) (hperf : ⁅L, L⁆ = L)
include hLM hperf

theorem exists_chief [Finite G] {A B : Subgroup G} (hAn : M ≤ Subgroup.normalizer (A : Set G))
    (hBn : M ≤ Subgroup.normalizer (B : Set G)) (hBM : B ≤ M) (hAB : A ≤ B)
    (hBA : ¬ ⁅B, L⁆ ≤ A) :
    ∃ N W : Subgroup G, A ≤ N ∧ N ≤ W ∧ W ≤ B ∧ M ≤ Subgroup.normalizer (N : Set G) ∧
      M ≤ Subgroup.normalizer (W : Set G) ∧ ¬ ⁅W, L⁆ ≤ N ∧
      ∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → N ≤ J → J ≤ W → J = N ∨ J = W := by
  induction hn : Nat.card B - Nat.card A using Nat.strong_induction_on generalizing A B with
  | _ n ih =>
    by_cases hmax : ∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → A ≤ J → J ≤ B →
        J = A ∨ J = B
    · exact ⟨A, B, le_rfl, hAB, le_rfl, hAn, hBn, hBA, hmax⟩
    push Not at hmax
    obtain ⟨J, hJn, hAJ, hJB, hJA, hJB'⟩ := hmax
    have hAJlt : Nat.card A < Nat.card J :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hAJ (Ne.symm hJA))
    have hJBlt : Nat.card J < Nat.card B := Subgroup.card_lt_of_lt (lt_of_le_of_ne hJB hJB')
    by_cases hJA' : ⁅J, L⁆ ≤ A
    ·
      have hBJ : ¬ ⁅B, L⁆ ≤ J := fun hBJ => hBA (commutator_le_of_two_step hperf
        (hLM.trans hAn) ((hBM).trans hAn) hBJ hJA')
      obtain ⟨N, W, hJN, hNW, hWB, hNn, hWn, hWN, hch⟩ :=
        ih (Nat.card B - Nat.card J) (by omega) hJn hBn hBM hJB hBJ rfl
      exact ⟨N, W, hAJ.trans hJN, hNW, hWB, hNn, hWn, hWN, hch⟩
    · obtain ⟨N, W, hAN, hNW, hWJ, hNn, hWn, hWN, hch⟩ :=
        ih (Nat.card J - Nat.card A) (by omega) hAn hJn (hJB.trans hBM) hAJ hJA' rfl
      exact ⟨N, W, hAN, hNW, hWJ.trans hJB, hNn, hWn, hWN, hch⟩

omit hLM hperf in
theorem relIndex_ge_mul [Finite G] {W N Y : Subgroup G} (hNW : N ≤ W) :
    ((W ⊓ Y) ⊔ N).relIndex W * Y.relIndex N ≤ Y.relIndex W := by
  have hne : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K => by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  set K := (W ⊓ Y) ⊔ N with hK
  have hKW : K ≤ W := sup_le inf_le_left hNW
  have hYK : Y ⊓ W ≤ K := by rw [inf_comm]; exact le_sup_left
  have h1 : (Y ⊓ W).relIndex K * K.relIndex W = Y.relIndex W := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hYK hKW, Subgroup.inf_relIndex_right]
  have h2 : Y.relIndex N ≤ (Y ⊓ W).relIndex K :=
    (Subgroup.relIndex_le_of_le_right le_sup_right (hne _ _)).trans
      (Subgroup.relIndex_le_of_le_left inf_le_left (hne _ _))
  calc K.relIndex W * Y.relIndex N ≤ K.relIndex W * (Y ⊓ W).relIndex K := Nat.mul_le_mul_left _ h2
    _ = Y.relIndex W := by rw [mul_comm, h1]

theorem le_or_le_of_count [Finite G] {V Y Z : Subgroup G} (hVM : V ≤ M) {q : ℕ} (hq : 2 ≤ q)
    (hYV : Y.relIndex V ≤ q ^ 3)
    (hFF : ∀ N W : Subgroup G, M ≤ Subgroup.normalizer (N : Set G) →
      M ≤ Subgroup.normalizer (W : Set G) → Z ≤ N → N ≤ W → W ≤ V → ¬ ⁅W, L⁆ ≤ N →
      (∀ J : Subgroup G, M ≤ Subgroup.normalizer (J : Set G) → N ≤ J → J ≤ W →
        J = N ∨ J = W) → q ^ 2 ≤ ((W ⊓ Y) ⊔ N).relIndex W)
    {A B C : Subgroup G} (hAn : M ≤ Subgroup.normalizer (A : Set G))
    (hBn : M ≤ Subgroup.normalizer (B : Set G)) (hCn : M ≤ Subgroup.normalizer (C : Set G))
    (hZA : Z ≤ A) (hAB : A ≤ B) (hBC : B ≤ C) (hCV : C ≤ V) :
    ⁅B, L⁆ ≤ A ∨ ⁅C, L⁆ ≤ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hne : ∀ H K : Subgroup G, H.relIndex K ≠ 0 := fun H K => by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  obtain ⟨N₁, W₁, hAN₁, hNW₁, hWB₁, hNn₁, hWn₁, hWN₁, hch₁⟩ :=
    exists_chief hLM hperf hAn hBn ((hBC.trans hCV).trans hVM) hAB h1
  obtain ⟨N₂, W₂, hBN₂, hNW₂, hWC₂, hNn₂, hWn₂, hWN₂, hch₂⟩ :=
    exists_chief hLM hperf hBn hCn (hCV.trans hVM) hBC h2
  have hq₁ := hFF N₁ W₁ hNn₁ hWn₁ (hZA.trans hAN₁) hNW₁ (hWB₁.trans (hBC.trans hCV)) hWN₁ hch₁
  have hq₂ := hFF N₂ W₂ hNn₂ hWn₂ (hZA.trans (hAB.trans hBN₂)) hNW₂ (hWC₂.trans hCV) hWN₂ hch₂
  have e1 : Y.relIndex W₂ ≤ Y.relIndex V :=
    Subgroup.relIndex_le_of_le_right (hWC₂.trans hCV) (hne _ _)
  have e2 := relIndex_ge_mul (Y := Y) hNW₂
  have e3 : Y.relIndex W₁ ≤ Y.relIndex N₂ :=
    Subgroup.relIndex_le_of_le_right (hWB₁.trans hBN₂) (hne _ _)
  have e4 : ((W₁ ⊓ Y) ⊔ N₁).relIndex W₁ ≤ Y.relIndex W₁ := by
    have := relIndex_ge_mul (Y := Y) hNW₁
    have hpos : 1 ≤ Y.relIndex N₁ := Nat.one_le_iff_ne_zero.mpr (hne _ _)
    nlinarith
  have key : q ^ 2 * q ^ 2 ≤ q ^ 3 := by
    calc q ^ 2 * q ^ 2 ≤ ((W₂ ⊓ Y) ⊔ N₂).relIndex W₂ * Y.relIndex N₂ :=
          Nat.mul_le_mul hq₂ (hq₁.trans (e4.trans e3))
      _ ≤ Y.relIndex W₂ := e2
      _ ≤ q ^ 3 := e1.trans hYV
  have : q ^ 3 < q ^ 2 * q ^ 2 := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

end CFSG.Quasithin.MS93.S52i
