module

import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofOrbit
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating10
public import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA10

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res162b

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13 Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2 CFSG.RankThree.PartTwo.Sec17.Proof171Gen

variable {G : Type} [Group G] [Finite G]

theorem exists_axisElt_of_mem_omegaA {A Y : Subgroup G} (hAY : A ≤ Y)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) (hΩ3 : (omegaA A).ncard = 3)
    {g : Perm (Fin 10)} (hinjA : ∀ a : ↥Y, (a : G) ∈ A → projTen Y φ a = 1 → a = 1)
    (hgA : ∀ a : ↥Y, (a : G) ∈ A → g * projTen Y φ a * g⁻¹ ∈ eTwentySeven)
    (hlift : ∀ h ∈ normAlt, ∃ y : ↥Y, (y : G) ∈ Subgroup.normalizer (A : Set G) ∧
      (∀ a : ↥Y, (a : G) ∈ A →
        g * projTen Y φ (y * a * y⁻¹) * g⁻¹ = h * (g * projTen Y φ a * g⁻¹) * h⁻¹) ∧
      ∃ a₀ : ↥Y, (a₀ : G) ∈ A ∧ g * projTen Y φ y * g⁻¹ = h * (g * projTen Y φ a₀ * g⁻¹))
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) :
    ∃ e : Fin 6, g * projTen Y φ ⟨a, hAY (zpowers_mem_omegaA_iff.mp ha).1⟩ * g⁻¹ = axisElt e := by
  classical
  obtain ⟨haA, ha3, -⟩ := zpowers_mem_omegaA_iff.mp ha
  set a' : ↥Y := ⟨a, hAY haA⟩ with ha'
  set x := g * projTen Y φ a' * g⁻¹ with hx
  obtain ⟨i, j, k, hxijk⟩ := hgA a' haA
  have hx1 : eTwentySevenF i j k ≠ 1 := by
    rw [← hxijk]
    intro h1
    rw [conj_eq_one_iff] at h1
    have h2 : a = 1 := congrArg Subtype.val (hinjA a' haA h1)
    rw [h2, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at ha3
    omega
  by_contra hax
  have hax' : ¬ ∃ e : Fin 6, eTwentySevenF i j k = axisElt e := by
    rintro ⟨e, he⟩
    exact hax ⟨e, hxijk.trans he⟩
  have key : ∀ n : Fin 4, ∃ y : ↥Y, (y : G) ∈ Subgroup.normalizer (A : Set G) ∧
      g * projTen Y φ (y * a' * y⁻¹) * g⁻¹ =
        Step163Alt.conjBy (Step163Alt.orbitTab i j k n) (eTwentySevenF i j k) := by
    intro n
    obtain ⟨y, hyA, hy, -⟩ := hlift _ (Step163Alt.orbitTab_mem i j k n)
    refine ⟨y, hyA, ?_⟩
    rw [hy a' haA, hxijk]
    rfl
  choose yf hyfA hyf using key
  set F : Fin 4 → Subgroup G := fun n =>
    Subgroup.zpowers ((yf n : G) * a * (yf n : G)⁻¹) with hF
  have hFΩ : ∀ n, F n ∈ omegaA A := by
    intro n
    have h1 := (map_conj_mem_omegaA_iff (hyfA n)).mpr ha
    rw [MonoidHom.map_zpowers] at h1
    exact h1
  have hFinj : Function.Injective F := by
    intro n n' hnn'
    by_contra hne
    obtain ⟨h1, h2⟩ := Step163Alt.orbitTab_distinct i j k hx1 hax' n n' hne
    have hmem : (yf n' : G) * a * (yf n' : G)⁻¹ ∈ F n := hnn' ▸ Subgroup.mem_zpowers _
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have ht' : (yf n * a' * (yf n)⁻¹) ^ t = yf n' * a' * (yf n')⁻¹ :=
      Subtype.ext (by simpa using ht)
    have hu3 : (Step163Alt.conjBy (Step163Alt.orbitTab i j k n) (eTwentySevenF i j k)) ^ 3 = 1 := by
      rw [Step163Alt.conjBy, conj_pow, eTwentySevenF_pow_three, mul_one, mul_inv_cancel]
    have hv1 : Step163Alt.conjBy (Step163Alt.orbitTab i j k n') (eTwentySevenF i j k) ≠ 1 :=
      fun h0 => hx1 (conj_eq_one_iff.mp h0)
    refine Step163Alt.not_mem_zpowers_of_ne hu3 hv1 h1 h2
      (Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩)
    rw [← hyf n, ← hyf n', ← ht', map_zpow, conj_zpow]
  have hsub : Set.range F ⊆ omegaA A := by
    rintro _ ⟨n, rfl⟩
    exact hFΩ n
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hFinj, Nat.card_eq_fintype_card,
    Fintype.card_fin, hΩ3] at hle
  omega

end CFSG.RankThree.PartTwo.Sec16.Res162b
