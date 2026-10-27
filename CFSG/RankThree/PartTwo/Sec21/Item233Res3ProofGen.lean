module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofU44

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Item233ZRootGenSL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) →
      (∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A) →
      Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 2)) → Nonempty (Z ≃* SL3 2) →
        Z ≤ (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔
          ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ

@[expose] def Item233ZRootGenSp44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) →
      (∀ ρ ∈ starOf A Z, IsReflectionOn ρ → ρ ∈ dStar A) →
      Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 2)) →
      Nonempty (Z ≃* projSp 2 (GaloisField 2 2)) →
        Z ≤ (Z ⊓ Subgroup.normalizer (A : Set G)) ⊔
          ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ

namespace Item233Res3Proof

variable {G : Type} [Group G]

theorem exists_ne_mem_dStar [Finite G] (h2131 : Item2131One) (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA27 : Nat.card A = 3 ^ 3)
    (φ : MulAut A) : ∃ ψ ∈ dStar A, ψ ≠ φ := by
  obtain ⟨f, -, hcase⟩ := exists_coord_image_dStar h2131 h222 hpair hA27
  have hp : p01 ∈ coordGL f '' dStar A := by
    rcases hcase with hD | hD <;> rw [hD]
    · simp [swapRefl]
    · exact Or.inr (by simp [swapRefl])
  have hm : m01 ∈ coordGL f '' dStar A := by
    rcases hcase with hD | hD <;> rw [hD]
    · simp [swapRefl]
    · exact Or.inr (by simp [swapRefl])
  obtain ⟨ψ₁, hψ₁, h₁⟩ := hp
  obtain ⟨ψ₂, hψ₂, h₂⟩ := hm
  by_cases h : ψ₁ = φ
  · refine ⟨ψ₂, hψ₂, fun h' => Item221ResProof.p01_ne_m01 ?_⟩
    rw [← h₁, ← h₂, h, h']
  · exact ⟨ψ₁, hψ₁, h⟩

end Item233Res3Proof

open Item233Res3Proof

theorem item233ZRootGenThreeNotU54_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (h2130 : Item2130) (h2131 : Item2131One) (h222 : Item222) (hKW : KOfWellDefinedAll)
    (hSL : Item233ZRootGenSL34) (hSp : Item233ZRootGenSp44) : Item233ZRootGenThreeNotU54 := by
  intro G _ _ A E U c L hpair hconc hA27 φ hφ Z hZ hKZ h3 hR hU5
  obtain ⟨ψ, hψ, hψφ⟩ := exists_ne_mem_dStar h2131 h222 hpair hA27 φ
  obtain ⟨m, hm0, hme, ⟨eK⟩, hZtype⟩ := h3 ψ hψ hψφ
  have hm2 : m = 2 := eq_two_of_kOf h2130 h222 hKW hpair hconc hA27 hφ hm0 hme eK
  subst hm2
  rcases hZtype with h | h | h | ⟨h4, -⟩ | ⟨-, h⟩
  · exact hSL G A E U c L hpair hconc hA27 φ hφ Z hZ hKZ h3 hR ⟨eK⟩ h
  · exact hSp G A E U c L hpair hconc hA27 φ hφ Z hZ hKZ h3 hR ⟨eK⟩ h
  · exact ((item233ZNotU44_of h45 h66 h2130 h222 hKW G A E U c L hpair hconc hA27 φ hφ Z hZ
      hKZ hR).false h.some).elim
  · norm_num at h4
  · exact (hU5.false h.some).elim

theorem item233ZGen_of_res''' (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h2130 : Item2130)
    (h222 : Item222) (hKW : KOfWellDefinedAll) (hInner : Item223OneInner)
    (h2131 : Item2131One) (h612 : Item612Sec21) (hSL : Item233ZRootGenSL34)
    (hSp : Item233ZRootGenSp44) : Item233ZGen :=
  item233ZGen_of_res'' h45 h66 h2130 h222 hKW hInner h2131 h612
    (item233ZRootGenThreeNotU54_of h45 h66 h2130 h2131 h222 hKW hSL hSp)

end CFSG.RankThree.PartTwo.Sec21
