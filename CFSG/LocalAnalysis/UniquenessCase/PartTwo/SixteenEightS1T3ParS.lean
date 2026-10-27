module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def T3ParabIn {E : Type*} [Group E] (N X : Subgroup E) (a : ℕ) : Prop :=
  ∃ P₀ : Subgroup E, P₀ ≤ N ∧ (∀ x ∈ X, ∀ p ∈ P₀, x * p * x⁻¹ ∈ P₀) ∧ X ⊓ N ≤ P₀ ∧
    Nat.card ↥P₀ = 3 ^ a * 2 ^ (Nat.card ↥N).factorization 2 ∧
    ∀ p ∈ P₀, ∀ m : ℕ, p ^ 3 ^ m = 1 → p ^ 3 = 1

theorem s16t3_parab_of_conj {E : Type*} [Group E] {G N P X : Subgroup E} {B : Set E}
    (hGN : G ≤ Subgroup.normalizer (N : Set E)) (hPN : P ≤ N)
    (hBP : ∀ y ∈ B, ∀ p ∈ P, y * p * y⁻¹ ∈ P) (hBN : ∀ y ∈ B, y ∈ N → y ∈ P) {g : E}
    (hg : g ∈ G) (hXB : ∀ x ∈ X, g⁻¹ * x * g ∈ B) :
    ∃ P₀ : Subgroup E, P₀ ≤ N ∧ (∀ x ∈ X, ∀ p ∈ P₀, x * p * x⁻¹ ∈ P₀) ∧ X ⊓ N ≤ P₀ ∧
      Nat.card ↥P₀ = Nat.card ↥P ∧
      ((∀ p ∈ P, ∀ m : ℕ, p ^ 3 ^ m = 1 → p ^ 3 = 1) →
        ∀ p ∈ P₀, ∀ m : ℕ, p ^ 3 ^ m = 1 → p ^ 3 = 1) := by
  have hgN : ∀ n : E, n ∈ N ↔ g * n * g⁻¹ ∈ N := Subgroup.mem_normalizer_iff.1 (hGN hg)
  have hconj : ∀ p : E, (MulAut.conj g).toMonoidHom p = g * p * g⁻¹ := fun p => rfl
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [hconj]
    exact (hgN p).1 (hPN hp)
  · rintro x hx _ ⟨p, hp, rfl⟩
    refine ⟨(g⁻¹ * x * g) * p * (g⁻¹ * x * g)⁻¹, hBP _ (hXB x hx) p hp, ?_⟩
    rw [hconj, hconj]
    group
  · rintro x ⟨hxX, hxN⟩
    have hxN' : g⁻¹ * x * g ∈ N := by
      have h1 := (hgN (g⁻¹ * x * g)).2
      apply h1
      have h2 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [h2]
      exact hxN
    refine ⟨g⁻¹ * x * g, hBN _ (hXB x hxX) hxN', ?_⟩
    rw [hconj]
    group
  · exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  · rintro hexp _ ⟨p, hp, rfl⟩ m hm
    rw [hconj] at hm ⊢
    have hm' : p ^ 3 ^ m = 1 := by
      have h1 : g * p ^ 3 ^ m * g⁻¹ = 1 := by
        rw [← conj_pow, hm]
      have h2 : p ^ 3 ^ m = g⁻¹ * (g * p ^ 3 ^ m * g⁻¹) * g := by group
      rw [h2, h1]
      group
    rw [conj_pow, hexp p hp m hm']
    group

theorem T3ParabIn.of_conj {E : Type*} [Group E] {G N P X : Subgroup E} {B : Set E} {a : ℕ}
    (hGN : G ≤ Subgroup.normalizer (N : Set E)) (hPN : P ≤ N)
    (hBP : ∀ y ∈ B, ∀ p ∈ P, y * p * y⁻¹ ∈ P) (hBN : ∀ y ∈ B, y ∈ N → y ∈ P)
    (hcard : Nat.card ↥P = 3 ^ a * 2 ^ (Nat.card ↥N).factorization 2)
    (hexp : ∀ p ∈ P, ∀ m : ℕ, p ^ 3 ^ m = 1 → p ^ 3 = 1) {g : E} (hg : g ∈ G)
    (hXB : ∀ x ∈ X, g⁻¹ * x * g ∈ B) : T3ParabIn N X a := by
  obtain ⟨P₀, h1, h2, h3, h4, h5⟩ := s16t3_parab_of_conj hGN hPN hBP hBN hg hXB
  exact ⟨P₀, h1, h2, h3, h4.trans hcard, h5 hexp⟩

theorem s16t3_exists_conj_sylow {E : Type*} [Group E] [Finite E] {G B X : Subgroup E}
    (hB : CFSG.ABGLocalTools.IsSylowOf 2 B G) (hX : IsPGroup 2 ↥X) (hXG : X ≤ G) :
    ∃ g ∈ G, ∀ x ∈ X, g⁻¹ * x * g ∈ B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀⟩ := hB.exists_sylow_eq_subgroupOf
  have hX' : IsPGroup 2 ↥(X.subgroupOf G) := hX.comap_subtype
  obtain ⟨Q, hQ⟩ := hX'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥G Q Q₀
  refine ⟨((h⁻¹ : ↥G) : E), (h⁻¹).2, fun x hx => ?_⟩
  have hxQ : (⟨x, hXG hx⟩ : ↥G) ∈ (Q : Subgroup ↥G) := hQ (Subgroup.mem_subgroupOf.2 hx)
  have hmem : (MulAut.conj h) (⟨x, hXG hx⟩ : ↥G) ∈ ((h • Q : Sylow 2 ↥G) : Subgroup ↥G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hxQ
  rw [hh, hQ₀, MulAut.conj_apply, Subgroup.mem_subgroupOf] at hmem
  simpa [mul_assoc] using hmem

theorem T3ParabIn.of_sylow {E : Type*} [Group E] [Finite E] {G N Y P X : Subgroup E} {a : ℕ}
    (hGN : G ≤ Subgroup.normalizer (N : Set E)) (hY : CFSG.ABGLocalTools.IsSylowOf 2 Y G)
    (hPN : P ≤ N) (hYP : ∀ y ∈ Y, ∀ p ∈ P, y * p * y⁻¹ ∈ P) (hYN : Y ⊓ N ≤ P)
    (hcard : Nat.card ↥P = 3 ^ a * 2 ^ (Nat.card ↥N).factorization 2)
    (hexp : ∀ p ∈ P, ∀ m : ℕ, p ^ 3 ^ m = 1 → p ^ 3 = 1) (hX : IsPGroup 2 ↥X) (hXG : X ≤ G) :
    T3ParabIn N X a := by
  obtain ⟨g, hg, hXB⟩ := s16t3_exists_conj_sylow hY hX hXG
  exact T3ParabIn.of_conj (B := (Y : Set E)) hGN hPN hYP (fun y hy hyN => hYN ⟨hy, hyN⟩)
    hcard hexp hg hXB

theorem T3ParabIn.of_sylow_le {E : Type*} [Group E] [Finite E] {N Y P X : Subgroup E} {a : ℕ}
    (hY : CFSG.ABGLocalTools.IsSylowOf 2 Y N) (hYP : Y ≤ P) (hPN : P ≤ N)
    (hcard : Nat.card ↥P = 3 ^ a * 2 ^ (Nat.card ↥N).factorization 2)
    (hexp : ∀ p ∈ P, ∀ m : ℕ, p ^ 3 ^ m = 1 → p ^ 3 = 1) (hX : IsPGroup 2 ↥X) (hXN : X ≤ N) :
    T3ParabIn N X a :=
  T3ParabIn.of_sylow Subgroup.le_normalizer hY hPN
    (fun y hy p hp => P.mul_mem (P.mul_mem (hYP hy) hp) (P.inv_mem (hYP hy)))
    (fun y hy => hYP hy.1) hcard hexp hX hXN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
