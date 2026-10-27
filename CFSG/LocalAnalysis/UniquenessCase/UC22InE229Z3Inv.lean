module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_eq_of_ne_one {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q ≤ 2) {c d : Q}
    (hc : c ≠ 1) (hd : d ≠ 1) : c = d := by
  classical
  by_contra hcd
  haveI := Fintype.ofFinite Q
  have h3 : ({1, c, d} : Finset Q).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, c, d, hc.symm, hd.symm, hcd, rfl⟩
  have h := Finset.card_le_univ ({1, c, d} : Finset Q)
  rw [h3, ← Nat.card_eq_fintype_card] at h
  omega

theorem uc22ine229_normalizer_le_or_card_le_two (k : Sec7Core4 G) (hp3 : k.p = 3)
    (hK3 : StronglyEmbeddedThree) {X : Subgroup G} (hX : X ≠ ⊥) (hXM : X ≤ k.M)
    {B₁ : Subgroup G} (hB₁M : B₁ ≤ k.M) (hB₁ : IsElemAbelian k.p B₁)
    (hB₁c : Nat.card B₁ = k.p ^ 2) (hB₁X : B₁ ≤ centralizer (X : Set G)) :
    normalizer (X : Set G) ≤ k.M ∨ Nat.card ↥(pCoreOf 2 k.M ⊓ normalizer (X : Set G)) ≤ 2 := by
  by_cases hnot : normalizer (X : Set G) ≤ k.M
  · exact Or.inl hnot
  refine Or.inr (k.step74w_of_stronglyEmbeddedThree hp3 hK3 _ ?_)
  exact k.config_normalizer hX hXM
    (CFSG.SectionRank.le_pRank k.prime.one_lt
      (le_inf hB₁M (hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G)))) hB₁ hB₁c) hnot

theorem uc22ine229_le_centralizer3 {M Y X B₁ : Subgroup G} (hB₁M : B₁ ≤ M)
    (hQ : Nat.card ↥(pCoreOf 2 M ⊓ normalizer (X : Set G)) ≤ 2) (hB₁ : IsElemAbelian 3 B₁)
    (hB₁X : B₁ ≤ centralizer (X : Set G))
    (hB₁Y : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M) :
    Y ⊓ normalizer (X : Set G) ≤ centralizer (B₁ : Set G) := by
  rintro w ⟨hwY, hwN⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbN : b ∈ normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) (hB₁X hb)
  obtain ⟨c, hc⟩ : ∃ c : G, c = b * w * b⁻¹ * w⁻¹ := ⟨_, rfl⟩
  have hcN : c ∈ normalizer (X : Set G) := by
    rw [hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hwN)
      (Subgroup.inv_mem _ hbN)) (Subgroup.inv_mem _ hwN)
  have hcQ : c ∈ pCoreOf 2 M ⊓ normalizer (X : Set G) := by
    refine ⟨?_, hcN⟩
    rw [hc]
    exact hB₁Y b hb w hwY
  have hbQ : b * c * b⁻¹ ∈ pCoreOf 2 M ⊓ normalizer (X : Set G) := by
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hcN) (Subgroup.inv_mem _ hbN)⟩
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hB₁M hb)) c).1 hcQ.1
  have hbc : b * c * b⁻¹ = c := by
    by_cases h1 : c = 1
    · rw [h1]
      group
    · refine congrArg Subtype.val (uc22ine229_eq_of_ne_one hQ (c := ⟨b * c * b⁻¹, hbQ⟩)
        (d := ⟨c, hcQ⟩) (fun h => h1 ?_) fun h => h1 (congrArg Subtype.val h))
      have h2 : b * c * b⁻¹ = 1 := congrArg Subtype.val h
      simpa using h2
  have key : ∀ x : G, b * (c * x) * b⁻¹ = c * (b * x * b⁻¹) := fun x => by
    calc b * (c * x) * b⁻¹ = (b * c * b⁻¹) * (b * x * b⁻¹) := by group
      _ = c * (b * x * b⁻¹) := by rw [hbc]
  have h1 : b * w * b⁻¹ = c * w := by rw [hc]; group
  have hb3 : b * b * b = 1 := by
    have h := hB₁.2 b hb
    rw [pow_succ, pow_succ, pow_one] at h
    exact h
  have h3 : w = c * (c * (c * w)) := by
    calc w = (b * b * b) * w * (b * b * b)⁻¹ := by rw [hb3]; group
      _ = b * (b * (b * w * b⁻¹) * b⁻¹) * b⁻¹ := by group
      _ = c * (c * (c * w)) := by rw [h1, key, h1, key, key, h1]
  have hc3 : c * c * c = 1 := by
    have h4 : (c * c * c) * w = 1 * w := by rw [one_mul, mul_assoc, mul_assoc, ← h3]
    exact mul_right_cancel h4
  have hc1 : c = 1 := by
    by_contra hne
    have hc2 : c * c = 1 := by
      by_contra hne2
      have heq := uc22ine229_eq_of_ne_one hQ (c := ⟨c * c, Subgroup.mul_mem _ hcQ hcQ⟩)
        (d := ⟨c, hcQ⟩) (fun h => hne2 (congrArg Subtype.val h))
        (fun h => hne (congrArg Subtype.val h))
      have h5 : c * c = c := congrArg Subtype.val heq
      exact hne (by simpa using h5)
    rw [hc2, one_mul] at hc3
    exact hne hc3
  have hcomm : b * w * b⁻¹ * w⁻¹ = 1 := by rw [← hc, hc1]
  calc b * w = (b * w * b⁻¹ * w⁻¹) * (w * b) := by group
    _ = w * b := by rw [hcomm, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22
