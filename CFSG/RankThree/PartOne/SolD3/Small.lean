module

public import CFSG.LocalAnalysis.OddStandard.Harada75Rank
public import CFSG.CGT.PushingUpLit.SolK.GenFour

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.GH74 CFSG.OddStandard.Harada75 CFSG.CGT.PushingUpLit.SolK
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def NoE32G (S : Subgroup G) : Prop :=
  ∀ B A : Subgroup G, B ≤ S → ¬ E32Section B A

theorem noE32_of_noE32G {S : Subgroup G} (h : NoE32G S) : NoE32 ↥S := by
  intro T U hTU
  obtain ⟨hUT, hsq, hcomm, hcard⟩ := hTU
  refine h (T.map S.subtype) (U.map S.subtype) (Subgroup.map_subtype_le T) ?_
  refine ⟨Subgroup.map_mono hUT, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x ^ 2, hsq x hx, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨⁅x, y⁆, hcomm x hx y hy, by simp⟩
  · rw [Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective S.subtype_injective]
    exact hcard

theorem sectionalTwoRankLE_four_of_noE32G [Finite G] (T : Sylow 2 G)
    (h : NoE32G (T : Subgroup G)) : SectionalTwoRankLE G 4 := by
  refine sectionalTwoRankLE_of_sylow T ?_
  intro P _
  exact gen4_of_noE32 T.isPGroup' (noE32_of_noE32G h) P

theorem noE32G_of_card_le_32 [Finite G] {S : Subgroup G} (h : Nat.card S ≤ 32)
    (h32 : Nat.card S = 32 → ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) : NoE32G S := by
  intro B A hBS hsec
  obtain ⟨-, -, hcomm, hcard⟩ := hsec
  have hle : Nat.card B ≤ Nat.card S := Subgroup.card_le_of_le hBS
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hA1 : Nat.card A = 1 := by omega
  have hS32 : Nat.card S = 32 := by omega
  have hBeq : B = S := Subgroup.eq_of_le_of_card_ge hBS (by omega)
  have hAbot : A = ⊥ := Subgroup.eq_bot_of_card_eq A hA1
  obtain ⟨x, hx, y, hy, hxy⟩ := h32 hS32
  apply hxy
  have hxB : x ∈ B := hBeq ▸ hx
  have hyB : y ∈ B := hBeq ▸ hy
  have h1 := hcomm x hxB y hyB
  rw [hAbot, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_commute.1 h1

@[expose] def SqComm (S : Subgroup G) (u : G) : Prop :=
  (∃ x ∈ S, u = x ^ 2) ∨ ∃ x ∈ S, ∃ y ∈ S, u = ⁅x, y⁆

theorem noE32G_of_card_le_64 [Finite G] {S : Subgroup G} (h : Nat.card S ≤ 64)
    (hE : ∀ B : Subgroup G, B ≤ S → Nat.card B = 32 →
      ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x ∨ x * x ≠ 1)
    (h64 : Nat.card S = 64 →
      ∃ u v : G, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ SqComm S u ∧ SqComm S v) : NoE32G S := by
  intro B A hBS hsec
  obtain ⟨hAB, hsq, hcomm, hcard⟩ := hsec
  have hle : Nat.card B ≤ Nat.card S := Subgroup.card_le_of_le hBS
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hA : Nat.card A = 1 ∨ Nat.card A = 2 := by omega
  rcases hA with hA1 | hA2
  ·
    have hB32 : Nat.card B = 32 := by omega
    have hAbot : A = ⊥ := Subgroup.eq_bot_of_card_eq A hA1
    obtain ⟨x, hx, y, hy, hxy⟩ := hE B hBS hB32
    rcases hxy with hxy | hxy
    · apply hxy
      have h1 := hcomm x hx y hy
      rw [hAbot, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_commute.1 h1
    · apply hxy
      have h1 := hsq x hx
      rw [hAbot, Subgroup.mem_bot] at h1
      simpa [pow_two] using h1
  · have hB64 : Nat.card B = 64 := by omega
    have hS64 : Nat.card S = 64 := by omega
    have hBeq : B = S := Subgroup.eq_of_le_of_card_ge hBS (by omega)
    obtain ⟨u, v, hu1, hv1, huv, hu, hv⟩ := h64 hS64
    have huA : u ∈ A := by
      rcases hu with ⟨x, hx, rfl⟩ | ⟨x, hx, y, hy, rfl⟩
      · exact hsq x (hBeq ▸ hx)
      · exact hcomm x (hBeq ▸ hx) y (hBeq ▸ hy)
    have hvA : v ∈ A := by
      rcases hv with ⟨x, hx, rfl⟩ | ⟨x, hx, y, hy, rfl⟩
      · exact hsq x (hBeq ▸ hx)
      · exact hcomm x (hBeq ▸ hx) y (hBeq ▸ hy)
    let f : Fin 3 → ↥A := ![1, ⟨u, huA⟩, ⟨v, hvA⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | rfl
          | (exfalso
             simp only [f] at hij
             first
               | exact hu1 (by simpa using (congrArg Subtype.val hij).symm)
               | exact hu1 (by simpa using congrArg Subtype.val hij)
               | exact hv1 (by simpa using (congrArg Subtype.val hij).symm)
               | exact hv1 (by simpa using congrArg Subtype.val hij)
               | exact huv (by simpa using congrArg Subtype.val hij)
               | exact huv (by simpa using (congrArg Subtype.val hij).symm))
    have h3 := Nat.card_le_card_of_injective f hf
    simp at h3
    omega

end CFSG.RankThree.PartOne.SolD3
