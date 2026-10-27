module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.WeakClosureOrbit
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenProof
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem barImage_facts_of_mem_conjSetOf {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ conjSetOf M L) (hZ : Subgroup.center (Bar2 L) = ⊥) :
    K ∈ calC M ∧ Subgroup.center ↥(barImage M K) = ⊥ ∧
      CFSG.Open.pRank 3 (barImage M K) = CFSG.Open.pRank 3 L := by
  have hKC : K ∈ calC M := uc22p2214_calC_of_mem_conjSetOf hL hK
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hKC
  refine ⟨hKC, ?_, ?_⟩
  · have h1 : Nat.card (Subgroup.center (Bar2 K)) = 1 := by
      rw [card_center_bar2_conj_of_mem_conjSetOf hK, hZ, Subgroup.card_bot]
    have h2 : Nat.card (Subgroup.center ↥(barImage M K)) = 1 := by
      rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact h1
    exact Subgroup.eq_bot_of_card_eq _ h2
  · rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (barImage M K)]
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    rw [pRank_bar2_eq_of_odd (Y := K) Nat.prime_three (by norm_num)]
    exact pRank_three_conj_of_mem_conjSetOf hK

theorem four_le_pRank_three_of_four_conj_of_center_eq_bot {M L L₁ L₂ L₃ L₄ : Subgroup G}
    (hL : L ∈ calC M) (h₁ : L₁ ∈ conjSetOf M L) (h₂ : L₂ ∈ conjSetOf M L)
    (h₃ : L₃ ∈ conjSetOf M L) (h₄ : L₄ ∈ conjSetOf M L) (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃)
    (h₁₄ : L₁ ≠ L₄) (h₂₃ : L₂ ≠ L₃) (h₂₄ : L₂ ≠ L₄) (h₃₄ : L₃ ≠ L₄)
    (hr : 1 ≤ CFSG.Open.pRank 3 L) (hZ : Subgroup.center (Bar2 L) = ⊥) :
    4 ≤ CFSG.Open.pRank 3 M := by
  obtain ⟨hC₁, -, hr₁⟩ := barImage_facts_of_mem_conjSetOf hL h₁ hZ
  obtain ⟨hC₂, hZ₂, hr₂⟩ := barImage_facts_of_mem_conjSetOf hL h₂ hZ
  obtain ⟨hC₃, hZ₃, hr₃⟩ := barImage_facts_of_mem_conjSetOf hL h₃ hZ
  obtain ⟨hC₄, hZ₄, hr₄⟩ := barImage_facts_of_mem_conjSetOf hL h₄ hZ
  have key : ∀ B C : Subgroup (Bar2 M), (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) →
      Subgroup.center ↥C = ⊥ → B ⊓ C = ⊥ := by
    intro B C hBC hC
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hx.2⟩ : ↥C) ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hBC x hx.1 c c.2).symm
    rw [hC, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
  have join : ∀ B₁ B₂ C : Subgroup (Bar2 M), (∀ b ∈ B₁, ∀ c ∈ C, b * c = c * b) →
      (∀ b ∈ B₂, ∀ c ∈ C, b * c = c * b) → ∀ b ∈ B₁ ⊔ B₂, ∀ c ∈ C, b * c = c * b := by
    intro B₁ B₂ C hB₁ hB₂ b hb c hc
    have hle : B₁ ⊔ B₂ ≤ Subgroup.centralizer (C : Set (Bar2 M)) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hB₁ x hx y hy).symm)
        (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hB₂ x hx y hy).symm)
    exact ((Subgroup.mem_centralizer_iff.1 (hle hb)) c hc).symm
  have c12 := uc22p22l_barImage_commute hC₁ hC₂ h₁₂
  have c13 := uc22p22l_barImage_commute hC₁ hC₃ h₁₃
  have c14 := uc22p22l_barImage_commute hC₁ hC₄ h₁₄
  have c23 := uc22p22l_barImage_commute hC₂ hC₃ h₂₃
  have c24 := uc22p22l_barImage_commute hC₂ hC₄ h₂₄
  have c34 := uc22p22l_barImage_commute hC₃ hC₄ h₃₄
  have c123 := join _ _ _ c13 c23
  have c1234 := join _ _ _ (join _ _ _ c14 c24) c34
  have s2 := CFSG.Quasithin.pRank_add_le_pRank_sup Nat.prime_three c12 (key _ _ c12 hZ₂)
  have s3 := CFSG.Quasithin.pRank_add_le_pRank_sup Nat.prime_three c123 (key _ _ c123 hZ₃)
  have s4 := CFSG.Quasithin.pRank_add_le_pRank_sup Nat.prime_three c1234 (key _ _ c1234 hZ₄)
  have hmono := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
    (le_top : barImage M L₁ ⊔ barImage M L₂ ⊔ barImage M L₃ ⊔ barImage M L₄ ≤ ⊤)
  rw [pRank_bar2_eq_of_odd (Y := M) Nat.prime_three (by norm_num)] at hmono
  omega

theorem ncard_conjSetOf_le_three_of_isL2Over17_seven {M L : Subgroup G} (hL : L ∈ calC M)
    (h7 : IsL2Over17 (Bar2 L) 7) (hm3 : CFSG.Open.pRank 3 M ≤ 3) :
    (conjSetOf M L).ncard ≤ 3 := by
  classical
  have h3 := isL3_one_of_isL2Over17_seven h7
  by_contra hlt
  have h4 : 3 ≤ (conjSetOf M L \ {L}).ncard := by
    rw [Set.ncard_diff_singleton_of_mem (mem_conjSetOf_self M L)]
    omega
  obtain ⟨t, ht_sub, ht_card⟩ :=
    Set.exists_subset_card_eq (s := conjSetOf M L \ {L}) (n := 3) h4
  obtain ⟨L₁, L₂, L₃, h12, h13, h23, rfl⟩ := Set.ncard_eq_three.mp ht_card
  have m1 : L₁ ∈ conjSetOf M L \ {L} := ht_sub (by simp)
  have m2 : L₂ ∈ conjSetOf M L \ {L} := ht_sub (by simp)
  have m3 : L₃ ∈ conjSetOf M L \ {L} := ht_sub (by simp)
  have h := four_le_pRank_three_of_four_conj_of_center_eq_bot hL (mem_conjSetOf_self M L)
    m1.1 m2.1 m3.1 (fun h => m1.2 (Set.mem_singleton_iff.2 h.symm))
    (fun h => m2.2 (Set.mem_singleton_iff.2 h.symm))
    (fun h => m3.2 (Set.mem_singleton_iff.2 h.symm))
    h12 h13 h23 (pRank_three_of_isL3 h3).ge (center_eq_bot_of_isL3 h3)
  omega

theorem gap17_15_tOrbitFour_of_e3 (D : Data G) (he3 : CFSG.Open.evenRank G = 3)
    (V₀ V : Subgroup G) : Gap17_15_TOrbitFour D V₀ V := by
  intro _ L hL h7 _ _ _ _ hgt _
  exfalso
  obtain ⟨n, hn⟩ := exists_ncard_conjSetOf_eq_two_pow D L
  have h4 : 4 ≤ (conjSetOf D.T L).ncard := by
    rw [hn] at hgt ⊢
    rcases n with _ | _ | n
    · simp at hgt
    · simp at hgt
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsub : conjSetOf D.T L ⊆ conjSetOf D.M L := by
    rintro K ⟨t, ht, rfl⟩
    exact ⟨t, D.sylowM.le ht, rfl⟩
  have hle : (conjSetOf D.T L).ncard ≤ (conjSetOf D.M L).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 := ncard_conjSetOf_le_three_of_isL2Over17_seven hL h7
    (pRank_three_M_le_three_of_evenRank D he3)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
