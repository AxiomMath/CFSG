module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenCyclic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteenFrattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ABGLocalTools Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace ElevenFourteen

theorem inCalV1_of_noncyclic_quotient (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {V X : Subgroup G} (hV : InCalV D.M V) (hXM : X ≤ D.M) (hXp : IsPGroup p X)
    [((X ⊓ centralizer (V : Set G)).subgroupOf X).Normal]
    (hXc : ¬ IsCyclic (↥X ⧸ (X ⊓ centralizer (V : Set G)).subgroupOf X)) :
    InCalV1 D.M D.T V := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : D.M ⊓ centralizer (V : Set G) ≤ D.M := inf_le_left
  have hMK := uc22p22nc_le_normalizer_inf_centralizer hV.2.2.1
  have hS : IsSylowOf 2 (D.T ⊓ centralizer (V : Set G)) (D.M ⊓ centralizer (V : Set G)) := by
    have h := D.sylowM.inf_of_le_normalizer hKM hMK
    rwa [← inf_assoc, inf_eq_left.2 D.sylowM.le] at h
  have hSX : X ⊓ (D.M ⊓ centralizer (V : Set G)) = X ⊓ centralizer (V : Set G) := by
    rw [← inf_assoc, inf_eq_left.2 hXM]
  obtain ⟨Y, hYM, hYp, hYnc, hYN⟩ := exists_noncyclic_pSubgroup_normalizer hKM hMK hS hXp hXM
    hSX hXc
  refine ⟨hV, Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, inf_le_left⟩, ?_⟩⟩
  rintro N ⟨hNloc, hNle⟩
  have hNY : N ∈ calMOf Y :=
    ⟨hNloc, fun x hx => hNle (Subgroup.mem_inf.2 ⟨hYM hx, hYN hx⟩)⟩
  have h1 : calMOf Y = {D.M} := h61 p hp Y hYM hYp hYnc
  rw [h1] at hNY
  exact hNY

theorem eleven_four_one_of_sig (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hH : F11.Hyp11 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {X : Subgroup G} (hXM : X ≤ D.M)
    (hXp : IsPGroup p X) [((X ⊓ centralizer (V₀ : Set G)).subgroupOf X).Normal] :
    IsCyclic (↥X ⧸ (X ⊓ centralizer (V₀ : Set G)).subgroupOf X) := by
  obtain ⟨-, -, hMV₀, hcase⟩ := uc22p22q_hyp11_unpack D hH
  by_cases h4 : Nat.card V₀ ≤ 4
  · exact isCyclic_quotient_of_card_le_four (D.sig_prime p hp).1 (D.sig_prime p hp).2 hXp
      (hXM.trans hMV₀) h4
  · have hbot : V₀ ≠ ⊥ := by
      rintro rfl
      exact h4 (by simp)
    obtain ⟨hV₀, -, -⟩ := hcase.resolve_left hbot
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h8 : 8 ≤ Nat.card V₀ := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem hV₀.2.2.2)
      rw [hm] at h4 ⊢
      by_contra h8
      apply h4
      have hm2 : m ≤ 2 := by
        by_contra h3
        exact h8 (calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega))
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    by_contra hnc
    exact (hH.2.2 h8).1 (inCalV1_of_noncyclic_quotient D h61 hp hV₀ hXM hXp hnc)

end ElevenFourteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
