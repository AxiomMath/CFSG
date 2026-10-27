module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.RankThree.PartTwo.Sec11 (CyclicSylowThreeOutAbelian)

variable {G : Type} [Group G] [Finite G]

theorem s13_shape_of_calC
    (D : Data G) (hS : Setting13 D) (hSig : SigmaStd D) (hThin : ThinList13)
    (hCyc : CyclicSylowThreeOutAbelian) (hrk3 : SigmaRankThree13 D) (h133 : R133 D)
    {K : Subgroup G} (hK : K ∈ calC D.M) :
    (∃ n : ℕ, IsPowTwo n ∧ IsL2 (Bar2 K) n) ∨ (∃ n : ℕ, IsPowTwo n ∧ IsU3 (Bar2 K) n) ∨
      (Thin13 K ∧ ((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ∧ IsL2Odd (Bar2 K) p) ∨ IsJ1 (Bar2 K))) := by
  rcases hS.hyp131.thinOrU3 K hK with hthin | ⟨n, hn, hU⟩
  · obtain ⟨-, h⟩ := s13_list_bar hThin D hK hthin
    rcases h with ⟨a, ha⟩ | ⟨p, hp, hp2, hpL⟩ | ⟨a, ha⟩ | hJ1
    · exact Or.inl ⟨a, isPowTwo_of_mem_calC D hS hSig hThin hCyc hrk3 h133 hK (Or.inl ha), ha⟩
    · obtain ⟨-, -, h5⟩ := s13_five_le_of_isL2Odd hpL
      by_cases hp5 : p = 5
      · subst p
        exact Or.inl ⟨2, ⟨1, by rw [pow_one]⟩, s13_isL2_two_of_isL2Odd_five hpL⟩
      · exact Or.inr (Or.inr ⟨hthin,
          Or.inl ⟨p, hp, hp2, Nat.lt_of_le_of_ne h5 (Ne.symm hp5), hpL⟩⟩)
    · exfalso
      exact s13_not_isSz_of_isPowTwo ha
        (isPowTwo_of_mem_calC D hS hSig hThin hCyc hrk3 h133 hK (Or.inr ha))
    · exact Or.inr (Or.inr ⟨hthin, Or.inr hJ1⟩)
  · exact Or.inr (Or.inl ⟨n, hn, hU⟩)

theorem s13_exists_ne_calC (D : Data G) (hS : Setting13 D) (hSig : SigmaStd D)
    (hThin : ThinList13) (hCyc : CyclicSylowThreeOutAbelian) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hthin : Thin13 L) : ∃ K ∈ calC D.M, K ≠ L := by
  obtain ⟨p, hp⟩ := hSig.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have h2 := s13_two_le_pRank_layer hThin hCyc D hS hSig hp
  have hJ₀ : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent hL
  have hrk : CFSG.Open.pRank p (barImage D.M L) ≤ 1 :=
    s13_pRank_barImage_le_one (s13_le_of_mem_calC hL) hthin hpp hp2
  obtain ⟨J, hJ, hJne⟩ := s13_exists_other_component hJ₀ hrk h2
  obtain ⟨K, hK, hKbar⟩ := s13_exists_calC_of_component D.M hJ
  refine ⟨K, hK, ?_⟩
  intro hKL
  exact hJne (by rw [← hKbar, hKL])

theorem isL2_or_isU3_of_mem_calC
    (D : Data G) (hS : Setting13 D) (hSig : SigmaStd D) (hThin : ThinList13)
    (hCyc : CyclicSylowThreeOutAbelian) (hrk3 : SigmaRankThree13 D) (h133 : R133 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) :
    (∃ n : ℕ, IsPowTwo n ∧ IsL2 (Bar2 L) n) ∨ (∃ n : ℕ, IsPowTwo n ∧ IsU3 (Bar2 L) n) := by
  rcases s13_shape_of_calC D hS hSig hThin hCyc hrk3 h133 hL with h | h | ⟨hthin, hshape⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have hshape' : IsJ1 (Bar2 L) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ f ∧
          CFSG.Blueprint.LieModel (Bar2 L) .PSL 2 p f := by
      rcases hshape with ⟨p, hp, hp2, h5, hpL⟩ | hJ1
      · exact Or.inr ⟨p, 1, hp, hp2, by simpa using h5, hpL⟩
      · exact Or.inl hJ1
    obtain ⟨K, hK, hKL⟩ := s13_exists_ne_calC D hS hSig hThin hCyc hL hthin
    have hKshape : (∃ n : ℕ, IsL2 (Bar2 K) (2 ^ n)) ∨ (∃ n : ℕ, IsU3 (Bar2 K) n) ∨
        (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd (Bar2 K) p) ∨ IsJ1 (Bar2 K) := by
      rcases s13_shape_of_calC D hS hSig hThin hCyc hrk3 h133 hK with
        ⟨n, ⟨k, hk⟩, hL2⟩ | ⟨n, _, hU⟩ | ⟨_, h⟩
      · exact Or.inl ⟨k, by rw [← hk]; exact hL2⟩
      · exact Or.inr (Or.inl ⟨n, hU⟩)
      · rcases h with ⟨p, hp, hp2, _, hpK⟩ | hJ1K
        · exact Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, hpK⟩))
        · exact Or.inr (Or.inr (Or.inr hJ1K))
    exact hS.hyp131.notAmong L hL hshape' K hK hKL hKshape

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
