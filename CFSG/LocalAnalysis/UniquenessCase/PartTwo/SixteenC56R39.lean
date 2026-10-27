module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R39A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R39C

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem r16_39_holds (D : Data G) (h126 : R126 D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h129 : R129_1 D)
    (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D) (h127 : R127 D) (h38 : R16_38 D) :
    R16_39 D := by
  intro V₀ V L hV hS m hm
  have h125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hm2 : 2 ≤ m := by rcases hm with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hWc : ∀ i, i + 1 ≤ m → E3.wClos V i D.T ≤ centralizer (V : Set G) := fun i hi =>
    wClos_le_centralizer_of_case1633 D hSg h1219 h21 h22 h61 hext h5 hS hm hi
  have hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p ↥D.M := fun p hp => by
    rw [UC6.groupPRank_eq_pRank]
    exact hext.three_le p hp
  have hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    fifteen_thirteen_a D h129 h61 hext.sig_nonempty hrk h125 (hWc 0 (by omega))
  have hβ : (D.k : ℕ∞) < betaN 0 D.M V := by
    obtain ⟨hδ, -⟩ := r16_35_holds D h61 hext h5 V₀ V L hV hS m hm
    calc (D.k : ℕ∞) < ((2 * m : ℕ) : ℕ∞) := by exact_mod_cast (by omega : D.k < 2 * m)
      _ ≤ deltaInf D.M V := hδ
      _ = deltaN (mSub V) D.M V := rfl
      _ ≤ deltaN 0 D.M V := deltaN_anti (Nat.zero_le _)
      _ ≤ betaN 0 D.M V := deltaN_le_betaN 0
  have h24 := trichotomy_of_lt D h126 h125
    (Sixteen24.k_lt_rParam_of_hyp125 D hSg h1219 hext h61 h125) hβ
  have hO : calO2 D.k D.M V₀ V = ∅ :=
    calO2_eq_empty D hSg h1219 h21 h22 h61 hext h5 h127 h38 hS hm (by omega)
  have hC : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M := by
    rcases h24 with h1 | h1 | h1
    · exact absurd hN h1
    · exact h1
    · rw [hO] at h1
      exact absurd h1 Set.not_nonempty_empty
  have hkm : m ≤ D.k := by
    by_contra h
    exact hC (centralizer_cClos_le_of_commutator_eq_bot D h125
      (Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hWc D.k (by omega))))
  have hk : D.k = 2 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · by_contra hV0
    exact hC (centralizer_cClos_le_of_ne_bot D h125 hV0 D.k)
  · rwa [hk] at hC

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
