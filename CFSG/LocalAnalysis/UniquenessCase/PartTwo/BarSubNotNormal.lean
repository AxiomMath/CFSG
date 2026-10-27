module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.HypSeventeenFiftyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem barSub_ne_bot_of_not_normal {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h117 : C117 D V₀ V) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hN : ¬ D.M ≤ normalizer (L : Set G)) :
    barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
  intro hbot
  have hp := hV.pairFacts
  have hLct : L ≤ F11.CTilde D.M V₀ V :=
    (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV.isElemAbelian
      hp.le_normalizer hp.le_normalizer₀ hL.1.le).1 hbot
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := by
    intro x hx
    simp only [F11.CTilde, Subgroup.mem_iInf] at hx
    exact (hx 1 V.one_mem).1
  have hsub : IsSubnormal L (F11.CTilde D.M V₀ V) := by
    have h := hL.1.inf (F11.CTilde D.M V₀ V)
    rwa [inf_eq_left.2 hLct, inf_eq_right.2 hCM] at h
  have hmem : L ∈ calC (F11.CTilde D.M V₀ V) := ⟨hsub, hL.2.1, hL.2.2⟩
  exact hN (h117 L hmem).1

theorem uniqueMax_conjClosure_of_case34 (D : Data G) (h61 : UC6.R6_1 D)
    {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X : Subgroup G}
    (h8100 : F08.Hyp8100 D L n r p A X)
    (hcase : F08.Case8100ThreeR D L p X ∨ F08.Case8100FourR D L p X) :
    UniqueMax D.M X := by
  obtain ⟨hcalC, hne, -, -, -, hp, -, -, hprod, -⟩ := h8100
  have hL0 := hcalC 0
  have hset : conjSetOf D.M (L 0) = {L 0, L 1} := by
    rcases hcase with h3 | h4
    · exact h3.1.symm
    · exact h4.1.symm
  have hdata : (IsL2 (Bar2 (L 0)) 3 ∧ p = 3) ∨ (IsSz (Bar2 (L 0)) 5 ∧ p = 5) := by
    rcases hcase with h3 | h4
    · exact Or.inl ⟨h3.2.1, h3.2.2.1⟩
    · exact Or.inr ⟨h4.2.1, h4.2.2.1⟩
  have hpc : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hc2 : (conjSetOf D.M (L 0)).ncard = 2 := by
    rw [hset]
    exact Set.ncard_pair hne
  have hpIdx : p ∣ (Subgroup.center (Bar2 (L 0))).index := by
    have : Fact p.Prime := ⟨hpc⟩
    have hcent : Subgroup.center (Bar2 (L 0)) = ⊥ := by
      rcases hdata with ⟨hL2, -⟩ | ⟨hSz, -⟩
      · have : IsSimpleGroup (Bar2 (L 0)) :=
          S17.isSimpleGroup_bar2_of_isL2_or_isSz (Or.inl hL2)
        exact uc22p21k_center_eq_bot hL0.2.2
      · have : IsSimpleGroup (Bar2 (L 0)) :=
          S17.isSimpleGroup_bar2_of_isL2_or_isSz (Or.inr hSz)
        exact uc22p21k_center_eq_bot hL0.2.2
    have hbd : p ∣ Nat.card (Bar2 (L 0)) := by
      rcases hdata with ⟨hL2, rfl⟩ | ⟨hSz, rfl⟩
      · exact S17.dvd_card_bar2_of_isL2 hL2 (by norm_num)
      · exact S17.dvd_card_bar2_of_isSz hSz (by norm_num)
    rwa [hcent, Subgroup.index_bot]
  have hrank : 2 ≤ CFSG.Open.pRank p (conjClosure D.M (L 0)) :=
    UC22.P2214R.two_le_pRank_pair hL0 hc2 hpc hp2 hpIdx
  obtain ⟨E, hEX, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hpc.one_lt (conjClosure D.M (L 0))
  have hE2 : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hpc.pos hrank
  have hEnc : ¬ IsCyclic E := by
    have : Fact p.Prime := ⟨hpc⟩
    exact CFSG.LocalAnalysis.GLTheoremB.not_isCyclic_of_isElemAbelian hEel hE2
  have hEc : conjClosure D.M (L 0) ≤ D.M :=
    (uc22p22u_conjClosure_isProd (M := D.M) (X := D.M) (K := L 0)
      le_rfl Subgroup.le_normalizer hL0).1
  have hU : UniqueMax D.M E := h61 p hp E (hEX.trans hEc) hEel.isPGroup hEnc
  have hUc : UniqueMax D.M (conjClosure D.M (L 0)) :=
    uc22p22u_uniqueMax_mono D hEX hEc hU
  have hclosure : conjClosure D.M (L 0) = L 0 ⊔ L 1 := by
    rw [conjClosure, hset, iSup_insert, iSup_singleton]
  have hXsup : X = L 0 ⊔ L 1 := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (L 0 : Set G) * (L 1 : Set G) := by
        rw [← hprod]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact (L 0 ⊔ L 1).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    · refine sup_le ?_ ?_
      · intro a ha
        have hmem : a ∈ (X : Set G) := by
          rw [hprod]
          exact ⟨a, ha, 1, (L 1).one_mem, by simp⟩
        exact hmem
      · intro b hb
        have hmem : b ∈ (X : Set G) := by
          rw [hprod]
          exact ⟨1, (L 0).one_mem, b, hb, by simp⟩
        exact hmem
  rw [hXsup, ← hclosure]
  exact hUc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
