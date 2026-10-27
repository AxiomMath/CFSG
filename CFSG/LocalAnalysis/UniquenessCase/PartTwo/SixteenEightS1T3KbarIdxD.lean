module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxDB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxDC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_normalizer_index_le_two (h : ThreeNat A L T) {J₀ : Subgroup W}
    (hJ₀ : J₀ ∈ irrSet L) (g : ↥A →* MulAut (↥J₀ ⧸ (J₀ ⊓ fixV L).subgroupOf J₀))
    (hg : ∀ l : ↥A, (l : MulAut W) ∈ L → ∀ u : ↥J₀, ∀ hu : (l : MulAut W) (u : W) ∈ J₀,
      g l (QuotientGroup.mk u) = QuotientGroup.mk ⟨(l : MulAut W) (u : W), hu⟩) :
    (((L.subgroupOf A).map g).subgroupOf
      (Subgroup.normalizer (((L.subgroupOf A).map g) :
        Set (MulAut (↥J₀ ⧸ (J₀ ⊓ fixV L).subgroupOf J₀))))).index ≤ 2 := by
  have hq : CFSG.Open.IsQuasisimple ↥L := h.quasi
  obtain ⟨n, hcases⟩ := h.natural_of_mem_irrSet hJ₀
  let gL : ↥L →* MulAut (↥J₀ ⧸ (J₀ ⊓ fixV L).subgroupOf J₀) :=
    g.comp (Subgroup.inclusion h.le)
  have hmapg : (⊤ : Subgroup ↥L).map gL = (L.subgroupOf A).map g := by
    change (⊤ : Subgroup ↥L).map (g.comp (Subgroup.inclusion h.le)) = (L.subgroupOf A).map g
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.inclusion_range]
  have finish : s16t3_normIdx ((⊤ : Subgroup ↥L).map gL) →
      (((L.subgroupOf A).map g).subgroupOf
        (Subgroup.normalizer (((L.subgroupOf A).map g) :
          Set (MulAut (↥J₀ ⧸ (J₀ ⊓ fixV L).subgroupOf J₀))))).index ≤ 2 := by
    intro hN
    rw [hmapg] at hN
    exact s16t3_index_le_two_of_normIdx hN
  rcases hcases with ⟨hIs, hsum⟩ | ⟨hIs, hsum⟩ | ⟨hIs, hsum⟩ | ⟨hIs, hsum⟩ | ⟨hIs, hsum⟩
  · obtain ⟨K, hKfield, hKfin, hKcard, hReal⟩ := s16t3_sumOfNat_one hsum
    letI := hKfield
    letI := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hR⟩ := hReal
    have hgL : ∀ (γ : ↥(StatedSL n K)) (u : ↥J₀),
        ∀ hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J₀,
        gL (π γ) (QuotientGroup.mk u) =
          QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ := by
      intro γ u hu
      exact hg (Subgroup.inclusion h.le (π γ)) (π γ).2 u hu
    exact finish (s16t3_normIdx_of_realizes_nat hK2 (s16t3_normIdx_sl hK2 n) hR gL hgL)
  · obtain ⟨-, K, hKfield, hKfin, hKcard, hReal⟩ := s16t3_sumOfNat_one hsum
    letI := hKfield
    letI := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    obtain ⟨π, hR⟩ := hReal
    have hgL : ∀ (γ : ↥(StatedSp (n / 2) K)) (u : ↥J₀),
        ∀ hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J₀,
        gL (π γ) (QuotientGroup.mk u) =
          QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ := by
      intro γ u hu
      exact hg (Subgroup.inclusion h.le (π γ)) (π γ).2 u hu
    exact finish
      (s16t3_normIdx_of_realizes_nat hK2 (s16t3_normIdx_sp hK2 (n / 2)) hR gL hgL)
  · obtain ⟨-, K, hKfield, hKfin, hKcard, hReal⟩ := s16t3_sumOfNat_one hsum
    letI := hKfield
    letI := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    have hm3 : 3 ≤ n / 2 := by have := s16k_six_le_of_isOmegaPlus hq hIs; omega
    obtain ⟨π, hR⟩ := hReal
    have hgL : ∀ (γ : ↥(StatedOmega (StatedQuadPlus (n / 2) K))) (u : ↥J₀),
        ∀ hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J₀,
        gL (π γ) (QuotientGroup.mk u) =
          QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ := by
      intro γ u hu
      exact hg (Subgroup.inclusion h.le (π γ)) (π γ).2 u hu
    exact finish
      (s16t3_normIdx_of_realizes_nat hK2 (s16t3_normIdx_omplus hK2 hm3) hR gL hgL)
  · obtain ⟨hEven, K, hKfield, hKfin, b, c, hKcard, hpoly, hReal⟩ :=
      s16t3_sumOfNat_one hsum
    letI := hKfield
    letI := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    have hm2 : 2 ≤ n / 2 := by have := s16k_four_le_of_isOmegaMinus hq hIs; omega
    obtain ⟨π, hR⟩ := hReal
    have hgL : ∀ (γ : ↥(StatedOmega (StatedQuadMinus (n / 2) K b c))) (u : ↥J₀),
        ∀ hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J₀,
        gL (π γ) (QuotientGroup.mk u) =
          QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ := by
      intro γ u hu
      exact hg (Subgroup.inclusion h.le (π γ)) (π γ).2 u hu
    by_cases hm3 : 3 ≤ n / 2
    · exact finish
        (s16t3_normIdx_of_realizes_nat hK2 (s16t3_normIdx_omminus hK2 hm3 hpoly) hR gL hgL)
    · have hn4 : n = 4 := by
        obtain ⟨k, hk⟩ := hEven
        have h2 : n / 2 = 2 := by omega
        omega
      subst n
      exact finish
        (s16t3_normIdx_of_realizes_nat hK2 (s16t3_normIdx_omminus_four hK2 hpoly) hR gL hgL)
  · have hn5 : 5 ≤ n := s16k_five_le_of_isAlt hq hIs
    obtain ⟨π, hR⟩ := (show (FFModel.altDn n).Realizes L J₀ (J₀ ⊓ fixV L) from
      s16t3_sumOfNat_one hsum)
    have hgL : ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥J₀),
        ∀ hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J₀,
        gL (π γ) (QuotientGroup.mk u) =
          QuotientGroup.mk ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ := by
      intro γ u hu
      exact hg (Subgroup.inclusion h.le (π γ)) (π γ).2 u hu
    exact finish (s16t3_normIdx_altDn hn5 hR gL hgL)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
