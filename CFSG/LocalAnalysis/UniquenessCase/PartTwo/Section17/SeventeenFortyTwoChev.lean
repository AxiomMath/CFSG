module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple


public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem thin8_map_conj {H : Subgroup G} (h : F08.Thin8 H) (g : G) :
    F08.Thin8 (H.map (MulAut.conj g).toMonoidHom) := by
  intro p hp hp2
  rw [CFSG.Quasithin.E3.pRank_map_mulEquiv' (MulAut.conj g) hp H]
  exact h p hp hp2

theorem false_of_concl_of_unique_thin {D : Data G} {L X : Subgroup G} {p : ℕ}
    (hL : L ∈ calC D.M) (hX : X = conjClosure D.M L)
    (hthin : F08.Thin8 L) (hm3 : CFSG.Open.pRank 3 L = 1)
    (huniq : ∀ K ∈ calC D.M, F08.Thin8 K → CFSG.Open.pRank 3 K = 1 → K = L)
    (hcounter : ¬ Concl17_42 D L X p) : False := by
  have hXL : X = L := by
    by_contra hne
    have hne' : conjClosure D.M L ≠ L := by
      intro h
      exact hne (hX.trans h)
    obtain ⟨K, hKmem, hKL⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne hne'
    obtain ⟨g, hgM, hKeq⟩ := hKmem
    have hKcal : K ∈ calC D.M := by
      have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (K := L)
        Subgroup.le_normalizer hL (m := g⁻¹) (D.M.inv_mem hgM)
      have hconj : uniqueFourConj g⁻¹ L = K := by
        rw [uniqueFourConj, hKeq]
        simp
      rwa [hconj] at h
    have hKthin : F08.Thin8 K := by
      rw [hKeq]
      exact thin8_map_conj hthin g
    have hKm3 : CFSG.Open.pRank 3 K = 1 := by
      rw [hKeq, CFSG.Quasithin.E3.pRank_map_mulEquiv' (MulAut.conj g) Nat.prime_three L, hm3]
    exact hKL (huniq K hKcal hKthin hKm3)
  exact hcounter (Concl17_42.of_p1 (Or.inl (hXL ▸ hthin)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
