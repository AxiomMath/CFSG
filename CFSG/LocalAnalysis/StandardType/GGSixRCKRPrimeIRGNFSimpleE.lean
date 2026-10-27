module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
  CFSG.ClassicalInvolution.ModelFacts
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgSE_adj_E6 (n f : ℕ)
    {a b : Fin 6}
    (hab : Tag.cartan .E6 a b = -1) (hba : Tag.cartan .E6 b a = -1) :
    GGSimpleConj (ggU .E6 n f).D a b := by
  refine ggSimpleConj_of_cartan_eq ?_ ?_
  · rw [ggU_cartan_E6]; exact hab
  · rw [ggU_cartan_E6]; exact hba

private theorem irgSE_adj_E7 (n f : ℕ)
    {a b : Fin 7}
    (hab : Tag.cartan .E7 a b = -1) (hba : Tag.cartan .E7 b a = -1) :
    GGSimpleConj (ggU .E7 n f).D a b := by
  refine ggSimpleConj_of_cartan_eq ?_ ?_
  · rw [ggU_cartan_E7]; exact hab
  · rw [ggU_cartan_E7]; exact hba

private theorem irgSE_adj_E8 (n f : ℕ)
    {a b : Fin 8}
    (hab : Tag.cartan .E8 a b = -1) (hba : Tag.cartan .E8 b a = -1) :
    GGSimpleConj (ggU .E8 n f).D a b := by
  refine ggSimpleConj_of_cartan_eq ?_ ?_
  · rw [ggU_cartan_E8]; exact hab
  · rw [ggU_cartan_E8]; exact hba

private theorem irgSE_conj_E6 (n f : ℕ)
    (i j : Fin 6) :
    GGSimpleConj (ggU .E6 n f).D i j := by
  have h02 : GGSimpleConj (ggU .E6 n f).D (0 : Fin 6) (2 : Fin 6) :=
    irgSE_adj_E6 n f (by decide +kernel) (by decide +kernel)
  have h23 : GGSimpleConj (ggU .E6 n f).D (2 : Fin 6) (3 : Fin 6) :=
    irgSE_adj_E6 n f (by decide +kernel) (by decide +kernel)
  have h34 : GGSimpleConj (ggU .E6 n f).D (3 : Fin 6) (4 : Fin 6) :=
    irgSE_adj_E6 n f (by decide +kernel) (by decide +kernel)
  have h45 : GGSimpleConj (ggU .E6 n f).D (4 : Fin 6) (5 : Fin 6) :=
    irgSE_adj_E6 n f (by decide +kernel) (by decide +kernel)
  have h13 : GGSimpleConj (ggU .E6 n f).D (1 : Fin 6) (3 : Fin 6) :=
    irgSE_adj_E6 n f (by decide +kernel) (by decide +kernel)
  have h0 : ∀ k : Fin 6, GGSimpleConj (ggU .E6 n f).D (0 : Fin 6) k := by
    intro k
    fin_cases k
    · exact GGSimpleConj.refl _
    · exact h02.trans (h23.trans h13.symm)
    · exact h02
    · exact h02.trans h23
    · exact h02.trans (h23.trans h34)
    · exact h02.trans (h23.trans (h34.trans h45))
  exact (h0 i).symm.trans (h0 j)

private theorem irgSE_conj_E7 (n f : ℕ)
    (i j : Fin 7) :
    GGSimpleConj (ggU .E7 n f).D i j := by
  have h02 : GGSimpleConj (ggU .E7 n f).D (0 : Fin 7) (2 : Fin 7) :=
    irgSE_adj_E7 n f (by decide +kernel) (by decide +kernel)
  have h23 : GGSimpleConj (ggU .E7 n f).D (2 : Fin 7) (3 : Fin 7) :=
    irgSE_adj_E7 n f (by decide +kernel) (by decide +kernel)
  have h34 : GGSimpleConj (ggU .E7 n f).D (3 : Fin 7) (4 : Fin 7) :=
    irgSE_adj_E7 n f (by decide +kernel) (by decide +kernel)
  have h45 : GGSimpleConj (ggU .E7 n f).D (4 : Fin 7) (5 : Fin 7) :=
    irgSE_adj_E7 n f (by decide +kernel) (by decide +kernel)
  have h56 : GGSimpleConj (ggU .E7 n f).D (5 : Fin 7) (6 : Fin 7) :=
    irgSE_adj_E7 n f (by decide +kernel) (by decide +kernel)
  have h13 : GGSimpleConj (ggU .E7 n f).D (1 : Fin 7) (3 : Fin 7) :=
    irgSE_adj_E7 n f (by decide +kernel) (by decide +kernel)
  have h0 : ∀ k : Fin 7, GGSimpleConj (ggU .E7 n f).D (0 : Fin 7) k := by
    intro k
    fin_cases k
    · exact GGSimpleConj.refl _
    · exact h02.trans (h23.trans h13.symm)
    · exact h02
    · exact h02.trans h23
    · exact h02.trans (h23.trans h34)
    · exact h02.trans (h23.trans (h34.trans h45))
    · exact h02.trans (h23.trans (h34.trans (h45.trans h56)))
  exact (h0 i).symm.trans (h0 j)

private theorem irgSE_conj_E8 (n f : ℕ)
    (i j : Fin 8) :
    GGSimpleConj (ggU .E8 n f).D i j := by
  have h02 : GGSimpleConj (ggU .E8 n f).D (0 : Fin 8) (2 : Fin 8) :=
    irgSE_adj_E8 n f (by decide +kernel) (by decide +kernel)
  have h23 : GGSimpleConj (ggU .E8 n f).D (2 : Fin 8) (3 : Fin 8) :=
    irgSE_adj_E8 n f (by decide +kernel) (by decide +kernel)
  have h34 : GGSimpleConj (ggU .E8 n f).D (3 : Fin 8) (4 : Fin 8) :=
    irgSE_adj_E8 n f (by decide +kernel) (by decide +kernel)
  have h45 : GGSimpleConj (ggU .E8 n f).D (4 : Fin 8) (5 : Fin 8) :=
    irgSE_adj_E8 n f (by decide +kernel) (by decide +kernel)
  have h56 : GGSimpleConj (ggU .E8 n f).D (5 : Fin 8) (6 : Fin 8) :=
    irgSE_adj_E8 n f (by decide +kernel) (by decide +kernel)
  have h67 : GGSimpleConj (ggU .E8 n f).D (6 : Fin 8) (7 : Fin 8) :=
    irgSE_adj_E8 n f (by decide +kernel) (by decide +kernel)
  have h13 : GGSimpleConj (ggU .E8 n f).D (1 : Fin 8) (3 : Fin 8) :=
    irgSE_adj_E8 n f (by decide +kernel) (by decide +kernel)
  have h0 : ∀ k : Fin 8, GGSimpleConj (ggU .E8 n f).D (0 : Fin 8) k := by
    intro k
    fin_cases k
    · exact GGSimpleConj.refl _
    · exact h02.trans (h23.trans h13.symm)
    · exact h02
    · exact h02.trans h23
    · exact h02.trans (h23.trans h34)
    · exact h02.trans (h23.trans (h34.trans h45))
    · exact h02.trans (h23.trans (h34.trans (h45.trans h56)))
    · exact h02.trans (h23.trans (h34.trans (h45.trans (h56.trans h67))))
  exact (h0 i).symm.trans (h0 j)

theorem irg_simple_roots_conj_E
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8) {g : ℕ}
    (i j : Fin (ggU t 0 g).D.rank) :
    ∃ w : (coxeterMatrix (ggU t 0 g).D.isFiniteType).Group,
      weylAction (ggU t 0 g).D.isFiniteType w (Pi.single i 1) = Pi.single j 1 := by
  rcases ht with rfl | rfl | rfl
  · exact irgSE_conj_E6 0 g i j
  · exact irgSE_conj_E7 0 g i j
  · exact irgSE_conj_E8 0 g i j

end CFSG.StandardType.RCKRP
