module

public import CFSG.RankThree.PartOne.KC1.Pair
public import CFSG.RankThree.PartOne.KE8F.E8Lat
public import CFSG.RankThree.PartOne.KE.E8ClassLists

public noncomputable section

namespace CFSG.RankThree.PartOne.KC1

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE8F
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chainRoot)
open scoped MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def e8a4bList : Fin 5 → List ℤ :=
  ![[1, 0, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 0, 1, 1, 1, 0, 0],
    [0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]

theorem e8a4Weight_eq_toVec (i : Fin 5) : e8a4Weight i = toVec Tag.E8.rank (e8a4bList i) := by
  fin_cases i <;> (funext k; fin_cases k <;> rfl)

@[expose] def e8a4rootL (W : List (List ℤ)) (i j : Fin 5) : List ℤ :=
  lmulVec Tag.E8.rank W (vadd Tag.E8.rank (e8a4bList i) (vneg Tag.E8.rank (e8a4bList j)))

theorem sigmaRootE8A4_wordProd (w : List (Fin Tag.E8.rank)) (i j : Fin 5) :
    sigmaRootE8A4 ((coxeterSystem Tag.E8).wordProd w) i j =
      toVec Tag.E8.rank (e8a4rootL (e8wl w) i j) := by
  rw [e8a4rootL, toVec_lmulVec, toVec_vadd, toVec_vneg, Matrix.mulVec_add, Matrix.mulVec_neg,
    ← wordMat_e8wl, ← e8a4Weight_eq_toVec, ← e8a4Weight_eq_toVec, sigmaRootE8A4, wbE8A4, wbE8A4,
    wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec, sub_eq_add_neg]

theorem e8P4_weylImage' (u : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd e8P4WW • u = e8P4V *ᵥ u := by
  rw [wordProd_smul_eq_wordMat_mulVec, e8P4_wordMat]

theorem e8P4_double (γ : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd e8P4WW • ((coxeterSystem Tag.E8).wordProd e8P4WW • γ) = -γ := by
  rw [e8P4_weylImage', e8P4_weylImage', Matrix.mulVec_mulVec, e8P4V_sq, Matrix.neg_mulVec,
    Matrix.one_mulVec]

@[expose] def e2List : List ℤ := [0, 1, 0, 0, 0, 0, 0, 0]

theorem single_e2 : (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ) = toVec Tag.E8.rank e2List := by
  funext k
  fin_cases k <;> rfl

theorem phiExp_toVec (l : List ℤ) :
    phiExp (toVec Tag.E8.rank l) = ∑ j : Fin Tag.E8.rank, aVec j * vget l j := rfl

theorem wordProd_ww_append_smul (ω : List (Fin Tag.E8.rank)) (x : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd (e8P4WW ++ ω) • x =
      e8P4V *ᵥ ((coxeterSystem Tag.E8).wordProd ω • x) := by
  rw [CoxeterSystem.wordProd_append, mul_smul, e8P4_weylImage']

@[expose] def mkPairDatum (ω w : List (Fin Tag.E8.rank)) (c : ℕ)
    (horth : ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
      toVec Tag.E8.rank (e8a4rootL (e8wl ω) i j) ⬝ᵥ
        (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank
          (lmulVec Tag.E8.rank e8P4VList (e8a4rootL (e8wl ω) k l))) = 0)
    (hback : lmulVec Tag.E8.rank e8P4VList (lmulVec Tag.E8.rank (e8wl ω)
      (lmulVec Tag.E8.rank (e8wl w) e2List)) = lmulVec Tag.E8.rank (e8wl ω) e2List)
    (hexp : ¬ (5 : ℤ) ∣ (∑ j : Fin Tag.E8.rank, aVec j * vget e2List j) +
      (c : ℤ) * ∑ j : Fin Tag.E8.rank, aVec j *
        vget (lmulVec Tag.E8.rank (e8wl w) e2List) j) :
    PairDatum e8P4WW where
  ω := ω
  w := w
  c := c
  hsq := e8P4_double
  horth := fun i j k l hij hkl => by
    rw [wordProd_ww_append_smul, ← sigmaRootE8A4_eq_smul, ← sigmaRootE8A4_eq_smul,
      sigmaRootE8A4_wordProd, sigmaRootE8A4_wordProd, e8P4V_eq, ← toVec_lmulVec]
    exact horth i j k l hij hkl
  hback := by
    rw [wordProd_ww_append_smul, single_e2, wordProd_smul_toVec, wordProd_smul_toVec,
      wordProd_smul_toVec, e8P4V_eq, ← toVec_lmulVec, hback]
  hexp := by
    rw [single_e2, wordProd_smul_toVec, phiExp_toVec, phiExp_toVec]
    exact hexp

@[expose] def omega2 : List (Fin Tag.E8.rank) := [1, 3, 4, 5, 0, 2, 3, 1]

@[expose] def back2 : List (Fin Tag.E8.rank) := [7, 6, 5, 3, 4, 1, 3]

theorem orth2 : ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
    toVec Tag.E8.rank (e8a4rootL (e8wl omega2) i j) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank
        (lmulVec Tag.E8.rank e8P4VList (e8a4rootL (e8wl omega2) k l))) = 0 := by
  decide +kernel

theorem hback2 : lmulVec Tag.E8.rank e8P4VList (lmulVec Tag.E8.rank (e8wl omega2)
      (lmulVec Tag.E8.rank (e8wl back2) e2List)) = lmulVec Tag.E8.rank (e8wl omega2) e2List := by
  decide +kernel

theorem hexp2 : ¬ (5 : ℤ) ∣ (∑ j : Fin Tag.E8.rank, aVec j * vget e2List j) +
      ((2 : ℕ) : ℤ) * ∑ j : Fin Tag.E8.rank, aVec j *
        vget (lmulVec Tag.E8.rank (e8wl back2) e2List) j := by
  decide +kernel

@[expose] def pairDatum2 : PairDatum e8P4WW := mkPairDatum omega2 back2 2 orth2 hback2 hexp2

@[expose] def omega3 : List (Fin Tag.E8.rank) := [7, 6, 3, 4, 5, 2, 3, 1]

@[expose] def back3 : List (Fin Tag.E8.rank) := [6, 5, 3, 4, 1, 3, 1]

theorem orth3 : ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
    toVec Tag.E8.rank (e8a4rootL (e8wl omega3) i j) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank
        (lmulVec Tag.E8.rank e8P4VList (e8a4rootL (e8wl omega3) k l))) = 0 := by
  decide +kernel

theorem hback3 : lmulVec Tag.E8.rank e8P4VList (lmulVec Tag.E8.rank (e8wl omega3)
      (lmulVec Tag.E8.rank (e8wl back3) e2List)) = lmulVec Tag.E8.rank (e8wl omega3) e2List := by
  decide +kernel

theorem hexp3 : ¬ (5 : ℤ) ∣ (∑ j : Fin Tag.E8.rank, aVec j * vget e2List j) +
      ((3 : ℕ) : ℤ) * ∑ j : Fin Tag.E8.rank, aVec j *
        vget (lmulVec Tag.E8.rank (e8wl back3) e2List) j := by
  decide +kernel

@[expose] def pairDatum3 : PairDatum e8P4WW := mkPairDatum omega3 back3 3 orth3 hback3 hexp3

theorem pairDatum2_c : pairDatum2.c = 2 := rfl

theorem pairDatum3_c : pairDatum3.c = 3 := rfl

end CFSG.RankThree.PartOne.KC1
