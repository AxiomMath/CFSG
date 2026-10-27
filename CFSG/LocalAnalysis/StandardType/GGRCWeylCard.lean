module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeD
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

lemma l05nK3a_card_reindex_le {ι ι' : Type} [Fintype ι] {M : CoxeterMatrix ι}
    (N : CoxeterMatrix ι') (e : ι' ≃ ι) {B : ℕ} (heq : M = N.reindex e)
    (hcard : Nat.card N.Group ≤ B) : Nat.card M.Group ≤ B := by
  subst heq
  calc Nat.card (N.reindex e).Group = Nat.card N.Group :=
        Nat.card_congr (N.reindexGroupEquiv e).toEquiv
    _ ≤ B := hcard

lemma l05nK3a_card_coxeterA (n : ℕ) :
    Nat.card (CoxeterMatrix.A n).Group = (n + 1).factorial := by
  rw [← coxeterMatrix_isFiniteType_A_eq n]
  rw [← Nat.card_congr (typeAWeylEquiv n).toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

lemma l05nK3a_coxeterA_le (n : ℕ) :
    Nat.card (CoxeterMatrix.A n).Group ≤ 2 ^ n * n.factorial := by
  rw [l05nK3a_card_coxeterA n]
  calc (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
    _ ≤ 2 ^ n * n.factorial :=
        Nat.mul_le_mul_right n.factorial
          (Nat.succ_le_iff.mpr Nat.lt_two_pow_self)

lemma l05nK3a_coxeterD_le (r : ℕ) (hr : 2 ≤ r) :
    Nat.card (ggCoxeterMatrixD r).Group ≤ 2 ^ r * r.factorial := by
  calc Nat.card (ggCoxeterMatrixD r).Group ≤ 2 ^ (r - 1) * r.factorial :=
        SpJoinRefl.card_coxeterD_le r hr
    _ ≤ 2 ^ r * r.factorial :=
        Nat.mul_le_mul_right r.factorial
          (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le r 1))

private theorem l05nK3a_ord_card_coxeterE8 :
    Nat.card (CoxeterMatrix.E₈).Group = 696729600 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E8 = CartanMatrix.E 8 :=
    CFSG.LieType.Chevalley.cartanE_eq 8
  have hmat : CoxeterMatrix.E₈ = CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E8) := by
    have h := coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E8)
      (M := CoxeterMatrix.E₈)
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E8)
      (hc.symm ▸ ggIntCartan_E₈)
    exact h.symm
  have hgroup : CFSG.LieType.Chevalley.WeylGroup .E8 = (CoxeterMatrix.E₈).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E8) =
      Nat.card (CoxeterMatrix.E₈).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact NoOffExc.card_weyl_E8

theorem ggRC_card_weyl_le
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : CoxeterMatrix ι)
    (hM : GGIsWeylMatrix M) (hr : 8 ≤ Fintype.card ι) :
    Nat.card M.Group ≤ 2 ^ Fintype.card ι * (Fintype.card ι).factorial ∨
      (Fintype.card ι = 8 ∧ Nat.card M.Group = 696729600) := by
  rcases hM with ⟨n, e, hn, hAD⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF4⟩ |
    ⟨e, hG2⟩
  · rcases hAD with hA | hBD
    ·
      have hcardI : Fintype.card ι = n := by
        rw [← Fintype.card_congr e, Fintype.card_fin]
      left
      rw [hcardI]
      exact l05nK3a_card_reindex_le (CoxeterMatrix.A n) e hA (l05nK3a_coxeterA_le n)
    · rcases hBD with ⟨hn2, hB⟩ | ⟨hn4, hD⟩
      ·
        have hcardI : Fintype.card ι = n := by
          rw [← Fintype.card_congr e, Fintype.card_fin]
        left
        rw [hcardI]
        exact l05nK3a_card_reindex_le (CoxeterMatrix.B n) e hB (card_coxeterB_le n)
      ·
        have hcardI : Fintype.card ι = n := by
          rw [← Fintype.card_congr e, Fintype.card_fin]
        left
        rw [hcardI]
        exact l05nK3a_card_reindex_le (ggCoxeterMatrixD n) e hD
          (l05nK3a_coxeterD_le n (by omega))
  ·
    exfalso
    have h6 : Fintype.card ι = 6 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  ·
    exfalso
    have h7 : Fintype.card ι = 7 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  ·
    right
    refine ⟨?_, ?_⟩
    · rw [← Fintype.card_congr e, Fintype.card_fin]
    · rw [hE8, Nat.card_congr (CoxeterMatrix.E₈.reindexGroupEquiv e).toEquiv]
      exact l05nK3a_ord_card_coxeterE8
  ·
    exfalso
    have h4 : Fintype.card ι = 4 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  ·
    exfalso
    have h2 : Fintype.card ι = 2 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega

end CFSG.StandardType
