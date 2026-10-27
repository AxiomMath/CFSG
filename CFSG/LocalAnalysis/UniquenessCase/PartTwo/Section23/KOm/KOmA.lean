module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusCoords
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusCore
public import CFSG.GroupTheory.GL52.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

theorem kOmA_holds : KOmA := by
  intro W _ _ H n S Tstar hF E hET hE hcard
  by_contra hE1
  obtain ⟨K, hKfield, hKfin, hKchar, b, c, hKcard, hirr, e, -, hT, -⟩ :=
    KOm.exists_minusCoords hF
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  classical
  set Y : Subgroup (GL ιM K) :=
    KOm.isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) ⊓
      Subgroup.normalizer
        ((StatedOmega (StatedQuadMinus 2 K b c) : Subgroup (GL ιM K)) : Set (GL ιM K))
    with hY
  have hXY : E.map (MulAut.congr e).toMonoidHom ≤ Y.map (s16gNatHom ιM K) := by
    rw [hY]
    exact (Subgroup.map_mono hET).trans hT
  obtain ⟨E', hE'Y, -, ⟨eE⟩, hfixcard⟩ :=
    KOm.exists_glModel (X := E) (Y := Y) e hXY
  have hE'fix : E' ≤ KOm.isoFix (StatedQuadMinus 2 K b c) (KTabC.e1M K) := by
    rw [hY] at hE'Y
    exact hE'Y.trans inf_le_left
  have hEcard : Nat.card ↥E = Nat.card ↥E' := Nat.card_congr eE.toEquiv
  have hE'ne : E' ≠ ⊥ := by
    intro hbot
    apply hE1
    have h1 : Nat.card ↥E' = 1 := by rw [hbot, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq E (by rw [hEcard, h1])
  have hE'2 : IsPGroup 2 ↥E' :=
    IsPGroup.of_equiv (IsElemAbelian.isPGroup hE) eE
  have hbound := KOm.card_mul_card_fix_le_two_mul (K := K) hirr hE'fix hE'2 hE'ne
  have hι : Nat.card ιM = 4 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_sum]
  have hW : Nat.card W = Nat.card K ^ 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hι]
  have hq : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hF.1
  have hlt : 2 * Nat.card K ^ 3 < Nat.card K ^ 4 := by
    have h2 : 2 < Nat.card K := by omega
    calc 2 * Nat.card K ^ 3 < Nat.card K * Nat.card K ^ 3 :=
          Nat.mul_lt_mul_of_pos_right h2 (pow_pos (by omega) 3)
      _ = Nat.card K ^ 4 := by ring
  have hle : Nat.card K ^ 4 ≤ 2 * Nat.card K ^ 3 := by
    calc Nat.card K ^ 4 = Nat.card W := hW.symm
      _ ≤ Nat.card ↥E * Nat.card ↥(CFSG.Quasithin.fixV E) := hcard
      _ = Nat.card ↥E' *
            Nat.card {v : ιM → K // ∀ g ∈ E', (g : Matrix ιM ιM K) *ᵥ v = v} := by
            rw [hEcard, hfixcard]
      _ ≤ 2 * Nat.card K ^ 3 := hbound
  exact (not_lt_of_ge hle) hlt

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
