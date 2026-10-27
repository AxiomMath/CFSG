module

public import CFSG.LocalAnalysis.StandardType.GGPZMultCore
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

theorem ggPZMult_A
    {Y : Type} [Group Y] {p l n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hΛ : LargeEvenInLambda2 ⟨.A, l, n⟩) (hperf : commutator Y = ⊤)
    (hlab : GGHasLabel ⟨.A, l, n⟩ (Y ⧸ Subgroup.center Y))
    (hpl : ¬ p ∣ l + 1) : ¬ p ∣ Nat.card (Subgroup.center Y) := by
  have hΛ' := hΛ
  dsimp only [LargeEvenInLambda2] at hΛ'
  have hl1 : 1 ≤ l := hΛ'.2.1
  have hn1 : 1 ≤ n := hΛ'.1
  have hbig : l = 1 → 2 ≤ n := hΛ'.2.2
  have hadm : StatedLieAdmissible .PSL (l + 1) 2 n :=
    ⟨Nat.prime_two, hn1, by omega,
      fun h => by
        simp only [Prod.mk.injEq] at h
        have hn2 : 2 ≤ n := hbig (by omega)
        have h4 : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        omega,
      fun h => by
        simp only [Prod.mk.injEq] at h
        have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
        rw [h.2] at hdvd
        norm_num at hdvd⟩
  unfold GGHasLabel at hlab
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hlab
  unfold LargeEvenRecipeLinear at hlab
  obtain ⟨K, hK, hKfin, hKcard, ⟨e⟩⟩ := hlab
  have hmod : StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K))
      .PSL (l + 1) 2 n :=
    statedClassicalModel_linear (l + 1) n hKcard hadm
  have hmod' : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL (l + 1) 2 n :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmod
  obtain ⟨-, ⟨e'⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hmod'
  refine ggPZMult_not_dvd_of_row hperf (Fact.out : p.Prime) hp2 ⟨e'⟩ ?_
  simp only [genericOrders, Nat.mul_one]
  intro h
  exact hpl (h.trans (Nat.gcd_dvd_left (l + 1) (2 ^ n - 1)))

end CFSG.StandardType

end
