module

public import CFSG.Quasithin.EmptyFaithful.S146zYZSzCount
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

namespace CFSG.Quasithin.S146zY.SzNoFive

theorem szSylowData_of_equiv {K : Type} [Group K] [Finite K]
    {a : ℕ} (ha : 1 ≤ a) (e : K ≃* CFSG.Open.Sz a) (S : Sylow 2 K) :
    SzSylowData K (2 ^ (2 * a + 1)) S := by
  obtain ⟨T, β, hβ, -⟩ :=
    CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiPointAction_cosets_of_mulEquiv_sz a e S
  have hstab : MulAction.stabilizer K
      (QuotientGroup.mk 1 : K ⧸ Subgroup.normalizer ((S : Subgroup K) : Set K)) =
      Subgroup.normalizer ((S : Subgroup K) : Set K) := MulAction.stabilizer_quotient _
  have hcardK : Nat.card K =
      (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨by omega, dvd_pow_self 2 (by omega), hcardK, hβ.card_U, ?_, ?_⟩
  · have h1 := Subgroup.card_mul_index (Subgroup.normalizer ((S : Subgroup K) : Set K))
    have h2 : (Subgroup.normalizer ((S : Subgroup K) : Set K)).index =
        (2 ^ (2 * a + 1)) ^ 2 + 1 := hβ.card_eq
    rw [h2, hcardK] at h1
    refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ (2 * a + 1)) ^ 2 + 1) ?_
    rw [h1]
    ring
  · have h := hβ.stronglyEmbedded
    rw [hstab] at h
    exact h.2.2

end CFSG.Quasithin.S146zY.SzNoFive
