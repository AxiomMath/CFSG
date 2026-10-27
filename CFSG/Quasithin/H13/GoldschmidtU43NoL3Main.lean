module

public import CFSG.Quasithin.H13.GoldschmidtU43NoL3Chk
public import CFSG.Quasithin.H13.GoldschmidtU43NoL3Grp
public import CFSG.LieType.Multipliers.U43
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.LieType.Multipliers.U43

theorem card_of_lieModel_psl_three_two {Y : Type} [Group Y]
    (h : CFSG.Blueprint.LieModel Y .PSL 3 2 1) : Nat.card Y = 168 :=
  CFSG.Blueprint.LieModel.card_psl_three_two h

theorem factorization_seven_X₀ : (Nat.card X₀).factorization 7 = 1 := by
  rw [card_X₀, Nat.factorization_def _ (by norm_num : Nat.Prime 7)]
  decide +kernel

theorem stmtU43NoL32Local_of_checks (hck : noSevenCheck 820 tabA tabB = true)
    (ho : orbCheck 820 tabA tabB = true) (hh : h4Check 820 tabA tabB rels4Codes = true)
    (hs : sylCheck 820 tabA tabB = true) : StmtU43NoL32Local := by
  intro G _ _ T L hG hT hL hPSL
  obtain ⟨e⟩ := nonempty_mulEquiv_X₀ hG
  obtain ⟨hord7, hno⟩ := x7_involution hck ho hh (x0OneClass_of_checks ho hs)
  have hQ : ∀ x f : G, orderOf x = 7 → orderOf f = 2 →
      ∃ i : ℕ, ¬ (f * (x ^ i * f * (x ^ i)⁻¹) = (x ^ i * f * (x ^ i)⁻¹) * f) := by
    intro x f hx hf
    obtain ⟨i, hi⟩ := exists_noncommute_pow hord7 factorization_seven_X₀
      (x := e x) (f := e f) (by rwa [MulEquiv.orderOf_eq]) (by rwa [MulEquiv.orderOf_eq]) hno
    refine ⟨i, fun hc => hi ?_⟩
    have := congrArg e hc
    simpa only [map_mul, map_pow, map_inv] using this
  have h168 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := card_of_lieModel_psl_three_two hPSL
  have h7 : 7 ∣ Nat.card ↥L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), h168]
    exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 h7
  obtain ⟨-, -, -, hA1⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 (L ⊔ T)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)
  have hyLT : (y : G) ∈ L ⊔ T := (le_sup_left : L ≤ L ⊔ T) y.2
  have hn : (y : G) ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) hyLT
  exact no_seven_normalizes_two_group hQ (by rw [Subgroup.orderOf_coe]; exact hy) hAp hA1 hn

end CFSG.Quasithin.H13.U43
