module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inner
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Upper
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSevenClasses
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
import CFSG.RankThree.PartOne.K133H.G2Plane

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open

section Upper

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

private theorem degCountTw_le_three {e : ℕ} (he : 3 ≤ e) :
    CFSG.LieType.SeitzGeneration.degCountTw e ≤ 3 := by
  by_contra hlt
  rcases CFSG.HardMathSupport.Timmesfeld.CrossChar.degCountTw_ge_three (e := e) (by omega) with
    rfl | rfl | rfl
  · omega
  · omega
  · exact hlt (by decide)

private theorem w5I_three_le_orderOf_of_ne {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hc1 : orderOf ((2 : ZMod p) ^ f) ≠ 1) (hc2 : orderOf ((2 : ZMod p) ^ f) ≠ 2) :
    3 ≤ orderOf ((2 : ZMod p) ^ f) := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have h0 : (2 : ZMod p) ^ f ≠ 0 := pow_ne_zero f h2
  have hfin : orderOf ((2 : ZMod p) ^ f) ≠ 0 := by
    have : orderOf ((2 : ZMod p) ^ f) ∣ p - 1 :=
      orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h0)
    intro h
    rw [h, zero_dvd_iff] at this
    have := hp.two_le
    omega
  omega

theorem upper_twE6_gen
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hc1 : orderOf ((2 : ZMod p) ^ f) ≠ 1) (hc2 : orderOf ((2 : ZMod p) ^ f) ≠ 2) :
    Nat.card B ≤ p ^ 3 := by
  have hp := h.prime
  have hc := w5I_three_le_orderOf_of_ne hp h.ne_two hc1 hc2
  obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.Mult.exists_index_of_chevalley
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll Nat.prime_two (by decide)
        (h.model.chevalleyExceptionalModel (by decide))
  cases d with
  | twistedE6 Q =>
    obtain ⟨hQp, hQe⟩ := hn
    have hQc : Q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hQp, hQe]
    have hQ : ((Q.card : ℕ) : ZMod p) = (2 : ZMod p) ^ f := by rw [hQc]; push_cast; rfl
    have he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p) := by rw [hQ]; exact hc
    have hpq : p ≠ Q.p := by rw [hQp]; exact h.ne_two
    have hp3 : p ≠ 3 := by
      have := CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.five_le_of_three_le_orderOf hp he
      omega
    refine h.card_le_of_inner (h.inner_twE6 (Or.inl hp3)) e (k := 3) fun F hF => ?_
    exact (CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.card_le_cat_twistedE6
      hv hp hpq he hF).trans
      (Nat.pow_le_pow_right hp.pos (max_le (by norm_num) (degCountTw_le_three he)))
  | _ => exact hn.elim

end Upper

end CFSG.StandardType.TableCRes

end
