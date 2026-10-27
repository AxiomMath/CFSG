module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiNormalizer
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint CFSG.LieType.Ree

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem false_of_Suzuki
    {f : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (h : G93Hyp Γ A L L m)
    (hS : SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 f) : False := by
  obtain ⟨-, a, ha, K, instF, instFin, hfa, hKc, ⟨e⟩⟩ := hS
  have hd : 4 * f ≤ Module.finrank (ZMod 2) V := by
    obtain ⟨p, hpP⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor
      (k := 4 * f) (by omega) (by omega)
    have hp := hpP.prime
    have hdvd : p ∣ 2 ^ (2 * f) + 1 :=
      (hpP.dvd_add_one_iff (by omega) (2 * f)).2
        ⟨⟨1, by ring⟩, fun h' => by have := Nat.le_of_dvd (by omega) h'; omega⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := hpP.ne_two (by omega)
    have hKc' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hKc
    have hcard : p ∣ Nat.card (suzukiGroup a K) := by
      rw [suzuki_order hKc']
      refine Dvd.dvd.mul_left ?_ _
      rw [← hfa, ← pow_mul, show f * 2 = 2 * f by ring]
      exact hdvd
    have h1 := orderOf_two_le_finrank_of_dvd_card_quotient e hp2 hcard
    have h2 : orderOf (2 : ZMod p) = 4 * f := by
      have hpow : (2 : ZMod p) ^ (4 * f) = 1 :=
        (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff (4 * f)).1 hpP.dvd
      have hdv : orderOf (2 : ZMod p) ∣ 4 * f := orderOf_dvd_of_pow_eq_one hpow
      have hpos : 0 < orderOf (2 : ZMod p) :=
        Nat.pos_of_ne_zero fun h0 => by rw [h0] at hdv; omega
      refine le_antisymm (Nat.le_of_dvd (by omega) hdv) ?_
      by_contra hlt
      push Not at hlt
      exact hpP.2.2 _ hpos hlt
        ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).2 (pow_orderOf_eq_one _))
    omega
  have hm : m ≤ f := by
    obtain ⟨hAN, hAel, hAcard, hirr⟩ := exists_mulaut_data
      (fun γ hγ l hl => h.H_normal γ hγ l hl) h.A_le h.A_elem h.A_card h.H_irr
    have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
    have hq := isQuasisimple_toMulSub h.L_comp.2.2
    have α := cqEquiv_toMulSub_comp e
    have hKc' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hKc
    haveI : Nontrivial (Multiplicative V) := hirr.1
    obtain ⟨-, -, hP2, -, -⟩ := suzuki_irreducible_normalizer_excludes a ha hKc'
      (Multiplicative V) hW (toMulSub L) hq.1 hirr.2 α
    have hsq : ∀ x ∈ toMulSub A, x * x = 1 := fun x hx => by
      rw [← pow_two]; exact hAel.2 x hx
    have hAL : toMulSub A ≤ toMulSub L :=
      hP2 _ (isPGroup_two_of_mul_self_eq_one _ hsq) hAN
    have hc := card_le_two_pow_of_le hW hirr hAL hAel α (r := f)
      (fun B _ hB2 => hfa ▸ suzuki_exponent_two_card_le hKc' B hB2)
    rw [hAcard] at hc
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hc
  have hb := h.bound
  omega

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
