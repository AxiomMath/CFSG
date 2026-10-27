module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConjSplit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConjCompanion
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem natCast_ne_zero_of_two_eq_zero (h2 : (2 : F) = 0) (hp2 : p ≠ 2) (hp : p.Prime) :
    (p : F) ≠ 0 := by
  intro h
  haveI : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ((CharP.cast_eq_zero_iff F 2 p).1 h)).symm

theorem exists_spPlaneConj (h2 : (2 : F) = 0) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F,
      (∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) ∧ SpPlaneConj F p ζ := by
  have hpF : (p : F) ≠ 0 := natCast_ne_zero_of_two_eq_zero h2 hp2 hp
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hsplit : p ∣ Nat.card F - 1
  · obtain ⟨ω, hωo⟩ : ∃ ω : Fˣ, orderOf ω = p := by
      classical
      haveI : Fintype F := Fintype.ofFinite F
      apply exists_prime_orderOf_dvd_card p
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card]
      exact hsplit
    have hω1 : ω ^ p = 1 := hωo ▸ pow_orderOf_eq_one ω
    refine ⟨spPlaneZetaSplit ω hω1, fun a => ?_, spPlaneConj_split hp2 hpF hω1 hωo⟩
    have hinv : CFSG.StandardType.TableBSymp.zmodPowHom hω1 a⁻¹ =
        (CFSG.StandardType.TableBSymp.zmodPowHom hω1 a)⁻¹ := map_inv _ _
    show sl2W * sl2Diag (CFSG.StandardType.TableBSymp.zmodPowHom hω1 a) * sl2W⁻¹ =
      sl2Diag (CFSG.StandardType.TableBSymp.zmodPowHom hω1 a⁻¹)
    rw [hinv, mul_inv_eq_iff_eq_mul]
    exact sl2W_mul_sl2Diag _
  · by_cases hnon : p ∣ Nat.card F + 1
    · obtain ⟨t, hirr, hgd⟩ := exists_quadratic_cyclotomic_factor hp hp2 hpF hnon
      have ht := spCompanion_pow_eq_one hp hgd
      exact ⟨spPlaneZetaCompanion t ht, spPlaneZetaCompanion_conj_sl2W hp h2 t ht,
        spPlaneConj_companion h2 hp hp2 hnon hirr hgd ht⟩
    · refine ⟨1, fun a => by simp, ?_⟩
      intro n E hE hcard
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · haveI : Subsingleton (StatedSp 0 F) := inferInstance
        refine ⟨1, Subgroup.ext fun x => ?_⟩
        rw [Subsingleton.elim x 1]
        simp only [one_mem, iff_true]
      · exact absurd (dvd_card_sub_one_or_add_one_of_pow_le_card hp hp2 hpF hn E hE hcard)
          (by tauto)

end CFSG.StandardType.SpJoin
