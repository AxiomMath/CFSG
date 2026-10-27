module

public import CFSG.RankThree.ThinCatalog.FiveModels
public import CFSG.RankThree.ThinCatalog.EvenLinearTwoLocal
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.RankThree.SteinbergR3EHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.LieType.Automorphisms.SteinbergBLCompleteIndexTwo

public section

namespace CFSG.RankThree.ThinCatalog

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

theorem not_three_dvd_of_dvd_two {n : ℕ} (h : n ∣ 2) : ¬ 3 ∣ n := fun h3 => by
  have := Nat.le_of_dvd (by norm_num) (h3.trans h)
  omega

theorem outer_card_dvd_of_psl_two {S : Type} [Group S] {p f : ℕ}
    (hm : StatedClassicalModel S .PSL 2 p f) :
    Nat.card (Outer S) ∣ f * Nat.gcd 2 (p ^ f - 1) := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  exact (linear_two_outer_order_divisor hp K hK).2 S
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩

theorem outer_card_dvd_two_of_psl_three_two {S : Type} [Group S]
    (hm : StatedClassicalModel S .PSL 3 2 1) : Nat.card (Outer S) ∣ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have h := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
    (K := K) Nat.prime_two le_rfl (le_refl 3) hK
  let e' : S ≃* LinearFlag.projectiveSL 3 K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  rw [Nat.card_congr (equivalence e').toEquiv]
  simpa using h

theorem card_le_three_of_not_three_dvd_outer {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S)) (h3 : CFSG.pRank 3 S ≤ 1)
    (E : Subgroup (MulAut S)) (hE : IsElementaryAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut S) :=
    Finite.of_injective (fun φ : MulAut S => (φ : S → S)) DFunLike.coe_injective
  have hEp : IsPGroup 3 E := IsElementaryAbelian.isPGroup 3 E
  have hEinn : E ≤ (MulAut.conj : S →* MulAut S).range := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hEp.map (QuotientGroup.mk' (inner S)))
    have hdvd : Nat.card (E.map (QuotientGroup.mk' (inner S))) ∣ Nat.card (Outer S) :=
      Subgroup.card_subgroup_dvd_card _
    have hk0 : k = 0 := by
      by_contra hk0
      exact hout ((dvd_pow_self 3 hk0).trans (by rw [← hk]; exact hdvd))
    rw [hk0, pow_zero, Subgroup.card_eq_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hk
    exact hk
  have hinj := CFSG.LieType.Automorphisms.conj_injective_of_center_eq_bot hZ
  let ψ : S ≃* (MulAut.conj : S →* MulAut S).range := MonoidHom.ofInjective hinj
  let φ : E →* S := ψ.symm.toMonoidHom.comp (Subgroup.inclusion hEinn)
  have hφ : Function.Injective φ := ψ.symm.injective.comp (Subgroup.inclusion_injective hEinn)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
  have hpow : ∀ a : E, a ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 E)
  have hle := CFSG.SectionRank.le_pRank_of_injective (p := 3) (A := ↥E) (by norm_num)
    (fun a b => mul_comm' a b) hpow hk φ hφ le_top
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at hle
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (hle.trans h3)
    _ = 3 := pow_one 3

theorem thin_catalog_two_local_prime_support_outer_three_free (S : Type) [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r S ≤ 1) (h3 : CFSG.pRank 3 S = 1)
    (hloc : ∀ V : Subgroup S, V ≠ ⊥ → IsPGroup 2 V → ∀ r : ℕ, r.Prime →
      r ∣ Nat.card (Subgroup.normalizer (V : Set S)) → r = 2 ∨ r = 3) :
    ¬ 3 ∣ Nat.card (Outer S) ∧
      ∀ E : Subgroup (MulAut S), IsElementaryAbelian 3 E → Nat.card E ≤ 3 := by
  have hout : ¬ 3 ∣ Nat.card (Outer S) := by
    rcases odd_rank_one_catalog_five_model_alternatives S hnab hcat hodd h3 with
      ⟨⟨e⟩⟩ | ⟨ℓ, -, -, -, hm⟩ | ⟨f, hf, hm⟩ | hm | ⟨⟨e⟩⟩
    · exact not_three_dvd_of_dvd_two
        (outer_card_dvd_two_of_equiv_outside_six (Or.inl rfl) e)
    · refine not_three_dvd_of_dvd_two ((outer_card_dvd_of_psl_two hm).trans ?_)
      rw [one_mul]
      exact Nat.gcd_dvd_left 2 _
    · obtain rfl : f = 2 := le_antisymm (le_two_of_two_local_prime_support hm hloc) hf
      exact not_three_dvd_of_dvd_two (by simpa using outer_card_dvd_of_psl_two hm)
    · exact not_three_dvd_of_dvd_two (outer_card_dvd_two_of_psl_three_two hm)
    · rw [Nat.card_congr (equivalence e).toEquiv, CFSG.Sporadic.Schreier.at_j1_schreier.1]
      norm_num
  exact ⟨hout, fun E hE => card_le_three_of_not_three_dvd_outer
    (CFSG.LieType.Automorphisms.center_eq_bot_of_simple hnab) hout (by omega) E hE⟩

end CFSG.RankThree.ThinCatalog
