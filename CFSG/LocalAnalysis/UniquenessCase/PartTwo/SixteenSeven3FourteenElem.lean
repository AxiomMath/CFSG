module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenFstar
public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1614_not_dvd_of_fstar_elem (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {p n ℓ : ℕ} (hp : p.Prime) (hF : IsElemAbelianOfRank p n ↥(fstarBar D.M V₀ V hV))
    (hℓ : ¬ ℓ ∣ p ^ n * ∏ i : Fin n, (p ^ n - p ^ (i : ℕ))) :
    ¬ ℓ ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  obtain ⟨e⟩ := hF
  have hcard : Nat.card ↥(fstarBar D.M V₀ V hV) = p ^ n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have hcomm : ∀ a b : ↥(fstarBar D.M V₀ V hV), a * b = b * a := fun a b =>
    e.injective (by rw [map_mul, map_mul, mul_comm])
  have hpow : ∀ a : ↥(fstarBar D.M V₀ V hV), a ^ p = 1 := by
    intro a
    apply e.injective
    rw [map_pow, map_one]
    induction e a using Multiplicative.rec with
    | ofAdd w =>
      rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p) p w, ZMod.natCast_self p, zero_smul,
        ofAdd_zero]
  have hdvd : Nat.card ↥(Mbar D.M V₀ V hV) ∣
      Nat.card ↥(fstarBar D.M V₀ V hV) * Nat.card (MulAut ↥(fstarBar D.M V₀ V hV)) :=
    s16c1614_card_dvd_fstar_subgroup _
  rw [hcard, CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary hcomm hpow hcard] at hdvd
  exact fun h => hℓ (h.trans hdvd)

theorem s16c1614_not_seven_dvd_case168_8 (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h8 : Case168_8 D V₀ V hV) : ¬ 7 ∣ Nat.card ↥(Mbar D.M V₀ V hV) :=
  s16c1614_not_dvd_of_fstar_elem D hV Nat.prime_three h8.1 (by norm_num [Fin.prod_univ_succ])

theorem s16c1614_not_seven_dvd_case168_10_three (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Case168_10At D V₀ V hV L 3) :
    ¬ 7 ∣ Nat.card ↥(Mbar D.M V₀ V hV) :=
  s16c1614_not_dvd_of_fstar_elem D hV Nat.prime_three h.2.2.2.2
    (by norm_num [Fin.prod_univ_succ])

theorem s16c1614_not_five_dvd_case168_10_seven (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Case168_10At D V₀ V hV L 7) :
    ¬ 5 ∣ Nat.card ↥(Mbar D.M V₀ V hV) :=
  s16c1614_not_dvd_of_fstar_elem D hV (by norm_num) h.2.2.2.2
    (by norm_num [Fin.prod_univ_succ])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
