module

public import CFSG.RankThree.PartOne.K133.UnitaryChar4
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartOne.K133.Leaf2
public import CFSG.RankThree.PartOne.K133.Unitary4
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.S13K TauCeti
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem goodRes_statedProj_su_four {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : f = 1) (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (h5 : 5 ≤ p)
    [IsSimpleGroup (StatedProj (StatedSU 4 (ℓ ^ f) K))]
    (hne : ∃ a b : StatedProj (StatedSU 4 (ℓ ^ f) K), a * b ≠ b * a)
    (hOut : ¬ p ∣ Nat.card (Outer (StatedProj (StatedSU 4 (ℓ ^ f) K)))) :
    GoodRes p (StatedProj (StatedSU 4 (ℓ ^ f) K)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  have hZ : Subgroup.center (StatedProj (StatedSU 4 (ℓ ^ f) K)) = ⊥ :=
    center_eq_bot_of_simple_nonabelian hne
  have hin : ∀ E : Subgroup (MulAut (StatedProj (StatedSU 4 (ℓ ^ f) K))), IsElementaryAbelian p E →
      E ≤ inner (StatedProj (StatedSU 4 (ℓ ^ f) K)) := fun E hE =>
    le_inner_of_isPGroup_of_not_dvd_outer hp hOut (IsElementaryAbelian.isPGroup p E)
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    exact goodRes_statedProj_su_four_char hK hf h5 hne hin
  · have hpK : (p : K) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff K ℓ p] at h0
      exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h0).symm
    have h2 : (2 : K) ≠ 0 := by
      intro h0
      have h1 := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h0)
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h1)
    by_cases hpq : p ∣ ℓ ^ f + 1
    · exact (dead_statedProj_su_four hK hp h5 hpq h2 hZ hin).good.goodRes
    · exact (noRankThree_statedProj_su_four hK hp h5 hpK hpq hZ hin).dead.good.goodRes

theorem goodRes_psu_four {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hne : ∃ a b : X, a * b ≠ b * a) {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hf : f = 1)
    (e1 : X ≃* StatedProj (StatedSU 4 (ℓ ^ f) (GaloisField ℓ (2 * f)))) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) : GoodRes p X := by
  let K := GaloisField ℓ (2 * f)
  have : IsSimpleGroup (StatedProj (StatedSU 4 (ℓ ^ f) K)) := e1.symm.isSimpleGroup
  have hne' : ∃ a b : StatedProj (StatedSU 4 (ℓ ^ f) K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hne
    exact ⟨e1 a, e1 b, fun h => hab (e1.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hf1 : 1 ≤ f := by omega
  have hcardK : Nat.card K = (ℓ ^ f) ^ 2 := by
    rw [GaloisField.card ℓ (2 * f) (by omega), ← pow_mul, mul_comm]
  have hq3 : (4, ℓ ^ f) ≠ (3, 2) := by
    intro h
    have := (Prod.mk.inj h).1
    omega
  have hmodel : StatedClassicalModel (StatedProj (StatedSU 4 (ℓ ^ f) K)) .PSU 4 ℓ f :=
    ⟨⟨Fact.out, hf1, by norm_num, hq3⟩, K, inferInstance, inferInstance, hcardK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hout, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := StatedProj (StatedSU 4 (ℓ ^ f) K)) (Or.inr rfl) (by norm_num) Fact.out hf1 hmodel
  have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSU 4 (ℓ ^ f) =
      Nat.gcd 4 (ℓ ^ f + 1) := rfl
  have hdpos : 0 < Nat.gcd 4 (ℓ ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdle : Nat.gcd 4 (ℓ ^ f + 1) ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hOut : ¬ p ∣ Nat.card (Outer (StatedProj (StatedSU 4 (ℓ ^ f) K))) := fun hdvd =>
    not_dvd_two_mul_mul hp h5 hf1 (by omega) hdpos hdle (hdvd.trans (hd ▸ hout))
  exact GoodRes.of_mulEquiv hp e1 (goodRes_statedProj_su_four hcardK hf hℓ2 hp h5 hne' hOut)

theorem kf133ResMaxAt_leaf4_two (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf4 2) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, he1, hv, ⟨e0⟩⟩ := hX
  have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)
  have hℓ : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p := by
    simp [ValidLieTypeIndex.characteristic]
  have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent := by
    simp [ValidLieTypeIndex.fieldExponent]
  exact goodRes_psu_four hne (ℓ := ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
    (f := ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩) (by rw [hℓ]; exact hq2)
    (by rw [hfe]; exact he1) e1 hp h5

end CFSG.RankThree.PartOne.K133
