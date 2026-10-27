module

public import CFSG.RankThree.PartOne.K133.Diag4
public import CFSG.RankThree.PartOne.K133.Leaf2
public import CFSG.RankThree.PartOne.KF.RankGL
import CFSG.Adapters.LinearCatalog
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.S13K TauCeti
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem goodRes_statedProj_sl_four {K : Type} [Field K] [Finite K] {r p : ℕ} [Fact r.Prime] [CharP K r]
    (hr2 : r ≠ 2) (hcard : Nat.card K = r) (hp : p.Prime) (h5 : 5 ≤ p)
    [IsSimpleGroup (StatedProj (StatedSL 4 K))]
    (hne : ∃ a b : StatedProj (StatedSL 4 K), a * b ≠ b * a)
    (hOut : ¬ p ∣ Nat.card (Outer (StatedProj (StatedSL 4 K)))) :
    GoodRes p (StatedProj (StatedSL 4 K)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hr : r.Prime := Fact.out
  have hZ : Subgroup.center (StatedProj (StatedSL 4 K)) = ⊥ := center_eq_bot_of_simple_nonabelian hne
  have hin : ∀ E : Subgroup (MulAut (StatedProj (StatedSL 4 K))), IsElementaryAbelian p E →
      E ≤ inner (StatedProj (StatedSL 4 K)) := fun E hE =>
    le_inner_of_isPGroup_of_not_dvd_outer hp hOut (IsElementaryAbelian.isPGroup p E)
  have hp4 : ¬ p ∣ 4 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  by_cases hpr : p = r
  · subst hpr
    exact goodRes_statedProj_four_char h5 (exists_natCast_of_card_eq_prime hcard) (by simp)
      (StatedSL 4 K) hne hin
  · have hpK : (p : K) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff K r p] at h0
      exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).1 h0).symm
    by_cases hdvd : p ∣ Nat.card K - 1
    · have h2 : (2 : K) ≠ 0 := by
        intro h0
        have h1 := (CharP.cast_eq_zero_iff K r 2).1 (by exact_mod_cast h0)
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h1)
      exact (dead_statedProj_sl_four hp h5 hdvd h2 hZ hin).good.goodRes
    · have hno : NoRankThree p (StatedProj (StatedSL 4 K)) := by
        refine noRankThree_of_inner_rank_el hp hZ hin ?_
        intro A hA hAc
        have hle := statedProj_card_le_of_bound (N := 4) (k := 2) hp hp4 (StatedSL 4 K)
          (fun z hz => statedSL_scalar_pow z hz)
          (fun E _ hcomm hexp => by
            have := LIT.card_le_pow_div_gl hp hpK (d := 2) (by norm_num)
              (fun i hi0 hi2 => by
                have : i = 1 := by omega
                subst this
                simpa using hdvd) E hcomm hexp
            simpa using this) A hA
        rw [hAc] at hle
        have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
        omega
      exact hno.dead.good.goodRes

theorem kf133ResMaxAt_leaf4_three (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf4 3) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, he1, hv, ⟨e0⟩⟩ := hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf1 : 1 ≤ q.exponent := q.exponent_pos
  let K := GaloisField q.p q.exponent
  have e1 : X ≃* StatedProj (StatedSL 4 K) :=
    (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv)).trans
      (projectiveSpecialLinearGroupEquivStatedProj 4 K)
  have : IsSimpleGroup (StatedProj (StatedSL 4 K)) := e1.symm.isSimpleGroup
  have hne' : ∃ a b : StatedProj (StatedSL 4 K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hne
    exact ⟨e1 a, e1 b, fun h => hab (e1.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hcardK : Nat.card K = q.p ^ q.exponent := GaloisField.card q.p q.exponent (by omega)
  have hcard1 : Nat.card K = q.p := by rw [hcardK, he1, pow_one]
  have hmodel : StatedClassicalModel (StatedProj (StatedSL 4 K)) .PSL 4 q.p q.exponent :=
    ⟨⟨q.prime_p, hf1, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance, hcardK,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hout, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := StatedProj (StatedSL 4 K)) (Or.inl rfl) (by norm_num) q.prime_p hf1 hmodel
  have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSL 4 (q.p ^ q.exponent) =
      Nat.gcd 4 (q.p ^ q.exponent - 1) := rfl
  have hdpos : 0 < Nat.gcd 4 (q.p ^ q.exponent - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdle : Nat.gcd 4 (q.p ^ q.exponent - 1) ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hOut : ¬ p ∣ Nat.card (Outer (StatedProj (StatedSL 4 K))) := fun hdvd =>
    not_dvd_two_mul_mul hp h5 hf1 (by omega) hdpos hdle (hdvd.trans (hd ▸ hout))
  exact GoodRes.of_mulEquiv hp e1
    (goodRes_statedProj_sl_four hq2 hcard1 hp h5 hne' hOut)

end CFSG.RankThree.PartOne.K133
