module

public import CFSG.RankThree.PartOne.K133.OddChar3
import CFSG.Adapters.LinearCatalog
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartOne.K133.ResTransfer
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.S13K TauCeti
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem not_dvd_two_mul_mul {p f d : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hf1 : 1 ≤ f) (hf3 : f ≤ 3)
    (hd1 : 1 ≤ d) (hd3 : d ≤ 4) : ¬ p ∣ 2 * f * d := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have := Nat.le_of_dvd (by omega) h2
      omega
  · have := Nat.le_of_dvd (by omega) h1
    omega

theorem kf133ResMaxAt_leaf2_zero (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf2 0) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, he3, hv, ⟨e0⟩⟩ := hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf1 : 1 ≤ q.exponent := q.exponent_pos
  let K := GaloisField q.p q.exponent
  have e1 : X ≃* StatedProj (StatedSL 3 K) :=
    (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (projectiveSpecialLinearGroupEquivStatedProj 3 K)
  have : IsSimpleGroup (StatedProj (StatedSL 3 K)) := e1.symm.isSimpleGroup
  have hne' : ∃ a b : StatedProj (StatedSL 3 K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hne
    exact ⟨e1 a, e1 b, fun h => hab (e1.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hcardK : Nat.card K = q.p ^ q.exponent := GaloisField.card q.p q.exponent (by omega)
  have hmodel : StatedClassicalModel (StatedProj (StatedSL 3 K)) .PSL 3 q.p q.exponent :=
    ⟨⟨q.prime_p, hf1, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance, hcardK,
      ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hout, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := StatedProj (StatedSL 3 K)) (Or.inl rfl) (by norm_num) q.prime_p hf1 hmodel
  have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSL 3 (q.p ^ q.exponent) =
      Nat.gcd 3 (q.p ^ q.exponent - 1) := rfl
  have hdpos : 0 < Nat.gcd 3 (q.p ^ q.exponent - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdle : Nat.gcd 3 (q.p ^ q.exponent - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hOut : ¬ p ∣ Nat.card (Outer (StatedProj (StatedSL 3 K))) := fun hdvd =>
    not_dvd_two_mul_mul hp h5 hf1 he3 hdpos (by omega) (hdvd.trans (hd ▸ hout))
  exact GoodRes.of_mulEquiv hp e1 (goodRes_statedProj_three hp h5 (StatedSL 3 K) le_rfl hne' hOut)

theorem statedSU_le_statedSL (n q : ℕ) (K : Type) [Field K] : StatedSU n q K ≤ StatedSL n K :=
  CFSG.Open.StatedAPI.statedSU_le_statedSL n q K

theorem goodRes_psu_three {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hne : ∃ a b : X, a * b ≠ b * a) {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hf1 : 1 ≤ f)
    (hf3 : f ≤ 3) (e1 : X ≃* StatedProj (StatedSU 3 (ℓ ^ f) (GaloisField ℓ (2 * f)))) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) : GoodRes p X := by
  let K := GaloisField ℓ (2 * f)
  have : IsSimpleGroup (StatedProj (StatedSU 3 (ℓ ^ f) K)) := e1.symm.isSimpleGroup
  have hne' : ∃ a b : StatedProj (StatedSU 3 (ℓ ^ f) K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hne
    exact ⟨e1 a, e1 b, fun h => hab (e1.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hcardK : Nat.card K = (ℓ ^ f) ^ 2 := by
    rw [GaloisField.card ℓ (2 * f) (by omega), ← pow_mul, mul_comm]
  have hq3 : (3, ℓ ^ f) ≠ (3, 2) := by
    intro h
    have h2 : ℓ ^ f = 2 := (Prod.mk.inj h).2
    have hodd : Odd (ℓ ^ f) := ((Fact.out : ℓ.Prime).eq_two_or_odd'.resolve_left hℓ2).pow
    rw [h2] at hodd
    exact absurd hodd (by decide)
  have hmodel : StatedClassicalModel (StatedProj (StatedSU 3 (ℓ ^ f) K)) .PSU 3 ℓ f :=
    ⟨⟨Fact.out, hf1, by norm_num, hq3⟩, K, inferInstance, inferInstance, hcardK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hout, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := StatedProj (StatedSU 3 (ℓ ^ f) K)) (Or.inr rfl) (by norm_num) Fact.out hf1 hmodel
  have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (ℓ ^ f) =
      Nat.gcd 3 (ℓ ^ f + 1) := rfl
  have hdpos : 0 < Nat.gcd 3 (ℓ ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdle : Nat.gcd 3 (ℓ ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hOut : ¬ p ∣ Nat.card (Outer (StatedProj (StatedSU 3 (ℓ ^ f) K))) := fun hdvd =>
    not_dvd_two_mul_mul hp h5 hf1 hf3 hdpos (by omega) (hdvd.trans (hd ▸ hout))
  exact GoodRes.of_mulEquiv hp e1
    (goodRes_statedProj_three hp h5 (StatedSU 3 (ℓ ^ f) K) (statedSU_le_statedSL _ _ _) hne' hOut)

theorem kf133ResMaxAt_leaf2_one (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf2 1) := by
  refine KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, he3, hv, ⟨e0⟩⟩ := hX
  have e1 := e0.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)
  have hℓ : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p := by
    simp [ValidLieTypeIndex.characteristic]
  have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent := by
    simp [ValidLieTypeIndex.fieldExponent]
  exact goodRes_psu_three hne (ℓ := ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
    (f := ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩) (by rw [hℓ]; exact hq2)
    (ValidLieTypeIndex.fieldExponent_pos _) (by rw [hfe]; exact he3) e1 hp h5

end CFSG.RankThree.PartOne.K133
