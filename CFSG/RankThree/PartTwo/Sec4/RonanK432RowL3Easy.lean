module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432PRank
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
import CFSG.Models.PGL
import CFSG.Open.StatedDefs
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

instance finite_projSL_three (K : Type) [Field K] [Finite K] : Finite (projSL 3 K) := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 3) K →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

instance finite_projSU_three (p f : ℕ) [Fact p.Prime] : Finite (projSU 3 p f) := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField p (2 * f))) :=
    Finite.of_surjective
      (Matrix.ProjGenLinGroup.mk : Matrix.GeneralLinearGroup (Fin 3) (GaloisField p (2 * f)) →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem listRow_projSL_three_of_mod_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) : ListRow (projSL 3 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 3 (projSL 3 K)))
  exact listRow_of_pRank_le_one
    (CFSG.AGLEmbedding.pRank_le_one_of_isCyclic_sylow Nat.prime_three T
      (CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_projSL hK T))

theorem listRow_projSU_three_of_mod_one (p f : ℕ) [Fact p.Prime] (hf : f ≠ 0)
    (hq : p ^ f % 3 = 1) : ListRow (projSU 3 p f) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 3 (projSU 3 p f)))
  exact listRow_of_pRank_le_one
    (CFSG.AGLEmbedding.pRank_le_one_of_isCyclic_sylow Nat.prime_three T
      (CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_projSU hf hq T))

theorem outerRow_projSL_three_of_mod_two (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (he2 : e ≤ 2)
    (hmod : p ^ e % 3 = 2) : OuterRow (projSL 3 (GaloisField p e)) := by
  apply outerRow_of_not_three_dvd_outer
  have hp : p.Prime := Fact.out
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 p e := by
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨hp, he, ?_⟩
    simp
  have hT := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm
    (MulEquiv.refl (projSL 3 (GaloisField p e)))
  have hdvd : Nat.card (Outer (projSL 3 (GaloisField p e))) ∣ 2 * e * Nat.gcd 3 (p ^ e - 1) :=
    (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inl rfl) (le_refl 3) hp he hT).1
  have hg : Nat.gcd 3 (p ^ e - 1) = 1 :=
    Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
  rw [hg, mul_one] at hdvd
  intro h3
  have h3' := h3.trans hdvd
  omega

theorem outerRow_projSU_three_of_mod_one (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (he2 : e ≤ 2)
    (hmod : p ^ e % 3 = 1) : OuterRow (projSU 3 p e) := by
  apply outerRow_of_not_three_dvd_outer
  have hq : ¬ (3 = 3 ∧ p ^ e = 2) := fun h => by
    have := h.2
    omega
  have hdvd := CFSG.RankThree.PartTwo.Sec4.card_outer_projSU_dvd 3 p e he (le_refl 3) hq
  intro h3
  have h3' := h3.trans hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h' | h' <;> omega
  · omega

theorem rowOf_two_SL_of_mod_two : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    p ^ e % 3 = 2 → RowOf (projSL 3 (GaloisField p e)) := by
  intro p e _ _ he he2 hmod
  intro S _ _ _ _ ⟨eS⟩
  have hK : Nat.card (GaloisField p e) % 3 = 2 := by
    rw [GaloisField.card p e (by omega)]
    exact hmod
  exact GoodRow.of_mulEquiv eS.symm
    ⟨listRow_projSL_three_of_mod_two (GaloisField p e) hK,
      outerRow_projSL_three_of_mod_two p e he he2 hmod⟩

theorem rowOf_two_SU_of_mod_one : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    p ^ e % 3 = 1 → RowOf (projSU 3 p e) := by
  intro p e _ _ he he2 hmod
  intro S _ _ _ _ ⟨eS⟩
  exact GoodRow.of_mulEquiv eS.symm
    ⟨listRow_projSU_three_of_mod_one p e (by omega) hmod,
      outerRow_projSU_three_of_mod_one p e he he2 hmod⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
