module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.AUTSL

theorem card_outer_matrixDerived_minus_dvd_two_mul {K : Type} [Field K] [Finite K]
    [CharP K 2] {n f : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : Nat.card K = 2 ^ f) :
    Nat.card (Outer (matrixDerived (Qm n hn b c))) ∣ 2 * f := by
  classical
  obtain ⟨τ, hgen, h2f, -, -⟩ := exists_frobenius_class n hn b c hirr hf
  set t : Outer (matrixDerived (Qm n hn b c)) :=
    QuotientGroup.mk (s := inner _) τ with ht
  have hzp : ∀ y, y ∈ Subgroup.zpowers t := fun y => by
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hgen α
    refine ⟨(k : ℤ), ?_⟩
    change QuotientGroup.mk (s := inner _) τ ^ (k : ℤ) =
      QuotientGroup.mk (s := inner _) α
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq]
    exact hk
  have ht2 : t ^ (2 * f) = 1 := by
    rw [ht, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa using h2f
  rw [← orderOf_eq_card_of_forall_mem_zpowers hzp]
  exact orderOf_dvd_of_pow_eq_one ht2

theorem k_OmegaMinusEightOutOrder_holds :
    ∀ (K : Type) [Group K] [Finite K] (f : ℕ),
      LieModel K .POmegaMinus 4 2 f → Nat.card (Outer K) ∣ 2 * f := by
  intro K _ _ f hK
  obtain ⟨-, F, hFld, hFin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    hK.statedClassicalModel_of_ne_zero (n := 4) (p := 2) (by norm_num)
  letI := hFld
  letI := hFin
  haveI : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by
      rw [← Nat.card_eq_fintype_card]
      exact hcard)
  letI := hchar
  have hn : 4 ≤ 4 := le_rfl
  have hQ : ∃ v, Qm 4 hn b c v ≠ 0 :=
    ⟨CFSG.StandardType.AutOm.tailVec 4 (by norm_num),
      CFSG.StandardType.AutOm.tailVec_form_ne_zero 4 (by norm_num) b c⟩
  let eΓ : K ≃* matrixDerived (Qm 4 hn b c) :=
    (coordinateMinusWitnessEquiv F (by norm_num) b c e).trans
      (derivedProjEquiv (Qm 4 hn b c) hQ).symm
  calc Nat.card (Outer K)
      = Nat.card (Outer (matrixDerived (Qm 4 hn b c))) :=
        Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eΓ).toEquiv
    _ ∣ 2 * f := card_outer_matrixDerived_minus_dvd_two_mul (n := 4) hn hirr hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
