module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunSet
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTwG2D4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section TripleBond

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LieType.RootSystem
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Asc77


theorem exists_commuting_of_triple_bond {p e : ℕ} [Fact p.Prime] {t : StatedLieTag} {k : ℕ}
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t k p e) (ht : t = .G2 ∨ t = .trialityD4)
    {i j : Fin (modelUniv t k p e Fact.out).D.rank}
    (hAij : (modelUniv t k p e Fact.out).D.cartan i j = -3)
    (hAji : (modelUniv t k p e Fact.out).D.cartan j i = -1)
    (hj : ModelFacts.IsLongNode t k j.val) :
    ∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, Commutes R S := by
  obtain ⟨_, _, _, hext⟩ :=
    ModelFacts.hasBruhatDatum t k p e Fact.out (ih8_isFundTag_mf hfund) hadm
  have hjl :=
    ModelFacts.isLongestRoot_single t k p e Fact.out (ih8_isFundTag_mf hfund) hadm j hj
  have hA := (modelUniv t k p e Fact.out).D.isFiniteType
  set wi := (coxeterMatrix hA).toCoxeterSystem.simple i with hwi
  set wj := (coxeterMatrix hA).toCoxeterSystem.simple j with hwj
  have hγ : ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D
      (weylAction hA wj (weylAction hA wi (Pi.single j 1))) :=
    ModelFacts.IsLongest.map_weylAction (ModelFacts.IsLongest.map_weylAction hjl wi) wj
  have h1 : weylAction hA wi (Pi.single j 1) = Pi.single j 1 + 3 • Pi.single i 1 := by
    rw [hwi, weylAction_simple, reflection_apply_coroot, coroot_single, hAij]
    module
  have h2 : weylAction hA wj (Pi.single j 1 + 3 • Pi.single i 1) =
      2 • Pi.single j 1 + 3 • Pi.single i 1 := by
    rw [hwj, weylAction_simple, reflection_apply_coroot, map_add, map_nsmul, coroot_single,
      coroot_single, hAji, hA.apply_self]
    module
  rw [h1, h2] at hγ
  have hc0 : coroot (modelUniv t k p e Fact.out).D.cartan i
      (2 • Pi.single j 1 + 3 • Pi.single i 1) = 0 := by
    rw [map_add, map_nsmul, map_nsmul, coroot_single, coroot_single, hAij, hA.apply_self]
    norm_num
  have hδ : (Pi.single i 1 : Fin (modelUniv t k p e Fact.out).D.rank → ℤ) ∈
      (modelUniv t k p e Fact.out).D.roots :=
    (isCTRootSystem hA (modelUniv t k p e Fact.out).D.divisible).single_mem i
  have horth := form_toRat_single_eq_zero (modelUniv t k p e Fact.out).D i _ hc0
  have hc := commutes_fund_of_orthogonal_of_longest (modelUniv t k p e Fact.out).D hext hγ.1 hδ
    hγ.2 horth
  exact ⟨_, ⟨1, _, Or.inl hγ, (conjSub_one _).symm⟩, _,
    ⟨1, Pi.single i 1, Or.inr (ht.imp (fun h => ⟨h, hδ⟩) (fun h => ⟨h, hδ⟩)),
      (conjSub_one _).symm⟩, hc⟩

theorem exists_commuting_fund_g2 {p e : ℕ} [Fact p.Prime] {k : ℕ}
    (hadm : StatedLieAdmissible .G2 k p e) :
    ∃ R ∈ ModelFund p .G2 k e, ∃ S ∈ ModelFund p .G2 k e, Commutes R S :=
  exists_commuting_of_triple_bond trivial hadm (Or.inl rfl) (i := (1 : Fin 2)) (j := (0 : Fin 2))
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .G2 (1 : Fin 2) (0 : Fin 2) = -3; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .G2 (0 : Fin 2) (1 : Fin 2) = -1; decide) rfl

theorem exists_commuting_fund_trialityD4 {p e : ℕ} [Fact p.Prime] {k : ℕ}
    (hadm : StatedLieAdmissible .trialityD4 k p e) :
    ∃ R ∈ ModelFund p .trialityD4 k e, ∃ S ∈ ModelFund p .trialityD4 k e, Commutes R S :=
  exists_commuting_of_triple_bond trivial hadm (Or.inr rfl) (i := (1 : Fin 2)) (j := (0 : Fin 2))
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .G2 (1 : Fin 2) (0 : Fin 2) = -3; decide)
    (by show CFSG.Blueprint.Chevalley.Tag.cartan .G2 (0 : Fin 2) (1 : Fin 2) = -1; decide) rfl

theorem fund_facts {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) :
    (∃ a ∈ R, orderOf a = p) ∧ (∀ c ∈ R, (∀ y ∈ R, c * y = y * c) → c * c = 1) := by
  have he : 1 ≤ e := hadm.2.1
  rcases ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hfund hadm hR
    with h1 | ⟨-, h1⟩
  · obtain ⟨φ⟩ := h1
    refine ⟨exists_orderOf_of_equiv_sl2 φ ?_, fun c hc hcc =>
      ModelFacts.fundCentral_sq_of_equiv_sl2 φ hc hcc⟩
    rw [GaloisField.card p e (by omega)]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  · obtain ⟨φ⟩ := h1
    refine ⟨exists_orderOf_of_equiv_sl2 φ ?_, fun c hc hcc =>
      ModelFacts.fundCentral_sq_of_equiv_sl2 φ hc hcc⟩
    rw [GaloisField.card p (3 * e) (by omega)]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _

end TripleBond

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie
