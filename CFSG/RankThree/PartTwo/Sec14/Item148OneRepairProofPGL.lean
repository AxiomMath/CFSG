module

public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item148OneRepairProofUni
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Item148StepKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem kf148PGLPi_holds : KF148PGLPi := by
  intro Γ _ _ X E hP hX hEN hE hE27 hcent ⟨z, hz1, hzE⟩ ⟨a, haE, ha⟩
  have hZX : Subgroup.center ↥X = ⊥ := kf148CenterL3 _ hP (Or.inl hX)
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE3 : ∀ a ∈ E, a ^ 3 = 1 := hE.2
  have ha' : ¬ IsInnerAut (X.normalizerMonoidHom ⟨a, hEN haE⟩) :=
    fun h1 => ha (Item148Rank.innerOn148_of_isInnerAut148 (hEN haE) h1)
  have hXnt : Nontrivial ↥X := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply ha
    refine ⟨1, X.one_mem, fun y hy => ?_⟩
    have hy1 : y = 1 := congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ : ↥X) 1)
    rw [hy1]
    group
  obtain ⟨p, e, hp, he, hcase⟩ := hX
  have hp' : p.Prime := hp.out
  rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  ·
    obtain ⟨ψ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p e)
    have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
    let eX : ↥X ≃* projectiveSL 3 (GaloisField p e) := φ.trans ψ
    have hZP : Subgroup.center (projectiveSL 3 (GaloisField p e)) = ⊥ :=
      center_eq_bot_of_mulEquiv148 eX.symm hZX
    obtain ⟨e1⟩ := Item148OneRepair.nonempty_mulEquiv_prod_of_autFacts148 eX
      (Item148OneRepair.autFacts148_linear hp' he hcard hq hZP) hEN hEc hE3 hE27 hcent hz1
      hzE haE ha'
    obtain ⟨e2⟩ := Item148OneRepair.nonempty_linearAutGroup_mulEquiv148
      (K := GaloisField p e) (p ^ e)
    exact ⟨p, e, he, true, GaloisField p e, inferInstance, ⟨hp', he, hcard⟩, hq,
      ⟨e1.trans (MulEquiv.prodCongr (MulEquiv.refl _) e2)⟩⟩
  ·
    have h : UnitaryFieldData p e (GaloisField p (2 * e)) :=
      ⟨hp', he, GaloisField.card p _ (by omega)⟩
    obtain ⟨ψ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    let eX : ↥X ≃* unitaryPSU h 3 := φ.trans ψ.symm
    have hq2 : 2 < p ^ e := by
      by_contra h2
      have h2' : p ^ e = 2 := by
        have := Nat.one_lt_pow (by omega : e ≠ 0) hp'.one_lt
        omega
      obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp' h2'
      have := isSolvable_projSU_two
      have hsol : Group.IsSolvable ↥X :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      exact Group.IsPerfect.not_isSolvable ↥X hsol
    have hZP : Subgroup.center (unitaryPSU h 3) = ⊥ := center_eq_bot_of_mulEquiv148 eX.symm hZX
    obtain ⟨e1⟩ := Item148OneRepair.nonempty_mulEquiv_prod_of_autFacts148 eX
      (Item148OneRepair.autFacts148_unitary h hq hq2 hZP) hEN hEc hE3 hE27 hcent hz1 hzE haE
      ha'
    obtain ⟨e2⟩ := Item148OneRepair.nonempty_range_psuConj_mulEquiv148 h
    refine ⟨p, e, he, false, GaloisField p (2 * e), inferInstance, ⟨hp', he, ?_⟩, hq,
      ⟨e1.trans (MulEquiv.prodCongr (MulEquiv.refl _) e2)⟩⟩
    rw [GaloisField.card p _ (by omega), pow_mul']
    rfl

end CFSG.RankThree.PartTwo.Sec14
