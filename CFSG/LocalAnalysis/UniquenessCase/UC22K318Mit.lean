module

public import CFSG.RankThree.SubgroupLists.MitchellQuasisimple
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Low
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Blueprint.Catalog
import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
import CFSG.RankThree.SubgroupLists.SymplecticFischerOrth
import CFSG.RankThree.SubgroupLists.SymplecticFischerUnitary
import CFSG.RankThree.SubgroupLists.SymplecticFischerRefl
import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Adapters.StatedPSLTwoNine
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.ClassicalGroups
public import CFSG.Foundations
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.M23.M23Group
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.SubgroupLists (MitchellPartThree)
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (eq_of_simple_quotients
  not_isSolvable_of_isQuasisimple statedClassicalModel_psl_two)
open scoped MatrixGroups

variable {q : ℕ} [Fact q.Prime]

theorem neg_one_ne_one_gl (hq2 : q ≠ 2) : (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ≠ 1 := by
  have hm1 : (-1 : ZMod q) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  intro h
  apply hm1
  have h1 := congrArg (fun M : GL (Fin 2 ⊕ Fin 2) (ZMod q) =>
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) (Sum.inl 0) (Sum.inl 0)) h
  simpa using h1

theorem two_dvd_card_center (hq2 : q ≠ 2)
    {P : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hPS : P ≤ StatedSp 2 (ZMod q))
    (hqs : CFSG.IsQuasisimple P) : 2 ∣ Nat.card (center P) := by
  by_cases hneg : (-1 : GL (Fin 2 ⊕ Fin 2) (ZMod q)) ∈ P
  · have hc : (⟨-1, hneg⟩ : P) ∈ center P :=
      mem_center_iff.2 fun g => Subtype.ext (by simp)
    have hz2 : (⟨⟨-1, hneg⟩, hc⟩ : center P) ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simp
    have hz1 : (⟨⟨-1, hneg⟩, hc⟩ : center P) ≠ 1 := fun h =>
      neg_one_ne_one_gl hq2
        (congrArg (fun w : center P => ((w : P) : GL (Fin 2 ⊕ Fin 2) (ZMod q))) h)
    have h := orderOf_dvd_natCard (⟨⟨-1, hneg⟩, hc⟩ : center P)
    rwa [orderOf_eq_prime hz2 hz1] at h
  · exact CFSG.RankThree.SubgroupLists.two_dvd_card_center_of_neg_one_not_mem hq2 hPS hqs hneg

theorem lieModel_psp_of_eq (hq2 : q ≠ 2) {P : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))}
    (hP : P = StatedSp 2 (ZMod q)) (hqs : CFSG.IsQuasisimple P) {S : Type} [Group S]
    (eS : P ⧸ center P ≃* S) : LieModel S .PSp 2 q 1 := by
  subst hP
  have hq : q.Prime := Fact.out
  have : Group.IsPerfect (StatedSp 2 (ZMod q)) := hqs.1
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 (ZMod q))) := by
    refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod q) 2
      (by norm_num) ?_
    rw [Nat.card_zmod]
    by_cases hq3 : q = 3
    · exact Or.inr (Or.inl ⟨hq3, le_rfl⟩)
    · refine Or.inl (Or.inr ?_)
      have h2 := hq.two_le
      omega
  have hZs : Group.IsSolvable (center (StatedSp 2 (ZMod q))) :=
    isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.1 b.2 a)
  have hZ : center (StatedSp 2 (ZMod q)) =
      (StatedScalars (Fin 2 ⊕ Fin 2) (ZMod q)).subgroupOf (StatedSp 2 (ZMod q)) :=
    eq_of_simple_quotients hZs hqs.2.1 hs
  refine Or.inl ⟨by decide, ⟨Fact.out, le_rfl, le_rfl, ?_⟩, ZMod q, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one], ⟨eS.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ)⟩⟩
  simp only [pow_one, ne_eq, Prod.mk.injEq, true_and]
  exact hq2


theorem list_of_quasisimple (hIII : MitchellPartThree) (hq2 : q ≠ 2)
    {P : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))} (hPS : P ≤ StatedSp 2 (ZMod q))
    (hqs : CFSG.IsQuasisimple P) {S : Type} [Group S] (eS : P ⧸ center P ≃* S) :
    2 ∣ Nat.card (center P) ∧
      (((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel S .PSL 2 p 1 ∨ LieModel S .PSL 3 p 1)) ∨
          IsAlt S 6 ∨ IsAlt S 7) ∨
        (P = StatedSp 2 (ZMod q) ∧ LieModel S .PSp 2 q 1) ∨
        (Nonempty (P ≃* SL(2, GaloisField q 2)) ∧ LieModel S .PSL 2 q 2)) := by
  have hq : q.Prime := Fact.out
  have hq3' : 3 ≤ q := by
    have := hq.two_le
    omega
  refine ⟨two_dvd_card_center hq2 hPS hqs, ?_⟩
  rcases CFSG.RankThree.SubgroupLists.mitchell_quasisimple_sp4_of hIII
      CFSG.RankThree.SubgroupLists.fischerSpClique CFSG.RankThree.SubgroupLists.fischerOrthClique
      CFSG.RankThree.SubgroupLists.fischerSpCard CFSG.RankThree.SubgroupLists.fischerOrthCard
      CFSG.RankThree.SubgroupLists.fischerUnitaryCard
      CFSG.RankThree.SubgroupLists.fischerReflectionCard hq2 hPS hqs with
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩
  ·
    have hPeq : P = StatedSp 2 (ZMod q) :=
      Subgroup.eq_of_le_of_card_ge hPS (Nat.card_congr e.toEquiv).symm.le
    exact Or.inr (Or.inl ⟨hPeq, lieModel_psp_of_eq hq2 hPeq hqs eS⟩)
  ·
    have h5 : 5 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq3' 2)
    exact Or.inr (Or.inr ⟨⟨e⟩, Or.inl ⟨by decide,
      CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv S q 2 h5
        (eS.symm.trans (QuotientGroup.congr (center P) (center SL(2, GaloisField q 2)) e
          (Subgroup.map_center_eq e)))⟩⟩)
  ·
    by_cases hq3 : q = 3
    · exfalso
      subst hq3
      have hcard : Nat.card P = 2 ^ 3 * 3 ^ 1 := by
        rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, ZMod.card]
        norm_num
      exact not_isSolvable_of_isQuasisimple hqs
        (TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
          hcard.dvd)
    have hq5 : 5 ≤ q := by
      have h4 : q ≠ 4 := by
        rintro rfl
        norm_num at hq
      omega
    exact Or.inl (Or.inl ⟨q, hq, hq2, Or.inl (Or.inl ⟨by decide,
      statedClassicalModel_psl_two hq5 (eS.symm.trans (QuotientGroup.congr (center P)
        (center SL(2, ZMod q)) e (Subgroup.map_center_eq e)))⟩)⟩)
  ·
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact Or.inl (Or.inl ⟨5, by norm_num, by norm_num, Or.inl (Or.inl ⟨by decide,
      statedClassicalModel_psl_two le_rfl (eS.symm.trans (QuotientGroup.congr (center P)
        (center SL(2, ZMod 5)) e (Subgroup.map_center_eq e)))⟩)⟩)
  ·
    exact Or.inl (Or.inr (Or.inl
      (CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine
        (CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv S 3 2 (by norm_num)
          (eS.symm.trans (QuotientGroup.congr (center P) (center SL(2, GaloisField 3 2)) e
            (Subgroup.map_center_eq e)))))))
  ·
    exact Or.inl (Or.inr (Or.inr ⟨eS.symm.trans e⟩))

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
