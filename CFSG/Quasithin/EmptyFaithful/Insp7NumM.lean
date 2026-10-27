module

public import CFSG.Quasithin.EmptyFaithful.Insp7Final
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Insp7

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem numFactAt_of_not_dvd_aut {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      ¬ 2 ^ 7 ∣ Nat.card (MulAut L)) : NumFactAt F := by
  intro L _ _ hq hFL z _ _ Gc _ _ ρ hρ _ ž _ Ŝ _ _ _ hcard
  exfalso
  apply hF L hq hFL
  have h1 : Nat.card Ŝ ∣ Nat.card Gc := Subgroup.card_subgroup_dvd_card Ŝ
  have h2 : Nat.card ρ.range = Nat.card Gc := Nat.card_range_of_injective hρ
  have h3 : Nat.card ρ.range ∣ Nat.card (MulAut L) := Subgroup.card_subgroup_dvd_card ρ.range
  have h4 : 2 ^ 7 ∣ Nat.card Ŝ := by
    rcases hcard with h | h
    · rw [h]
    · rw [h]
      exact pow_dvd_pow 2 (by norm_num)
  refine h4.trans (h1.trans ?_)
  rw [← h2]
  exact h3

theorem numFactAt_of_not_nine_dvd_aut {F : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      ¬ 9 ∣ Nat.card (MulAut L)) : NumFactAt F := by
  intro L _ _ hq hFL z _ _ Gc _ _ ρ hρ _ ž _ Ŝ _ _ _ _ hC
  apply hF L hq hFL
  have h1 : Nat.card (Subgroup.centralizer ({ž} : Set Gc)) ∣ Nat.card Gc :=
    Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card ρ.range = Nat.card Gc := Nat.card_range_of_injective hρ
  have h3 : Nat.card ρ.range ∣ Nat.card (MulAut L) := Subgroup.card_subgroup_dvd_card ρ.range
  have h4 : 9 ∣ Nat.card (Subgroup.centralizer ({ž} : Set Gc)) := ⟨Nat.card Ŝ, hC⟩
  refine h4.trans (h1.trans ?_)
  rw [← h2]
  exact h3

theorem card_mulAut_dvd_mul_outer (L : Type) [Group L] [Finite L] :
    Nat.card (MulAut L) ∣ Nat.card L * Nat.card (Outer L) := by
  have h1 := Subgroup.card_mul_index (Inn L)
  have h2 : Nat.card (Inn L) = Nat.card (L ⧸ Subgroup.center L) := by
    unfold CFSG.ComponentClassification.OuterAutomorphisms.inner
    rw [← ker_conj_eq_center]
    exact (Nat.card_congr
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L)).toEquiv).symm
  have h3 : (Inn L).index = Nat.card (Outer L) := rfl
  have h4 : Nat.card (L ⧸ Subgroup.center L) ∣ Nat.card L := Subgroup.card_quotient_dvd_card _
  rw [← h1, h2, h3]
  exact Nat.mul_dvd_mul_right h4 _

theorem numFactAt_a6 : NumFactAt (fun L _ => Nonempty (L ≃* alternatingGroup (Fin 6))) :=
  numFactAt_of_not_dvd_aut (fun _ _ _ _ ⟨e⟩ => by
    rw [CFSG.QuasithinUnique.DoubleA3.card_mulAut_alt6 e]
    decide)

theorem numFactAt_l33 : NumFactAt L33Fam := by
  refine numFactAt_of_not_dvd_aut (fun L _ _ _ hL hdvd => ?_)
  obtain ⟨hcard, -, -, -, hout⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound L 3 3 1 hL
  have h1 : Nat.card L = 5616 := by
    rw [hcard]
    decide
  have h2 : Nat.card (Outer L) ∣ 2 := by
    have := hout (by norm_num)
    simpa using this
  have h3 := hdvd.trans (card_mulAut_dvd_mul_outer L)
  rw [h1] at h3
  have h4 : Nat.card (Outer L) ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have h5 : 0 < Nat.card (Outer L) := Nat.card_pos
  interval_cases (Nat.card (Outer L))
  · exact absurd h3 (by decide)
  · exact absurd h3 (by decide)

end Insp7

end CFSG.Quasithin
