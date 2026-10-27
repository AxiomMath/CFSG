module

public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.GF2n.Stroth80.Sec4Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.isIndecSec_Vt_sp (hc : Ctx M Q Z B) {t : G} (hsp : SpNat hc t) :
    IsIndecSec (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z := by
  obtain ⟨K, hK, hKf, hKc, m, hm, hrep⟩ := hsp
  obtain ⟨e, -, he, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKc.trans he)
  rintro ⟨A₁, A₂, hZA₁, hA₁V, hZA₂, hA₂V, hA₁ne, hA₂ne, hsup, hinf, hinv⟩
  have hRU : ∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ A₁, r * u * r⁻¹ ∈ A₁ := by
    intro r hr u hu
    have h : conjSubgroup r A₁ = A₁ := (hinv r hr).1
    rw [← h]
    exact ⟨u, hu, rfl⟩
  rcases hrep.eq_or_eq_of_invariant natIrred_statedSp addCommutantScalar_statedSp
    hZA₁ hA₁V hRU with h₁ | h₁
  · exact hA₁ne h₁
  · have h₂ : A₂ = Z := by
      rw [← hinf]
      rw [h₁]
      exact (inf_of_le_right hA₂V).symm
    exact hA₂ne h₂

theorem Ctx.isIndecSec_vone_of_eq (hc : Ctx M Q Z B) {t r : G} (hsp : SpNat hc t)
    (hV1 : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t) :
    IsIndecSec (Rt M (LB M Q B) t) (Vone Q B (conjSubgroup r B)
      (Vt M (LB M Q B) B Z t)) Z := by
  rw [hV1]
  exact hc.isIndecSec_Vt_sp hsp

end CFSG.RankThree.GF2n.Stroth80
