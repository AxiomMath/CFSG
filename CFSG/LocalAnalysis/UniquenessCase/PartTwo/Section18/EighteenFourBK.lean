module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourWeak
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeCalW

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L K : Subgroup G}

namespace A5Config18

theorem bBar_eq_two_of_normal (c : A5Config18 D V₀ V L K) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G) {J : Subgroup G}
    (hJ : J ∈ calC D.M) (hJn : (J.subgroupOf D.M).Normal)
    (hJ1 : barSub ⊥ V c.elemAbelian J ≠ ⊥)
    (hJU : UniqueMax D.M (J ⊔ F12.Wi 1 D.T V))
    (hb : bBar J D.M ⊥ V c.elemAbelian ≤ 2) :
    bBar J D.M ⊥ V c.elemAbelian = 2 := by
  have hp125 : Hyp125 D ⊥ V := by
    rw [← c.v0]
    exact c.pair.data.hyp.hyp125
  obtain ⟨hWs, -⟩ : InCalWStar D.M D.T V ∧ (⊥ : Subgroup G) = ⊥ := by
    rcases hp125.1 with h1 | ⟨h0, -, -⟩
    · exact h1
    · exact absurd rfl h0.1.1
  have hJM : J ≤ D.M := hJ.1.le
  have hJsub : CFSG.Open.IsSubnormal J D.M := .step hJM hJn (.refl D.M)
  have hU : UniqueMax D.M (UC22.conjClosure D.M J ⊔ D.T) := by
    rw [uc22p2214_conjClosure_eq_of_normal hJM hJn]
    exact uc22p22u_uniqueMax_mono D
      (sup_le_sup_left ((S17.Wi_eq_wClos 1 D.T V c.elemAbelian).le.trans (E3.wClos_le 1 D.T)) J)
      (sup_le hJM D.sylowM.le) hJU
  have h1223 := twelve_twentyThree_one_of_inCalW D hx h61 h126 h111 hp125.2 hWs.1
    c.elemAbelian hJsub hJ.2.2 hJ1 hU
  rw [uc22p2214_conjClosure_eq_of_normal hJM hJn] at h1223
  have hm : mBar D.M ⊥ V c.elemAbelian = 4 := c.numerics.1
  have hk : D.k = 2 := c.numerics.2.2.1
  omega

theorem bParam_eq_two (c : A5Config18 D V₀ V L K) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) (h127 : R127 D) (h119 : R119W D) (h77 : W4Lem7_7) :
    bParam (barSub ⊥ V c.elemAbelian L) (Mbar D.M ⊥ V c.elemAbelian) = 2 ∧
      bParam (barSub ⊥ V c.elemAbelian K) (Mbar D.M ⊥ V c.elemAbelian) = 2 := by
  have hb := c.pair.bBar_le_two_gen c.numerics.2.1.le
  rcases c.pair.dichotomy with ⟨-, hsw⟩ | ⟨-, hLn, hKn⟩
  · have hamax := c.pair.aBar_eq_max_gen c.v0 h127 h119 h77 c.numerics.2.1
    exact c.pair.bParam_eq_two_of_swap c.v0 hb.1 hb.2 hamax c.numerics.2.1 hsw
  · exact ⟨c.bBar_eq_two_of_normal hx h61 h126 h111 c.pair.mem_calC_L hLn c.barSubL
      c.uniqueMaxL hb.1,
      c.bBar_eq_two_of_normal hx h61 h126 h111 c.pair.mem_calC hKn c.barSubK
        c.uniqueMaxK hb.2⟩

theorem trichotomy_all (c : A5Config18 D V₀ V L K) (hW : W4Thm14_4)
    (hKG : IsKGroup ↥(Mbar D.M ⊥ V c.elemAbelian))
    (hO2 : O2Trivial (Mbar D.M ⊥ V c.elemAbelian))
    (hBasic : IsBasicModule (Mbar D.M ⊥ V c.elemAbelian))
    (hcompL : IsComponentOf (barSub ⊥ V c.elemAbelian L) (Mbar D.M ⊥ V c.elemAbelian))
    (hcompK : IsComponentOf (barSub ⊥ V c.elemAbelian K) (Mbar D.M ⊥ V c.elemAbelian))
    (hne : barSub ⊥ V c.elemAbelian L ≠ barSub ⊥ V c.elemAbelian K)
    (hXnorm : ((barSub ⊥ V c.elemAbelian L ⊔ barSub ⊥ V c.elemAbelian K).subgroupOf
      (Mbar D.M ⊥ V c.elemAbelian)).Normal)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (h127 : R127 D) (h119 : R119W D) (h77 : W4Lem7_7) :
    CaseOne18 D V L K c.elemAbelian ∨ CaseTwo18 D V L K c.elemAbelian ∨
      CaseThree18 D V L K c.elemAbelian := by
  have hp125 : Hyp125 D ⊥ V := by
    rw [← c.v0]
    exact c.pair.data.hyp.hyp125
  obtain ⟨hbL, hbK⟩ := c.bParam_eq_two hx h61 h126 h111 h127 h119 h77
  have hLalt : IsAlt ↥(barSub ⊥ V c.elemAbelian L) 5 :=
    isAlt_barSub_of_isAlt_bar2 hp125 c.pair.mem_calC_L c.barSubL c.pair.data.alt
  have hKalt : IsAlt ↥(barSub ⊥ V c.elemAbelian K) 5 :=
    isAlt_barSub_of_isAlt_bar2 hp125 c.pair.mem_calC c.barSubK c.pair.alt_K
  exact c.trichotomy hW hKG hO2 hBasic hcompL hcompK hLalt hKalt hne hXnorm hbL hbK
    (c.fixV_of_normal hne)

end A5Config18

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
