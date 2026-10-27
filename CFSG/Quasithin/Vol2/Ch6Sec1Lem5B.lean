module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5A
public import CFSG.Quasithin.Background.E2Three

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

structure Cx615 (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ) : Prop where
  hyp : Hyp611 G T M L V n
  hH : IsHStar T M H
  notZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  ZV : quasithinOmegaOneCenter T ≤ V

theorem Hyp611.cx615 (h614 : Stmt6_1_4) (h : Hyp611 G T M L V n) (hH : IsHStar T M H)
    (hZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    Cx615 G T M L (reducedAggregate (L ⊔ T)) H n :=
  ⟨h.reduced_ch615 h614, hH, hZ, h.omega_le_reduced_ch615⟩

namespace Cx615

variable (c : Cx615 G T M L V H n)
include c

abbrev UH (T H : Subgroup G) : Subgroup G := conjClosure (quasithinOmegaOneCenter T) H

theorem isSylowTwoOf : IsSylowTwoOf T H := c.hyp.toHyp5_0_1.isSylowTwoOf c.hH.1.1

theorem minParabolic (h331 : Stmt3_3_1) : MinParabolic H T (H ⊓ M) :=
  (c.hyp.toHyp5_0_1.minParabolic_of_isHStar h331 c.hH).1

theorem charTwo : CharTwo H :=
  charTwo_of_inH' c.hyp.qtke c.hyp.sylow c.hH.1

theorem sqtk : SQTKGroup ↥H := by
  obtain ⟨hk, hq⟩ := isSQTKSub_of_inH c.hyp.qtke c.hyp.simple c.hyp.nonabelian c.hH.1
  exact ⟨hq, hk⟩

theorem UH_red : IsElemAbelian 2 (UH T H) ∧ IsTwoReducedIn H (UH T H) := by
  obtain ⟨-, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo c.isSylowTwoOf c.charTwo le_rfl
  exact ⟨hel, hred⟩

theorem not_le_centralizer_UH : ¬ H ≤ Subgroup.centralizer (UH T H : Set G) := by
  intro hle
  exact c.notZ
    (hle.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ H))))

theorem thompsonJ_not_le (h331 : Stmt3_3_1) (h5172 : Stmt5_1_7_two) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (UH T H : Set G) := by
  have hMP := c.minParabolic h331
  have hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro hb
    apply c.notZ
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
    exact hb
  obtain ⟨-, hKeq, -⟩ := h5172 G T M L V H n c.hyp.toHyp5_0_1 c.hyp.module c.hH hZH
  have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  intro hJC
  have hJO : thompsonJ T ≤ pCoreOf 2 H := by
    rw [← hMP.inf_centralizer_eq_pCoreOf c.UH_red.2 c.not_le_centralizer_UH]
    exact le_inf hJT hJC
  have hii := hMP.commutator_lt_iff_le_pCoreOf hJT hTJ
  rw [twoResidual_eq_oTwoUpper'] at hii
  have hlt := hii.mpr hJO
  rw [← hKeq] at hlt
  exact lt_irrefl _ hlt

theorem e23 (h331 : Stmt3_3_1) (h5172 : Stmt5_1_7_two) (he23 : E2.E23Statement) :
    E2.E23Concl H T (UH T H) c.UH_red.1 :=
  he23 G H T (H ⊓ M) (UH T H) c.UH_red.1 (c.minParabolic h331) c.sqtk c.charTwo c.UH_red.2
    (c.thompsonJ_not_le h331 h5172)

end Cx615

end CFSG.Quasithin.H13
