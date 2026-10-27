module

public import CFSG.LocalAnalysis.StandardType.GGRCSShadowBasic
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatSeitzExc
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalInner
public import CFSG.Holt.SmallGroups
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import Certificates.Certificate9530

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Small

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

private theorem ggShS_factorial_le_of_lt_six {n : ℕ} (hn : n < 6) : n.factorial ≤ 120 := by
  interval_cases n <;> decide

theorem ggShadow_false_altSix (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hKH : ¬ CFSG.generalizedFitting W ≤ H) (hp : p = 3)
    (he : Nonempty (↥(CFSG.generalizedFitting W) ≃* alternatingGroup (Fin 6))) : False := by
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hyp.2.1.1
  have hKcard : Nat.card ↥(CFSG.generalizedFitting W) = 360 := by
    rw [Nat.card_congr he.some.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
    norm_num
  have hX : H.subgroupOf (CFSG.generalizedFitting W) ≠ ⊤ :=
    ggSeitzExc_subgroupOf_ne_top hKH
  have h3 : ¬ 3 ∣ (H.subgroupOf (CFSG.generalizedFitting W)).index :=
    hp ▸ ggSeitzExc_not_dvd_index_flat hyp
  have hfact : 360 ≤ (H.subgroupOf (CFSG.generalizedFitting W)).index.factorial := by
    rw [← hKcard]
    exact CFSG.Holt.SmallGroups.card_le_factorial_index hX
  have hidx6 : 6 ≤ (H.subgroupOf (CFSG.generalizedFitting W)).index := by
    by_contra h
    push Not at h
    have h120 : (H.subgroupOf (CFSG.generalizedFitting W)).index.factorial ≤ 120 :=
      ggShS_factorial_le_of_lt_six h
    omega
  have hmul : Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) *
      (H.subgroupOf (CFSG.generalizedFitting W)).index = 360 := by
    rw [Subgroup.card_mul_index, hKcard]
  have hlt : Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) < 60 := by
    have hle1 : Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) * 6 ≤ 360 := by
      rw [← hmul]
      exact Nat.mul_le_mul_left _ hidx6
    have hle : Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) ≤ 60 := by omega
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      rw [h] at hmul
      have hidx : (H.subgroupOf (CFSG.generalizedFitting W)).index = 6 := by omega
      exact h3 (by rw [hidx]; norm_num)
  exact ggShadow_not_isSolvable hperf hL
    (CFSG.GroupTheory.groups_order_below_sixty_solvable hlt)

theorem ggShadow_false_lTwoEight (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hKH : ¬ CFSG.generalizedFitting W ≤ H) (hp : p = 3)
    (hK : LieModel ↥(CFSG.generalizedFitting W) .PSL 2 2 3) : False := by
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hyp.2.1.1
  have hcard : Nat.card ↥(CFSG.generalizedFitting W) = 504 := by
    have h := (CFSG.Timmesfeld.card_statedClassicalModel_two
      (hK.statedClassicalModel (by decide))).1 rfl
    rw [h]
    norm_num [CFSG.Open.ordA]
  have hX : H.subgroupOf (CFSG.generalizedFitting W) ≠ ⊤ :=
    ggSeitzExc_subgroupOf_ne_top hKH
  have h3 : ¬ 3 ∣ (H.subgroupOf (CFSG.generalizedFitting W)).index :=
    hp ▸ ggSeitzExc_not_dvd_index_flat hyp
  exact ggShadow_not_isSolvable hperf hL
    (ggIsSolvable_of_not_dvd_index_of_card_eq_504 hcard hX h3)

theorem ggShadow_false_szThirtyTwo
    (hyp : GGHypThreeSixteenFlat p H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hK : LieModel ↥(CFSG.generalizedFitting W) .twistedB2 0 2 5) : False := by
  have hcard : Nat.card ↥(CFSG.generalizedFitting W) = 32537600 :=
    CFSG.HardMathSupport.Dickson.Bal207.card_of_suzukiModel_two_five hK.suzukiModel.2
  obtain ⟨C, hC⟩ := ggExists_component_of_layer_ne_bot hL
  obtain ⟨-, hmark⟩ := hyp.2.2.1 C hC
  obtain ⟨lab, -, R, _, I, F, θ, -, -, ⟨htag, -⟩, hmod⟩ :=
    largeEvenMarking_exists_markedModel hmark
  refine ggMarkedModel_not_dvd_szThirtyTwo htag hmod ?_
  rw [← Nat.card_congr θ.toEquiv, ← hcard]
  exact (Subgroup.card_quotient_dvd_card _).trans
    ((ggShadow_card_quotComponent_dvd hperf hC).trans
      (Subgroup.card_subgroup_dvd_card _))

end Small

end CFSG.StandardType
