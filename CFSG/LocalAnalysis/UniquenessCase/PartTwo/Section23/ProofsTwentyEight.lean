module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.Adapters.LieModelOrders
public import CFSG.GroupTheory.SquarefreeOrderClosure
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.CyclicSubgroup.NormalizerCommutator
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmega
public import CFSG.LocalAnalysis.UniquenessCase.UC1K43Ext
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UCK
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem two_pow_mul_ne {m : ℕ} (hm : 1 ≤ m) :
    2 ^ m * (2 ^ (2 * m) - 1) ≠ 2 ^ (2 * m) * (2 ^ (4 * m) - 1) := by
  have h1 : 2 ^ m < 2 ^ (2 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (2 * m) ≤ 2 ^ (4 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 1 < 2 ^ (2 * m) := Nat.one_lt_two_pow (by omega)
  exact (Nat.mul_lt_mul_of_lt_of_le h1 (Nat.sub_le_sub_right h2 1) (by omega)).ne

theorem isL2_two_mul_of_isOmegaMinus_four {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hO : IsOmegaMinus X 4 m) : IsL2 X (2 * m) := by
  obtain ⟨-, K, hKfield, hKfin, b, c, hKcard, hirr, he⟩ := hO
  letI : Field K := hKfield
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  obtain ⟨e⟩ := he
  let P : HypPair (quadMinus 2 K b c) := minusPair K b c (⟨0, by norm_num⟩ : Fin 1)
  have hv₀ : quadMinus 2 K b c (P.e + P.f) ≠ 0 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (Q := quadMinus 2 K b c) (Q₀ := StatedQuadMinus 2 K b c)
    (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c) ⟨P.e + P.f, hv₀⟩
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus 2 K b c)) ≃*
      StatedOmega (StatedQuadMinus 2 K b c) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_isL2_of_omegaMinus4 hm hKcard b c
    hirr (e.trans eΩ)

theorem not_isOmegaMinus_four_of_isL2 {X : Type} [Group X] {m : ℕ}
    (hO : IsOmegaMinus X 4 m) (hL : IsL2 X m) : False := by
  have hm : 1 ≤ m := hL.admissible.2.1
  have hL2 := isL2_two_mul_of_isOmegaMinus_four hm hO
  have hcard_small : Nat.card X = 2 ^ m * (2 ^ (2 * m) - 1) := by
    rw [hL.card_eq_lieOrd (by norm_num : 2 ≠ 0)]
    have h := CFSG.RankThree.PartOne.KFU.ordA_one_two_pow hm
    have hpow : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by
      conv_lhs => rw [← pow_mul]
      congr 1
      ring
    rw [hpow] at h
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h
  have hcard_big : Nat.card X = 2 ^ (2 * m) * (2 ^ (4 * m) - 1) := by
    rw [hL2.card_eq_lieOrd (by norm_num : 2 ≠ 0)]
    have h := CFSG.RankThree.PartOne.KFU.ordA_one_two_pow (by omega : 1 ≤ 2 * m)
    have hpow : (2 ^ (2 * m)) ^ 2 = 2 ^ (4 * m) := by
      conv_lhs => rw [← pow_mul]
      congr 1
      ring
    rw [hpow] at h
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using h
  exact two_pow_mul_ne hm (hcard_small.symm.trans hcard_big)

namespace Ctx23L

theorem n_eq_pRank {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h52 : S23_5_2 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) :
    c.n = CFSG.Open.pRank 2 D.Z := by
  rcases h52 h1930 c with h | ⟨-, hOm, -⟩
  · exact h
  · exact absurd (h23 h1930 c).choose_spec.1
      (not_isOmegaMinus_four_of_isL2 hOm)

theorem orderOf_squarefree_of_mem_calB1 {T M L A : Subgroup G}
    (hA : A ∈ calB1 T M L) {x : G} (hx : x ∈ A) : Squarefree (orderOf x) := by
  obtain ⟨-, hAcomm, B, C, hBmem, hCcomm, -, hCsyl, hAeq, -, -, -⟩ := hA
  rw [hAeq] at hx hAcomm
  haveI : IsMulCommutative ↥(B ⊔ C) := hAcomm
  have hBcent : B ≤ Subgroup.centralizer (C : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h := IsMulCommutative.is_comm.comm
      (⟨b, Subgroup.mem_sup_left hb⟩ : ↥(B ⊔ C))
      (⟨c, Subgroup.mem_sup_right hc⟩ : ↥(B ⊔ C))
    exact congrArg Subtype.val h.symm
  have hBC : B ≤ Subgroup.normalizer (C : Set G) :=
    hBcent.trans (Subgroup.centralizer_le_normalizer (C : Set G))
  have hxmem : x ∈ (B : Set G) * (C : Set G) := by
    have hx' : x ∈ ((B ⊔ C : Subgroup G) : Set G) := hx
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right B C hBC] at hx'
  obtain ⟨b, hbB, c, hcC, hbc⟩ := hxmem
  have hcomm : Commute b c := by
    have h := IsMulCommutative.is_comm.comm
      (⟨b, Subgroup.mem_sup_left hbB⟩ : ↥(B ⊔ C))
      (⟨c, Subgroup.mem_sup_right hcC⟩ : ↥(B ⊔ C))
    exact congrArg Subtype.val h
  have hsqb : Squarefree (orderOf b) :=
    Squarefree.squarefree_of_dvd (Subgroup.orderOf_dvd_natCard B hbB) hBmem.2.2.1
  have hsqc : Squarefree (orderOf c) :=
    CFSG.GroupTheory.orderOf_squarefree_of_forall_sylow_square hCcomm hCsyl hcC
  have hdvd : orderOf x ∣ Nat.lcm (orderOf b) (orderOf c) := by
    rw [← hbc]
    exact hcomm.orderOf_mul_dvd_lcm
  have hlcm : Squarefree (Nat.lcm (orderOf b) (orderOf c)) := by
    refine Nat.squarefree_of_factorization_le_one
      (Nat.lcm_ne_zero (orderOf_pos b).ne' (orderOf_pos c).ne') fun p => ?_
    rw [Nat.factorization_lcm (orderOf_pos b).ne' (orderOf_pos c).ne']
    exact max_le (Squarefree.natFactorization_le_one p hsqb)
      (Squarefree.natFactorization_le_one p hsqc)
  exact Squarefree.squarefree_of_dvd hdvd hlcm

theorem commutator_bar_mem_centralizer_of_isCyclic {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {b t : G} (hbB : b ∈ c.B) (ht : t ∈ D.T)
    {Dbar : Subgroup (Bar2 D.M)} (hDn : Dbar.Normal) (hcyc : IsCyclic ↥Dbar) :
    ⁅uc22p21cPi D.M ⟨b, c.hBM (c.hle hbB)⟩,
      uc22p21cPi D.M ⟨t, D.sylowM.le ht⟩⁆ ∈ Subgroup.centralizer (Dbar : Set (Bar2 D.M)) := by
  let bbar : Bar2 D.M := uc22p21cPi D.M ⟨b, c.hBM (c.hle hbB)⟩
  let tbar : Bar2 D.M := uc22p21cPi D.M ⟨t, D.sylowM.le ht⟩
  let Tbar : Subgroup (Bar2 D.M) := barImage D.M D.T
  have htbar : tbar ∈ Tbar :=
    uc22p21c_mem_barImage.2 ⟨⟨t, D.sylowM.le ht⟩, ht, rfl⟩
  have hnorm : ∀ U : Subgroup (Bar2 D.M),
      U ≤ Subgroup.normalizer (Dbar : Set (Bar2 D.M)) :=
    fun U => Subgroup.le_normalizer_of_normal
  have hle := CFSG.GroupTheory.CyclicSubgroup.commutator_le_centralizer Dbar
    (Subgroup.zpowers bbar) Tbar (hnorm _) (hnorm _)
  exact hle (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers bbar) htbar)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
