module

public import CFSG.RankThree.PartTwo.Sec6.HeringB3Tools
public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofKFacts
import CFSG.RankThree.PartOne.RF4.FinalKFacts
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.KFacts.K71Residual

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts

section Certs


theorem not_suzukiOrder_dvd_35942400 {a : ℕ} (ha : 1 ≤ a) : ¬ suzukiOrder a ∣ 35942400 := by
  intro h
  have haB := le_of_suzukiOrder_dvd (M := 35942400) (B := 5) (by norm_num) (by norm_num) h
  interval_cases a <;> exact absurd h (by decide)

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem exists_order_three_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x : ReeTag.F4.reeGamma K a, x ≠ 1 ∧ x ^ 3 = 1 := by
  obtain ⟨u, -, hu1, hu3, -⟩ := Sec8.Item8KFactsProof.reeGamma_exists_e9 a K hK
  exact ⟨u, hu1, hu3⟩

theorem perfSubnormalBot_centralizer_reeF4 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : ReeTag.F4.reeGamma K a) (hy3 : y ^ 3 = 1) :
    PerfSubnormalBot (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hy1 : y = 1
  · subst hy1
    have hC : Subgroup.centralizer ({1} : Set (ReeTag.F4.reeGamma K a)) = ⊤ := by
      ext z
      refine ⟨fun _ => Subgroup.mem_top z, fun _ => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_one z).trans (one_mul z).symm
    rw [hC]
    haveI : IsSimpleGroup (ReeTag.F4.reeGamma K a) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 ha hK
    obtain ⟨x, hx1, hx3⟩ := exists_order_three_reeGamma hK
    exact perfSubnormalBot_of_isSimpleGroup Subgroup.topEquiv.isSimpleGroup
      ⟨x, Subgroup.mem_top x, hx1, hx3⟩
  · have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    obtain ⟨K', _, _, hK', ⟨e⟩⟩ := Sec8.ReeF4Conj2Proof.kF83ReeCentThree_holds a K ha hK y hyo
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h8 : 2 < 2 ^ (2 * a + 1) := by
      calc 2 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
      (f := 2 * a + 1) (n := 3) hK' le_rfl (by
        intro h32
        have := congrArg Prod.snd h32
        simp only at this
        omega)).1
    have hcard := Sec8.Item87Proof.card_statedSU_three_two (F := K') (f := 2 * a + 1) hK'
    have h3 : 3 ∣ Nat.card (CFSG.Open.StatedSU 3 (2 ^ (2 * a + 1)) K') := by
      rw [hcard]
      refine Dvd.dvd.mul_left (Dvd.dvd.mul_right (three_dvd_sq_sub_one
        (not_three_dvd_two_pow _)) _) _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hx3 : x ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have hx1 : x ≠ 1 := fun h => by simp [h] at hx
    have hN : PerfSubnormalBotGrp (inSubgroup perfectResidual
        (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)))) :=
      perfSubnormalBotGrp_of_mulEquiv e (perfSubnormalBotGrp_of_isQuasisimple hq ⟨x, hx1, hx3⟩)
    exact perfSubnormalBot_of_le_grp (Subgroup.map_subtype_le _)
      (fun Y hYC hYp => le_inSubgroup_perfectResidual hYp hYC) hN

theorem b3Fix_reeF4_of_outer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {β : MulAut (ReeTag.F4.reeGamma K a)} (hβ : β ^ 3 = 1) (hout : ¬ IsInnerAut β)
    {C : Subgroup (ReeTag.F4.reeGamma K a)} (hC : ∀ z, z ∈ C ↔ β z = z) : B3Fix C := by
  obtain ⟨σ, hσ, hcos⟩ := KFacts.largeRee_order_three_inFieldCoset ha hK hβ hout
  obtain ⟨x, hx⟩ := CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj a K hK σ hσ β hβ hcos
  obtain ⟨b, hchar, hcard, -, ι, hιinj, hιrange⟩ :=
    Sec8.Item8KFactsProof.exists_fixedPoints_reeGammaFieldAut hK σ hσ
  have hmap := map_conj_fixed_eq x hx hC (R := ι.range) (fun y => hιrange y)
  have hB : B3Fix ι.range := by
    haveI : CharP (fixSubfield σ) ReeTag.F4.prime := hchar
    by_cases hb : 1 ≤ b
    · haveI : IsSimpleGroup (ReeTag.F4.reeGamma (fixSubfield σ) b) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hcard
      have hs' : IsSimpleGroup ι.range := (MonoidHom.ofInjective hιinj).symm.isSimpleGroup
      obtain ⟨x₃, hx1, hx3⟩ := exists_order_three_reeGamma (K := fixSubfield σ) hcard
      refine b3Fix_of_perfSubnormalBot (perfSubnormalBot_of_isSimpleGroup hs'
        ⟨ι x₃, ⟨x₃, rfl⟩, fun h => hx1 (hιinj (h.trans (map_one ι).symm)), ?_⟩)
      rw [← map_pow, hx3, map_one]
    · have hb0 : b = 0 := by omega
      subst hb0
      refine b3Fix_of_card_dvd (M := 35942400) ?_ fun n hn => not_suzukiOrder_dvd_35942400 hn
      have hcr : Nat.card ι.range = Nat.card (ReeTag.F4.reeGamma (fixSubfield σ) 0) :=
        (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm
      rw [hcr,
        (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
          0 (fixSubfield σ) hcard).1]
      exact dvd_of_eq (by norm_num)
  exact b3Fix_of_map (MulAut.conj x⁻¹ : ReeTag.F4.reeGamma K a ≃* _) (by rw [hmap]; exact hB)

theorem threePrimeB3_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ThreePrimeB3 (ReeTag.F4.reeGamma K a) := by
  refine threePrimeB3_of_b3Fix fun β hβ C hC => ?_
  by_cases hin : IsInnerAut β
  · obtain ⟨y, rfl⟩ := hin
    have hy3 := pow_three_eq_one_of_conj_pow_three
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK) hβ
    rw [fixed_conj_eq_centralizer hC]
    exact b3Fix_of_perfSubnormalBot (perfSubnormalBot_centralizer_reeF4 ha hK y hy3)
  · exact b3Fix_reeF4_of_outer ha hK hβ hin hC

theorem threePrimeB3_of_reeTitsModel {X : Type} [Group X] {f : ℕ}
    (h : ReeTitsModel X .twistedF4 2 f) : ThreePrimeB3 X := by
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma h
  exact threePrimeB3_of_mulEquiv e (threePrimeB3_reeGamma ha hK)

end Certs

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
