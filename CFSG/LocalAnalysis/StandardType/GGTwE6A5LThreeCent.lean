module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParityAt
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLBridgeDefs
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.Timmesfeld.Orders.ClassicalLinear
import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem card_largeEvenProj_SU_3c {N g : ℕ} (hN : 1 ≤ N) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ g) ^ 2) :
    1 ≤ g ∧ Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g))) =
      CFSG.Open.ordTwistedA N (2 ^ g) := by
  have hg : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  refine ⟨hg, ?_⟩
  change Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU (N + 1) (2 ^ g) K)) = _
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hg hK (by omega),
    CFSG.Open.ordTwistedA, Nat.add_sub_cancel, Nat.mul_comm (N + 1) N]

private theorem card_quotient_center_of_twA_five_3c {R : Type} [Group R] {J : Subgroup R}
    {n : ℕ} (hmark : LargeEvenMarking ↥J (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩)) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = CFSG.Open.ordTwistedA 5 (2 ^ n) := by
  obtain ⟨-, lab', -, hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := largeEvenRawDatum_exists hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, _, _, hK, -, -, θ, -⟩ := hraw
  exact (Nat.card_congr θ.toEquiv).trans (card_largeEvenProj_SU_3c (N := 5) (by norm_num) hK).2

theorem three_mul_ordTwistedA_five_dvd_card_of_conj {R : Type} [Group R] [Finite R]
    (hR : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a) {x : R}
    (hx3 : MulAut.conj x ^ 3 = 1) (hx1 : MulAut.conj x ≠ 1) {J₁ : Subgroup R}
    (hJ₁ : J₁ ≤ ggFix (MulAut.conj x)) {n : ℕ}
    (hmark : LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩)) :
    3 * CFSG.Open.ordTwistedA 5 (2 ^ n) ∣ Nat.card R := by
  haveI := hR
  have hnc : ¬ IsMulCommutative R := fun h => by
    obtain ⟨a, b, hab⟩ := hna
    exact hab (h.is_comm.comm a b)
  have hcen := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  have hx3' : x ^ 3 = 1 := by
    rw [← Subgroup.mem_bot, ← hcen, Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun β : MulAut R => β y) hx3
    simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x ^ 3 = x ^ 3 * y * (x ^ 3)⁻¹ * x ^ 3 := by rw [h]
      _ = x ^ 3 * y := by group
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hxC : x ∈ Subgroup.centralizer (J₁ : Set R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h := mem_ggFix.1 (hJ₁ hj)
    rw [MulAut.conj_apply] at h
    calc j * x = x * j * x⁻¹ * x := by rw [h]
      _ = x * j := by group
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer (J₁ : Set R)) := by
    have h := orderOf_dvd_natCard (⟨x, hxC⟩ : Subgroup.centralizer (J₁ : Set R))
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hx3' hx1'] at h
  rw [← card_quotient_center_of_twA_five_3c hmark,
    CFSG.GroupTheory.card_eq_index_mul_card_quotient_center_mul_card_centralizer J₁, mul_assoc,
    mul_comm 3]
  exact Dvd.dvd.mul_left (mul_dvd_mul_left _ h3) _


theorem ggTwE6A5LAt_of_inner_not_marking_twA_five {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R → ∀ (s : MulAut R) (n : ℕ), s ∈ I → s ^ 3 = 1 → s ≠ 1 → 3 ∣ 2 ^ n + 1 →
        lab.n ∣ n → ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
          ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩)) :
    GGTwE6A5LAt lab := by
  refine (largeEvenLabelAll_and (largeEvenLabelAll_n_dvd_of_isComponentOf_ggFix hlab) h).mono ?_
  rintro R _ I _ ⟨hp, hno⟩ hR hna hfin B' s n hB hBI hsB hs1 _ h3n J₁ hJ₁ _ hmark
  exact absurd hmark (hno hR hna hfin s n (hBI s hsB) (hB.2 s hsB) hs1 h3n
    (hp hR hna hfin 3 Nat.prime_three (by norm_num) s (hBI s hsB) (hB.2 s hsB) hs1 J₁ hJ₁ _
      (by simp) hmark) J₁ hJ₁)

end CFSG.StandardType.SCFourCover

end
