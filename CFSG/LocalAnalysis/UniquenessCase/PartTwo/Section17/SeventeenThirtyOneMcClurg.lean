module

public import CFSG.Quasithin.Background.IrredInvolutionRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoAutInner
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.Quasithin
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

@[expose] def TwistedF4IrredBound : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), CFSG.Quasithin.Is2F4 n X →
    IrredInvolutionRankBound X (4 * n + 3)

@[expose] def TrialityD4IrredBound : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ),
    CFSG.LocalAnalysis.UniquenessCase.UC22.Is3D4 X n → Odd n →
      IrredInvolutionRankBound X (6 * n)

theorem w4McClurg2F4_of_irredBound
    (h : TwistedF4IrredBound) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.W4McClurg2F4 := by
  intro W _ _ hW Y L n hLY hN h2F4 hfix
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Finite ↥L := Subtype.finite
  have hS : IsSimpleGroup ↥L :=
    (CFSG.LieType.Simplicity.fam_2f4_simplicity ↥L 2 n h2F4).2
  haveI : IsSimpleGroup ↥L := hS
  obtain ⟨k, hk1, hcardk⟩ :=
    CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel h2F4
  have hqpow : 2 ^ 12 ∣ (2 ^ (2 * k + 1)) ^ 12 := by
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hdvd12 : 2 ^ 12 ∣ Nat.card ↥L := by
    rw [hcardk]
    unfold CFSG.Open.ordTwistedF4
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hqpow _) _) _) _
  have h2dvd : 2 ∣ Nat.card ↥L :=
    (Nat.pow_dvd_pow 2 (by norm_num : 1 ≤ 12)).trans hdvd12
  have hcard_gt : 2 < Nat.card ↥L := by
    have hge : 2 ^ 12 ≤ Nat.card ↥L := Nat.le_of_dvd Nat.card_pos hdvd12
    have h212 : (2 : ℕ) < 2 ^ 12 := by norm_num
    omega
  have hnonab : ¬ IsMulCommutative ↥L := by
    intro hcomm
    haveI : IsMulCommutative ↥L := hcomm
    have hp : (Nat.card ↥L).Prime :=
      (Group.is_simple_iff_prime_card (α := ↥L)).1 hS
    rcases Nat.Prime.eq_one_or_self_of_dvd hp 2 h2dvd with h1 | h2
    · omega
    · omega
  have hZ : Subgroup.center ↥L = ⊥ :=
    CFSG.OrderReductions.Helpers.simple_noncommutative_center_eq_bot ↥L hnonab
  obtain ⟨-, -, -, -, -, hinnerRee, -⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions ↥L 2 n h2F4
  have hinner : ∀ α : MulAut ↥L, α ^ 2 = 1 →
      ∃ g : ↥L, ∀ x, α x = g * x * g⁻¹ := by
    intro α hα
    obtain ⟨g, hg⟩ := hinnerRee α hα
    exact ⟨g, fun x => by rw [← hg]; exact MulAut.conj_apply g x⟩
  have hinv : ∃ l : ↥L, orderOf l = 2 := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hb : IrredInvolutionRankBound ↥L (4 * n + 3) := h ↥L n h2F4
  have hm := le_mParam_of_irredInvolutionRankBound hW Y L hLY hN hS hZ hinner hinv hfix
    (4 * n + 3) hb
  omega

theorem w4McClurg3D4_of_irredBound
    (h : TrialityD4IrredBound) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.W4McClurg3D4 := by
  intro W _ _ hW Y L n hLY hN h3D4 hfix hnodd
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Finite ↥L := Subtype.finite
  have hX' : CFSG.Blueprint.ChevalleyExceptionalModel ↥L .trialityD4 2 n :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 h3D4).2
  have hS : IsSimpleGroup ↥L :=
    (CFSG.LieType.Simplicity.fam_3d4_simplicity ↥L 2 n hX').2
  haveI : IsSimpleGroup ↥L := hS
  obtain ⟨-, -, -, -, h4, -⟩ :=
    CFSG.LieType.Chevalley.graph_twisted_exceptional_model_outer_two_part_bound
      ↥L .trialityD4 2 n 3 hX' (Or.inr ⟨rfl, rfl⟩)
  have h4' : 4 ≤ 2 ^ (Nat.card ↥L).factorization 2 := h4
  have hfac : 2 ≤ (Nat.card ↥L).factorization 2 := by
    have h : 2 ^ 2 ≤ 2 ^ (Nat.card ↥L).factorization 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact h4'
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 h
  have h2dvd : 2 ∣ Nat.card ↥L :=
    (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := 1) Nat.prime_two
      Nat.card_pos.ne').2 (by omega)
  have hnonab : ¬ IsMulCommutative ↥L := by
    intro hcomm
    haveI : IsMulCommutative ↥L := hcomm
    have hp : (Nat.card ↥L).Prime :=
      (Group.is_simple_iff_prime_card (α := ↥L)).1 hS
    rcases Nat.Prime.eq_one_or_self_of_dvd hp 2 h2dvd with h1 | h2
    · omega
    · have hcard_ge : 4 ≤ Nat.card ↥L :=
        h4'.trans (Nat.ordProj_le 2 Nat.card_pos.ne')
      omega
  have hZ : Subgroup.center ↥L = ⊥ :=
    CFSG.OrderReductions.Helpers.simple_noncommutative_center_eq_bot ↥L hnonab
  have hinner : ∀ α : MulAut ↥L, α ^ 2 = 1 →
      ∃ g : ↥L, ∀ x, α x = g * x * g⁻¹ := by
    intro α hα
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_3D4TwoAutInner_holds
      ↥L n h3D4 hnodd α ⟨1, by simpa using hα⟩
  have hinv : ∃ l : ↥L, orderOf l = 2 := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hb : IrredInvolutionRankBound ↥L (6 * n) := h ↥L n h3D4 hnodd
  have hm := le_mParam_of_irredInvolutionRankBound hW Y L hLY hN hS hZ hinner hinv hfix
    (6 * n) hb
  exact hm


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
