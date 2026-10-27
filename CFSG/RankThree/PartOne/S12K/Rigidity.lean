module

public import CFSG.RankThree.PartOne.S12K.OrdRigid
public import CFSG.RankThree.PartOne.S12K.RigidDef
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersRee
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartOne.S12K

open CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Ree CFSG.LieType.Chevalley

theorem ordTwistedF4_eq_factored {q : ℕ} (hq : 2 ≤ q) :
    ordTwistedF4 q = q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1) := by
  have h1 : 1 ≤ q := by omega
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : q ^ 2 ≤ q ^ 4 := by nlinarith [Nat.mul_le_mul h2 h2]
  have h4 : 1 ≤ q ^ 4 := by nlinarith
  unfold ordTwistedF4
  zify [h1, h2, h3, h4]
  ring


theorem card_of_reeTitsModel_twistedF4 {T : Type} [Group T] {f : ℕ}
    (h : ReeTitsModel T .twistedF4 2 f) : Nat.card T = ordTwistedF4 (2 ^ f) := by
  obtain ⟨⟨-, -, -, hp, -, hf3⟩, a, hfa, hmodel⟩ := h
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.EvenSmallLie.CatalogOrders.exists_mulEquiv_of_reeTitsRelationModel_F4 hmodel
  have hK2 : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hK' : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1) := hK2
  have hperf := CFSG.LieType.Simplicity.commutator_reeFixed_F4 a (by omega) hK'
  have hZ : Subgroup.center (reeFixed ReeTag.F4 K a) = ⊥ := by
    have hc := ReeTag.large_Ree_fixed_group_center_trivial a K hK2
    rw [eq_bot_iff]
    intro z hz
    have hz' : ReeTag.reeFixedEquivReeGamma K a z ∈ Subgroup.center (ReeTag.F4.reeGamma K a) :=
      (MulEquivClass.apply_mem_center_iff (ReeTag.reeFixedEquivReeGamma K a)).2 hz
    rw [hc, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 ((ReeTag.reeFixedEquivReeGamma K a).injective (hz'.trans (map_one _).symm))
  let eΓ : commutator (reeFixed ReeTag.F4 K a) ≃* reeFixed ReeTag.F4 K a :=
    (MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv
  rw [Nat.card_congr (e.trans (QuotientGroup.congr _ _ eΓ (Subgroup.map_center_eq _))).toEquiv,
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv,
    Nat.card_congr (ReeTag.reeFixedEquivReeGamma K a).toEquiv,
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K
      hK2).1,
    hfa, ordTwistedF4_eq_factored (by
      have : 2 ≤ 2 ^ (2 * a + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact this)]

theorem card_of_reeTitsModel_Tits {T : Type} [Group T] {f : ℕ}
    (h : ReeTitsModel T .Tits 2 f) : Nat.card T = ordTits := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv T 2 f h
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  decide

theorem card_of_lieModel_two {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel S t n 2 f) : StatedLieAdmissible t n 2 f ∧ Nat.card S = charTwoOrder t n f := by
  rcases h with ⟨-, hc⟩ | ⟨rfl, ht, hm⟩ | ⟨rfl, ht, hm⟩ | ⟨rfl, rfl, hm⟩
  · refine ⟨hc.1, ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := CFSG.Timmesfeld.card_statedClassicalModel_two hc
    have hadm := hc.1
    cases t
    case PSL => exact h1 rfl
    case PSU => exact h2 rfl
    case PSp => exact h3 rfl
    case POmegaOdd => exact absurd rfl hadm.2.2.2
    case POmegaPlus => exact h4 rfl
    case POmegaMinus => exact h5 rfl
    all_goals exact hc.2.elim
  · refine ⟨hm.1, ?_⟩
    have hc := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
    cases t <;> first | exact hc | (exfalso; revert ht; decide)
  · cases t
    case twistedG2 => exact absurd hm.1.2.2.2.1 (by norm_num)
    case twistedF4 => exact ⟨hm.1, card_of_reeTitsModel_twistedF4 hm⟩
    case Tits => exact ⟨hm.1, card_of_reeTitsModel_Tits hm⟩
    all_goals exact absurd ht (by decide)
  · obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hm
    refine ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, by omega⟩, by omega⟩, ?_⟩
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', hf]
    simp only [charTwoOrder, ordSuzuki]
    ring

theorem lieRigidity3 : LieRigidity3 := by
  intro S _ t n f hmod
  have main : ∀ (t' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible t' n' 2 f' →
      Nat.card S = charTwoOrder t' n' f' →
      (∀ g : ℕ, StatedClassicalModel S .PSU 3 2 g → t' = .PSU ∧ n' = 3 ∧ f' = g) ∧
      (∀ g : ℕ, StatedClassicalModel S .PSp 2 2 g → t' = .PSp ∧ n' = 2 ∧ f' = g) ∧
      (∀ g : ℕ, StatedClassicalModel S .PSL 2 2 g → t' = .PSL ∧ n' = 2 ∧ f' = g) := by
    intro t' n' f' hadm hcard
    refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg => ?_⟩
    · have hg2 : 2 ≤ g := by
        by_contra hlt
        obtain rfl : g = 1 := by have := hg.1.2.1; omega
        exact hg.1.2.2.2 (by norm_num)
      have hU := (CFSG.Timmesfeld.card_statedClassicalModel_two hg).2.1 rfl
      exact rigid_U hadm hg2 (hcard.symm.trans hU)
    · have hg2 : 2 ≤ g := by
        by_contra hlt
        obtain rfl : g = 1 := by have := hg.1.2.1; omega
        exact hg.1.2.2.2 (by norm_num)
      have hS := (CFSG.Timmesfeld.card_statedClassicalModel_two hg).2.2.1 rfl
      exact rigid_Sp hadm hg2 (hcard.symm.trans hS)
    · have hL := (CFSG.Timmesfeld.card_statedClassicalModel_two hg).1 rfl
      exact rigid_L hadm hg.1.2.1 (hcard.symm.trans hL)
  rcases hmod with hmod | ⟨rfl, rfl, rfl, hT⟩
  · obtain ⟨hadm, hcard⟩ := card_of_lieModel_two hmod
    exact main t n f hadm hcard
  · obtain ⟨hadm, hcard⟩ := card_of_lieModel_two hT
    obtain ⟨hU, hS, hL⟩ := main .Tits 0 1 hadm hcard
    exact ⟨fun g hg => absurd (hU g hg).1 (by decide), fun g hg => absurd (hS g hg).1 (by decide),
      fun g hg => absurd (hL g hg).1 (by decide)⟩

end CFSG.RankThree.PartOne.S12K
