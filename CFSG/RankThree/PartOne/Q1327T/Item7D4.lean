module

public import CFSG.RankThree.PartOne.Q1327T.Item7D4Inv
public import CFSG.RankThree.PartOne.Q1327T.Item7D4S
public import CFSG.RankThree.PartOne.K133X.D4
public import CFSG.RankThree.PartOne.K128.D4Syl

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem card_multiplier_trialityD4_dvd_one (f : ℕ) :
    Nat.card (Blueprint.Multiplier.generic .trialityD4 0 2 f ×
      Blueprint.Multiplier.exceptional .trialityD4 0 2 f) ∣ 1 := by
  have hgen : Blueprint.Multiplier.genericOrders .trialityD4 0 2 f = (1, 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .trialityD4 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem D4_prime_cases {Q₂ p : ℕ} (hp : p.Prime) (hQ : 2 ≤ Q₂) (hpQ : ¬ p ∣ Q₂)
    (h : p ∣ Q₂ ^ 12 * (Q₂ ^ 2 - 1) * (Q₂ ^ 6 - 1) * (Q₂ ^ 8 + Q₂ ^ 4 + 1)) :
    p ∣ Q₂ ^ 2 - 1 ∨ (p : ℤ) ∣ (Q₂ : ℤ) ^ 2 + 1 * (Q₂ : ℤ) + 1 ∨
      (p : ℤ) ∣ (Q₂ : ℤ) ^ 2 + (-1) * (Q₂ : ℤ) + 1 ∨ p ∣ Q₂ ^ 4 - Q₂ ^ 2 + 1 := by
  have h1 : 1 ≤ Q₂ := by omega
  have h2 : Q₂ ≤ Q₂ ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : Q₂ ^ 2 ≤ Q₂ ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e6 : Q₂ ^ 6 - 1 = (Q₂ ^ 2 - 1) * (Q₂ ^ 4 + Q₂ ^ 2 + 1) := by
    have : 1 ≤ Q₂ ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : 1 ≤ Q₂ ^ 6 := Nat.one_le_pow _ _ (by omega)
    zify [*]
    ring
  have e8 : Q₂ ^ 8 + Q₂ ^ 4 + 1 = (Q₂ ^ 4 + Q₂ ^ 2 + 1) * (Q₂ ^ 4 - Q₂ ^ 2 + 1) := by
    zify [h3]
    ring
  have e4 : Q₂ ^ 4 + Q₂ ^ 2 + 1 = (Q₂ ^ 2 + Q₂ + 1) * (Q₂ ^ 2 - Q₂ + 1) := by
    zify [h2]
    ring
  have hfin : p ∣ Q₂ ^ 4 + Q₂ ^ 2 + 1 → (p : ℤ) ∣ (Q₂ : ℤ) ^ 2 + 1 * (Q₂ : ℤ) + 1 ∨
      (p : ℤ) ∣ (Q₂ : ℤ) ^ 2 + (-1) * (Q₂ : ℤ) + 1 := fun hd => by
    rw [e4] at hd
    rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · left
      have := Int.natCast_dvd_natCast.2 hd
      push_cast at this
      simpa using this
    · right
      have := Int.natCast_dvd_natCast.2 hd
      rw [Nat.cast_add, Nat.cast_sub h2, Nat.cast_one, Nat.cast_pow] at this
      simpa [sub_eq_add_neg] using this
  have hQ12 : ¬ p ∣ Q₂ ^ 12 := fun hd => hpQ (hp.dvd_of_dvd_pow hd)
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd h hQ12
      · exact Or.inl h
    · rw [e6] at h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl h
      · rcases hfin h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
  · rw [e8] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases hfin h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

set_option linter.unusedSectionVars false

theorem row8U3At_leaf7_eight
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 8) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hiso⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have := h.elem
  have hmodel := K133X.chevalleyExceptionalModel_trialityD4_of_isoLie hq2 hiso
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hLie : Models.LieModel (Q ⧸ Subgroup.center Q) .trialityD4 0 2 q.exponent :=
    ⟨hmodel.1, Or.inr ⟨rfl, ⟨.trialityD4 q, hv⟩, ⟨hq2, rfl⟩, ⟨e0⟩⟩⟩
  have hZ : Subgroup.center Q = ⊥ := by
    refine center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p hLie fun hd => ?_
    have := Nat.le_of_dvd (by norm_num) (hd.trans (card_multiplier_trialityD4_dvd_one q.exponent))
    omega
  refine h.concl_of_inv hZ ?_
  have hf1 : 1 ≤ q.exponent := hmodel.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨θ⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf1 hmodel.2
  have hKq : Nat.card K = (2 ^ q.exponent) ^ 3 := hK
  let ce : Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eQ : Q ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := ce.trans θ
  refine exists_inv_of_equiv eQ ?_
  have hEel : IsElementaryAbelian p (Ē.map eQ.toMonoidHom) := IsElementaryAbelian.map _
  have hEcard : Nat.card (Ē.map eQ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective eQ.injective, h.card]
  have hpg : IsPGroup p (Ē.map eQ.toMonoidHom) := IsElementaryAbelian.isPGroup p _
  have hQ₂ : 2 ≤ 2 ^ q.exponent := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hf1
  have hpQ : ¬ p ∣ 2 ^ q.exponent := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hCcard := (triality_both_orientations_exact_finite_order 2 q.exponent Nat.prime_two hf1 K
    hKq 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  have hpC : p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    have h1 := Subgroup.card_subgroup_dvd_card (Ē.map eQ.toMonoidHom)
    rw [hEcard] at h1
    exact (dvd_pow_self p two_ne_zero).trans h1
  rw [hCcard] at hpC
  rcases D4_prime_cases hp hQ₂ hpQ hpC with hd | hd | hd | hd
  · exact exists_inv_of_isPGroup_D4_split hf1 K hKq σ hσ hp hp5 hd hpg
  · exact exists_inv_of_isPGroup_D4_36 hf1 K hKq σ hσ (ε := 1) (Or.inl rfl) hp (by omega) hd hpg
  · exact exists_inv_of_isPGroup_D4_36 hf1 K hKq σ hσ (ε := -1) (Or.inr rfl) hp (by omega) hd hpg
  · exfalso
    have hrk := K128.pRank_le_one_D4_twelve Nat.prime_two hf1 K hKq σ hσ hp hp5 hd
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt _ hEel hEcard
    omega

end CFSG.RankThree.PartOne.Q1327T
