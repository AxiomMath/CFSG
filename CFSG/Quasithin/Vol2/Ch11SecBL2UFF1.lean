module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UKp
public import CFSG.Quasithin.Vol2.Ch11SecBFactsG2S
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Cases
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

section U3

variable {Kp Y : Type} [Group Kp] [Group Y] [Finite Y] [IsSimpleGroup Y] [Group.IsPerfect Kp]
  (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup Kp} [N.Normal] (hN : IsPGroup 2 N)
  (hQ : CFSG.Open.IsQuasisimple (Kp ⧸ N)) (ψ : Kp →* Y) (hψ : Function.Surjective ψ) {k : ℕ}
  (hk : 2 ≤ k) (hU : IsPSU 3 2 k Y)
include hY hN hQ hψ hk hU

theorem u3_false_of_card_le {X : Type} [Group X] [Finite X] (f : Kp →* X)
    (hf : Function.Surjective f) (h1 : 1 < Nat.card X) (h2 : Nat.card X ≤ 20160) : False := by
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp h1
  have h := card_le_of_surjective hY hN hQ ψ hψ f hf
  rw [card_isPSU3 hU] at h
  have := lt_ordTwistedA_two hk
  omega

theorem u3_false_of_simple_mem {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (f : Kp →* X) (hf : Function.Surjective f)
    (hX : Nat.card X ∈ CFSG.Timmesfeld.evenOrdersExceptUnitarySp4) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY (nonabelian_of_perfect_surjective f hf)
    hN hQ ψ hψ f hf
  have hc : Nat.card Y = Nat.card X := Nat.card_congr e.toEquiv
  exact (CFSG.Timmesfeld.evenOrdersExceptUnitarySp4_ne hX).1 2 k le_rfl (by omega)
    (hc.symm.trans (card_isPSU3 hU))

theorem u3_false_of_alt {X : Type} [Group X] [Finite X] (f : Kp →* X)
    (hf : Function.Surjective f) {m : ℕ} (hm5 : 5 ≤ m) (hm8 : m ≤ 8)
    (e : X ≃* alternatingGroup (Fin m)) : False := by
  have hc : Nat.card X = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, card_alt (by omega)]
  refine u3_false_of_card_le hY hN hQ ψ hψ hk hU f hf ?_ ?_ <;> rw [hc]
  · interval_cases m <;> decide
  · interval_cases m <;> decide

theorem u3_false_of_SL {K : Type} [Field K] [Finite K] {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    (hmn : 3 ≤ m ∨ 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (f : Kp →* Matrix.SpecialLinearGroup (Fin m) K) (hf : Function.Surjective f) : False := by
  have h4 : 3 ≤ m ∨ 4 ≤ Nat.card K := by
    rcases hmn with h | h
    · exact Or.inl h
    · right
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin m) K) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 m hm (by omega) (by omega)
  refine u3_false_of_simple_mem hY hN hQ ψ hψ hk hU
    ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K))).comp f)
    ((QuotientGroup.mk'_surjective _).comp hf) ?_
  rw [card_psl_eq_ordA hm, hK]
  exact ordA_mem (by omega) hn (by intro h; simp only [Prod.mk.injEq] at h; omega)

theorem u3_false_of_statedSp {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (f : Kp →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K)) (hf : Function.Surjective f) :
    False := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hK
      exact absurd hK (Finite.one_lt_card).ne'
    · exact h0
  have : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hK
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  ·
    have hK2 : Nat.card K = 2 := by rw [hK, show n = 1 by omega, pow_one]
    refine u3_false_of_card_le hY hN hQ ψ hψ hk hU f hf ?_ ?_ <;>
      rw [card_statedSp_two_two hK2] <;> norm_num
  ·
    have hmod : IsPSp4 2 n
        (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) :=
      ⟨⟨Nat.prime_two, hn, le_rfl, by
        intro h
        simp only [Prod.mk.injEq, true_and] at h
        have : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        omega⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    have : IsSimpleGroup
        (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 n hmod
    set π := QuotientGroup.mk'
      ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
        (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) with hπ
    obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY
      (nonabelian_of_perfect_surjective (π.comp f) ((QuotientGroup.mk'_surjective _).comp hf))
      hN hQ ψ hψ (π.comp f) ((QuotientGroup.mk'_surjective _).comp hf)
    have hc : Nat.card Y = ordBC 2 (2 ^ n) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hK, ordBC_two_eq hn,
        prod_Icc_one_two]
      ring
    exact ordBC_two_ne_ordTwistedA_two hn (by omega) (hc.symm.trans (card_isPSU3 hU))

theorem u3_false_of_G2
    (hG2 : FactG2Simple) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (f : Kp →* ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (hf : Function.Surjective f) : False := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hK
      exact absurd hK (Finite.one_lt_card).ne'
    · exact h0
  have : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hK
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  ·
    have hK2 : Nat.card K = 2 := by rw [hK, show n = 1 by omega, pow_one]
    have : IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
      CFSG.Quasithin.H13.isSimpleGroup_g2Two_commutator hK2
    have hle : Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ ≤ 12096 := by
      have hc : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
        Subgroup.commutator_le.mpr fun a ha b hb => by
          rw [commutatorElement_def]
          exact (quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ((quasithinG2 K).mul_mem ha hb)
            ((quasithinG2 K).inv_mem ha)) ((quasithinG2 K).inv_mem hb)
      have h1 := Subgroup.card_le_of_le hc
      have h2 : Nat.card ↥(quasithinG2 K) = 12096 := by
        rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
          CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup, hK2]
        norm_num
      omega
    exact u3_false_of_card_le hY hN hQ ψ hψ hk hU f hf Finite.one_lt_card (by omega)
  · have : IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ := hG2 K n hn2 hK
    refine u3_false_of_simple_mem hY hN hQ ψ hψ hk hU f hf ?_
    rw [CFSG.Quasithin.Vol2.KGNat.factG2DerivedOrder_holds K n hn2 hK]
    refine Set.mem_union_left _ ⟨n, hn, Or.inr (Or.inr (Or.inr (Or.inl ⟨hn2, ?_⟩)))⟩
    rw [ordG2]
    ring

end U3

end CFSG.Quasithin.Vol2.Ch11.SecB
