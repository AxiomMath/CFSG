module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cF4Ord
public import CFSG.Quasithin.Vol2.Ch11L2Q5cFFGen

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

theorem lt_ordTwistedF4 {k : ℕ} (hk : 1 ≤ k) : 20160 < ordTwistedF4 (2 ^ (2 * k + 1)) := by
  unfold ordTwistedF4
  generalize hq : 2 ^ (2 * k + 1) = q
  have hq8 : 8 ≤ q := by
    rw [← hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 20160 < q ^ 12 :=
    calc 20160 < 8 ^ 12 := by norm_num
      _ ≤ q ^ 12 := Nat.pow_le_pow_left hq8 12
  have h4 : 1 ≤ q ^ 4 - 1 := by
    have : 2 ≤ q ^ 4 := (show 2 ≤ q by omega).trans (Nat.le_self_pow (by norm_num) q)
    omega
  calc 20160 < q ^ 12 := h1
    _ ≤ q ^ 12 * (q ^ 6 + 1) := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) :=
        Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) :=
        Nat.le_mul_of_pos_right _ (by omega)

section TwistedF4

variable {Kp Y : Type} [Group Kp] [Group Y] [Finite Y] [IsSimpleGroup Y] [Group.IsPerfect Kp]
  (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup Kp} [N.Normal] (hN : IsPGroup 2 N)
  (hQ : CFSG.Open.IsQuasisimple (Kp ⧸ N)) (ψ : Kp →* Y) (hψ : Function.Surjective ψ)
  {k : ℕ} (hk : 1 ≤ k) (hYc : Nat.card Y = ordTwistedF4 (2 ^ (2 * k + 1)))
include hY hN hQ hψ hk hYc

theorem false_of_card_le_of_twistedF4 {X : Type} [Group X] [Finite X] (f : Kp →* X)
    (hf : Function.Surjective f) (h1 : 1 < Nat.card X) (h2 : Nat.card X ≤ 20160) : False := by
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp h1
  have h := card_le_of_surjective hY hN hQ ψ hψ f hf
  have := lt_ordTwistedF4 hk
  omega

omit hk in
theorem false_of_simple_of_twistedF4 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (f : Kp →* X) (hf : Function.Surjective f)
    (hX : Nat.card X ≠ ordTwistedF4 (2 ^ (2 * k + 1))) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY (nonabelian_of_perfect_surjective f hf)
    hN hQ ψ hψ f hf
  exact hX (by rw [← Nat.card_congr e.toEquiv, hYc])

omit hk in
theorem false_of_SL_of_twistedF4 {K : Type} [Field K] [Finite K] {m n : ℕ} (hm : 2 ≤ m)
    (hn : 1 ≤ n) (hmn : 3 ≤ m ∨ 2 ≤ n) (hK : Nat.card K = 2 ^ n)
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
  refine false_of_simple_of_twistedF4 hY hN hQ ψ hψ hYc
    ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K))).comp f)
    ((QuotientGroup.mk'_surjective _).comp hf) ?_
  rw [card_psl_eq_ordA hm, hK]
  have h := ordTwistedF4_ne_ordA (f := 2 * k + 1) (m := m - 1) (n := n) (by omega) (by omega) hn
  exact fun h' => h h'.symm

theorem false_of_statedSp_of_twistedF4 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (f : Kp →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K))
    (hf : Function.Surjective f) : False := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hK
      exact absurd hK (Finite.one_lt_card).ne'
    · exact h0
  have : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hK
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hK2 : Nat.card K = 2 := by rw [hK, show n = 1 by omega, pow_one]
    exact false_of_card_le_of_twistedF4 hY hN hQ ψ hψ hk hYc f hf
      (by rw [card_statedSp_two_two hK2]; norm_num) (by rw [card_statedSp_two_two hK2]; norm_num)
  · have hmod : IsPSp4 2 n
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
    refine false_of_simple_of_twistedF4 hY hN hQ ψ hψ hYc (π.comp f)
      ((QuotientGroup.mk'_surjective _).comp hf) ?_
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.1 rfl]
    exact fun h => CFSG.Timmesfeld.Orders.ordTwistedF4_ne_ordBC_two (by omega) hn h.symm

theorem false_of_G2_of_twistedF4
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
  · have hK2 : Nat.card K = 2 := by rw [hK, show n = 1 by omega, pow_one]
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
    exact false_of_card_le_of_twistedF4 hY hN hQ ψ hψ hk hYc f hf Finite.one_lt_card (by omega)
  · have : IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ := hG2 K n hn2 hK
    refine false_of_simple_of_twistedF4 hY hN hQ ψ hψ hYc f hf ?_
    rw [CFSG.Quasithin.Vol2.KGNat.factG2DerivedOrder_holds K n hn2 hK, ← mul_assoc]
    exact fun h => ordTwistedF4_ne_ordG2 ⟨k, rfl⟩ hn h.symm

end TwistedF4

theorem twoF4_false_of_concl701FF {G : Type} [Group G] [Finite G]
    (h325 : H13.Stmt3_2_5) (h328 : H13.Stmt3_2_8)
    (hG2 : FactG2Simple) {T Kp Ip : Subgroup G} (hfsu : H13.FSU G T Kp Ip)
    (hTK : T ≤ Subgroup.normalizer (Kp : Set G))
    (hVN : Kp ⊔ T ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G))
    [IsMulCommutative ↥(H13.fsuV T Ip)] [Group.IsPerfect ↥Kp] {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup ↥Kp} [N.Normal]
    (hN : IsPGroup 2 N) (hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ N)) (ψ : ↥Kp →* Y)
    (hψ : Function.Surjective ψ) {k : ℕ} (hk : 1 ≤ k)
    (hYc : Nat.card Y = ordTwistedF4 (2 ^ (2 * k + 1))) (hFF : H13.Concl701FF T Kp Ip) :
    False :=
  false_of_concl701FF_of_leaves h325 h328 hfsu hTK hVN
    (fun f hf h1 h2 => false_of_card_le_of_twistedF4 hY hN hQ ψ hψ hk hYc f hf h1 h2)
    (fun hm hn hmn hK f hf =>
      false_of_SL_of_twistedF4 hY hN hQ ψ hψ hYc hm hn hmn hK f hf)
    (fun hK f hf => false_of_statedSp_of_twistedF4 hY hN hQ ψ hψ hk hYc hK f hf)
    (fun hK f hf => false_of_G2_of_twistedF4 hY hN hQ ψ hψ hk hYc hG2 hK f hf)
    hFF

end CFSG.Quasithin.Vol2.Ch11.SecB
