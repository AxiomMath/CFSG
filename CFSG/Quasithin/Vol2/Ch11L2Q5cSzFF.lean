module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cNot3
public import CFSG.Quasithin.Vol2.Ch11L2Q5cFFGen

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

section NotThree

variable {Kp Y : Type} [Group Kp] [Group Y] [Finite Y] [IsSimpleGroup Y] [Group.IsPerfect Kp]
  (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup Kp} [N.Normal] (hN : IsPGroup 2 N)
  (hQ : CFSG.Open.IsQuasisimple (Kp ⧸ N)) (ψ : Kp →* Y) (hψ : Function.Surjective ψ)
  (hY3 : ¬ 3 ∣ Nat.card Y) (hYc : 20160 < Nat.card Y)
include hY hN hQ hψ hY3 hYc

omit hYc in
theorem false_of_SL_of_not_three {K : Type} [Field K] [Finite K] {m n : ℕ} (hm : 2 ≤ m)
    (_hn : 1 ≤ n) (hmn : 3 ≤ m ∨ 2 ≤ n) (hK : Nat.card K = 2 ^ n)
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
  exact false_of_simple_of_three_dvd hY hN hQ ψ hψ hY3
    ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K))).comp f)
    ((QuotientGroup.mk'_surjective _).comp hf) (three_dvd_card_psl hm)

theorem false_of_statedSp_of_not_three {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (f : Kp →* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K))
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
    exact false_of_card_eq_of_not_three hY hN hQ ψ hψ hYc f hf (card_statedSp_two_two hK2)
      (by norm_num) (by norm_num)
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
    exact false_of_simple_of_three_dvd hY hN hQ ψ hψ hY3 (π.comp f)
      ((QuotientGroup.mk'_surjective _).comp hf) three_dvd_card_statedProj_statedSp

theorem false_of_G2_of_not_three
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
    exact false_of_card_le_of_not_three hY hN hQ ψ hψ hYc f hf Finite.one_lt_card (by omega)
  · have : IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ := hG2 K n hn2 hK
    refine false_of_simple_of_three_dvd hY hN hQ ψ hψ hY3 f hf ?_
    rw [CFSG.Quasithin.Vol2.KGNat.factG2DerivedOrder_holds K n hn2 hK]
    exact ((three_dvd_two_pow_sq_sub_one n).mul_left _).mul_left _

end NotThree

section FF

variable {G : Type} [Group G] [Finite G]

theorem not_three_false_of_concl701FF
    (h325 : H13.Stmt3_2_5) (h328 : H13.Stmt3_2_8)
    (hG2 : FactG2Simple) {T Kp Ip : Subgroup G} (hfsu : H13.FSU G T Kp Ip)
    (hTK : T ≤ Subgroup.normalizer (Kp : Set G))
    (hVN : Kp ⊔ T ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G))
    [IsMulCommutative ↥(H13.fsuV T Ip)] [Group.IsPerfect ↥Kp] {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup ↥Kp} [N.Normal]
    (hN : IsPGroup 2 N) (hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ N)) (ψ : ↥Kp →* Y)
    (hψ : Function.Surjective ψ) (hY3 : ¬ 3 ∣ Nat.card Y) (hYc : 20160 < Nat.card Y)
    (hFF : H13.Concl701FF T Kp Ip) : False :=
  false_of_concl701FF_of_leaves h325 h328 hfsu hTK hVN
    (fun f hf h1 h2 => false_of_card_le_of_not_three hY hN hQ ψ hψ hYc f hf h1 h2)
    (fun hm hn hmn hK f hf => false_of_SL_of_not_three hY hN hQ ψ hψ hY3 hm hn hmn hK f hf)
    (fun hK f hf => false_of_statedSp_of_not_three hY hN hQ ψ hψ hY3 hYc hK f hf)
    (fun hK f hf => false_of_G2_of_not_three hY hN hQ ψ hψ hY3 hYc hG2 hK f hf)
    hFF

end FF

theorem not_three_dvd_ordSuzuki_odd (a : ℕ) : ¬ 3 ∣ CFSG.Open.ordSuzuki (2 ^ (2 * a + 1)) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : Nat.Prime 3 := by norm_num
  unfold CFSG.Open.ordSuzuki
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  intro h
  rcases (Nat.Prime.dvd_mul h3).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h3).1 h with h | h
    · have := h3.dvd_of_dvd_pow h
      omega
    · have h4 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
      omega
  · omega

theorem not_three_dvd_card_isSz {Y : Type} [Group Y] {k : ℕ}
    (h : IsSz k Y) : ¬ 3 ∣ Nat.card Y := by
  obtain ⟨⟨a, rfl⟩, -, hc⟩ := card_isSz h
  rw [hc]
  exact not_three_dvd_ordSuzuki_odd a

theorem lt_card_isSz {Y : Type} [Group Y] {k : ℕ}
    (h : IsSz k Y) : 20160 < Nat.card Y := by
  obtain ⟨-, hk3, hc⟩ := card_isSz h
  rw [hc]
  unfold CFSG.Open.ordSuzuki
  generalize hq : 2 ^ k = q
  have hq8 : 8 ≤ q := by
    rw [← hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  have h1 : 64 ≤ q ^ 2 := by nlinarith
  have h2 : 65 ≤ q ^ 2 + 1 := by omega
  have h3 : 7 ≤ q - 1 := by omega
  calc 20160 < 64 * 65 * 7 := by norm_num
    _ ≤ q ^ 2 * (q ^ 2 + 1) * (q - 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

theorem sz_false_of_concl701FF {G : Type} [Group G] [Finite G]
    (h325 : H13.Stmt3_2_5) (h328 : H13.Stmt3_2_8)
    (hG2 : FactG2Simple) {T Kp Ip : Subgroup G} (hfsu : H13.FSU G T Kp Ip)
    (hTK : T ≤ Subgroup.normalizer (Kp : Set G))
    (hVN : Kp ⊔ T ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G))
    [IsMulCommutative ↥(H13.fsuV T Ip)] [Group.IsPerfect ↥Kp] {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup ↥Kp} [N.Normal]
    (hN : IsPGroup 2 N) (hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ N)) (ψ : ↥Kp →* Y)
    (hψ : Function.Surjective ψ) {k : ℕ} (hSz : IsSz k Y) (hFF : H13.Concl701FF T Kp Ip) :
    False :=
  not_three_false_of_concl701FF h325 h328 hG2 hfsu hTK hVN hY hN hQ ψ hψ
    (not_three_dvd_card_isSz hSz) (lt_card_isSz hSz) hFF

end CFSG.Quasithin.Vol2.Ch11.SecB
