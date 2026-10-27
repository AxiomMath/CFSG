module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch11L2Q5cFFGen
public import CFSG.Quasithin.Vol2.Ch11L2Q5cNot3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Timmesfeld.Orders

theorem ordA_ne_m23 {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) : ordA (m - 1) (2 ^ n) ≠ 2 ^ 7 * 79695 := by
  intro he
  obtain ⟨r, hr, hr'⟩ := (profile_ordA (n := m - 1) (by omega) hn).two
  rw [hr'] at he
  have h7 : n * ((m - 1) * (m - 1 + 1) / 2) = 7 :=
    eq_of_two_pow_mul_odd hr ⟨39847, by norm_num⟩ he
  have hn7 : n ∣ 7 := Dvd.intro _ h7
  rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd n hn7 with rfl | rfl
  ·
    rw [one_mul] at h7
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [show j + 1 - 1 = j by omega] at h7
    have hlt : j * (j + 1) < 16 := by
      have := Nat.lt_mul_div_succ (j * (j + 1)) (show 0 < 2 by norm_num)
      rw [h7] at this
      omega
    have hj : j ≤ 3 := by nlinarith
    interval_cases j <;> omega
  ·
    have hT : (m - 1) * (m - 1 + 1) / 2 = 1 := by omega
    have hm2 : m = 2 := by
      by_contra hne
      have h3 : 3 ≤ m := by omega
      have : 2 * 3 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    subst hm2
    rw [← hr', show (2 : ℕ) - 1 = 1 from rfl, ordA_one_two_pow_eq (n := 7) (by norm_num)] at he
    norm_num at he

section M23

variable {Kp Y : Type} [Group Kp] [Group Y] [Finite Y] [IsSimpleGroup Y] [Group.IsPerfect Kp]
  (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup Kp} [N.Normal] (hN : IsPGroup 2 N)
  (hQ : CFSG.Open.IsQuasisimple (Kp ⧸ N)) (ψ : Kp →* Y) (hψ : Function.Surjective ψ)
  (hYc : Nat.card Y = 2 ^ 7 * 79695)
include hY hN hQ hψ hYc

theorem false_of_card_le_of_m23 {X : Type} [Group X] [Finite X] (f : Kp →* X)
    (hf : Function.Surjective f) (h1 : 1 < Nat.card X) (h2 : Nat.card X ≤ 20160) : False := by
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp h1
  have h := card_le_of_surjective hY hN hQ ψ hψ f hf
  omega

theorem false_of_simple_of_m23 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (f : Kp →* X) (hf : Function.Surjective f) (hX : Nat.card X ≠ 2 ^ 7 * 79695) : False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_surjective hY (nonabelian_of_perfect_surjective f hf)
    hN hQ ψ hψ f hf
  exact hX (by rw [← Nat.card_congr e.toEquiv, hYc])

theorem false_of_SL_of_m23 {K : Type} [Field K] [Finite K] {m n : ℕ} (hm : 2 ≤ m)
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
  refine false_of_simple_of_m23 hY hN hQ ψ hψ hYc
    ((QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K))).comp f)
    ((QuotientGroup.mk'_surjective _).comp hf) ?_
  rw [card_psl_eq_ordA hm, hK]
  exact ordA_ne_m23 hm hn

theorem false_of_statedSp_of_m23 {K : Type} [Field K] [Finite K] {n : ℕ}
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
    exact false_of_card_le_of_m23 hY hN hQ ψ hψ hYc f hf
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
    refine false_of_simple_of_m23 hY hN hQ ψ hψ hYc (π.comp f)
      ((QuotientGroup.mk'_surjective _).comp hf) ?_
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.1 rfl]
    obtain ⟨r, hr, hr'⟩ : ∃ r, Odd r ∧ ordBC 2 (2 ^ n) = 2 ^ (n * 4) * r :=
      (profile_ordBC (n := 2) hn).two
    rw [hr']
    intro he
    have := eq_of_two_pow_mul_odd hr ⟨39847, by norm_num⟩ he
    omega

theorem false_of_G2_of_m23
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
    exact false_of_card_le_of_m23 hY hN hQ ψ hψ hYc f hf Finite.one_lt_card (by omega)
  · have : IsSimpleGroup ↥⁅quasithinG2 K, quasithinG2 K⁆ := hG2 K n hn2 hK
    refine false_of_simple_of_m23 hY hN hQ ψ hψ hYc f hf ?_
    rw [CFSG.Quasithin.Vol2.KGNat.factG2DerivedOrder_holds K n hn2 hK, ← mul_assoc]
    show ordG2 (2 ^ n) ≠ 2 ^ 7 * 79695
    obtain ⟨r, hr, hr'⟩ := (profile_ordG2 hn).two
    rw [hr']
    intro he
    have := eq_of_two_pow_mul_odd hr ⟨39847, by norm_num⟩ he
    omega

end M23

theorem m23_false_of_concl701FF {G : Type} [Group G] [Finite G]
    (h325 : H13.Stmt3_2_5) (h328 : H13.Stmt3_2_8)
    (hG2 : FactG2Simple) {T Kp Ip : Subgroup G} (hfsu : H13.FSU G T Kp Ip)
    (hTK : T ≤ Subgroup.normalizer (Kp : Set G))
    (hVN : Kp ⊔ T ≤ Subgroup.normalizer (H13.fsuV T Ip : Set G))
    [IsMulCommutative ↥(H13.fsuV T Ip)] [Group.IsPerfect ↥Kp] {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hY : ∃ a b : Y, a * b ≠ b * a) {N : Subgroup ↥Kp} [N.Normal]
    (hN : IsPGroup 2 N) (hQ : CFSG.Open.IsQuasisimple (↥Kp ⧸ N)) (ψ : ↥Kp →* Y)
    (hψ : Function.Surjective ψ) (hYc : Nat.card Y = 2 ^ 7 * 79695)
    (hFF : H13.Concl701FF T Kp Ip) : False :=
  false_of_concl701FF_of_leaves h325 h328 hfsu hTK hVN
    (fun f hf h1 h2 => false_of_card_le_of_m23 hY hN hQ ψ hψ hYc f hf h1 h2)
    (fun hm hn hmn hK f hf => false_of_SL_of_m23 hY hN hQ ψ hψ hYc hm hn hmn hK f hf)
    (fun hK f hf => false_of_statedSp_of_m23 hY hN hQ ψ hψ hYc hK f hf)
    (fun hK f hf => false_of_G2_of_m23 hY hN hQ ψ hψ hYc hG2 hK f hf)
    hFF

end CFSG.Quasithin.Vol2.Ch11.SecB
