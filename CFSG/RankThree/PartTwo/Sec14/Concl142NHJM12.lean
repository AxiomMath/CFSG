module

public import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KP4Basic
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
open CFSG.GH74.M12.Hyp (G12)
open CFSG.RankThree.PartTwo.Toolkit.M12 (x y P0 card_P0 basisE basisF basisA basisA' nine_eq
  centralizer_E centralizer_F le_centralizer_sub card_centralizer_basisA g0 map_g0_A' z_comm_x
  z_comm_y cube_of_mem_P0 z_mem_P0 z_ne_one)
open CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig (V ai card_V normal_V V_le_C invariant_E
  invariant_F le_V_of_mem_invariant)
open scoped commutatorElement

@[expose] def SignalAt {X : Type} [Group X] (E : Subgroup X) (b : X) : Prop :=
  ∃ W : Subgroup X, ¬ 3 ∣ Nat.card W ∧
    Subgroup.centralizer ({b} : Set X) ≤ Subgroup.normalizer (W : Set X) ∧
    ∀ U : Subgroup X, U ≤ Subgroup.centralizer ({b} : Set X) → ¬ 3 ∣ Nat.card U →
      E ≤ Subgroup.normalizer (U : Set X) → U ≤ W

theorem signalAt_of_map {X : Type} [Group X] (σ : X ≃* X) {E : Subgroup X} {b : X}
    (h : SignalAt (E.map σ.toMonoidHom) (σ b)) : SignalAt E b := by
  obtain ⟨W, hW3, hWN, hWle⟩ := h
  have hcen : (Subgroup.centralizer ({b} : Set X)).map σ.toMonoidHom =
      Subgroup.centralizer ({σ b} : Set X) :=
    CFSG.RankThree.PartTwo.map_centralizer_singleton σ b
  refine ⟨W.comap σ.toMonoidHom, ?_, ?_, ?_⟩
  · rwa [← Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective,
      Subgroup.map_comap_eq_self_of_surjective (f := σ.toMonoidHom) σ.surjective]
  · intro g hg
    have hσg : σ g ∈ Subgroup.normalizer (W : Set X) :=
      hWN (hcen ▸ Subgroup.mem_map_of_mem σ.toMonoidHom hg)
    rw [Subgroup.mem_normalizer_iff] at hσg ⊢
    intro w
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    exact hσg (σ w)
  · intro U hU hU3 hEU
    have hUC : U.map σ.toMonoidHom ≤ Subgroup.centralizer ({σ b} : Set X) :=
      hcen ▸ Subgroup.map_mono hU
    have hU3' : ¬ 3 ∣ Nat.card (U.map σ.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective σ.injective]
    have hEU' : E.map σ.toMonoidHom ≤
        Subgroup.normalizer ((U.map σ.toMonoidHom : Subgroup X) : Set X) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hEU
    exact Subgroup.map_le_iff_le_comap.mp (hWle _ hUC hU3' hEU')

theorem card_G12_m12 : Nat.card G12 = 95040 := KFacts.KS14.card_nativeM12

theorem exists_conj_le_P0_m12 {E : Subgroup G12} (hE : IsPGroup 3 E) :
    ∃ g : G12, E.map (MulAut.conj g).toMonoidHom ≤ P0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP0 : IsPGroup 3 P0 := IsPGroup.of_card (n := 3) (by rw [card_P0]; norm_num)
  have hidx : ¬ 3 ∣ P0.index := by
    have h := P0.index_mul_card
    rw [card_P0, card_G12_m12] at h
    omega
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G12 S (hP0.toSylow hidx)
  refine ⟨g, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hmem : (MulAut.conj g).toMonoidHom e ∈ ((g • S : Sylow 3 G12) : Subgroup G12) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have : (MulAut.conj g)⁻¹ • (MulAut.conj g).toMonoidHom e = e := by
      rw [MulAut.smul_def, ← map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MulAut.conj_apply]
      group
    rw [this]
    exact hES he
  rw [hg, IsPGroup.toSylow_coe] at hmem
  exact hmem

theorem centralizer_basisA :
    Subgroup.centralizer (basisA.sub : Set G12) = basisA.sub :=
  (Subgroup.eq_of_le_of_card_ge (le_centralizer_sub basisA)
    (card_centralizer_basisA.trans basisA.card.symm).le).symm

theorem card_modEq_one_of_normalizer {T R : Subgroup G12} (hT3 : IsPGroup 3 T)
    (hCT : Subgroup.centralizer (T : Set G12) ≤ T) (hR3 : ¬ 3 ∣ Nat.card R)
    (hTR : T ≤ Subgroup.normalizer (R : Set G12)) : Nat.card R ≡ 1 [MOD 3] := by
  let _ : MulDistribMulAction T R :=
    MulDistribMulAction.compHom R (R.normalizerMonoidHom.comp (Subgroup.inclusion hTR))
  have hfix : MulAction.fixedPoints T R = {1} := by
    ext r
    simp only [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    refine ⟨fun hr => ?_, fun hr t => by rw [hr, smul_one]⟩
    have hrC : (r : G12) ∈ Subgroup.centralizer (T : Set G12) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have h := congrArg Subtype.val (hr ⟨t, ht⟩)
      change t * (r : G12) * t⁻¹ = r at h
      calc t * (r : G12) = t * r * t⁻¹ * t := by group
        _ = r * t := by rw [h]
    have hrT := hCT hrC
    have hr3 : orderOf (r : G12) ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T hrT
    have hrR : orderOf (r : G12) ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R r.2
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hT3)
    rw [hn] at hr3
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hr3
    have hk0 : k = 0 := by
      by_contra hk0
      apply hR3
      exact (dvd_pow_self 3 hk0).trans (hk' ▸ hrR)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
    exact Subtype.ext hk'
  have h := hT3.card_modEq_card_fixedPoints R
  rw [hfix] at h
  simpa using h

theorem isPiSubgroup_two_of_invariant {T U : Subgroup G12} (hT3 : IsPGroup 3 T)
    (hCT : Subgroup.centralizer (T : Set G12) ≤ T) (hU3 : ¬ 3 ∣ Nat.card U)
    (hTU : T ≤ Subgroup.normalizer (U : Set G12)) : IsPiSubgroup (piOf 2) U := by
  intro q hq
  show (q : ℕ) = 2
  have hqp : (q : ℕ).Prime := q.2
  have hqG : (q : ℕ) ∣ 2 ^ 6 * 3 ^ 3 * 5 * 11 := by
    have := hq.trans (Subgroup.card_subgroup_dvd_card U)
    rwa [card_G12_m12] at this
  have hcases : (q : ℕ) = 2 ∨ (q : ℕ) = 3 ∨ (q : ℕ) = 5 ∨ (q : ℕ) = 11 := by
    rcases (Nat.Prime.dvd_mul hqp).mp hqG with h | h
    · rcases (Nat.Prime.dvd_mul hqp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hqp).mp h with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp
            (hqp.dvd_of_dvd_pow h))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).mp
            (hqp.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h)))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp h)))
  have hnot : ∀ p : ℕ, p.Prime → p ∣ Nat.card U → p % 3 = 2 → ¬ p ^ 2 ∣ 95040 → False := by
    intro p hp hpU hp3 hp2
    obtain ⟨S, hTS, hS1⟩ :=
      CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial 3 p
        Nat.prime_three hp T U hT3 hTU
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hU3) hpU
    set R := (S : Subgroup U).map U.subtype with hR
    have : Fact p.Prime := ⟨hp⟩
    have hRp : IsPGroup p R := S.isPGroup'.map U.subtype
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hS1 (Subgroup.card_eq_one.mp hk)
    have hk1 : k = 1 := by
      by_contra hk1
      have hdvd : p ^ k ∣ 95040 := by
        rw [← card_G12_m12, ← hk]
        exact Subgroup.card_subgroup_dvd_card R
      exact hp2 ((pow_dvd_pow p (by omega)).trans hdvd)
    rw [hk1, pow_one] at hk
    have hR3 : ¬ 3 ∣ Nat.card R := by
      rw [hk]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
      omega
    have hmod := card_modEq_one_of_normalizer hT3 hCT hR3 hTS
    rw [hk, Nat.ModEq] at hmod
    omega
  rcases hcases with h | h | h | h
  · exact h
  · exact absurd (h ▸ hq) hU3
  · exact (hnot 5 (by norm_num) (h ▸ hq) (by norm_num) (by norm_num)).elim
  · exact (hnot 11 (by norm_num) (h ▸ hq) (by norm_num) (by norm_num)).elim

theorem signalAt_E_F
    {T : Subgroup G12} (hT : T = basisE.sub ∨ T = basisF.sub)
    (b : G12) :
    SignalAt T b := by
  have hT3 : IsPGroup 3 T := by
    rcases hT with rfl | rfl
    · exact IsPGroup.of_card (n := 2) (by rw [basisE.card]; norm_num)
    · exact IsPGroup.of_card (n := 2) (by rw [basisF.card]; norm_num)
  have hCT : Subgroup.centralizer (T : Set G12) ≤ T := by
    rcases hT with rfl | rfl
    · exact centralizer_E.le
    · exact centralizer_F.le
  refine ⟨⊥, by rw [Subgroup.card_bot]; norm_num, fun g _ => by
    rw [Subgroup.normalizer_eq_top ⊥]; trivial, fun U _ hU3 hTU => ?_⟩
  have hU2 := isPiSubgroup_two_of_invariant hT3 hCT hU3 hTU
  have hmem : U ∈ invariantPiSubgroups ⊤ T (piOf 2) := ⟨le_top, hU2, hTU⟩
  rcases hT with rfl | rfl
  · rw [invariant_E] at hmem
    exact (Set.mem_singleton_iff.mp hmem).le
  · rw [invariant_F] at hmem
    exact (Set.mem_singleton_iff.mp hmem).le

theorem z_comm_xy_m12 : Commute ⁅x, y⁆ (x * y) := z_comm_x.mul_right z_comm_y

theorem z_cube' : ⁅x, y⁆ ^ 3 = 1 := cube_of_mem_P0 z_mem_P0

theorem mem_centralizer_A_of_commute {g : G12} (hz : Commute g ⁅x, y⁆) {j : Fin 3}
    (ha : Commute g (ai j)) : g ∈ Subgroup.centralizer (basisA.sub : Set G12) := by
  have hxy : Commute g (x * y) := by
    have h := (hz.pow_right j.val).inv_right.mul_right ha
    rwa [ai, ← mul_assoc, inv_mul_cancel, one_mul] at h
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact hz.symm.eq
  · exact hxy.symm.eq

theorem commute_z_of_commute_ai {g : G12} {i j : Fin 3} (hij : i ≠ j) (hi : Commute g (ai i))
    (hj : Commute g (ai j)) : Commute g ⁅x, y⁆ := by
  have hz3 := z_cube'
  have hzo : orderOf ⁅x, y⁆ = 3 := orderOf_eq_prime hz3 z_ne_one
  set w := ⁅x, y⁆ ^ i.val * (⁅x, y⁆ ^ j.val)⁻¹ with hw
  have hq : Commute g w := by
    have h := hi.mul_right hj.inv_right
    rwa [ai, ai, mul_inv_rev, ← mul_assoc, mul_assoc (⁅x, y⁆ ^ i.val), mul_inv_cancel,
      mul_one] at h
  have hw1 : w ≠ 1 := by
    intro h
    rw [hw, mul_inv_eq_one, pow_inj_mod, hzo, Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt] at h
    exact hij (Fin.ext h)
  have hwz : w ∈ Subgroup.zpowers ⁅x, y⁆ :=
    mul_mem (pow_mem (Subgroup.mem_zpowers _) _) (inv_mem (pow_mem (Subgroup.mem_zpowers _) _))
  have hw3 : w ^ 3 = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hzw : ⁅x, y⁆ ∈ Subgroup.zpowers w := by
    have hle : Subgroup.zpowers w ≤ Subgroup.zpowers ⁅x, y⁆ := Subgroup.zpowers_le.mpr hwz
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hzo, orderOf_eq_prime hw3 hw1])
    rw [heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzw
  rw [← hk]
  exact hq.zpow_right k

theorem eq_one_of_mem_basisA {U : Subgroup G12} (hU3 : ¬ 3 ∣ Nat.card U) {g : G12}
    (hgA : g ∈ basisA.sub) (hgU : g ∈ U) : g = 1 := by
  have h1 : orderOf g ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← basisA.card]
    exact Subgroup.orderOf_dvd_natCard _ hgA
  have h2 : orderOf g ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hgU
  have hcop : Nat.Coprime (3 ^ 2) (Nat.card U) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hU3)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem basisA_point_cases {b : G12} (hb : b ∈ basisA.sub) (hb1 : b ≠ 1) :
    (b = ⁅x, y⁆ ∨ b = ⁅x, y⁆ ^ 2) ∨ ∃ i : Fin 3,
      Subgroup.centralizer ({b} : Set G12) = Subgroup.centralizer ({ai i} : Set G12) := by
  have hz3 := z_cube'
  have hzo : orderOf ⁅x, y⁆ = 3 := orderOf_eq_prime hz3 z_ne_one
  have hxy3 : (x * y) ^ 3 = 1 := Toolkit.M12.a_cube
  obtain ⟨m, n, hm, hn, rfl⟩ := basisA.exists_pow_mul_pow hb
  change ⁅x, y⁆ ^ m * (x * y) ^ n ≠ 1 at hb1
  change (⁅x, y⁆ ^ m * (x * y) ^ n = ⁅x, y⁆ ∨ ⁅x, y⁆ ^ m * (x * y) ^ n = ⁅x, y⁆ ^ 2) ∨
    ∃ i : Fin 3, Subgroup.centralizer ({⁅x, y⁆ ^ m * (x * y) ^ n} : Set G12) =
      Subgroup.centralizer ({ai i} : Set G12)
  interval_cases n
  ·
    left
    interval_cases m
    · exact absurd (by simp) hb1
    · left; simp
    · right; simp
  ·
    right
    exact ⟨⟨m, hm⟩, by simp [ai]⟩
  ·
    right
    refine ⟨⟨(2 * m) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    have hb3 : (⁅x, y⁆ ^ m * (x * y) ^ 2) ^ 3 = 1 := by
      rw [(z_comm_xy_m12.pow_pow m 2).mul_pow, ← pow_mul, ← pow_mul, mul_comm m 3, pow_mul, hz3,
        one_pow, one_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hxy3, one_pow]
    have hsq : (⁅x, y⁆ ^ m * (x * y) ^ 2) ^ 2 = ai ⟨(2 * m) % 3, Nat.mod_lt _ (by norm_num)⟩ := by
      have h1 : ⁅x, y⁆ ^ (m * 2) = ⁅x, y⁆ ^ ((2 * m) % 3) := by
        rw [← hzo, pow_mod_orderOf, mul_comm]
      have h2 : (x * y) ^ (2 * 2) = x * y := by
        rw [show 2 * 2 = 3 + 1 from rfl, pow_succ, hxy3, one_mul]
      rw [(z_comm_xy_m12.pow_pow m 2).mul_pow, ← pow_mul, ← pow_mul, ai, h1, h2]
    rw [← KFacts.KP4.centralizer_sq_eq hb3, hsq]

theorem signalAt_basisA
    {b : G12} (hb : b ∈ basisA.sub) (hb1 : b ≠ 1) :
    SignalAt basisA.sub b := by
  have hA3 : IsPGroup 3 basisA.sub := IsPGroup.of_card (n := 2) (by rw [basisA.card]; norm_num)
  have hCA : Subgroup.centralizer (basisA.sub : Set G12) ≤ basisA.sub := centralizer_basisA.le
  have hV : ∀ U : Subgroup G12, ¬ 3 ∣ Nat.card U →
      basisA.sub ≤ Subgroup.normalizer (U : Set G12) → U = ⊥ ∨ ∃ j : Fin 3, U ≤ V j := by
    intro U hU3 hAU
    by_cases hU : U = ⊥
    · exact Or.inl hU
    · exact Or.inr (le_V_of_mem_invariant
        ⟨le_top, isPiSubgroup_two_of_invariant hA3 hCA hU3 hAU, hAU⟩ hU)
  rcases basisA_point_cases hb hb1 with hbz | ⟨i, hCi⟩
  ·
    have hCz : Subgroup.centralizer ({b} : Set G12) =
        Subgroup.centralizer ({⁅x, y⁆} : Set G12) := by
      rcases hbz with rfl | rfl
      · rfl
      · exact KFacts.KP4.centralizer_sq_eq z_cube'
    refine ⟨⊥, by rw [Subgroup.card_bot]; norm_num, fun g _ => by
      rw [Subgroup.normalizer_eq_top ⊥]; trivial, fun U hUC hU3 hAU => ?_⟩
    rcases hV U hU3 hAU with hU | ⟨j, hUj⟩
    · exact hU.le
    · intro g hg
      rw [Subgroup.mem_bot]
      have hgb := hUC hg
      rw [hCz] at hgb
      have hgz : Commute g ⁅x, y⁆ := Subgroup.mem_centralizer_singleton_iff.mp hgb
      have hgj : Commute g (ai j) :=
        Subgroup.mem_centralizer_singleton_iff.mp (V_le_C j (hUj hg))
      exact eq_one_of_mem_basisA hU3 (hCA (mem_centralizer_A_of_commute hgz hgj)) hg
  ·
    refine ⟨V i, by rw [card_V]; norm_num, fun c hc => ?_, fun U hUC hU3 hAU => ?_⟩
    · rw [hCi] at hc
      refine Subgroup.mem_normalizer_fintype fun v hv => ?_
      have h := (normal_V i).conj_mem ⟨v, V_le_C i hv⟩ (Subgroup.mem_subgroupOf.mpr hv) ⟨c, hc⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    · rcases hV U hU3 hAU with hU | ⟨j, hUj⟩
      · rw [hU]
        exact bot_le
      · by_cases hji : j = i
        · exact hji ▸ hUj
        · intro g hg
          have hgb := hUC hg
          rw [hCi] at hgb
          have hgi : Commute g (ai i) := Subgroup.mem_centralizer_singleton_iff.mp hgb
          have hgj : Commute g (ai j) :=
            Subgroup.mem_centralizer_singleton_iff.mp (V_le_C j (hUj hg))
          have hgz := commute_z_of_commute_ai (Ne.symm hji) hgi hgj
          rw [eq_one_of_mem_basisA hU3 (hCA (mem_centralizer_A_of_commute hgz hgj)) hg]
          exact one_mem _

theorem ks142SignalM12 :
    KS142SignalM12 := by
  intro E hE hE9 b hbE hb1
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le_P0_m12 hE3
  have hE'9 : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9]
  have hmemS : E.map (MulAut.conj g).toMonoidHom ∈
      {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9} := ⟨hg, hE'9⟩
  rw [nine_eq] at hmemS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemS
  have hσb : MulAut.conj g b ∈ E.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hbE
  have hσb1 : MulAut.conj g b ≠ 1 := fun h =>
    hb1 ((MulAut.conj g).injective (h.trans (MulAut.conj g).map_one.symm))
  change SignalAt E b
  refine signalAt_of_map (MulAut.conj g) ?_
  rcases hmemS with h | h | h | h
  · rw [h]
    exact signalAt_E_F (Or.inl rfl) _
  · rw [h]
    exact signalAt_E_F (Or.inr rfl) _
  · rw [h] at hσb ⊢
    exact signalAt_basisA hσb hσb1
  · rw [h] at hσb ⊢
    refine signalAt_of_map (MulAut.conj g0) ?_
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj g0).toMonoidHom hσb
    rw [map_g0_A'] at hmem ⊢
    refine signalAt_basisA hmem fun h1 => hσb1 ?_
    exact (MulAut.conj g0).injective (h1.trans (MulAut.conj g0).map_one.symm)

theorem step142M12_of'
    (h131 : Item131)
    (hspor : SporadicModels131) : Step142M12 :=
  step142M12_of h131 hspor ks142SignalM12

end CFSG.RankThree.PartTwo.Sec14
