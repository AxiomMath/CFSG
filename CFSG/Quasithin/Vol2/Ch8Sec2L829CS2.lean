module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS1
public import CFSG.Quasithin.Background.F918Z4c1Sz
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L829CS2

variable {G : Type} [Group G] [Finite G]

theorem card_starQuot_dvd_of_le {M H I : Subgroup G} (hIH : I ≤ H) :
    Nat.card (E2.StarQuot (M ⊓ I) I) ∣ Nat.card (E2.StarQuot (H ⊓ M) H) := by
  let f : ↥I →* E2.StarQuot (H ⊓ M) H :=
    (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)).comp (Subgroup.inclusion hIH)
  have hker : f.ker ≤ (kerIn (M ⊓ I) I).subgroupOf I := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h : Subgroup.inclusion hIH x ∈ (kerIn (H ⊓ M) H).subgroupOf H :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hIH x)).mp hx
    have hx' : (x : G) ∈ kerIn (H ⊓ M) H := Subgroup.mem_subgroupOf.mp h
    rw [Subgroup.mem_subgroupOf, mem_kerIn]
    intro b hb
    have hb' := mem_kerIn.mp hx' b (hIH hb)
    exact ⟨hb'.2, I.mul_mem (I.mul_mem hb x.2) (I.inv_mem hb)⟩
  have h1 : ((kerIn (M ⊓ I) I).subgroupOf I).index ∣ f.ker.index :=
    Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card f.range)

theorem sixty_dvd_starQuot_H_cocode_829 {M H I : Subgroup G} (hIH : I ≤ H)
    (hI : IsPSL 2 2 2 (E2.StarQuot (M ⊓ I) I)) :
    60 ∣ Nat.card (E2.StarQuot (H ⊓ M) H) := by
  have h := card_starQuot_dvd_of_le (M := M) hIH
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hI] at h
  norm_num at h
  exact h

theorem dvd_card_star_of_case2 {M H T K : Subgroup G} {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hT : IsPGroup 2 ↥T) (hH : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hdvd : p ∣ Nat.card (E2.StarQuot (H ⊓ M) H)) :
    p ∣ Nat.card ↥(E2.star (H ⊓ M) H K) := by
  have hTH : T ≤ H := hH ▸ le_sup_right
  have hKH : K ≤ H := hH ▸ le_sup_left
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hH]
    exact sup_le Subgroup.le_normalizer hTK
  have hKnorm : (K.subgroupOf H).Normal := by
    constructor
    intro n hn g
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHN g.2) _).mp hn
  have hKstar : (E2.star (H ⊓ M) H K).Normal :=
    Subgroup.Normal.map hKnorm _ (QuotientGroup.mk'_surjective _)
  haveI := hKstar
  have hKT : ∀ h ∈ H, ∃ k ∈ K, ∃ t ∈ T, h = k * t := by
    intro h hh
    let S : Subgroup G :=
      { carrier := {x | ∃ k ∈ K, ∃ t ∈ T, x = k * t}
        mul_mem' := by
          rintro _ _ ⟨k1, hk1, t1, ht1, rfl⟩ ⟨k2, hk2, t2, ht2, rfl⟩
          refine ⟨k1 * (t1 * k2 * t1⁻¹), K.mul_mem hk1 ?_, t1 * t2, T.mul_mem ht1 ht2, ?_⟩
          · exact (Subgroup.mem_normalizer_iff.mp (hTK ht1) k2).mp hk2
          · group
        one_mem' := ⟨1, K.one_mem, 1, T.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨k, hk, t, ht, rfl⟩
          refine ⟨t⁻¹ * k⁻¹ * t, ?_, t⁻¹, T.inv_mem ht, by group⟩
          have := (Subgroup.mem_normalizer_iff.mp (hTK (T.inv_mem ht)) k⁻¹).mp (K.inv_mem hk)
          rw [inv_inv] at this
          exact this }
    have hS : K ⊔ T ≤ S := sup_le (fun k hk => ⟨k, hk, 1, T.one_mem, by group⟩)
      (fun t ht => ⟨1, K.one_mem, t, ht, by group⟩)
    have hh' : h ∈ K ⊔ T := hH ▸ hh
    obtain ⟨k, hk, t, ht, e⟩ := hS hh'
    exact ⟨k, hk, t, ht, e⟩
  let φ : ↥T →* (E2.StarQuot (H ⊓ M) H ⧸ E2.star (H ⊓ M) H K) :=
    (QuotientGroup.mk' (E2.star (H ⊓ M) H K)).comp
      ((QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)).comp (Subgroup.inclusion hTH))
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (E2.star (H ⊓ M) H K) y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (H ⊓ M) H).subgroupOf H) z
    obtain ⟨k, hk, t, ht, e⟩ := hKT (h : G) h.2
    have hkH : k ∈ H := hKH hk
    have hk' : (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H) ⟨k, hkH⟩ :
        E2.StarQuot (H ⊓ M) H) ∈ E2.star (H ⊓ M) H K :=
      ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hh_eq : h = (⟨k, hkH⟩ : ↥H) * ⟨t, hTH ht⟩ := Subtype.ext (by simp [e])
    refine ⟨⟨t, ht⟩, ?_⟩
    have hk1 : (QuotientGroup.mk' (E2.star (H ⊓ M) H K))
        (QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H) ⟨k, hkH⟩) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hk'
    show (QuotientGroup.mk' (E2.star (H ⊓ M) H K))
        ((QuotientGroup.mk' ((kerIn (H ⊓ M) H).subgroupOf H)) (Subgroup.inclusion hTH ⟨t, ht⟩)) = _
    rw [hh_eq, map_mul, map_mul, hk1, one_mul]
    rfl
  have hQ : IsPGroup 2 (E2.StarQuot (H ⊓ M) H ⧸ E2.star (H ⊓ M) H K) := hT.of_surjective φ hφ
  by_contra hnd
  have hidx : (E2.star (H ⊓ M) H K).index * Nat.card ↥(E2.star (H ⊓ M) H K) =
      Nat.card (E2.StarQuot (H ⊓ M) H) := Subgroup.index_mul_card _
  have hpi : p ∣ (E2.star (H ⊓ M) H K).index := by
    rw [← hidx] at hdvd
    rcases (Nat.Prime.dvd_mul hp.out).mp hdvd with h | h
    · exact h
    · exact absurd h hnd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpi
  obtain ⟨j, hj⟩ := hQ g
  have h2 : p ∣ 2 ^ j := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one hj
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h2))

theorem two_pow_odd_mod_three (j : ℕ) : 2 ^ (2 * j + 1) % 3 = 2 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem two_pow_odd_mod_five {k : ℕ} (hk : Odd k) : 2 ^ k % 5 = 2 ∨ 2 ^ k % 5 = 3 := by
  obtain ⟨j, rfl⟩ := hk
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem sq_cube_mod_five {x : ℕ} (hx : x % 5 = 2 ∨ x % 5 = 3) :
    x ^ 2 % 5 = 4 ∧ (x ^ 3 % 5 = 3 ∨ x ^ 3 % 5 = 2) := by
  rcases hx with h | h
  · simp [Nat.pow_mod, h]
  · simp [Nat.pow_mod, h]

theorem not_three_dvd_sz_odd {n : ℕ} {X : Type} [Group X] (h : IsSz n X) (hn : Odd n) :
    ¬ 3 ∣ Nat.card X := by
  rw [CFSG.Quasithin.card_of_isSz h]
  obtain ⟨j, rfl⟩ := hn
  have hx3 : 2 ^ (2 * j + 1) % 3 = 2 := two_pow_odd_mod_three j
  generalize hxdef : 2 ^ (2 * j + 1) = x at hx3 ⊢
  have hx1 : 2 ≤ x := by omega
  have hx2 : x ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hx3]
  have e1 : (x ^ 2 + 1) % 3 = 2 := by omega
  have e2 : (x - 1) % 3 = 1 := by omega
  have key : ((x ^ 2 + 1) * x ^ 2 * (x - 1)) % 3 = 2 := by
    rw [Nat.mul_mod, Nat.mul_mod (x ^ 2 + 1), e1, hx2, e2]
  intro hd
  have h0 := Nat.mod_eq_zero_of_dvd hd
  rw [key] at h0
  norm_num at h0

theorem not_five_dvd_psu3_odd {n : ℕ} {X : Type} [Group X] (h : IsPSU 3 2 n X) (hn : Odd n) :
    ¬ 5 ∣ Nat.card X := by
  obtain ⟨-, K, hKF, hKfin, hK, ⟨e⟩⟩ := h
  have hdvd : Nat.card X ∣ Nat.card ↥(StatedSU 3 (2 ^ n) K) := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.index_dvd_card _
  rw [CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK] at hdvd
  intro h5
  have h5' := h5.trans hdvd
  have hx := two_pow_odd_mod_five hn
  obtain ⟨h2, h3⟩ := sq_cube_mod_five hx
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5' with h5a | h5a
  · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5a with h5b | h5b
    · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5b)
      rcases hx with hx | hx <;> omega
    · omega
  · omega

theorem not_five_dvd_psl3_odd {n : ℕ} {X : Type} [Group X] (h : IsPSL 3 2 n X) (hn : Odd n) :
    ¬ 5 ∣ Nat.card X := by
  obtain ⟨-, K, hKF, hKfin, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card X = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.toEquiv]
  rw [hcard, CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 3 (by norm_num), hK]
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  have hNeq : ∀ q : ℕ, q ^ (3 * (3 - 1) / 2) * ∏ index ∈ Finset.Icc 2 3, (q ^ index - 1) =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    intro q
    rw [hI, Finset.prod_pair (by norm_num)]
  rw [hNeq]
  intro h5
  have hq5 := two_pow_odd_mod_five hn
  obtain ⟨hsq, hcube⟩ := sq_cube_mod_five hq5
  have hq1 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
    simpa using this
  have hq2 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := hq1
  have hd : Nat.gcd 3 (2 ^ n - 1) ∣ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    (Nat.gcd_dvd_right 3 (2 ^ n - 1)).trans
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hq2 _) _)
  have h5N := h5.trans (Nat.div_dvd_of_dvd hd)
  have hp5 : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp5).mp h5N with h6 | h6
  · have h7 := Nat.Prime.dvd_of_dvd_pow hp5 h6
    rcases hq5 with h8 | h8 <;> omega
  · rcases (Nat.Prime.dvd_mul hp5).mp h6 with h7 | h7
    · omega
    · omega

theorem surv2a_cocode_829 {H T M K : Subgroup G} (hH : H = K ⊔ T) (hT : IsPGroup 2 ↥T)
    (h3 : 3 ∣ Nat.card (E2.StarQuot (H ⊓ M) H)) (h5 : 5 ∣ Nat.card (E2.StarQuot (H ⊓ M) H))
    (hc : E22Surv2a H T (H ⊓ M) K) :
    ∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥(E2.star (H ⊓ M) H K) ∨
      (IsPSU 3 2 n ↥(E2.star (H ⊓ M) H K) ∧ Even n)) := by
  obtain ⟨hTK, -, n, hB, -⟩ := hc
  obtain ⟨hn2, hcase⟩ := hB
  rcases hcase with hL | hS | hU
  · exact ⟨n, hn2, Or.inl hL⟩
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hodd : Odd n := by
      obtain ⟨-, a, -, -, -, -, hf, -, -⟩ := hS
      exact ⟨a, by omega⟩
    have hd := dvd_card_star_of_case2 (p := 3) (by norm_num) hT hH hTK h3
    exact absurd hd (not_three_dvd_sz_odd hS hodd)
  · rcases Nat.even_or_odd n with he | ho
    · exact ⟨n, hn2, Or.inr ⟨hU, he⟩⟩
    · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hd := dvd_card_star_of_case2 (p := 5) (by norm_num) hT hH hTK h5
      exact absurd hd (not_five_dvd_psu3_odd hU ho)

theorem surv2b_cocode_829 {H T M K : Subgroup G} (hH : H = K ⊔ T) (hT : IsPGroup 2 ↥T)
    (h5 : 5 ∣ Nat.card (E2.StarQuot (H ⊓ M) H)) (hc : E22Surv2b H T (H ⊓ M) K) :
    ∃ n : ℕ, 1 ≤ n ∧ ((IsPSL 3 2 n ↥(E2.star (H ⊓ M) H K) ∧ Even n) ∨
      E2.IsSp4Prime n ↥(E2.star (H ⊓ M) H K)) := by
  obtain ⟨hTK, -, n, hn1, hX, -, -⟩ := hc
  rcases hX with hL | hSp
  · rcases Nat.even_or_odd n with he | ho
    · exact ⟨n, hn1, Or.inl ⟨hL, he⟩⟩
    · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hd := dvd_card_star_of_case2 (p := 5) (by norm_num) hT hH hTK h5
      exact absurd hd (not_five_dvd_psl3_odd hL ho)
  · exact ⟨n, hn1, Or.inr hSp⟩

end L829CS2

end CFSG.Quasithin.H13
