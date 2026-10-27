module

public import CFSG.RankThree.PartOne.MB3.Triple
public import CFSG.RankThree.PartOne.MB3.Independent
public import CFSG.RankThree.PartOne.MB3.Orbit

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly.RankThreeEven

variable {G : Type} [Group G]

theorem forall_comm_of_conj {K : Subgroup G} {x y : G}
    (h : ∀ k' ∈ conjBy x K, x * y * x⁻¹ * k' = k' * (x * y * x⁻¹)) :
    ∀ k ∈ K, y * k = k * y := by
  intro k hk
  have h1 := h (x * k * x⁻¹) (conj_mem_conjBy hk x)
  have e1 : x * y * x⁻¹ * (x * k * x⁻¹) = x * (y * k) * x⁻¹ := by group
  have e2 : x * k * x⁻¹ * (x * y * x⁻¹) = x * (k * y) * x⁻¹ := by group
  rw [e1, e2] at h1
  exact mul_left_cancel (mul_right_cancel h1)

theorem pow_eq_one_of_dvd' {q : ℕ} {g : G} (hg : g ^ q = 1) {a : ℕ} (ha : q ∣ a) : g ^ a = 1 := by
  obtain ⟨m, rfl⟩ := ha
  rw [pow_mul, hg, one_pow]

theorem conj_pow_eq_one {g : G} {n : ℕ} (hg : g ^ n = 1) (x : G) : (x * g * x⁻¹) ^ n = 1 := by
  rw [conj_pow, hg, mul_one, mul_inv_cancel]

section Normalizers

variable {K : Subgroup G} {x : G} {U : Subgroup G}

theorem Triple.mem_normalizer_U₃_zero (T : Triple K x) (hUK : U ≤ K) {g : G} (hg : g ∈ K)
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) :
    g ∈ Subgroup.normalizer ((U₃ U x : Subgroup G) : Set G) :=
  mem_normalizer_U₃ hgU
    (mem_normalizer_of_commute fun n hn => T.c01 g hg n (Subgroup.map_mono hUK hn))
    (mem_normalizer_of_commute fun n hn =>
      T.c02 g hg n (Subgroup.map_mono (Subgroup.map_mono hUK) hn))

theorem Triple.mem_normalizer_U₃_one (T : Triple K x) (hUK : U ≤ K) {g : G}
    (hg : g ∈ conjBy x K)
    (hgU : g ∈ Subgroup.normalizer ((conjBy x U : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((U₃ U x : Subgroup G) : Set G) :=
  mem_normalizer_U₃ (mem_normalizer_of_commute fun n hn => (T.c01 n (hUK hn) g hg).symm) hgU
    (mem_normalizer_of_commute fun n hn =>
      T.c12 g hg n (Subgroup.map_mono (Subgroup.map_mono hUK) hn))

theorem Triple.mem_normalizer_U₃_two (T : Triple K x) (hUK : U ≤ K) {g : G}
    (hg : g ∈ conjBy x (conjBy x K))
    (hgU : g ∈ Subgroup.normalizer ((conjBy x (conjBy x U) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((U₃ U x : Subgroup G) : Set G) :=
  mem_normalizer_U₃ (mem_normalizer_of_commute fun n hn => (T.c02 n (hUK hn) g hg).symm)
    (mem_normalizer_of_commute fun n hn =>
      (T.c12 n (Subgroup.map_mono hUK hn) g hg).symm) hgU

theorem mem_normalizer_U₃_of_commute (hUK : U ≤ K) {g : G} (h0 : ∀ k ∈ K, g * k = k * g)
    (h1 : ∀ k ∈ conjBy x K, g * k = k * g) (h2 : ∀ k ∈ conjBy x (conjBy x K), g * k = k * g) :
    g ∈ Subgroup.normalizer ((U₃ U x : Subgroup G) : Set G) :=
  mem_normalizer_U₃ (mem_normalizer_of_commute fun n hn => h0 n (hUK hn))
    (mem_normalizer_of_commute fun n hn => h1 n (Subgroup.map_mono hUK hn))
    (mem_normalizer_of_commute fun n hn =>
      h2 n (Subgroup.map_mono (Subgroup.map_mono hUK) hn))

end Normalizers

section Main

variable [Finite G]

theorem no_order_seven {K : Subgroup G} {x : G} (T : Triple K x) (hr : localRank 7 G ≤ 3) {b : G}
    (hb7 : orderOf b = 7) (hb0 : ∀ k ∈ K, b * k = k * b) (hb1 : ∀ k ∈ conjBy x K, b * k = k * b)
    (hb2 : ∀ k ∈ conjBy x (conjBy x K), b * k = k * b)
    (hZ : ¬ 7 ∣ Nat.card (Subgroup.center K)) {y : G} (hyK : y ∈ K) (hy7 : orderOf y = 7)
    {U : Subgroup G} (hUK : U ≤ K) (hU0 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) : False := by
  have hq : Nat.Prime 7 := by norm_num
  have hy : y ^ 7 = 1 := by rw [← hy7]; exact pow_orderOf_eq_one y
  have hb : b ^ 7 = 1 := by rw [← hb7]; exact pow_orderOf_eq_one b
  have hU₃0 := U₃_ne_bot (x := x) hU0
  have hU₃2 := T.isPGroup_U₃ hUK hU2
  have hy' : x * y * x⁻¹ ∈ conjBy x K := conj_mem_conjBy hyK x
  have hy'' : x * (x * y * x⁻¹) * x⁻¹ ∈ conjBy x (conjBy x K) := conj_mem_conjBy hy' x
  have key : ∀ m : ℕ, (∀ k ∈ K, y ^ m * k = k * y ^ m) → 7 ∣ m := fun m hm => by
    have hmem : (⟨y ^ m, K.pow_mem hyK m⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hm g g.2).symm
    have hv : (⟨y ^ m, K.pow_mem hyK m⟩ : K) ^ 7 = 1 := Subtype.ext (by
      show (y ^ m) ^ 7 = 1
      rw [← pow_mul, mul_comm, pow_mul, hy, one_pow])
    have h1 := congrArg Subtype.val (S11d.eq_one_of_mem_center_of_pow hq hZ hmem hv)
    rw [← hy7]
    exact orderOf_dvd_of_pow_eq_one h1
  have hind : ∀ a a' a'' d : ℕ, y ^ a * (x * y * x⁻¹) ^ a' * (x * (x * y * x⁻¹) * x⁻¹) ^ a'' *
      b ^ d = 1 → 7 ∣ a ∧ 7 ∣ a' ∧ 7 ∣ a'' ∧ 7 ∣ d := by
    intro a a' a'' d h
    obtain ⟨h0, h1, h2⟩ := central_of_prod_eq_one T.c01 T.c02 T.c12 (K.pow_mem hyK a)
      ((conjBy x K).pow_mem hy' a') ((conjBy x (conjBy x K)).pow_mem hy'' a'')
      (fun k hk => (Commute.pow_left (show Commute b k from hb0 k hk) d).eq)
      (fun k hk => (Commute.pow_left (show Commute b k from hb1 k hk) d).eq)
      (fun k hk => (Commute.pow_left (show Commute b k from hb2 k hk) d).eq) h
    have ha := key a h0
    have ha' : 7 ∣ a' := key a' (forall_comm_of_conj (K := K) (y := y ^ a') (x := x) (by
      rw [← conj_pow]
      exact h1))
    have ha'' : 7 ∣ a'' := by
      have h2' : ∀ k ∈ conjBy x K, (x * y * x⁻¹) ^ a'' * k = k * (x * y * x⁻¹) ^ a'' :=
        forall_comm_of_conj (K := conjBy x K) (y := (x * y * x⁻¹) ^ a'') (x := x) (by
          rw [← conj_pow]
          exact h2)
      exact key a'' (forall_comm_of_conj (K := K) (y := y ^ a'') (x := x) (by
        rw [← conj_pow]
        exact h2'))
    refine ⟨ha, ha', ha'', ?_⟩
    have ea : y ^ a = 1 := pow_eq_one_of_dvd' hy ha
    have eb : (x * y * x⁻¹) ^ a' = 1 := pow_eq_one_of_dvd' (conj_pow_eq_one hy x) ha'
    have ec : (x * (x * y * x⁻¹) * x⁻¹) ^ a'' = 1 :=
      pow_eq_one_of_dvd' (conj_pow_eq_one (conj_pow_eq_one hy x) x) ha''
    rw [ea, eb, ec, one_mul, one_mul, one_mul] at h
    rw [← hb7]
    exact orderOf_dvd_of_pow_eq_one h
  have h4 := four_le_localRank_of_independent hq hy (conj_pow_eq_one hy x)
    (conj_pow_eq_one (conj_pow_eq_one hy x) x) hb (T.c01 y hyK _ hy') (T.c02 y hyK _ hy'')
    (hb0 y hyK).symm (T.c12 _ hy' _ hy'') (hb1 _ hy').symm (hb2 _ hy'').symm hind hU₃0 hU₃2
    (T.mem_normalizer_U₃_zero hUK hyK hyU)
    (T.mem_normalizer_U₃_one hUK hy' (Equivariance.conjBy_le_normalizer
      (Subgroup.zpowers_le.mpr hyU : Subgroup.zpowers y ≤ Subgroup.normalizer (U : Set G))
      (conj_mem_conjBy (Subgroup.mem_zpowers y) x)))
    (T.mem_normalizer_U₃_two hUK hy'' (Equivariance.conjBy_le_normalizer
      (Equivariance.conjBy_le_normalizer
        (Subgroup.zpowers_le.mpr hyU : Subgroup.zpowers y ≤ Subgroup.normalizer (U : Set G)))
      (conj_mem_conjBy (conj_mem_conjBy (Subgroup.mem_zpowers y) x) x)))
    (mem_normalizer_U₃_of_commute hUK hb0 hb1 hb2)
  omega

end Main

end CFSG.RankThree.PartOne.MB3
