module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofTwoThree
import CFSG.RankThree.SubgroupLists.ExtraspecialCore

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open scoped commutatorElement

@[expose] def KF2110SylowNoncentralBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ d : G, d ≠ 1 → d ^ 3 = 1 →
    ∀ J ∈ thetaComponentsAt 3 d, d ∈ J →
      27 ∣ Nat.card (lBar J ⧸ Subgroup.center (lBar J)) →
      ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S J →
        ∃ s ∈ S, s ^ 3 = 1 ∧ ∃ t ∈ S, s * t ≠ t * s

namespace Item21Res8Proof

open Subgroup

theorem map_eq_one_of_isPerfect {X A : Type*} [Group X] [CommGroup A] [Group.IsPerfect X]
    (f : X →* A) (x : X) : f x = 1 :=
  Abelianization.commutator_subset_ker f
    (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top x)

theorem mem_commutator_of_mem_center {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (S : Sylow 3 X) {z : X} (hz : z ∈ center X) (hzS : z ∈ (S : Subgroup X)) :
    (⟨z, hzS⟩ : (S : Subgroup X)) ∈ commutator (S : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup X := (S : Subgroup X) with hH
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ center X := pow_mem hz k
    rw [mem_center_iff.mp hzk g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have h1 := MonoidHom.transfer_eq_pow (Abelianization.of : H →* Abelianization H) z key
  rw [map_eq_one_of_isPerfect] at h1
  have h2 : (⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z key⟩ : H) ∈ commutator H := by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact h1.symm
  set y : H := ⟨z, hzS⟩ with hy
  have hyidx : (⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z key⟩ : H) = y ^ H.index :=
    Subtype.ext (by simp [hy])
  rw [hyidx] at h2
  have hcop : (orderOf y).Coprime H.index :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard y) (Sylow.card_coprime_index S)
  have hord : orderOf (y ^ H.index) = orderOf y := Nat.Coprime.orderOf_pow hcop
  have hle : zpowers (y ^ H.index) ≤ zpowers y := zpowers_le.mpr (pow_mem (mem_zpowers y) _)
  have heq : zpowers (y ^ H.index) = zpowers y :=
    eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  have hyy : y ∈ zpowers (y ^ H.index) := heq ▸ mem_zpowers y
  exact (zpowers_le.mpr h2) hyy

def commLeftHom {P : Type*} [Group P] (hclass : commutator P ≤ center P) (v : P) :
    P →* P where
  toFun u := ⁅u, v⁆
  map_one' := by simp
  map_mul' a b := SubgroupLists.commutatorElement_mul_left hclass a b v

def commRightHom {P : Type*} [Group P] (hclass : commutator P ≤ center P) (u : P) :
    P →* P where
  toFun v := ⁅u, v⁆
  map_one' := by simp
  map_mul' a b := SubgroupLists.commutatorElement_mul_right hclass u a b

theorem exists_noncentral_of_card_quotient_dvd_nine {P : Type*} [Group P] [Finite P]
    (Z₀ : Subgroup P) [Z₀.Normal] (hZ₀ : Z₀ ≤ center P)
    (hZ₀c : Z₀ ≤ commutator P) (hne : Z₀ ≠ ⊥) (h9 : Nat.card (P ⧸ Z₀) ∣ 9) :
    ∃ s : P, s ^ 3 = 1 ∧ ∃ t : P, s * t ≠ t * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hnc : ¬ ∀ a b : P, a * b = b * a := by
    intro hab
    apply hne
    have : IsMulCommutative P := ⟨⟨hab⟩⟩
    have hc : commutator P = ⊥ := (commutator_eq_bot_iff P).mpr this
    exact eq_bot_iff.mpr (hc ▸ hZ₀c)
  push Not at hnc
  obtain ⟨x, y, hxy⟩ := hnc
  have hcyc : ∀ K : Subgroup P, Z₀ ≤ K →
      IsCyclic (K.map (QuotientGroup.mk' Z₀)) → ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro K hZK hcy a ha b hb
    have hker : ((QuotientGroup.mk' Z₀).subgroupMap K).ker ≤ center K := by
      intro k hk
      rw [MonoidHom.mem_ker] at hk
      have hk' : (k : P) ∈ Z₀ := by
        have h1 := congrArg Subtype.val hk
        rw [MonoidHom.subgroupMap_apply_coe] at h1
        exact (QuotientGroup.eq_one_iff _).mp h1
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp (hZ₀ hk') g)
    have hcK := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      ((QuotientGroup.mk' Z₀).subgroupMap K) hker
    exact congrArg Subtype.val (hcK.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hQ9 : Nat.card (P ⧸ Z₀) = 9 := by
    have hcop : ¬ IsCyclic (P ⧸ Z₀) := by
      intro hcy
      have h := hcyc ⊤ le_top (by
        rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk']
        exact isCyclic_of_surjective (topEquiv.symm : P ⧸ Z₀ ≃* (⊤ : Subgroup (P ⧸ Z₀)))
          (topEquiv.symm.surjective))
      exact hxy (h x (mem_top x) y (mem_top y))
    obtain ⟨k, hk, hk9⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card (P ⧸ Z₀) ∣ 3 ^ 2 by simpa using h9)
    interval_cases k
    · exact absurd (isCyclic_of_card_dvd_prime (p := 3) (by rw [hk9]; norm_num)) hcop
    · exact absurd (isCyclic_of_prime_card (p := 3) (hk9.trans (by norm_num))) hcop
    · exact hk9.trans (by norm_num)
  have hQcomm : IsMulCommutative (P ⧸ Z₀) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hQ9]; norm_num)
  have hPZ : commutator P ≤ Z₀ := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hQcomm
  have hclass : commutator P ≤ center P := hPZ.trans hZ₀
  have hcube : ∀ u : P, u ^ 3 ∈ Z₀ := by
    intro u
    have hdvd : orderOf (u : P ⧸ Z₀) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = Nat.card (P ⧸ Z₀) by rw [hQ9]; norm_num]
      exact orderOf_dvd_natCard _
    obtain ⟨k, hk, hk9⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk2 : k ≠ 2 := by
      rintro rfl
      have hcy : IsCyclic (P ⧸ Z₀) :=
        isCyclic_of_orderOf_eq_card (u : P ⧸ Z₀) (by rw [hk9, hQ9]; norm_num)
      have h := hcyc ⊤ le_top (by
        rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk']
        exact isCyclic_of_surjective (topEquiv.symm : P ⧸ Z₀ ≃* (⊤ : Subgroup (P ⧸ Z₀)))
          (topEquiv.symm.surjective))
      exact hxy (h x (mem_top x) y (mem_top y))
    have h3 : orderOf (u : P ⧸ Z₀) ∣ 3 := by
      interval_cases k <;> simp_all
    have := orderOf_dvd_iff_pow_eq_one.mp h3
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
    exact this
  have hpow : ∀ u : P, u ^ 3 ∈ center P := fun u => hZ₀ (hcube u)
  set w := ⁅x, y⁆ with hw
  have hw1 : w ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← SubgroupLists.commutatorElement_pow_left hclass,
      commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp (hpow x) y).symm
  have hcardw : Nat.card (zpowers w) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hw3)
  set H : Subgroup (P ⧸ Z₀) := closure {(x : P ⧸ Z₀), (y : P ⧸ Z₀)} with hH
  have hHtop : H = ⊤ := by
    by_contra hHt
    have hlt : Nat.card H < Nat.card (P ⧸ Z₀) := by
      have h1 := card_lt_of_lt (lt_of_le_of_ne le_top hHt)
      rwa [card_top] at h1
    have hdvd : Nat.card H ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = Nat.card (P ⧸ Z₀) by rw [hQ9]; norm_num]
      exact card_subgroup_dvd_card H
    obtain ⟨k, hk, hk9⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hcy : IsCyclic H := by
      interval_cases k
      · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hk9]; norm_num)
      · exact isCyclic_of_prime_card (p := 3) (hk9.trans (by norm_num))
      · rw [hk9, hQ9] at hlt; norm_num at hlt
    set K := H.comap (QuotientGroup.mk' Z₀) with hK
    have hZK : Z₀ ≤ K := by
      intro z hz
      rw [hK, mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
      exact one_mem H
    have hKmap : K.map (QuotientGroup.mk' Z₀) = H :=
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z₀) H
    have hxK : x ∈ K := subset_closure (Set.mem_insert _ _)
    have hyK : y ∈ K := subset_closure (Set.mem_insert_of_mem _ rfl)
    exact hxy (hcyc K hZK (hKmap ▸ hcy) x hxK y hyK)
  have hgen : ∀ u : P, ∃ a b : ℤ, ∃ z ∈ Z₀, u = x ^ a * y ^ b * z := by
    intro u
    have hmem : (u : P ⧸ Z₀) ∈ H := hHtop ▸ mem_top _
    have hform : ∀ q ∈ H, ∃ a b : ℤ, q = (x : P ⧸ Z₀) ^ a * (y : P ⧸ Z₀) ^ b := by
      intro q hq
      induction hq using closure_induction with
      | mem q hq =>
        rcases hq with rfl | rfl
        · exact ⟨1, 0, by simp⟩
        · exact ⟨0, 1, by simp⟩
      | one => exact ⟨0, 0, by simp⟩
      | mul q r _ _ hq hr =>
        obtain ⟨a, b, rfl⟩ := hq
        obtain ⟨c, d, rfl⟩ := hr
        refine ⟨a + c, b + d, ?_⟩
        have hc : Commute ((y : P ⧸ Z₀) ^ b) ((x : P ⧸ Z₀) ^ c) := hQcomm.is_comm.comm _ _
        rw [zpow_add, zpow_add]
        calc (x : P ⧸ Z₀) ^ a * (y : P ⧸ Z₀) ^ b * ((x : P ⧸ Z₀) ^ c * (y : P ⧸ Z₀) ^ d)
            = (x : P ⧸ Z₀) ^ a * ((y : P ⧸ Z₀) ^ b * (x : P ⧸ Z₀) ^ c) * (y : P ⧸ Z₀) ^ d := by
              simp only [mul_assoc]
          _ = (x : P ⧸ Z₀) ^ a * ((x : P ⧸ Z₀) ^ c * (y : P ⧸ Z₀) ^ b) * (y : P ⧸ Z₀) ^ d := by
              rw [hc.eq]
          _ = _ := by simp only [mul_assoc]
      | inv q _ hq =>
        obtain ⟨a, b, rfl⟩ := hq
        refine ⟨-a, -b, ?_⟩
        have hc : Commute ((x : P ⧸ Z₀) ^ a) ((y : P ⧸ Z₀) ^ b) := hQcomm.is_comm.comm _ _
        rw [mul_inv_rev, zpow_neg, zpow_neg, ← hc.inv_inv.eq]
    obtain ⟨a, b, hab⟩ := hform _ hmem
    refine ⟨a, b, (x ^ a * y ^ b)⁻¹ * u, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, ← hab, inv_mul_cancel]
  have hcomm_w : ∀ u v : P, ⁅u, v⁆ ∈ zpowers w := by
    intro u v
    obtain ⟨a, b, z, hz, rfl⟩ := hgen u
    obtain ⟨c, d, z', hz', rfl⟩ := hgen v
    have hzc : ∀ g : P, ⁅z, g⁆ = 1 := fun g =>
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hZ₀ hz) g).symm
    have hzc' : ∀ g : P, ⁅g, z'⁆ = 1 := fun g =>
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hZ₀ hz') g)
    set v := x ^ c * y ^ d * z' with hv
    have e1 : ⁅x ^ a * y ^ b * z, v⁆ = ⁅x, v⁆ ^ a * ⁅y, v⁆ ^ b := by
      have := map_mul (commLeftHom hclass v) (x ^ a * y ^ b) z
      simp only [commLeftHom, MonoidHom.coe_mk, OneHom.coe_mk] at this
      rw [this, hzc, mul_one]
      have h2 := map_mul (commLeftHom hclass v) (x ^ a) (y ^ b)
      have h3 := map_zpow (commLeftHom hclass v) x a
      have h4 := map_zpow (commLeftHom hclass v) y b
      simp only [commLeftHom, MonoidHom.coe_mk, OneHom.coe_mk] at h2 h3 h4
      rw [h2, h3, h4]
    have e2 : ∀ g : P, ⁅g, v⁆ = ⁅g, x⁆ ^ c * ⁅g, y⁆ ^ d := by
      intro g
      have := map_mul (commRightHom hclass g) (x ^ c * y ^ d) z'
      simp only [commRightHom, MonoidHom.coe_mk, OneHom.coe_mk] at this
      rw [hv, this, hzc', mul_one]
      have h2 := map_mul (commRightHom hclass g) (x ^ c) (y ^ d)
      have h3 := map_zpow (commRightHom hclass g) x c
      have h4 := map_zpow (commRightHom hclass g) y d
      simp only [commRightHom, MonoidHom.coe_mk, OneHom.coe_mk] at h2 h3 h4
      rw [h2, h3, h4]
    have hyx : ⁅y, x⁆ = w⁻¹ := by rw [hw, commutatorElement_inv]
    rw [e1, e2 x, e2 y, commutatorElement_self, commutatorElement_self, one_zpow, one_zpow,
      one_mul, mul_one, hyx]
    exact mul_mem (zpow_mem (zpow_mem (mem_zpowers w) d) a)
      (zpow_mem (zpow_mem (inv_mem (mem_zpowers w)) c) b)
  have hPw : commutator P ≤ zpowers w := by
    rw [_root_.commutator_def, commutator_le]
    intro u _ v _
    exact hcomm_w u v
  have hZ₀3 : Nat.card Z₀ ≤ 3 := (card_le_of_le (hZ₀c.trans hPw)).trans hcardw
  let cube : P →* P :=
    { toFun := fun u => u ^ 3
      map_one' := one_pow 3
      map_mul' := fun u v => SubgroupLists.mul_pow_prime_eq (by norm_num) hclass hpow u v }
  have hker : cube.ker ≤ center P := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    rw [mem_center_iff]
    intro g
    exact (hcon u hu g).symm
  have hrange : cube.range ≤ Z₀ := by
    rintro _ ⟨u, rfl⟩
    exact hcube u
  have hidx : (center P).index ≤ 3 := by
    have h1 : (center P).index ∣ cube.ker.index := index_dvd_of_le hker
    rw [Subgroup.index_ker] at h1
    exact (Nat.le_of_dvd Nat.card_pos h1).trans ((card_le_of_le hrange).trans hZ₀3)
  have hcyc' : IsCyclic (P ⧸ center P) := by
    have hcard : Nat.card (P ⧸ center P) ≤ 3 := by rwa [← index_eq_card]
    have hpos : 0 < Nat.card (P ⧸ center P) := Nat.card_pos
    interval_cases h : Nat.card (P ⧸ center P)
    · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [h]; norm_num)
    · exact isCyclic_of_prime_card (p := 2) h
    · exact isCyclic_of_prime_card (p := 3) h
  have hcomm : IsMulCommutative P := isMulCommutative_of_isCyclic_quotient_center_self P
  exact hxy (hcomm.is_comm.comm x y)

theorem exists_noncentral_of_not_dvd {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (S : Sylow 3 X) {z : X} (hz : z ∈ center X) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (h27 : ¬ 27 ∣ Nat.card (X ⧸ center X)) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S : Subgroup X), s * t ≠ t * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup X := (S : Subgroup X) with hH
  have hzS : z ∈ H := by
    have hN : (zpowers z).Normal := normal_of_le_center (zpowers_le.mpr hz)
    have hp : IsPGroup 3 (zpowers z) := by
      have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    exact IsPGroup.le_sylow_of_normal hp S (mem_zpowers z)
  set Z₀ : Subgroup H := (center X).subgroupOf H with hZ₀def
  have : Z₀.Normal := Normal.subgroupOf inferInstance H
  have hZ₀ : Z₀ ≤ center H := by
    intro w hw
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp (mem_subgroupOf.mp hw) g)
  have hZ₀c : Z₀ ≤ commutator H := fun w hw =>
    mem_commutator_of_mem_center S (mem_subgroupOf.mp hw) w.2
  have hne : Z₀ ≠ ⊥ := by
    intro hbot
    have hmem : (⟨z, hzS⟩ : H) ∈ Z₀ := mem_subgroupOf.mpr hz
    rw [hbot, mem_bot] at hmem
    exact hz1 (congrArg Subtype.val hmem)
  set f : H →* X ⧸ center X := (QuotientGroup.mk' (center X)).comp H.subtype with hf
  have hker : f.ker = Z₀ := by
    ext w
    rw [MonoidHom.mem_ker, hZ₀def, mem_subgroupOf, hf, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hcardf : Nat.card (H ⧸ Z₀) = Nat.card f.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hdvdX : Nat.card (H ⧸ Z₀) ∣ Nat.card (X ⧸ center X) :=
    hcardf ▸ card_subgroup_dvd_card f.range
  have hpq : IsPGroup 3 (H ⧸ Z₀) := (S.isPGroup').to_quotient Z₀
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpq
  have hk2 : k ≤ 2 := by
    by_contra hk3
    apply h27
    have h1 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    rw [← hk] at h1
    exact (by norm_num : (27 : ℕ) = 3 ^ 3) ▸ h1.trans hdvdX
  have h9 : Nat.card (H ⧸ Z₀) ∣ 9 := by
    rw [hk, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact pow_dvd_pow 3 hk2
  obtain ⟨s, hs3, t, hst⟩ := exists_noncentral_of_card_quotient_dvd_nine Z₀ hZ₀ hZ₀c hne h9
  refine ⟨s, s.2, by simpa using congrArg Subtype.val hs3, t, t.2, fun h => hst ?_⟩
  exact Subtype.ext h

theorem exists_center_lBar {G : Type} [Group G] [Finite G] {d : G} {J : Subgroup G}
    (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (hJ : J ∈ thetaComponentsAt 3 d) (hdJ : d ∈ J) :
    ∃ z ∈ center (lBar J), z ≠ 1 ∧ z ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J) with hπ
  set d₀ : J := ⟨d, hdJ⟩ with hd₀
  have hJd : J ≤ centralizer ({d} : Set G) := Sec6.le_centralizer_of_mem_thetaComponentsAt hJ
  have hdZ : π d₀ ∈ center (lBar J) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hJd x.2))
  have hd₀3 : d₀ ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hp : IsPGroup 3 (zpowers d₀) := by
    have hord : orderOf d₀ = 3 := orderOf_eq_prime hd₀3 fun h1 => hd1 (congrArg Subtype.val h1)
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hinjd := injOn_mk_of_isPGroup Nat.prime_three hp
  refine ⟨π d₀, hdZ, fun h1 => ?_, by rw [← map_pow, hd₀3, map_one]⟩
  have h1' : π d₀ = π 1 := by rw [h1, map_one]
  have := hinjd (mem_zpowers d₀) (one_mem _) h1'
  exact hd1 (congrArg Subtype.val this)

theorem exists_of_lBar {G : Type} [Group G] [Finite G] {J S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S J)
    (h : ∀ Q : Sylow 3 (lBar J), ∃ s ∈ (Q : Subgroup (lBar J)), s ^ 3 = 1 ∧
      ∃ t ∈ (Q : Subgroup (lBar J)), s * t ≠ t * s) :
    ∃ s ∈ S, s ^ 3 = 1 ∧ ∃ t ∈ S, s * t ≠ t * s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥J) with hπ
  obtain ⟨Q, hQ⟩ := hS
  set Qb : Sylow 3 (lBar J) := Q.mapSurjective (QuotientGroup.mk'_surjective _) with hQb
  obtain ⟨sb, hsb, hsb3, tb, htb, hst⟩ := h Qb
  rw [hQb, Sylow.coe_mapSurjective] at hsb htb
  obtain ⟨s, hs, rfl⟩ := mem_map.mp hsb
  obtain ⟨t, ht, rfl⟩ := mem_map.mp htb
  have hinj := injOn_mk_of_isPGroup Nat.prime_three Q.isPGroup'
  have hs3 : s ^ 3 = 1 := by
    have h1 : π (s ^ 3) = π 1 := by rw [map_pow, map_one]; exact hsb3
    exact hinj (pow_mem hs 3) (one_mem _) h1
  refine ⟨s, hQ ▸ mem_map_of_mem _ hs, by simpa using congrArg Subtype.val hs3,
    t, hQ ▸ mem_map_of_mem _ ht, fun hcomm => hst ?_⟩
  have hc : s * t = t * s := Subtype.ext hcomm
  rw [← map_mul, ← map_mul, hc]

end Item21Res8Proof

open Item21Res8Proof

theorem kF2110SylowNoncentral_of (h : KF2110SylowNoncentralBig) : KF2110SylowNoncentral := by
  intro G _ _ hst d hd1 hd3 J hJ hdJ S hS
  by_cases h27 : 27 ∣ Nat.card (lBar J ⧸ Subgroup.center (lBar J))
  · exact h G hst d hd1 hd3 J hJ hdJ h27 S hS
  have hq : IsQuasisimple (lBar J) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hJ
  have : Group.IsPerfect (lBar J) := hq.1
  obtain ⟨z, hz, hz1, hz3⟩ := exists_center_lBar hd1 hd3 hJ hdJ
  exact exists_of_lBar hS fun Q => exists_noncentral_of_not_dvd Q hz hz1 hz3 h27

end CFSG.RankThree.PartTwo.Sec21
