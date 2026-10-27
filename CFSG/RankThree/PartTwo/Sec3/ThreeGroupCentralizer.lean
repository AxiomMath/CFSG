module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup

variable {G : Type*} [Group G]

theorem card_inf_centralizer_conj {S : Subgroup G} {c : G} (hc : c ∈ normalizer (S : Set G))
    (x : G) :
    Nat.card ↥(S ⊓ centralizer ({c * x * c⁻¹} : Set G)) =
      Nat.card ↥(S ⊓ centralizer ({x} : Set G)) := by
  have hcS : ∀ s, s ∈ S ↔ c * s * c⁻¹ ∈ S := fun s => mem_normalizer_iff.mp hc s
  refine Nat.card_congr
    { toFun := fun s => ⟨c⁻¹ * s * c, ?_⟩
      invFun := fun s => ⟨c * s * c⁻¹, ?_⟩
      left_inv := fun s => Subtype.ext (by simp only; group)
      right_inv := fun s => Subtype.ext (by simp only; group) }
  · obtain ⟨hs, hsx⟩ := mem_inf.mp s.2
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [hcS]
      simpa [mul_assoc] using hs
    · rw [mem_centralizer_singleton_iff] at hsx ⊢
      calc c⁻¹ * ↑s * c * x = c⁻¹ * (↑s * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * ↑s) * c := by rw [hsx]
        _ = x * (c⁻¹ * ↑s * c) := by group
  · obtain ⟨hs, hsx⟩ := mem_inf.mp s.2
    refine mem_inf.mpr ⟨(hcS _).mp hs, ?_⟩
    rw [mem_centralizer_singleton_iff] at hsx ⊢
    calc c * ↑s * c⁻¹ * (c * x * c⁻¹) = c * (↑s * x) * c⁻¹ := by group
      _ = c * (x * ↑s) * c⁻¹ := by rw [hsx]
      _ = c * x * c⁻¹ * (c * ↑s * c⁻¹) := by group

theorem centralizer_sq_eq_of_pow_three {d : G} (hd : d ^ 3 = 1) :
    centralizer ({d ^ 2} : Set G) = centralizer ({d} : Set G) := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hdd : d = (d ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hd, one_mul, pow_one]
    rw [hdd, pow_two, ← mul_assoc, h, mul_assoc, h, mul_assoc]
  · intro h
    rw [pow_two, ← mul_assoc, h, mul_assoc, h, mul_assoc]

theorem commute_of_card_le_two {K : Subgroup G} [Finite K] (hK : Nat.card K ≤ 2) {c : G}
    (hc : c ∈ normalizer (K : Set G)) {s : G} (hs : s ∈ K) : s * c = c * s := by
  classical
  by_cases hs1 : s = 1
  · rw [hs1, one_mul, mul_one]
  have hcs : c * s * c⁻¹ ∈ K := (mem_normalizer_iff.mp hc s).mp hs
  have hcs1 : c * s * c⁻¹ ≠ 1 := by
    intro h
    apply hs1
    calc s = c⁻¹ * (c * s * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  have hK2 : ∀ t ∈ K, t ≠ 1 → t = s := by
    intro t ht ht1
    by_contra hts
    have h3 : 3 ≤ Nat.card K := by
      have : ({(⟨1, K.one_mem⟩ : K), (⟨s, hs⟩ : K), (⟨t, ht⟩ : K)} : Finset K).card ≤
          Nat.card K := by
        have := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card]
        exact Finset.card_le_univ _
      refine le_trans ?_ this
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]
        intro h
        exact hts (congrArg Subtype.val h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hs1 (congrArg Subtype.val h).symm,
          fun h => ht1 (congrArg Subtype.val h).symm⟩
    omega
  have := hK2 _ hcs hcs1
  calc s * c = c * s * c⁻¹ * c := by rw [this]
    _ = c * s := by group

theorem rank3II_3_19 [Finite G] {P S : Subgroup G} (hP : IsPGroup 3 P) (hS : IsPGroup 2 S)
    (hPS : P ≤ normalizer (S : Set G)) (hfaith : ∀ g ∈ P, (∀ s ∈ S, g * s = s * g) → g = 1)
    {x : G} (hxP : x ∈ P) (hx : orderOf x = 3) :
    (∀ y ∈ (Subgroup.upperCentralSeries P 2).map P.subtype, x * y = y * x) ∨
      2 < Nat.card ↥(S ⊓ centralizer ({x} : Set G)) := by
  classical
  by_contra hcon
  rw [not_or, not_forall, not_lt] at hcon
  obtain ⟨⟨y, hcomm⟩, hcard⟩ := hcon
  rw [Classical.not_imp] at hcomm
  obtain ⟨hy, hxy⟩ := hcomm
  obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
  obtain ⟨z, hzdef⟩ : ∃ z : G, z = y' * x * (y' : G)⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hzP : z ∈ P := hzdef ▸
    P.mul_mem (P.mul_mem (P.mul_mem y'.2 hxP) (P.inv_mem y'.2)) (P.inv_mem hxP)
  have hzcen : ∀ g ∈ P, g * z = z * g := by
    have h1 := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mp hy' ⟨x, hxP⟩
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff] at h1
    intro g hg
    have h2 := congrArg Subtype.val (h1 ⟨g, hg⟩)
    rw [hzdef]
    simpa [commutatorElement_def] using h2
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hz1 : z ≠ 1 := by
    intro h
    apply hxy
    have : (y' : G) * x * (y' : G)⁻¹ * x⁻¹ = 1 := hzdef ▸ h
    calc x * y' = (y' * x * (y' : G)⁻¹ * x⁻¹)⁻¹ * (y' * x) := by group
      _ = y' * x := by rw [this, inv_one, one_mul]
  have hyx1 : (y' : G) * x * (y' : G)⁻¹ = z * x := by rw [hzdef]; group
  have hyx : ∀ k : ℕ, (y' : G) ^ k * x * ((y' : G) ^ k)⁻¹ = z ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzy : (y' : G) * z ^ k = z ^ k * y' :=
        ((Commute.pow_right (hzcen _ y'.2) k)).eq
      calc (y' : G) ^ (k + 1) * x * ((y' : G) ^ (k + 1))⁻¹
          = y' * ((y' : G) ^ k * x * ((y' : G) ^ k)⁻¹) * (y' : G)⁻¹ := by group
        _ = y' * (z ^ k * x) * (y' : G)⁻¹ := by rw [ih]
        _ = z ^ k * (y' * x * (y' : G)⁻¹) := by rw [← mul_assoc, hzy]; group
        _ = z ^ k * (z * x) := by rw [hyx1]
        _ = z ^ (k + 1) * x := by rw [pow_succ, mul_assoc (z ^ k) z x]
  have hz3 : z ^ 3 = 1 := by
    have h := hyx 3
    have hxz : x * z = z * x := hzcen x hxP
    have h3 : (z * x) ^ 3 = z ^ 3 * x ^ 3 := (Commute.mul_pow hxz.symm 3)
    have h4 : (y' : G) * x ^ 3 * (y' : G)⁻¹ = (z * x) ^ 3 := by
      have := hyx 1
      rw [pow_one, pow_one] at this
      calc (y' : G) * x ^ 3 * (y' : G)⁻¹ = (y' * x * (y' : G)⁻¹) ^ 3 := conj_pow.symm
        _ = (z * x) ^ 3 := by rw [this]
    rw [hx3, mul_one, mul_inv_cancel, h3, hx3, mul_one] at h4
    exact h4.symm
  have hzx : z ∉ zpowers x := by
    intro hz
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
    have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have hle : zpowers z ≤ zpowers x := zpowers_le.mpr hz
    have heq : zpowers z = zpowers x :=
      eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hord])
    have hxz : x ∈ zpowers z := heq ▸ mem_zpowers x
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hxz
    apply hxy
    change x * y' = y' * x
    rw [← hm]
    exact ((Commute.zpow_left (hzcen _ y'.2).symm m)).eq
  set A : Subgroup G := closure {x, z} with hAdef
  have hAP : A ≤ P := by
    rw [hAdef, closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact hxP
    · exact hzP
  have hxzc : x * z = z * x := hzcen x hxP
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    have hsub : ({x, z} : Set G) ⊆ centralizer ({x, z} : Set G) := by
      intro g hg h hh
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
      · rfl
      · exact hxzc.symm
      · exact hxzc
      · rfl
    have hle : A ≤ centralizer (A : Set G) := by
      rw [hAdef, centralizer_closure]
      exact (closure_le_centralizer_centralizer _).trans
        (centralizer_le hsub)
    intro a ha b hb
    exact (mem_centralizer_iff.mp (hle hb) a ha)
  have hAexp : ∀ a ∈ A, a ^ 3 = 1 := by
    intro a ha
    induction ha using closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact hx3
      · exact hz3
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [(Commute.mul_pow (hAcomm a ha b hb) 3), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hxA : x ∈ A := subset_closure (Set.mem_insert x _)
  have hzA : z ∈ A := subset_closure (Set.mem_insert_of_mem x rfl)
  have hAcard : 3 ^ (1 + 1) ≤ Nat.card A := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((hP.to_le hAP))
    have hdvd : 3 ∣ Nat.card A := by
      have := card_dvd_of_le (zpowers_le.mpr hxA)
      rwa [Nat.card_zpowers, hx] at this
    have hne : Nat.card A ≠ 3 := by
      intro h3
      apply hzx
      have heq : zpowers x = A :=
        eq_of_le_of_card_ge (zpowers_le.mpr hxA) (by rw [Nat.card_zpowers, hx, h3])
      rw [heq]
      exact hzA
    rw [hk] at hdvd hne ⊢
    rcases k with _ | _ | k
    · norm_num at hdvd
    · norm_num at hne
    · rw [show 3 ^ (k + 2) = 3 ^ (1 + 1) * 3 ^ k by ring]
      exact Nat.le_mul_of_pos_right _ (by positivity)
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three A S ⟨⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩, hAexp⟩ hAcard
    (hAP.trans hPS) hcop
  have hAelt : ∀ a ∈ A, ∃ i j : ℕ, a = x ^ i * z ^ j := by
    intro a ha
    induction ha using closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨i, j, rfl⟩ := iha
      obtain ⟨i', j', rfl⟩ := ihb
      refine ⟨i + i', j + j', ?_⟩
      have hc : Commute (z ^ j) (x ^ i') := (Commute.pow_pow hxzc.symm j i')
      rw [pow_add, pow_add, mul_assoc, ← mul_assoc (z ^ j), hc.eq]
      group
    | inv a ha iha =>
      obtain ⟨i, j, rfl⟩ := iha
      refine ⟨2 * i, 2 * j, ?_⟩
      have hc : Commute (x ^ i) (z ^ j) := (Commute.pow_pow hxzc i j)
      have hxi : (x ^ i)⁻¹ = x ^ (2 * i) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hx3,
          one_pow]
      have hzj : (z ^ j)⁻¹ = z ^ (2 * j) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hz3,
          one_pow]
      rw [mul_inv_rev, ← hxi, ← hzj, hc.inv_inv.eq]
  have hyN : ∀ k : ℕ, (y' : G) ^ k ∈ normalizer (S : Set G) :=
    fun k => hPS (P.pow_mem y'.2 k)
  have hxzj : ∀ j : ℕ, Nat.card ↥(S ⊓ centralizer ({x * z ^ j} : Set G)) ≤ 2 := by
    intro j
    have h := card_inf_centralizer_conj (hyN j) x
    rw [hyx j, ← (Commute.pow_right hxzc j).eq] at h
    rw [h]
    exact hcard
  have hsmall : ∀ d ∈ A, d ∉ zpowers z → Nat.card ↥(S ⊓ centralizer ({d} : Set G)) ≤ 2 := by
    intro d hd hdz
    obtain ⟨i, j, rfl⟩ := hAelt d hd
    have hxi : x ^ i = x ^ (i % 3) := by
      conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, hx3, one_pow, mul_one]
    rw [hxi] at hdz ⊢
    have hmod : i % 3 < 3 := Nat.mod_lt i (by norm_num)
    interval_cases (i % 3)
    · exact absurd (by rw [pow_zero, one_mul]; exact pow_mem (mem_zpowers z) j) hdz
    · rw [pow_one]
      exact hxzj j
    · have hd3 : (x ^ 2 * z ^ j) ^ 3 = 1 :=
        hAexp _ (mul_mem (pow_mem hxA 2) (pow_mem hzA j))
      rw [← centralizer_sq_eq_of_pow_three hd3]
      have hsq : (x ^ 2 * z ^ j) ^ 2 = x * z ^ (2 * j) := by
        have hc : Commute (x ^ 2) (z ^ j) := (Commute.pow_pow hxzc 2 j)
        rw [hc.mul_pow, ← pow_mul, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3,
          one_mul, pow_one, mul_comm j 2]
      rw [hsq]
      exact hxzj (2 * j)
  have hzS : ∀ s ∈ S, z * s = s * z := by
    intro s hs
    rw [← hgen] at hs
    have hle : (⨆ D ∈ CFSG.Open.signalizerFunctorEk 3 1 A,
        S ⊓ centralizer (D : Set G)) ≤ centralizer ({z} : Set G) := by
      refine iSup₂_le fun D hD => ?_
      obtain ⟨hDA, hDcard⟩ := hD
      by_cases hzD : z ∈ D
      · intro t ht
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp (mem_inf.mp ht).2 z hzD).symm
      ·
        obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
          rcases D.bot_or_exists_ne_one with h | h
          · rw [h, card_bot] at hDcard
            norm_num at hDcard
          · exact h
        have hdz : d ∉ zpowers z := by
          intro hdz
          apply hzD
          have hd3 : d ^ 3 = 1 := hAexp d (hDA hdD)
          have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
          have hle : zpowers d ≤ zpowers z := zpowers_le.mpr hdz
          have hordz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
          have heq : zpowers d = zpowers z :=
            eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordz])
          exact (zpowers_le.mpr hdD) (heq ▸ mem_zpowers z)
        have hsub : S ⊓ centralizer (D : Set G) ≤ S ⊓ centralizer ({d} : Set G) := by
          refine inf_le_inf_left _ (centralizer_le ?_)
          simpa using hdD
        have hcardD : Nat.card ↥(S ⊓ centralizer (D : Set G)) ≤ 2 :=
          (card_le_of_le hsub).trans (hsmall d (hDA hdD) hdz)
        have hzDc : ∀ g ∈ D, Commute g z := fun g hg => hAcomm g (hDA hg) z hzA
        have hzN : z ∈ normalizer ((S ⊓ centralizer (D : Set G) : Subgroup G) : Set G) := by
          rw [mem_normalizer_iff]
          intro t
          have hzSN := mem_normalizer_iff.mp (hPS (hAP hzA)) t
          constructor
          · intro ht
            obtain ⟨htS, htD⟩ := mem_inf.mp ht
            refine mem_inf.mpr ⟨hzSN.mp htS, mem_centralizer_iff.mpr fun g hg => ?_⟩
            have hgt : Commute g t := mem_centralizer_iff.mp htD g hg
            exact (((hzDc g hg).mul_right hgt).mul_right (hzDc g hg).inv_right).eq
          · intro ht
            obtain ⟨htS, htD⟩ := mem_inf.mp ht
            refine mem_inf.mpr ⟨hzSN.mpr htS, mem_centralizer_iff.mpr fun g hg => ?_⟩
            have hgt : Commute g (z * t * z⁻¹) := mem_centralizer_iff.mp htD g hg
            have ht' : t = z⁻¹ * (z * t * z⁻¹) * z := by group
            rw [ht']
            exact ((((hzDc g hg).inv_right).mul_right hgt).mul_right (hzDc g hg)).eq
        intro t ht
        rw [mem_centralizer_singleton_iff]
        exact commute_of_card_le_two hcardD hzN ht
    have := hle hs
    rw [mem_centralizer_singleton_iff] at this
    exact this.symm
  exact hz1 (hfaith z hzP fun s hs => hzS s hs)

end CFSG.RankThree.PartTwo.Sec3
