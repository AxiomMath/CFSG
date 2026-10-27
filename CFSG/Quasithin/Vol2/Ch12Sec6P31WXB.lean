module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31c
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WInp
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WD
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WNT

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

theorem pow_two_pow_ne_self' {C : Type*} [Group C] {p k j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpk : p ∣ 2 ^ k + 1) (hj : Odd j) {y : C} (hy : orderOf y = p) : y ^ (2 ^ j) ≠ y := by
  intro h
  have h1 : y ^ (2 ^ j) = y ^ 1 := by rw [pow_one]; exact h
  have h2 : 2 ^ j ≡ 1 [MOD orderOf y] := pow_eq_pow_iff_modEq.mp h1
  rw [hy] at h2
  exact P31NT.not_two_pow_odd_modEq_one hp hp2 hpk hj h2

theorem exists_moved_p_element_of_dvd {Y : Type*} [Group Y] [Finite Y] {B U : Subgroup Y} {r : Y}
    {k j p : ℕ} (hUB : U ≤ B) (hBU : B ≤ Subgroup.normalizer (U : Set Y))
    (hpN : p ∣ (U.subgroupOf B).index)
    (hfrob : ∀ b ∈ B, r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ 2 ^ k + 1) (hj : Odd j) :
    ∃ n ∈ B, n ^ p ∈ U ∧ n * r * n⁻¹ * r⁻¹ ∉ U := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hN : (U.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).2 hBU
  have hdvd : p ∣ Nat.card (↥B ⧸ U.subgroupOf B) := by rw [← Subgroup.index]; exact hpN
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥B ⧸ U.subgroupOf B) p hdvd
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨(b : Y), b.2, ?_, ?_⟩
  · have h1 : (QuotientGroup.mk b : ↥B ⧸ U.subgroupOf B) ^ p = 1 := by
      rw [← hy]; exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · intro hmem
    have h2 := hfrob (b : Y) b.2
    have h3 : (b : Y) * (((b : Y) ^ 2 ^ j))⁻¹ ∈ U := by
      have e : (b : Y) * (((b : Y) ^ 2 ^ j))⁻¹ =
          ((b : Y) * r * (b : Y)⁻¹ * r⁻¹) * (r * (b : Y) * r⁻¹ * ((b : Y) ^ 2 ^ j)⁻¹) := by group
      rw [e]
      exact U.mul_mem hmem h2
    have h4 : (QuotientGroup.mk b : ↥B ⧸ U.subgroupOf B) ^ (2 ^ j) = QuotientGroup.mk b := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hc : Commute (b : Y) ((b : Y) ^ (2 ^ j)) := (Commute.refl _).pow_right _
      have h5 : (((b ^ 2 ^ j)⁻¹ * b : ↥B) : Y) = ((b : Y) ^ 2 ^ j)⁻¹ * (b : Y) := by simp
      rw [h5, ← hc.inv_right.eq]
      exact h3
    exact pow_two_pow_ne_self' (k := k) hp hp2 hpk hj hy h4

theorem exists_moved_p_element {Y : Type*} [Group Y] [Finite Y] {B U : Subgroup Y} {r : Y}
    {k j p : ℕ} (hUB : U ≤ B) (hBU : B ≤ Subgroup.normalizer (U : Set Y))
    (hcard : Nat.card B = Nat.card U * (2 ^ (2 * k) - 1))
    (hfrob : ∀ b ∈ B, r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpk : p ∣ 2 ^ k + 1) (hj : Odd j) :
    ∃ n ∈ B, n ^ p ∈ U ∧ n * r * n⁻¹ * r⁻¹ ∉ U := by
  have hUcard : Nat.card (U.subgroupOf B) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
  have hindex : (U.subgroupOf B).index = 2 ^ (2 * k) - 1 := by
    have h1 := Subgroup.index_mul_card (U.subgroupOf B)
    rw [hUcard, hcard, mul_comm (Nat.card U)] at h1
    have hpos : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  refine exists_moved_p_element_of_dvd hUB hBU ?_ hfrob hp hp2 hpk hj
  rw [hindex]
  have h2k : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hfac : 2 ^ (2 * k) - 1 = (2 ^ k + 1) * (2 ^ k - 1) := by
    rw [h2k]
    obtain ⟨b, hb⟩ : ∃ b, 2 ^ k = b + 1 := ⟨2 ^ k - 1, (Nat.sub_add_cancel hk1).symm⟩
    rw [hb, Nat.add_sub_cancel]
    have hsq : (b + 1) * (b + 1) = (b + 1 + 1) * b + 1 := by ring
    rw [hsq, Nat.add_sub_cancel]
  rw [hfac]
  exact Dvd.dvd.mul_right hpk _

section Star

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P31

theorem exists_pSubgroup_of_star {G : Type} [Group G] [Finite G] {T L H : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hT : IsPGroup 2 T) (hTH : T ≤ H)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hQT : pCoreOf 2 H ≤ T)
    {Ns Us : Subgroup (HStar H)} (hNsM : Ns ≤ star H (Subgroup.normalizer (L : Set G) ⊓ H))
    (hTsN : star H T ≤ Subgroup.normalizer (Ns : Set (HStar H)))
    (hUsT : Us ≤ star H T) (hUsN : Us ≤ Ns)
    (hNsU : Ns ≤ Subgroup.normalizer (Us : Set (HStar H)))
    (hNp : ∀ x ∈ Ns, ∃ k : ℕ, x ^ (p ^ k) ∈ Us) {n r : HStar H} (hn : n ∈ Ns)
    (hr : r ∈ star H (T ⊓ L)) (hmoved : n * r * n⁻¹ * r⁻¹ ∉ Us) :
    ∃ P : Subgroup G, P ≤ L ∧ P ≠ ⊥ ∧ IsPGroup p P ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  have hQM : pCoreOf 2 H ≤ Subgroup.normalizer (L : Set G) := hQT.trans hTL
  have hNsN : ∀ x ∈ pre H Ns, x ∈ Subgroup.normalizer (L : Set G) := by
    intro x hx
    obtain ⟨hxH, hxN⟩ := mem_pre.1 hx
    obtain ⟨m, hm, hmx⟩ := hNsM hxN
    have hmL : (m : G) ∈ Subgroup.normalizer (L : Set G) := (Subgroup.mem_subgroupOf.1 hm).1
    have hq := F126.mem_pCoreOf_of_mk_eq hmx
    have : x = m * ((m : G)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ hmL (hQM hq)
  have hTNh : T ≤ Subgroup.normalizer (pre H Ns : Set G) :=
    le_normalizer_pre hTH hTsN
  have hQle : pre H Us ≤ T := by
    intro x hx
    obtain ⟨hxH, hxU⟩ := mem_pre.1 hx
    obtain ⟨t, ht, htx⟩ := hUsT hxU
    have hq := F126.mem_pCoreOf_of_mk_eq htx
    have : x = (t : G) * ((t : G)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.1 ht) (hQT hq)
  have hQNh : pre H Us ≤ pre H Ns := fun x hx => by
    obtain ⟨hxH, hxU⟩ := mem_pre.1 hx
    exact mem_pre.2 ⟨hxH, hUsN hxU⟩
  have hNhQ : pre H Ns ≤ Subgroup.normalizer (pre H Us : Set G) := by
    refine le_normalizer_pre (pre_le Ns) ?_
    rw [star_pre]
    exact hNsU
  have hNhQp : ∀ x ∈ pre H Ns, ∃ k : ℕ, x ^ (p ^ k) ∈ pre H Us := by
    intro x hx
    obtain ⟨hxH, hxN⟩ := mem_pre.1 hx
    obtain ⟨k, hk⟩ := hNp _ hxN
    refine ⟨k, mem_pre.2 ⟨H.pow_mem hxH _, ?_⟩⟩
    have : (QuotientGroup.mk ⟨x ^ p ^ k, H.pow_mem hxH _⟩ : HStar H) =
        (QuotientGroup.mk ⟨x, hxH⟩ : HStar H) ^ p ^ k := rfl
    rw [this]
    exact hk
  have hnl : n ∈ star H (pre H Ns) := by rw [star_pre]; exact hn
  obtain ⟨n', hn'H, hn'⟩ := hnl
  obtain ⟨r', hr'H, hr'⟩ := hr
  have hn'N : (n' : G) ∈ pre H Ns := Subgroup.mem_subgroupOf.1 hn'H
  have hr'N : (r' : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.1 hr'H
  have hmoved' : (n' : G) * r' * (n' : G)⁻¹ * (r' : G)⁻¹ ∉ pre H Us := by
    intro hmem
    obtain ⟨hH, hU⟩ := mem_pre.1 hmem
    apply hmoved
    have e : (⟨(n' : G) * r' * (n' : G)⁻¹ * (r' : G)⁻¹, hH⟩ : ↥H) = n' * r' * n'⁻¹ * r'⁻¹ := rfl
    rw [e] at hU
    have : (QuotientGroup.mk (n' * r' * n'⁻¹ * r'⁻¹) : HStar H) = n * r * n⁻¹ * r⁻¹ := by
      rw [← hn', ← hr']
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [this] at hU
    exact hU
  exact P31D.exists_pSubgroup_of_moved hp hp2 hT le_rfl (fun x hx => hNsN x hx) hTNh hTL rfl hQle
    hQNh hNhQ hNhQp hn'N hr'N hmoved'

end Star


section PermData

variable {Y : Type*} [Group Y]

@[expose] def PermData (Ts Ms Tls : Subgroup Y) : Prop :=
  ∃ (p : ℕ) (Ns Us : Subgroup Y) (n r : Y), p.Prime ∧ 3 < p ∧ Ns ≤ Ms ∧
    Ts ≤ Subgroup.normalizer (Ns : Set Y) ∧ Us ≤ Ts ∧ Us ≤ Ns ∧
    Ns ≤ Subgroup.normalizer (Us : Set Y) ∧ (∀ x ∈ Ns, ∃ k : ℕ, x ^ (p ^ k) ∈ Us) ∧ n ∈ Ns ∧
    r ∈ Tls ∧ n * r * n⁻¹ * r⁻¹ ∉ Us

end PermData

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P31
open scoped IsMulCommutative

theorem permData_absurd (hNP : NoPermL_w31) {G : Type} [Group G] [Finite G] (T L V : Subgroup G)
    [IsMulCommutative ↥V] (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G} (hTH : T ≤ H)
    (hQT : pCoreOf 2 H ≤ T)
    (hD : PermData (star H T) (star H (Subgroup.normalizer (L : Set G) ⊓ H)) (star H (T ⊓ L))) :
    False := by
  obtain ⟨p, Ns, Us, n, r, hp, hp3, hNsM, hTsN, hUsT, hUsN, hNsU, hNp, hn, hr, hmoved⟩ := hD
  have hT2 : IsPGroup 2 T := (isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow
    (le_sup_right : T ≤ L ⊔ T)).2.1
  obtain ⟨P, hPL, hP0, hPp, hperm⟩ := exists_pSubgroup_of_star hp (by omega) hT2 hTH
    hH.hyp.normalizes hQT hNsM hTsN hUsT hUsN hNsU hNp hn hr hmoved
  exact hP0 (hNP G T L V F hH hZ P hPL p hp hp3 hPp hperm)

end CFSG.Quasithin.H13.P31X
