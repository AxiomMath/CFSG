module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

@[expose] def FF79KTypeLn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (J : Subgroup G), (n = 4 ∨ n = 5) →
    CFSG.IsQuasisimple ↥J → IsTypeLnq n 2 1 J →
    Nat.Coprime 3 (Nat.card ↥(Subgroup.center ↥J)) ∧
    (∀ P : Sylow 3 ↥J, IsElemAb 3 2 ((P : Subgroup ↥J).map J.subtype)) ∧
    ∀ x ∈ Nor J, (∃ k : ℕ, x ^ (3 ^ k) = 1) → ∃ j ∈ J, ∀ y ∈ J, x * y * x⁻¹ = j * y * j⁻¹

variable {G : Type} [Group G] [Finite G]

private theorem isSylowOf_card {H P : Subgroup G} (h : IsSylowOf 3 P H) :
    Nat.card P = 3 ^ (Nat.card H).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hp, hcop⟩ := h
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, ha] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hf : (P.relIndex H).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
  rw [← h1, Nat.factorization_mul hne (by positivity), Finsupp.add_apply, hf,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same, zero_add, ha]

private theorem isSylowOf_of_card {H P : Subgroup G} (hle : P ≤ H)
    (hc : Nat.card P = 3 ^ (Nat.card H).factorization 3) : IsSylowOf 3 P H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hle, IsPGroup.of_card hc, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, hc] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  have hpos : 0 < (P.relIndex H).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hne hdvd
  have h2 : (P.relIndex H * 3 ^ (Nat.card H).factorization 3).factorization 3 =
      (Nat.card H).factorization 3 := by rw [h1]
  rw [Nat.factorization_mul hne (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at h2
  omega

private theorem exists_sylowOf (H : Subgroup G) : ∃ P : Subgroup G, IsSylowOf 3 P H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  refine ⟨(P : Subgroup H).map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact P.isPGroup'.map H.subtype
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (P.not_dvd_index)

private theorem exists_conj_le_sylowOf {H P Q : Subgroup G} (hP : IsSylowOf 3 P H) (hQH : Q ≤ H)
    (hQ : IsPGroup 3 Q) : ∃ k ∈ H, ∀ x ∈ Q, k * x * k⁻¹ ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPH, hPp, hPi⟩ := hP
  let A : Subgroup ↥H := P.subgroupOf H
  let Q' : Subgroup ↥H := Q.subgroupOf H
  have hAp : IsPGroup 3 A := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hQ'p : IsPGroup 3 Q' := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hAi : ¬ 3 ∣ A.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hPi
  obtain ⟨S, hS⟩ := hQ'p.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥H (hAp.toSylow hAi) S
  refine ⟨((k : ↥H) : G)⁻¹, H.inv_mem k.2, fun x hx => ?_⟩
  have hxS : (⟨x, hQH hx⟩ : ↥H) ∈ ((k • hAp.toSylow hAi : Sylow 3 ↥H) : Subgroup ↥H) := by
    rw [hk]
    exact hS (show (⟨x, hQH hx⟩ : ↥H) ∈ Q' from hx)
  rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
    Subgroup.mem_smul_pointwise_iff_exists] at hxS
  obtain ⟨s, hs, hseq⟩ := hxS
  have h1 := congrArg Subtype.val hseq
  have hsP : (s : G) ∈ P := hs
  have h2 : ((k : ↥H) : G) * (s : G) * ((k : ↥H) : G)⁻¹ = x := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  have h3 : ((k : ↥H) : G)⁻¹ * x * ((k : ↥H) : G) = s := by
    rw [← h2]; group
  have : ((k : ↥H) : G)⁻¹ * x * ((k : ↥H) : G)⁻¹⁻¹ = s := by rw [inv_inv]; exact h3
  rw [this]
  exact hsP

private theorem isSylowOf_inf_normal {H B N : Subgroup G} (hB : IsSylowOf 3 B H) (hNH : N ≤ H)
    (hnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : IsSylowOf 3 (B ⊓ N) N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := exists_sylowOf (G := G) N
  obtain ⟨k, hkH, hk⟩ := exists_conj_le_sylowOf hB (hQ.1.trans hNH) hQ.2.1
  let Q' : Subgroup G := Q.map (MulAut.conj k).toMonoidHom
  have hQ'le : Q' ≤ B ⊓ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hk x hx, hnorm k hkH x (hQ.1 hx)⟩
  have hQ'card : Nat.card Q' = 3 ^ (Nat.card N).factorization 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact isSylowOf_card hQ
  have hQ'syl : IsSylowOf 3 Q' N := isSylowOf_of_card (hQ'le.trans inf_le_right) hQ'card
  refine ⟨inf_le_right, hB.2.1.to_le inf_le_left, ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex Q' (B ⊓ N) N hQ'le inf_le_right
  have h2 : Nat.Coprime 3 (Q'.relIndex N) := hQ'syl.2.2
  rw [← h1] at h2
  exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) h2

private theorem decomp_of_sylow {C J C₀ B : Subgroup G} (hB : IsSylowOf 3 B C) (hJC : J ≤ C)
    (hC₀C : C₀ ≤ C) (hJn : ∀ g ∈ C, ∀ j ∈ J, g * j * g⁻¹ ∈ J)
    (hC₀n : ∀ g ∈ C, ∀ c ∈ C₀, g * c * g⁻¹ ∈ C₀)
    (hcomm : ∀ j ∈ J, ∀ c ∈ C₀, j * c = c * j)
    (hI : Nat.Coprime 3 (Nat.card ↥(J ⊓ C₀)))
    (hBM : ∀ x ∈ B, ∃ j ∈ J, ∃ c ∈ C₀, x = j * c) :
    IsSylowOf 3 (B ⊓ J) J ∧ (∀ x ∈ B, ∃ u ∈ B ⊓ J, ∃ v ∈ B ⊓ C₀, x = u * v) ∧
      Nat.card B = Nat.card ↥(B ⊓ J) * Nat.card ↥(B ⊓ C₀) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBJ := isSylowOf_inf_normal hB hJC hJn
  have hBC₀ := isSylowOf_inf_normal hB hC₀C hC₀n
  have hBp : IsPGroup 3 B := hB.2.1
  have hBM' : B ≤ J ⊔ C₀ := by
    intro x hx
    obtain ⟨j, hj, c, hc, rfl⟩ := hBM x hx
    exact Subgroup.mul_mem_sup hj hc
  have hMC : J ⊔ C₀ ≤ C := sup_le hJC hC₀C
  have hBsyl : IsSylowOf 3 B (J ⊔ C₀) := by
    refine ⟨hBM', hBp, ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex B (J ⊔ C₀) C hBM' hMC
    have hBi := hB.2.2
    rw [← h1] at hBi
    exact Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hBi
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute J C₀ hcomm
  have h1 : Nat.card B = 3 ^ (Nat.card ↥(J ⊔ C₀)).factorization 3 := isSylowOf_card hBsyl
  have h2 : Nat.card ↥(B ⊓ J) = 3 ^ (Nat.card ↥J).factorization 3 := isSylowOf_card hBJ
  have h3 : Nat.card ↥(B ⊓ C₀) = 3 ^ (Nat.card ↥C₀).factorization 3 := isSylowOf_card hBC₀
  have hfI : (Nat.card ↥(J ⊓ C₀)).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hI)
  have hMne : Nat.card ↥(J ⊔ C₀) ≠ 0 := Nat.card_pos.ne'
  have hIne : Nat.card ↥(J ⊓ C₀) ≠ 0 := Nat.card_pos.ne'
  have hJne : Nat.card ↥J ≠ 0 := Nat.card_pos.ne'
  have hC₀ne : Nat.card ↥C₀ ≠ 0 := Nat.card_pos.ne'
  have h4 : (Nat.card ↥(J ⊔ C₀) * Nat.card ↥(J ⊓ C₀)).factorization 3 =
      (Nat.card ↥J * Nat.card ↥C₀).factorization 3 := by rw [hprod]
  rw [Nat.factorization_mul hMne hIne, Nat.factorization_mul hJne hC₀ne] at h4
  simp only [Finsupp.add_apply, hfI, add_zero] at h4
  have hcardB : Nat.card B = Nat.card ↥(B ⊓ J) * Nat.card ↥(B ⊓ C₀) := by
    rw [h1, h2, h3, h4, pow_add]
  let f : ↥(B ⊓ J) × ↥(B ⊓ C₀) → B := fun p =>
    ⟨(p.1 : G) * (p.2 : G), B.mul_mem p.1.2.1 p.2.2.1⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ heq
    have h : u * v = u' * v' := congrArg Subtype.val heq
    have hz : u'⁻¹ * u = v' * v⁻¹ := by
      calc u'⁻¹ * u = u'⁻¹ * (u * v) * v⁻¹ := by group
        _ = u'⁻¹ * (u' * v') * v⁻¹ := by rw [h]
        _ = v' * v⁻¹ := by group
    have hzI : u'⁻¹ * u ∈ J ⊓ C₀ :=
      ⟨J.mul_mem (J.inv_mem hu'.2) hu.2, by rw [hz]; exact C₀.mul_mem hv'.2 (C₀.inv_mem hv.2)⟩
    have hzB : u'⁻¹ * u ∈ B := B.mul_mem (B.inv_mem hu'.1) hu.1
    have hz1 : u'⁻¹ * u = 1 := by
      have hd : orderOf (⟨u'⁻¹ * u, hzI⟩ : ↥(J ⊓ C₀)) ∣ Nat.card ↥(J ⊓ C₀) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hd
      obtain ⟨k, hk⟩ := hBp ⟨_, hzB⟩
      have hd2 : orderOf (u'⁻¹ * u) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hI) hd2 hd)
    have huu : u' = u := inv_mul_eq_one.mp hz1
    subst huu
    have hvv : v = v' := mul_left_cancel h
    subst hvv
    rfl
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, ← hcardB])
  refine ⟨hBJ, fun x hx => ?_, hcardB⟩
  obtain ⟨⟨u, v⟩, hp⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨u, u.2, v, v.2, (congrArg Subtype.val hp).symm⟩

private theorem mem_zpowers_of_orderOf_three {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {u v : Z} (hu : orderOf u = 3) (hv : orderOf v = 3) : v ∈ Subgroup.zpowers u := by
  have : Subgroup.zpowers v = Subgroup.zpowers u :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hu, hv])
  rw [← this]
  exact Subgroup.mem_zpowers v

private theorem cyclic_dichotomy {B₁ : Subgroup G} [IsCyclic ↥B₁] (hp : IsPGroup 3 B₁) {b : G}
    (hb : b ∈ B₁) (hb3 : orderOf b = 3) :
    B₁ = Subgroup.zpowers b ∨ ∃ w ∈ B₁, w ^ 3 = b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥B₁)
  have hgo : orderOf g = 3 ^ m := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hm]
  have hzle : Subgroup.zpowers b ≤ B₁ := Subgroup.zpowers_le.mpr hb
  have hzcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb3]
  by_cases hm2 : 2 ≤ m
  · right
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    set w₀ : ↥B₁ := g ^ (3 ^ m') with hw₀
    have hw3 : w₀ ^ 3 = g ^ (3 ^ (m' + 1)) := by
      rw [hw₀, ← pow_mul, ← pow_succ]
    have hord : orderOf (w₀ ^ 3) = 3 := by
      rw [hw3, orderOf_pow_of_dvd (by positivity) (by rw [hgo]; exact pow_dvd_pow 3 (by omega)),
        hgo, Nat.pow_div (by omega) (by norm_num)]
      simp
    have hord' : orderOf (⟨b, hb⟩ : ↥B₁) = 3 := by rw [Subgroup.orderOf_mk, hb3]
    have hmem : (⟨b, hb⟩ : ↥B₁) ∈ Subgroup.zpowers (w₀ ^ 3) :=
      mem_zpowers_of_orderOf_three hord hord'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨((w₀ ^ j : ↥B₁) : G), (w₀ ^ j).2, ?_⟩
    have : (w₀ ^ j) ^ 3 = ⟨b, hb⟩ := by
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    simpa using congrArg Subtype.val this
  · left
    have hle : Nat.card B₁ ≤ 3 := by
      rw [hm]
      calc 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 3 := by norm_num
    exact (Subgroup.eq_of_le_of_card_ge hzle (by omega)).symm

private theorem mem_cen_iff {x z : G} : z ∈ Cen x ↔ z * x = x * z :=
  Subgroup.mem_centralizer_singleton_iff

private theorem nsc_contra {b : G} {B : Subgroup G} (hb3 : orderOf b = 3)
    (hB : IsSylowOf 3 B (Cen b)) (hbB : b ∈ B)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hS : ∀ z ∈ B, z ^ 3 = 1 → (∃ w ∈ B, w ^ 3 = z) → z ∈ Subgroup.zpowers b)
    (hcube : ∃ w ∈ B, w ^ 3 = b) (hnsc : FFNotStronglyClosed b) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, g, hg1, hg2⟩ := hnsc
  obtain ⟨w, hwB, hwb⟩ := hcube
  have hxB : x ∈ B := (Subgroup.zpowers_le.mpr hbB) hx
  have hx3 : x ^ 3 = 1 := by
    have hd : orderOf x ∣ 3 := hb3 ▸ orderOf_dvd_of_mem_zpowers hx
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  have hx1 : x ≠ 1 := by
    intro h
    apply hg2
    rw [h]
    simpa using Subgroup.one_mem _
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hxcube : ∃ w' ∈ B, w' ^ 3 = x := by
    refine ⟨w ^ m, B.zpow_mem hwB m, ?_⟩
    rw [← hm, ← hwb, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hbx : ∀ z : G, z * x = x * z → z * b = b * z := by
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr hx
    have hcard : Nat.card (Subgroup.zpowers b) ≤ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hb3, hxo]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    have hb' : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb'
    intro z hz
    rw [← hj]
    exact (Commute.zpow_right (show Commute z x from hz) j).eq
  have hxb : ∀ z : G, z * b = b * z → z * x = x * z := fun z hz => by
    rw [← hm]
    exact (Commute.zpow_right (show Commute z b from hz) m).symm.eq.symm
  set x' : G := g * x * g⁻¹ with hx'def
  have hx'3 : x' ^ 3 = 1 := by
    rw [hx'def, conj_pow, hx3]
    group
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hx1
    have : x = g⁻¹ * x' * g := by rw [hx'def]; group
    rw [this, h]
    group
  have hx'o : orderOf x' = 3 := orderOf_eq_prime hx'3 hx'1
  have hx'p : IsPGroup 3 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'o]; norm_num)
  have hx'C : Subgroup.zpowers x' ≤ Cen b := Subgroup.zpowers_le.mpr hg1
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_sylowOf hB hx'C hx'p
  have hyB : c * x' * c⁻¹ ∈ B := hc x' (Subgroup.mem_zpowers x')
  set k : G := c * g with hk
  set y : G := c * x' * c⁻¹ with hy
  have hyk : y = k * x * k⁻¹ := by rw [hy, hx'def, hk]; group
  have hCy : (Cen b).map (MulAut.conj k).toMonoidHom = Cen y := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwx : w * x = x * w := hxb w (mem_cen_iff.mp hw)
      rw [mem_cen_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hyk]
      calc k * w * k⁻¹ * (k * x * k⁻¹) = k * (w * x) * k⁻¹ := by group
        _ = k * (x * w) * k⁻¹ := by rw [hwx]
        _ = k * x * k⁻¹ * (k * w * k⁻¹) := by group
    · intro hz
      rw [mem_cen_iff, hyk] at hz
      refine ⟨k⁻¹ * z * k, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      show k⁻¹ * z * k ∈ Cen b
      rw [mem_cen_iff]
      apply hbx
      have : (k⁻¹ * z * k) * x = x * (k⁻¹ * z * k) := by
        calc (k⁻¹ * z * k) * x = k⁻¹ * (z * (k * x * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * x * k⁻¹) * z) * k := by rw [hz]
          _ = x * (k⁻¹ * z * k) := by group
      exact this
  have hcardCy : Nat.card ↥(Cen y) = Nat.card ↥(Cen b) := by
    rw [← hCy, Subgroup.card_map_of_injective (MulAut.conj k).injective]
  have hBle : B ≤ Cen y := fun β hβ => mem_cen_iff.mpr (hcomm β hβ y hyB)
  have hDle : B.map (MulAut.conj k).toMonoidHom ≤ Cen y :=
    hCy ▸ Subgroup.map_mono hB.1
  have hBy : IsSylowOf 3 B (Cen y) :=
    isSylowOf_of_card hBle (by rw [isSylowOf_card hB, hcardCy])
  obtain ⟨h, hhC, hh⟩ := exists_conj_le_sylowOf hBy hDle (hB.2.1.map _)
  have hN : ∀ β ∈ B, h * k * β * (h * k)⁻¹ ∈ B := by
    intro β hβ
    have := hh (k * β * k⁻¹) ⟨β, hβ, by simp [MulAut.conj_apply]⟩
    simpa [mul_assoc] using this
  have hhy : h * y = y * h := mem_cen_iff.mp hhC
  have hNx : h * k * x * (h * k)⁻¹ = y := by
    calc h * k * x * (h * k)⁻¹ = h * (k * x * k⁻¹) * h⁻¹ := by group
      _ = h * y * h⁻¹ := by rw [← hyk]
      _ = y := by rw [hhy]; group
  have hy3 : y ^ 3 = 1 := by rw [hyk, conj_pow, hx3]; group
  obtain ⟨w', hw'B, hw'3⟩ := hxcube
  have hyS : y ∈ Subgroup.zpowers b := by
    refine hS y hyB hy3 ⟨h * k * w' * (h * k)⁻¹, hN w' hw'B, ?_⟩
    rw [conj_pow, hw'3, hNx]
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hyS
  have hcb : c * b = b * c := mem_cen_iff.mp hcC
  have hcy : c * y = y * c := by
    rw [← hs]
    exact (Commute.zpow_right (show Commute c b from hcb) s).eq
  apply hg2
  have : x' = c⁻¹ * y * c := by rw [hy]; group
  rw [this, mul_assoc, ← hcy]
  simpa using hyS

private theorem isCyclic_of_le_centralizer {J Q : Subgroup G} (hcyc : FFCentCyclicSylow J)
    (hQ : Q ≤ CenS J) (hp : IsPGroup 3 Q) : IsCyclic ↥Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ'p : IsPGroup 3 (Q.subgroupOf (CenS J)) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hQ).symm
  obtain ⟨P, hP⟩ := hQ'p.exists_le_sylow
  haveI := hcyc P
  have h2 : IsCyclic ↥(Q.subgroupOf (CenS J)) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hP)
      (Subgroup.subgroupOfEquivOfLe hP).surjective
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQ)
    (Subgroup.subgroupOfEquivOfLe hQ).surjective

private theorem mem_zpowers_of_cyclic {B₁ : Subgroup G} [IsCyclic ↥B₁] {b z : G} (hb : b ∈ B₁)
    (hz : z ∈ B₁) (hb3 : orderOf b = 3) (hz3 : z ^ 3 = 1) : z ∈ Subgroup.zpowers b := by
  by_cases hz1 : z = 1
  · rw [hz1]
    exact Subgroup.one_mem _
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have h := mem_zpowers_of_orderOf_three (u := (⟨b, hb⟩ : ↥B₁)) (v := (⟨z, hz⟩ : ↥B₁))
    (by rw [Subgroup.orderOf_mk, hb3]) (by rw [Subgroup.orderOf_mk, hzo])
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
  exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩

theorem ff79_1_3_struct (hK : FF79KTypeLn) {G : Type} [Group G] [Finite G] {n : ℕ}
    (hn : n = 4 ∨ n = 5) {b : G} {J : Subgroup G} (h : FF79Hyp n b J) {B : Subgroup G}
    (hB : IsSylowOf 3 B (Cen b)) :
    IsElemAb 3 3 B ∧ IsElemAb 3 2 (B ⊓ J) ∧ Subgroup.zpowers b ⊔ (B ⊓ J) = B ∧
      B ⊓ CenS J = Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJC, hcomp, huniq⟩ := h.std
  have hJq : CFSG.IsQuasisimple ↥J :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hcomp.1
  obtain ⟨hZ3, hSyl, hact⟩ := hK G n J hn hJq h.model
  have h3J : 3 ∣ Nat.card ↥J := by
    obtain ⟨P⟩ : Nonempty (Sylow 3 ↥J) := inferInstance
    have h9 : Nat.card ((P : Subgroup ↥J).map J.subtype) = 3 ^ 2 := (hSyl P).2
    rw [Subgroup.card_map_of_injective J.subtype_injective] at h9
    have hd : Nat.card (P : Subgroup ↥J) ∣ Nat.card ↥J := Subgroup.card_subgroup_dvd_card _
    rw [h9] at hd
    exact (dvd_pow_self 3 (by norm_num)).trans hd
  have hJn : ∀ c ∈ Cen b, ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
    intro c hc j hj
    let φ : ↥(Cen b) ≃* ↥(Cen b) := MulAut.conj (⟨c, hc⟩ : ↥(Cen b))
    have hcomp' := CFSG.LocalCores.isComponent_map_mulEquiv φ hcomp
    have hjC : j ∈ Cen b := hJC hj
    have hdvd : 3 ∣ Nat.card ↥(J.subgroupOf (Cen b)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv]
    have hdvd' : 3 ∣ Nat.card ↥((J.subgroupOf (Cen b)).map φ.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective φ.injective]
    have heq := huniq _ hcomp' hdvd'
    have hmem : φ ⟨j, hjC⟩ ∈ (J.subgroupOf (Cen b)).map φ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, hj, rfl⟩
    rw [heq] at hmem
    exact hmem
  have hnor : ∀ x ∈ B, x ∈ Nor J := by
    intro x hx
    refine Subgroup.mem_set_normalizer_iff.mpr (fun y => ⟨fun hy => hJn x (hB.1 hx) y hy,
      fun hy => ?_⟩)
    have := hJn x⁻¹ (Subgroup.inv_mem _ (hB.1 hx)) _ hy
    have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rw [e] at this
    exact this
  set C₀ : Subgroup G := CenS J ⊓ Cen b with hC₀
  have hBM : ∀ x ∈ B, ∃ j ∈ J, ∃ c ∈ C₀, x = j * c := by
    intro x hx
    have hp : ∃ k : ℕ, x ^ (3 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hB.2.1 ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    obtain ⟨j, hj, hjy⟩ := hact x (hnor x hx) hp
    refine ⟨j, hj, j⁻¹ * x, ⟨?_, ?_⟩, by group⟩
    · show j⁻¹ * x ∈ CenS J
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := hjy y hy
      calc y * (j⁻¹ * x) = j⁻¹ * (j * y * j⁻¹) * x := by group
        _ = j⁻¹ * (x * y * x⁻¹) * x := by rw [this]
        _ = j⁻¹ * x * y := by group
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hJC hj)) (hB.1 hx)
  have hcomm : ∀ j ∈ J, ∀ c ∈ C₀, j * c = c * j := fun j hj c hc =>
    Subgroup.mem_centralizer_iff.mp hc.1 j hj
  have hC₀n : ∀ g ∈ Cen b, ∀ c ∈ C₀, g * c * g⁻¹ ∈ C₀ := by
    intro g hg c hc
    refine ⟨?_, ?_⟩
    · show g * c * g⁻¹ ∈ CenS J
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hj' : g⁻¹ * j * g ∈ J := by
        have := hJn g⁻¹ (Subgroup.inv_mem _ hg) j hj
        simpa using this
      have hcj := hcomm _ hj' c hc
      calc j * (g * c * g⁻¹) = g * ((g⁻¹ * j * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * j * g)) * g⁻¹ := by rw [hcj]
        _ = g * c * g⁻¹ * j := by group
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hc.2) (Subgroup.inv_mem _ hg)
  have hI : Nat.Coprime 3 (Nat.card ↥(J ⊓ C₀)) := by
    have hle : J ⊓ C₀ ≤ (Subgroup.center ↥J).map J.subtype := by
      rintro z ⟨hzJ, hzC⟩
      refine ⟨⟨z, hzJ⟩, ?_, rfl⟩
      show (⟨z, hzJ⟩ : ↥J) ∈ Subgroup.center ↥J
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC.1 g g.2)
    have hd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective J.subtype_injective] at hd
    exact Nat.Coprime.coprime_dvd_right hd hZ3
  obtain ⟨hBJ, hdec, hcardB⟩ := decomp_of_sylow hB hJC inf_le_right hJn hC₀n hcomm hI hBM
  have hB₁eq : B ⊓ C₀ = B ⊓ CenS J :=
    le_antisymm (inf_le_inf_left B inf_le_left) (fun x hx => ⟨hx.1, hx.2, hB.1 hx.1⟩)
  have hB₀ : IsElemAb 3 2 (B ⊓ J) := by
    have hp : IsPGroup 3 ((B ⊓ J).subgroupOf J) :=
      hBJ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hBJ.1).symm
    have hi : ¬ 3 ∣ ((B ⊓ J).subgroupOf J).index :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hBJ.2.2
    have := hSyl (hp.toSylow hi)
    rwa [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left inf_le_right] at this
  haveI : IsElementaryAbelian 3 ↥(B ⊓ J) := hB₀.1
  have hB₁p : IsPGroup 3 ↥(B ⊓ CenS J) := hB.2.1.to_le inf_le_left
  haveI hB₁cyc : IsCyclic ↥(B ⊓ CenS J) := isCyclic_of_le_centralizer h.cyc inf_le_right hB₁p
  have hcomm₀₁ : ∀ u ∈ B ⊓ J, ∀ v ∈ B ⊓ CenS J, u * v = v * u := fun u hu v hv =>
    Subgroup.mem_centralizer_iff.mp hv.2 u hu.2
  have hdec' : ∀ x ∈ B, ∃ u ∈ B ⊓ J, ∃ v ∈ B ⊓ CenS J, x = u * v := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec x hx
    exact ⟨u, hu, v, hB₁eq ▸ hv, rfl⟩
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec' x hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hdec' y hy
    have huu' : Commute u u' := congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥(B ⊓ J))).comm ⟨u, hu⟩ ⟨u', hu'⟩)
    have hvv' : Commute v v' := congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥(B ⊓ CenS J))).comm ⟨v, hv⟩ ⟨v', hv'⟩)
    have huv' : Commute u v' := hcomm₀₁ u hu v' hv'
    have hvu' : Commute v u' := (hcomm₀₁ u' hu' v hv).symm
    exact ((huu'.mul_right huv').mul_left (hvu'.mul_right hvv')).eq
  have hb3pow : b ^ 3 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [h.ord] at this
  have hbB : b ∈ B := by
    obtain ⟨c, hcC, hc⟩ := exists_conj_le_sylowOf hB
      (Subgroup.zpowers_le.mpr (show b ∈ Cen b from mem_cen_iff.mpr rfl))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord]; norm_num))
    have := hc b (Subgroup.mem_zpowers b)
    have hcb : c * b = b * c := mem_cen_iff.mp hcC
    have e : c * b * c⁻¹ = b := by rw [hcb]; group
    rwa [e] at this
  have hbJ : ∀ j ∈ J, j * b = b * j := fun j hj => mem_cen_iff.mp (hJC hj)
  have hbB₁ : b ∈ B ⊓ CenS J := ⟨hbB, Subgroup.mem_centralizer_iff.mpr hbJ⟩
  have hS : ∀ z ∈ B, z ^ 3 = 1 → (∃ w ∈ B, w ^ 3 = z) → z ∈ Subgroup.zpowers b := by
    rintro z hzB hz3 ⟨w, hwB, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec' w hwB
    have hu3 : u ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := B ⊓ J) u hu
    have hcu : Commute u v := hcomm₀₁ u hu v hv
    have hv3 : (u * v) ^ 3 = v ^ 3 := by rw [hcu.mul_pow, hu3, one_mul]
    rw [hv3] at hz3 ⊢
    exact mem_zpowers_of_cyclic (B₁ := B ⊓ CenS J) hbB₁ (pow_mem hv 3) h.ord hz3
  have hB₁ : B ⊓ CenS J = Subgroup.zpowers b := by
    rcases cyclic_dichotomy hB₁p hbB₁ h.ord with h1 | ⟨w, hw, hw3⟩
    · exact h1
    · exact (nsc_contra h.ord hB hbB hBab hS ⟨w, hw.1, hw3⟩ h.nsc).elim
  have hsup : Subgroup.zpowers b ⊔ (B ⊓ J) = B := by
    refine le_antisymm (sup_le (Subgroup.zpowers_le.mpr hbB) inf_le_left) (fun x hx => ?_)
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec' x hx
    rw [hB₁] at hv
    rw [hcomm₀₁ u hu v (hB₁ ▸ hv)]
    exact Subgroup.mul_mem_sup hv hu
  refine ⟨⟨?_, ?_⟩, hB₀, hsup, hB₁⟩
  · haveI : IsElementaryAbelian 3 ↥(Subgroup.zpowers b) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hb3pow
    have hCE : Subgroup.zpowers b ≤ Subgroup.centralizer ((B ⊓ J : Subgroup G) : Set G) := by
      refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
      exact hbJ u hu.2
    have hEA := IsElementaryAbelian.sup_of_le_centralizer (p := 3) (E := B ⊓ J)
      (C := Subgroup.zpowers b) hCE
    rw [sup_comm, hsup] at hEA
    exact hEA
  · rw [hcardB, hB₀.2, hB₁eq, hB₁, Nat.card_zpowers, h.ord]
    norm_num

end CFSG.RankThree.PartTwo.Sec21.FF79
