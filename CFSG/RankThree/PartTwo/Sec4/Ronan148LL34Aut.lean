module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LL34A5
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LL34Facts

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts

section Inn

variable {X : Type*} [Group X]

theorem inn_normal : (MulAut.conj : X →* MulAut X).range.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ φ
  refine ⟨φ x, ?_⟩
  ext y
  simp [MulAut.mul_apply, MulAut.inv_def, MulAut.conj_apply]

theorem conj_injective_of_center (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut X => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact hxZ

end Inn

theorem factorization_mulAut_three : (241920 : ℕ).factorization 3 = 3 := by
  rw [show (241920 : ℕ) = 3 ^ 3 * 8960 by norm_num,
    Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

section L34

variable {k : Type} [Field k] (hk : Nat.card k = 4) {X : Type} [Group X]
  (χ : X ≃* projectiveSL 3 k) (hZ : Subgroup.center X = ⊥)
include hk χ hZ

theorem l34_card_inn : Nat.card (MulAut.conj : X →* MulAut X).range = 20160 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center hZ)).toEquiv,
    l34_card hk χ]

theorem l34_card_quot_inn :
    Nat.card (MulAut X ⧸ (MulAut.conj : X →* MulAut X).range) = 12 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAut.conj : X →* MulAut X).range
  rw [l34_mulAut_card hk χ, l34_card_inn hk χ hZ] at h
  omega

theorem inf_inn_card_eq_three {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) {α : MulAut X} (hαB : α ∈ B)
    (hαI : α ∉ (MulAut.conj : X →* MulAut X).range) :
    Nat.card (B ⊓ (MulAut.conj : X →* MulAut X).range : Subgroup (MulAut X)) = 3 ∧
      ∀ x ∈ B, ∃ i : ℤ, α ^ i * x ∈ (MulAut.conj : X →* MulAut X).range := by
  haveI := inn_normal (X := X)
  haveI := l34_mulAut_finite hk χ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set q : MulAut X →* MulAut X ⧸ I := QuotientGroup.mk' I with hq
  have hker : q.ker = I := QuotientGroup.ker_mk' I
  have h1 := card_map_mul_card_inf_ker q B
  rw [hker, hB9] at h1
  have hd9 : Nat.card (B.map q) ∣ 9 := hB9 ▸ B.card_map_dvd q
  have hd12 : Nat.card (B.map q) ∣ 12 :=
    (l34_card_quot_inn hk χ hZ) ▸ Subgroup.card_subgroup_dvd_card _
  have hd3 : Nat.card (B.map q) ∣ 3 := by
    have := Nat.dvd_gcd hd9 hd12
    norm_num at this
    exact this
  have hqα1 : q α ≠ 1 := fun h => hαI (hker ▸ (MonoidHom.mem_ker.mpr h))
  have hqα3 : q α ^ 3 = 1 := by rw [← map_pow, hB.2 α hαB, map_one]
  have hoα : orderOf (q α) = 3 := orderOf_eq_prime hqα3 hqα1
  have hzle : Subgroup.zpowers (q α) ≤ B.map q :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem q hαB)
  have h3d : 3 ∣ Nat.card (B.map q) := by
    rw [← hoα, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hzle
  have hc3 : Nat.card (B.map q) = 3 := Nat.dvd_antisymm hd3 h3d
  refine ⟨by rw [hc3] at h1; omega, ?_⟩
  have heq : Subgroup.zpowers (q α) = B.map q :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hc3, Nat.card_zpowers, hoα])
  intro x hx
  have hqx : q x ∈ Subgroup.zpowers (q α) := heq ▸ Subgroup.mem_map_of_mem q hx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hqx
  refine ⟨-j, ?_⟩
  rw [← hker, MonoidHom.mem_ker, map_mul, map_zpow, zpow_neg, ← hj, inv_mul_cancel]

theorem false_of_inner_commute {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) {α : MulAut X} (hαB : α ∈ B)
    (hαI : α ∉ (MulAut.conj : X →* MulAut X).range)
    (hcomm : ∀ x : X, x ^ 3 = 1 → MulAut.conj x ∈ Subgroup.normalizer (B : Set (MulAut X)) →
      MulAut.conj x * α = α * MulAut.conj x) : False := by
  haveI := inn_normal (X := X)
  haveI := l34_mulAut_finite hk χ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := (MulAut.conj : X →* MulAut X).range with hI
  obtain ⟨hBI3, hdec⟩ := inf_inn_card_eq_three hk χ hZ hB hB9 hαB hαI
  have hBp : IsPGroup 3 B := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 x x.2)⟩
  obtain ⟨R, hBR⟩ := hBp.exists_le_sylow
  have hR27 : Nat.card (R : Subgroup (MulAut X)) = 27 := by
    rw [Sylow.card_eq_multiplicity, l34_mulAut_card hk χ, factorization_mulAut_three]
    norm_num
  have hBRn : (B.subgroupOf (R : Subgroup (MulAut X))).Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    have hc : Nat.card (B.subgroupOf (R : Subgroup (MulAut X))) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBR).toEquiv, hB9]
    have hmul := (B.subgroupOf (R : Subgroup (MulAut X))).card_mul_index
    rw [hc, hR27] at hmul
    rw [hR27, show (27 : ℕ).minFac = 3 by norm_num]
    omega
  set q : MulAut X →* MulAut X ⧸ I := QuotientGroup.mk' I with hq
  have hker : q.ker = I := QuotientGroup.ker_mk' I
  have hRI9 : Nat.card ((R : Subgroup (MulAut X)) ⊓ I : Subgroup (MulAut X)) = 9 := by
    have h1 := card_map_mul_card_inf_ker q (R : Subgroup (MulAut X))
    rw [hker, hR27] at h1
    have hd27 : Nat.card ((R : Subgroup (MulAut X)).map q) ∣ 27 :=
      hR27 ▸ (R : Subgroup (MulAut X)).card_map_dvd q
    have hd12 : Nat.card ((R : Subgroup (MulAut X)).map q) ∣ 12 :=
      (l34_card_quot_inn hk χ hZ) ▸ Subgroup.card_subgroup_dvd_card _
    have hd3 : Nat.card ((R : Subgroup (MulAut X)).map q) ∣ 3 := by
      have := Nat.dvd_gcd hd27 hd12
      norm_num at this
      exact this
    have e27 : Nat.card ((R : Subgroup (MulAut X)) ⊓ I : Subgroup (MulAut X)) ∣ 27 :=
      hR27 ▸ Subgroup.card_dvd_of_le inf_le_left
    have e20160 : Nat.card ((R : Subgroup (MulAut X)) ⊓ I : Subgroup (MulAut X)) ∣ 20160 :=
      (l34_card_inn hk χ hZ) ▸ Subgroup.card_dvd_of_le inf_le_right
    have e9 : Nat.card ((R : Subgroup (MulAut X)) ⊓ I : Subgroup (MulAut X)) ∣ 9 := by
      have := Nat.dvd_gcd e27 e20160
      norm_num at this
      exact this
    have hle3 := Nat.le_of_dvd (by norm_num) hd3
    have hle9 := Nat.le_of_dvd (by norm_num) e9
    nlinarith
  obtain ⟨n, hnRI, hnB⟩ : ∃ n ∈ (R : Subgroup (MulAut X)) ⊓ I, n ∉ B := by
    by_contra hcon
    push Not at hcon
    have hle : (R : Subgroup (MulAut X)) ⊓ I ≤ B ⊓ I := fun x hx => ⟨hcon x hx, hx.2⟩
    have := Subgroup.card_le_of_le hle
    rw [hRI9, hBI3] at this
    omega
  obtain ⟨y, rfl⟩ := hnRI.2
  set Q : Subgroup X := (R : Subgroup (MulAut X)).comap (MulAut.conj : X →* MulAut X) with hQdef
  have hQ : IsPGroup 3 Q := R.isPGroup'.comap_of_injective _ (conj_injective_of_center hZ)
  have hyQ : y ∈ Q := hnRI.1
  have hy3 : y ^ 3 = 1 := l34_pow_three hk χ hQ hyQ
  have hn3 : MulAut.conj y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hnN : MulAut.conj y ∈ Subgroup.normalizer (B : Set (MulAut X)) := by
    apply Subgroup.mem_normalizer_fintype
    intro b hb
    exact hBRn.conj_mem ⟨b, hBR hb⟩ hb ⟨MulAut.conj y, hnRI.1⟩
  have hnα := hcomm y hy3 hnN
  have hnB' : ∀ b ∈ B, b * MulAut.conj y = MulAut.conj y * b := by
    intro b hb
    obtain ⟨i, x, hx⟩ := hdec b hb
    have hxQ : x ∈ Q := by
      show MulAut.conj x ∈ (R : Subgroup (MulAut X))
      rw [hx]
      exact hBR (B.mul_mem (B.zpow_mem hαB i) hb)
    have hxy : x * y = y * x := l34_comm_of_isPGroup hk χ hQ hxQ hyQ
    have hcx : Commute (MulAut.conj x) (MulAut.conj y) := by
      change MulAut.conj x * MulAut.conj y = MulAut.conj y * MulAut.conj x
      rw [← map_mul, ← map_mul, hxy]
    have hαy : Commute (α ^ (-i)) (MulAut.conj y) :=
      (show Commute (MulAut.conj y) α from hnα).symm.zpow_left (-i)
    have hb' : b = α ^ (-i) * MulAut.conj x := by rw [hx, zpow_neg, inv_mul_cancel_left]
    rw [hb']
    exact (hαy.mul_left hcx).eq
  have hB' := isElemAbelian_sup_zpowers hB hn3 hnB'
  have hlt : B < B ⊔ Subgroup.zpowers (MulAut.conj y) := by
    refine lt_of_le_of_ne le_sup_left fun h => hnB ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := l34_card_le_nine hk χ hB'
  omega

end L34

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
