module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Heis
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin
open CFSG.RankThree.PartTwo.KFacts (centerDescend centerDescend_mk
  eq_one_of_forall_mul_inv_mem_center)

section Main

variable {Y : Type} [Group Y] [Finite Y] {L B : Subgroup Y}

theorem false_of_inf_ne_bot (hq : CFSG.IsQuasisimple ↥L) (h1 : CFSG.Open.pRank 3 L = 1)
    (hBN : B ≤ Subgroup.normalizer (L : Set Y)) (hB : IsPOnePlusTwo 3 ↥B) (hBL : B ⊓ L ≠ ⊥)
    (hS : OutThreeBound (↥L ⧸ Subgroup.center ↥L)) : False := by
  classical
  obtain ⟨hext, hBcard, hBexp⟩ := hB
  have := hext
  have hperf : Group.IsPerfect ↥L := hq.1
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  set B₀ : Subgroup ↥B := (B ⊓ L).subgroupOf B with hB₀
  have hB₀normal : B₀.Normal := by
    constructor
    intro n hn g
    have hnL : (n : Y) ∈ L := (Subgroup.mem_subgroupOf.mp hn).2
    have h := (Subgroup.mem_normalizer_iff.mp (hBN g.2) (n : Y)).mp hnL
    exact Subgroup.mem_subgroupOf.mpr ⟨(g * n * g⁻¹ : ↥B).2, h⟩
  have hB₀ne : B₀ ≠ ⊥ := by
    intro hbot
    apply hBL
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hy.1⟩ : ↥B) ∈ B₀ := Subgroup.mem_subgroupOf.mpr hy
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨z, hzB₀, hzc, hz1⟩ := exists_mem_center_of_normal_ne_bot hB₀ne
  have hzL : (z : Y) ∈ L := (Subgroup.mem_subgroupOf.mp hzB₀).2
  set a : ↥L := ⟨(z : Y), hzL⟩ with ha
  have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using congrArg Subtype.val (hBexp z))
  have ha_nc : a ∉ Subgroup.center ↥L := fun hac => by
    have h0 : a = 1 := eq_one_of_mem_center_of_cube hperf h1 hac ha3
    have h0' : (z : Y) = 1 := by
      have := congrArg (Subtype.val : ↥L → Y) h0
      simpa [ha] using this
    exact hz1 (Subtype.ext (by simpa using h0'))
  have : B.Normalizes L := ⟨hBN⟩
  let ρ₁ : ↥B →* MulAut ↥L := MulDistribMulAction.toMulAut ↥B ↥L
  have hρ₁coe : ∀ (b : ↥B) (s : ↥L), ((ρ₁ b s : ↥L) : Y) = (b : Y) * (s : Y) * (b : Y)⁻¹ :=
    fun b s => Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe B L (a := b) (k := s)
  let ρ : ↥B →* MulAut (↥L ⧸ Subgroup.center ↥L) := (centerDescend ↥L).comp ρ₁
  have hkerbot : ρ.ker = ⊥ := by
    by_contra hne
    obtain ⟨z', hz'ker, hz'c, hz'1⟩ := exists_mem_center_of_normal_ne_bot (N := ρ.ker) hne
    have hzz' : z ∈ Subgroup.zpowers z' := by
      rw [← center_eq_zpowers_of_extraspecial hz'c hz'1]
      exact hzc
    have hzker : z ∈ ρ.ker := (Subgroup.zpowers_le.mpr hz'ker) hzz'
    have hρz : ρ z = 1 := hzker
    have hρ₁z : ρ₁ z = 1 := by
      have : Group.IsPerfect ↥L := hperf
      refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
      have h := congrArg
        (fun φ : MulAut (↥L ⧸ Subgroup.center ↥L) => φ (s : ↥L ⧸ Subgroup.center ↥L)) hρz
      simp only [ρ, MonoidHom.comp_apply, centerDescend_mk, MulAut.one_apply] at h
      exact QuotientGroup.eq.mp h.symm
    apply ha_nc
    rw [Subgroup.mem_center_iff]
    intro s
    have h2 := hρ₁coe z s
    rw [hρ₁z, MulAut.one_apply] at h2
    apply Subtype.ext
    change (s : Y) * (z : Y) = (z : Y) * (s : Y)
    calc (s : Y) * (z : Y) = ((z : Y) * (s : Y) * (z : Y)⁻¹) * (z : Y) := by rw [← h2]
      _ = (z : Y) * (s : Y) := by group
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hkerbot
  have hcard : Nat.card ↥ρ.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv, hBcard]
    norm_num
  have hexp : ∀ x ∈ ρ.range, x ^ 3 = 1 := by
    rintro _ ⟨b, rfl⟩
    rw [← map_pow, hBexp b, map_one]
  have hZ : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    center_eq_bot_of_simple_nonabelian hq.2.2
  have hle := card_le_nine_of_outThreeBound (fun T hT => isCyclic_of_isPGroup_quotient h1 hT) hZ
    hS ρ.range hexp
  omega

theorem false_of_elemAbelian_nine (h1 : CFSG.Open.pRank 3 L = 1)
    {E : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEc : Nat.card ↥E = 9) : False := by
  have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hEcyc : IsCyclic ↥E := isCyclic_of_isPGroup_quotient h1 hEp
  have hexp : Monoid.exponent ↥E ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hE.2 g g.2)
  rw [IsCyclic.exponent_eq_card, hEc] at hexp
  omega

theorem three_le_pRank_of_rank_one (hq : CFSG.IsQuasisimple ↥L) (h1 : CFSG.Open.pRank 3 L = 1)
    (hBN : B ≤ Subgroup.normalizer (L : Set Y)) (hB : IsPOnePlusTwo 3 ↥B)
    (hgood : OutThreeOrElemNine (↥L ⧸ Subgroup.center ↥L)) :
    3 ≤ CFSG.Open.pRank 3 (L ⊔ B) := by
  by_cases hBL : B ⊓ L = ⊥
  · obtain ⟨a, haL, ha3, c, hcL, hac⟩ := exists_noncentral_order_three hq h1
    have hL3 : 3 ∣ Nat.card ↥L := by
      have ha1 : (⟨a, haL⟩ : ↥L) ≠ 1 := fun h => hac (by
        have : a = 1 := congrArg Subtype.val h
        rw [this]
        simp)
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hord : orderOf (⟨a, haL⟩ : ↥L) = 3 :=
        orderOf_eq_prime (Subtype.ext (by simpa using ha3)) ha1
      rw [← hord]
      exact orderOf_dvd_natCard _
    obtain ⟨E, hEle, hE, hEc⟩ := exists_elemAbelian_twentySeven_of_inf_eq_bot
      (fun T hTL hT => isCyclic_of_le_of_pRank_eq_one h1 hTL hT) hL3 hBN hB.2.1
      (fun b hb => hB.2.2 ⟨b, hb⟩ |> fun h => by simpa using congrArg Subtype.val h) hBL
    exact CFSG.RankThree.PartTwo.Sec5.le_pRank_of_elemAbelian Nat.prime_three hEle hE
      (by rw [hEc]; norm_num)
  · exfalso
    rcases hgood with hS | ⟨E, hE, hEc⟩
    · exact false_of_inf_ne_bot hq h1 hBN hB hBL hS
    · exact false_of_elemAbelian_nine h1 hE hEc

end Main

end CFSG.Quasithin.SBd19F
