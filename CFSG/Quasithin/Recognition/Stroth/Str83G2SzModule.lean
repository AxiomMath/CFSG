module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SzThreeGen
public import CFSG.Quasithin.Vol2.Ch11SecE3LieSzGen
public import CFSG.Timmesfeld.Bridge.SchurNarrowCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedCentre
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzSmall

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.Quasithin.H CFSG.Quasithin.H.Sz CFSG.QuasithinUnique.Setup.X7
open scoped Matrix MatrixGroups Pointwise

theorem dEnt_ne_one {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ} (hl : l ≠ 1) (i : Fin 4) :
    dEnt a l i ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hb4⟩ := suzuki_frobenius_exponents a K hK
  have hodd := odd_card_units hK
  have hcop2 : Nat.Coprime (2 ^ a) (Nat.card Kˣ) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have hpow2 : l ^ (2 ^ a) = 1 → l = 1 := by
    intro hn
    have h2 : orderOf l ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hn
    have h3 : orderOf l ∣ Nat.card Kˣ := orderOf_dvd_natCard l
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop2 h2 h3)
  fin_cases i
  · intro h
    have h' : l ^ (1 + (2 ^ a : ℤ)) = 1 := Units.ext (by simpa [dEnt] using h)
    have h'' : l ^ (((1 + 2 ^ a : ℕ) : ℤ)) = 1 := by
      rw [show (((1 + 2 ^ a : ℕ) : ℤ)) = 1 + (2 ^ a : ℤ) by push_cast; ring]
      exact h'
    exact hl (hb4.1 (by simpa [one_zpow] using h''))
  · intro h
    have h' : l ^ (((2 ^ a : ℕ) : ℤ)) = 1 := by
      have h1 : ((l ^ (2 ^ a : ℤ) : Kˣ) : K) = 1 := by simpa [dEnt] using h
      exact Units.ext h1
    have h'' : l ^ (2 ^ a) = 1 := by
      rw [zpow_natCast] at h'
      exact h'
    exact hl (hpow2 h'')
  · intro h
    have h1 : ((l ^ (-(2 ^ a : ℤ)) : Kˣ) : K) = 1 := by simpa [dEnt] using h
    have h2 : l ^ (-(2 ^ a : ℤ)) = 1 := Units.ext h1
    have h3 : l ^ (((2 ^ a : ℕ) : ℤ)) = 1 := by
      rw [zpow_neg] at h2
      exact inv_eq_one.mp h2
    have h4 : l ^ (2 ^ a) = 1 := by
      rw [zpow_natCast] at h3
      exact h3
    exact hl (hpow2 h4)
  · intro h
    have h1 : ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) = 1 := by simpa [dEnt] using h
    have h2 : l ^ (-1 - (2 ^ a : ℤ)) = 1 := Units.ext h1
    have h3 : l ^ (-(((1 + 2 ^ a : ℕ) : ℤ))) = 1 := by
      rw [show -(((1 + 2 ^ a : ℕ) : ℤ)) = -1 - (2 ^ a : ℤ) by push_cast; ring]
      exact h2
    rw [zpow_neg, inv_eq_one] at h3
    exact hl (hb4.1 (by simpa [one_zpow] using h3))

private theorem eq_zero_of_suzukiD_map_mulVec_eq_self {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ} (hl : l ≠ 1) (c : ℕ)
    {v : Fin 4 → K} (h : (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = v) : v = 0 := by
  have hf : Function.Injective (fun x : K => x ^ 2 ^ c) := by
    intro x y hxy
    exact iterateFrobenius_inj K 2 c (by simpa [iterateFrobenius_def] using hxy)
  have hne : ∀ i : Fin 4, (dEnt a l i) ^ 2 ^ c ≠ 1 := by
    intro i h1
    exact dEnt_ne_one hK hl i (hf (by simpa using h1))
  have hMdiag : (suzukiD a l).map (· ^ 2 ^ c) =
      Matrix.diagonal (fun i : Fin 4 => (dEnt a l i) ^ 2 ^ c) := by
    rw [suzukiD_eq_diagonal, Matrix.diagonal_map]
    simp
  have hv : (Matrix.diagonal (fun i : Fin 4 => (dEnt a l i) ^ 2 ^ c)) *ᵥ v = v := by
    simpa [hMdiag] using h
  funext i
  have hi := congrFun hv i
  rw [Matrix.mulVec_diagonal] at hi
  have hsub : ((dEnt a l i) ^ 2 ^ c - 1) * v i = 0 := by
    rw [sub_mul, one_mul, hi, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr (hne i))

theorem isSzNatural_suzukiDElt_fixedSub_eq_bot {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (↥(suzukiGroup a K)) W) (hρ : IsSzNatural ρ)
    {l : Kˣ} (hl : l ≠ 1) :
    fixedSub ρ (Subgroup.zpowers (suzukiDElt a K l)) = ⊥ := by
  haveI : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  obtain ⟨c, φ, hφ⟩ := hρ
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hfix : ρ (suzukiDElt a K l) w = w :=
    mem_fixedSub.mp hw _ (Subgroup.mem_zpowers _)
  have h1 : ((suzukiD a l).map (· ^ 2 ^ c)) *ᵥ (φ w) = φ w := by
    have := hφ (suzukiDElt a K l) w
    rw [coe_suzukiDElt, hfix] at this
    exact this.symm
  have h2 : φ w = 0 := eq_zero_of_suzukiD_map_mulVec_eq_self hK hl c h1
  exact φ.injective (by rw [h2, map_zero])

theorem isSzNatural_mem_suzukiT_fixedSub_eq_bot {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (↥(suzukiGroup a K)) W) (hρ : IsSzNatural ρ)
    {h : ↥(suzukiGroup a K)} (hh : h ∈ suzukiT a K) (h1 : h ≠ 1) :
    fixedSub ρ (Subgroup.zpowers h) = ⊥ := by
  obtain ⟨l, rfl⟩ := (mem_suzukiT_iff).1 hh
  refine isSzNatural_suzukiDElt_fixedSub_eq_bot hK ρ hρ ?_
  intro hl
  exact h1 (by rw [hl, suzukiDElt_one])

theorem suzukiB_le_normalizer_suzukiZ0 {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ≤ Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := by
  have hconjU : ∀ y ∈ suzukiU a K, ∀ z ∈ suzukiZ0 a K,
      y * z * y⁻¹ ∈ suzukiZ0 a K := by
    intro y hy z hz
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
    obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
    have hEq : suzukiSElt a K c d * suzukiSElt a K 0 v * (suzukiSElt a K c d)⁻¹ =
        suzukiSElt a K 0 v := by
      rw [← suzukiSElt_zero_commute hK v c d]
      group
    rw [hEq]
    exact hz
  have hconjT : ∀ y ∈ suzukiT a K, ∀ z ∈ suzukiZ0 a K,
      y * z * y⁻¹ ∈ suzukiZ0 a K := by
    intro y hy z hz
    obtain ⟨l, rfl⟩ := (mem_suzukiT_iff).1 hy
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
    rw [suzukiDElt_conj' hK l 0 v]
    simp only [mul_zero]
    exact (mem_suzukiZ0_iff hK).2 ⟨_, rfl⟩
  refine sup_le ?_ ?_
  · intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨hconjU u hu z, fun hz => by
      have h := hconjU u⁻¹ ((suzukiU a K).inv_mem hu) (u * z * u⁻¹) hz
      simpa [mul_assoc] using h⟩
  · intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨hconjT t ht z, fun hz => by
      have h := hconjT t⁻¹ ((suzukiT a K).inv_mem ht) (t * z * t⁻¹) hz
      simpa [mul_assoc] using h⟩

theorem suzukiZ0_sup_szZ_eq_top {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiZ0 a K ⊔ szZ a K = ⊤ := by
  haveI : IsSimpleGroup ↥(suzukiGroup a K) := (suzuki_simple ha hK).2.2
  have hsz : szZ a K = CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (suzukiZ0 a K) :=
    rfl
  let H : Subgroup ↥(suzukiGroup a K) :=
    suzukiZ0 a K ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (suzukiZ0 a K)
  have hH : H = suzukiZ0 a K ⊔ szZ a K := by rw [hsz]
  have hZ0 : suzukiZ0 a K ≤ H := by
    change suzukiZ0 a K ≤ suzukiZ0 a K ⊔
      CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (suzukiZ0 a K)
    exact le_sup_left
  have hZ0ne : suzukiZ0 a K ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (suzukiZ0 a K) = 1 := by rw [hbot, Subgroup.card_bot]
    rw [CFSG.Quasithin.Vol2.Ch11.SecE3.card_suzukiZ0 hK, hK] at hcard
    have h2 : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    omega
  by_cases hW : suzukiWElt a K ∈ H
  · have htop : H = ⊤ :=
      suzuki_eq_top_of_suzukiZ0_le_of_W_mem hK ha hZ0 hW
    rw [hH] at htop
    exact htop
  · let Ksub : Subgroup ↥(suzukiGroup a K) := H ⊔ Subgroup.zpowers (suzukiWElt a K)
    have hKtop : Ksub = ⊤ := by
      change H ⊔ Subgroup.zpowers (suzukiWElt a K) = ⊤
      have hZ0' : suzukiZ0 a K ≤ H ⊔ Subgroup.zpowers (suzukiWElt a K) :=
        hZ0.trans le_sup_left
      have hW' : suzukiWElt a K ∈ H ⊔ Subgroup.zpowers (suzukiWElt a K) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers (suzukiWElt a K))
      exact suzuki_eq_top_of_suzukiZ0_le_of_W_mem hK ha hZ0' hW'
    have hW2 : suzukiWElt a K * suzukiWElt a K = 1 := suzukiWElt_mul_self
    have hW1 : suzukiWElt a K ≠ 1 := suzukiWElt_ne_one
    have horder : orderOf (suzukiWElt a K) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hW2) hW1
    have hHw : CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) H = H := by
      have hHdef : H = suzukiZ0 a K ⊔
          CFSG.CGT.Timmesfeld75.conjSubgroup (suzukiWElt a K) (suzukiZ0 a K) := rfl
      rw [hHdef, CFSG.CGT.Timmesfeld75.conjSubgroup_sup_eq_sup,
        CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, suzukiWElt_mul_self,
        CFSG.CGT.Timmesfeld75.conjSubgroup_one, sup_comm]
    have hKN : Subgroup.zpowers (suzukiWElt a K) ≤
        Subgroup.normalizer (H : Set ↥(suzukiGroup a K)) := by
      rw [Subgroup.zpowers_le, CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq]
      exact hHw
    have hinf : H ⊓ Subgroup.zpowers (suzukiWElt a K) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxH, hxZ⟩ := Subgroup.mem_inf.mp hx
      rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two horder).mp hxZ with
        rfl | rfl
      · exact Subgroup.mem_bot.mpr rfl
      · exact absurd hxH hW
    have hprod : (H : Set ↥(suzukiGroup a K)) *
        (Subgroup.zpowers (suzukiWElt a K) : Set ↥(suzukiGroup a K)) = Set.univ := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left H
          (Subgroup.zpowers (suzukiWElt a K)) hKN,
        show H ⊔ Subgroup.zpowers (suzukiWElt a K) = Ksub from rfl, hKtop, Subgroup.coe_top]
    have hcomp : H.IsComplement' (Subgroup.zpowers (suzukiWElt a K)) :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) hprod
    have hidx : H.index = 2 := by
      rw [hcomp.symm.index_eq_card, Nat.card_zpowers, horder]
    have hHne : H ≠ ⊥ := by
      intro hbot
      exact hZ0ne (le_bot_iff.mp (hbot ▸ hZ0))
    haveI : H.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
    · exact absurd h hHne
    · rw [hH] at h
      exact h

end CFSG.Quasithin.Stroth
