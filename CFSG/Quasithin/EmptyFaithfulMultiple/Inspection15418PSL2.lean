module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Involution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace Insp15418

theorem twelve_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : 12 ∣ p ^ 2 - 1 := by
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  have hp12 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
  have hsq : p ^ 2 = p * p := by ring
  have hpos : 1 ≤ p * p := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [hsq]
  rcases hp12 with h12 | h12 | h12 | h12 <;>
  · have : (p * p) % 12 = 1 := by
      rw [Nat.mul_mod, h12]
    omega

open CFSG.GorensteinWalter CFSG.BenderSuzuki.External in
theorem exists_involution_hasOddNormal {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = p ^ 2) :
    ∃ s₀ : PSL2 K, s₀ ^ 2 = 1 ∧ s₀ ≠ 1 ∧
      HasOddNormal (Subgroup.centralizer ({s₀} : Set (PSL2 K))) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, w, hUcyc, hUcard, -, -, -, -, -, hnorm⟩ :=
    huppert_II_8_3_split_torus_reflection_data (F := K) (p := p) (f := 2) hK
  have h12 := twelve_dvd_sq_sub_one hp h5
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    rw [hK]
    exact Nat.gcd_eq_right (dvd_trans (by norm_num) h12)
  have h6 : 6 ∣ Nat.card U := by
    rw [hUcard, hgcd, hK]
    obtain ⟨m, hm⟩ := h12
    rw [hm, show 12 * m = 2 * (6 * m) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact dvd_mul_right 6 m
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (dvd_trans (by norm_num) h6)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := U) 3 (dvd_trans (by norm_num) h6)
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have := (IsCyclic.isMulCommutative (α := ↥U)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  set s₀ : PSL2 K := (s : PSL2 K) with hs₀
  set Y := Subgroup.zpowers (y : PSL2 K) with hY
  have hs₀ord : orderOf s₀ = 2 := by rw [hs₀, Subgroup.orderOf_coe, hs]
  have hyord : orderOf (y : PSL2 K) = 3 := by rw [Subgroup.orderOf_coe, hy]
  have hYU : Y ≤ U := Subgroup.zpowers_le.mpr y.2
  have hYne : Y ≠ ⊥ := by
    intro h
    have : (y : PSL2 K) ∈ Y := Subgroup.mem_zpowers _
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hyord
    omega
  have hs₀ne : Subgroup.zpowers s₀ ≠ ⊥ := by
    intro h
    have : s₀ ∈ Subgroup.zpowers s₀ := Subgroup.mem_zpowers _
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hs₀ord
    omega
  refine ⟨s₀, by have := pow_orderOf_eq_one s₀; rwa [hs₀ord] at this, fun h => by
    rw [h, orderOf_one] at hs₀ord; omega, Y, ?_, ?_, ?_, hYne⟩
  ·
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hUcomm z (hYU hz) s₀ s.2)
  ·
    have hCN : Subgroup.centralizer ({s₀} : Set (PSL2 K)) ≤
        Subgroup.normalizer (Subgroup.zpowers s₀ : Set (PSL2 K)) := by
      refine le_normalizer_of_forall fun g hg z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hgs : g * s₀ = s₀ * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      have hconj : g * s₀ * g⁻¹ = s₀ := by rw [hgs]; group
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hconj]
      exact (Subgroup.zpowers s₀).zpow_mem (Subgroup.mem_zpowers s₀) k
    rw [hnorm Y hYU hYne, ← hnorm (Subgroup.zpowers s₀) (Subgroup.zpowers_le.mpr s.2) hs₀ne]
    exact hCN
  · rw [Nat.card_zpowers, hyord]
    decide

end Insp15418

open Insp15418

open CFSG.GorensteinWalter in
theorem involutionCentralizerPSL2_holds : InvolutionCentralizerPSL2 := by
  intro p hp h5 K _ _ hK x hx2 hx1
  obtain ⟨s₀, hs2, hs1, hY⟩ := exists_involution_hasOddNormal hp h5 K hK
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp, hp.odd_of_ne_two (by omega), by norm_num, hK⟩
  obtain ⟨g, hg⟩ :=
    psl2_involutions_conjugate_of_odd_prime_power K hodd s₀ x ⟨hs1, hs2⟩ ⟨hx1, hx2⟩
  refine oddCoreIn_ne_bot_of_hasOddNormal (HasOddNormal.of_map_equiv (MulAut.conj g).symm ?_)
  rw [map_centralizer_singleton]
  have : (MulAut.conj g).symm x = s₀ := by
    rw [← hg, MulAut.conj_symm_apply]
    group
  rw [this]
  exact hY

theorem involutionCentralizer15418_holds : InvolutionCentralizer15418 :=
  involutionCentralizer15418_of involutionCentralizerPSL2_holds

end CFSG.Quasithin.EmptyFaithfulMultiple
