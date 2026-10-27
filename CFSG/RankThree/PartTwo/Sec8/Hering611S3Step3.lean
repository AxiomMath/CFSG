module

public import CFSG.LieType.BorelTits.Basic
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem le_pCoreOf_centralizer {V : Subgroup G} (hV2 : IsPGroup 2 V)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    V ≤ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V : Set G)) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 ?_ ?_ hV2
  · intro v hv
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    exact (hVc v hv h hh).symm
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (n : G) * (g : G) = (g : G) * (n : G) :=
      Subgroup.mem_centralizer_iff.mp g.2 n hn
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ V
    rw [← hc, mul_inv_cancel_right]
    exact hn

theorem step3_not_le_centralizer (hchar : CFSG.Assembly.IsCharTwoType G) {V : Subgroup G}
    (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥) (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {d : G}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hdV : d ∈ Subgroup.centralizer (V : Set G)) :
    ¬ CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer (V : Set G)) ≤
      Subgroup.centralizer ({d} : Set G) := by
  intro hsc
  set N : Subgroup G := Subgroup.centralizer (V : Set G) with hNdef
  set M : Subgroup G := Subgroup.normalizer (V : Set G) with hMdef
  set O : Subgroup G := CFSG.Assembly.pCoreOf 2 M with hOdef
  have hNM : N ≤ M := Subgroup.centralizer_le_normalizer (V : Set G)
  have hMloc : CFSG.Assembly.IsTwoLocal M := ⟨V, hV1, hV2, rfl⟩
  have hdM : d ∈ M := hNM hdV
  have hOle : O ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hOM : ∀ m ∈ M, ∀ x ∈ O, m * x * m⁻¹ ∈ O := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm) x).mp hx
  have hNM' : ∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N := by
    intro m hm x hx
    have hx' : ∀ h ∈ V, h * x = x * h := Subgroup.mem_centralizer_iff.mp hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro v hv
    have hmv : m⁻¹ * v * m ∈ V := by
      refine (Subgroup.mem_normalizer_iff.mp hm (m⁻¹ * v * m)).mpr ?_
      have e : m * (m⁻¹ * v * m) * m⁻¹ = v := by group
      rw [e]
      exact hv
    have hc : (m⁻¹ * v * m) * x = x * (m⁻¹ * v * m) := hx' _ hmv
    calc v * (m * x * m⁻¹) = m * ((m⁻¹ * v * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * v * m)) * m⁻¹ := by rw [hc]
      _ = m * x * m⁻¹ * v := by group
  have hXM : Subgroup.zpowers d ≤ M := Subgroup.zpowers_le.mpr hdM
  have hXN : Subgroup.zpowers d ≤ N := Subgroup.zpowers_le.mpr hdV
  have hK : ⁅O, Subgroup.zpowers d⁆ ≤ O ⊓ N := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    have hhM : h ∈ M := hXM hh
    have hhN : h ∈ N := hXN hh
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : h * g⁻¹ * h⁻¹ ∈ O := hOM h hhM g⁻¹ (O.inv_mem hg)
      have e : g * h * g⁻¹ * h⁻¹ = g * (h * g⁻¹ * h⁻¹) := by group
      rw [e]
      exact O.mul_mem hg h1
    · have h2 : g * h * g⁻¹ ∈ N := hNM' g (hOle hg) h hhN
      exact N.mul_mem h2 (N.inv_mem hhN)
  have hON : O ⊓ N ≤ CFSG.Assembly.pCoreOf 2 N := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_ (hOp.to_le inf_le_left)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnO, hnN⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact hOM (g : G) (hNM g.2) (n : G) hnO
    · exact N.mul_mem (N.mul_mem g.2 hnN) (N.inv_mem g.2)
  have hKd : ∀ k ∈ ⁅O, Subgroup.zpowers d⁆, k * d = d * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hsc (hON (hK hk)))
  have hKcomm : ⁅⁅O, Subgroup.zpowers d⁆, Subgroup.zpowers d⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro k hk x hx
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hkd : Commute k d := hKd k hk
    exact hkd.zpow_right j
  have hXO : Subgroup.zpowers d ≤ Subgroup.normalizer (O : Set G) :=
    hXM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hord : orderOf d = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hd3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hd1
    · exact h
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers d)) (Nat.card O) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hOp
    rw [Nat.card_zpowers, hord, hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hOX : ⁅O, Subgroup.zpowers d⁆ = ⊥ := by
    have h := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_coprime
      hXO hcop
    rw [hKcomm] at h
    exact h.symm
  have hdO : d ∈ Subgroup.centralizer (O : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro o ho
    have hmem : ⁅o, d⁆ ∈ ⁅O, Subgroup.zpowers d⁆ :=
      Subgroup.commutator_mem_commutator ho (Subgroup.mem_zpowers d)
    rw [hOX, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hdO' : d ∈ O := hchar M hMloc (Subgroup.mem_inf.mpr ⟨hdM, hdO⟩)
  obtain ⟨k, hpow⟩ := hOp ⟨d, hdO'⟩
  have hk' : d ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hpow
    simpa using h
  have hgcd : d ^ Nat.gcd (2 ^ k) 3 = 1 :=
    pow_gcd_eq_one.mpr ⟨hk', hd3⟩
  have hg1 : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
  rw [hg1, pow_one] at hgcd
  exact hd1 hgcd

end CFSG.RankThree.PartTwo.Sec8.Hering611
