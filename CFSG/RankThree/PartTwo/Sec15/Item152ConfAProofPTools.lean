module

import CFSG.GH74.GLS.LU.Local.FiveSL2
import CFSG.RankThree.PartTwo.Sec10.Item109
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped MatrixGroups

namespace Proof152ConfA

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem eq_one_of_mem_of_pow_two_pow {F : Subgroup Q} (hF : Odd (Nat.card F)) {x : Q}
    (hx : x ∈ F) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ Nat.card F := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : F)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card F) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hF)
  have h3 := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem exists_pow_sq_eq_one_mk {F : Subgroup Q} [F.Normal] (hF : Odd (Nat.card F)) (y : Q)
    (hz : (QuotientGroup.mk' F y) ^ 2 = 1) :
    ∃ k : ℕ, (y ^ k) ^ 2 = 1 ∧ QuotientGroup.mk' F (y ^ k) = QuotientGroup.mk' F y := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨b, ?_, ?_⟩
  · have hmem : (y ^ b) ^ 2 ∈ F := by
      rw [← QuotientGroup.eq_one_iff (N := F)]
      change QuotientGroup.mk' F ((y ^ b) ^ 2) = 1
      rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, hz, one_pow]
    refine eq_one_of_mem_of_pow_two_pow hF hmem (k := a) ?_
    rw [← pow_mul, ← pow_mul, show b * (2 * 2 ^ a) = (2 ^ a * b) * 2 by ring, pow_mul, ← hab,
      pow_orderOf_eq_one, one_pow]
  · obtain ⟨m, rfl⟩ := hb
    rw [map_pow, pow_succ, pow_mul, hz, one_pow, one_mul]

theorem exists_involution_mem_normal (e : Q ⧸ CFSG.oddCore Q ≃* SL(2, ZMod 5)) :
    ∃ t : Q, t ^ 2 = 1 ∧ t ∉ CFSG.oddCore Q ∧
      QuotientGroup.mk' (CFSG.oddCore Q) t ∈ Subgroup.center (Q ⧸ CFSG.oddCore Q) ∧
      ∀ N : Subgroup Q, N.Normal → ¬ N ≤ CFSG.oddCore Q → t ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := CFSG.oddCore Q with hFdef
  have hFodd : Odd (Nat.card F) := Sec10.odd_card_oddCore
  set π := QuotientGroup.mk' F with hπ
  have hZ2 : Nat.card (Subgroup.center (Q ⧸ F)) = 2 :=
    CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e.symm
  have : Nontrivial (Subgroup.center (Q ⧸ F)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hZ2]
    norm_num
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := exists_ne (1 : Subgroup.center (Q ⧸ F))
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz2 : z ^ 2 = 1 := by
    have h := orderOf_dvd_natCard (⟨z, hzZ⟩ : Subgroup.center (Q ⧸ F))
    rw [hZ2, Subgroup.orderOf_mk] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1'
  have hlift : ∀ y : Q, π y = z → ∃ s : Q, s ^ 2 = 1 ∧ π s = z ∧ s ∈ Subgroup.zpowers y := by
    intro y hy
    obtain ⟨k, hk2, hkπ⟩ := exists_pow_sq_eq_one_mk hFodd y (by rw [← hπ, hy]; exact hz2)
    exact ⟨y ^ k, hk2, hkπ.trans hy, Subgroup.npow_mem_zpowers y k⟩
  have hnotF : ∀ s : Q, π s = z → s ∉ F := fun s hs h =>
    hz1' (hs ▸ (QuotientGroup.eq_one_iff s).mpr h)
  obtain ⟨y0, hy0⟩ := QuotientGroup.mk'_surjective F z
  obtain ⟨t, ht2, htz, -⟩ := hlift y0 hy0
  refine ⟨t, ht2, hnotF t htz, htz ▸ hzZ, fun N hN hNF => ?_⟩
  have hNbar : (N.map π).Normal := hN.map _ (QuotientGroup.mk'_surjective F)
  have hzN : z ∈ N.map π := by
    rcases CFSG.GH74.GLS.LU.Local.Five.sl2_five_normal_cases e.symm (N.map π) with h | h | h
    · exfalso
      apply hNF
      intro n hn
      have hmem : π n ∈ N.map π := ⟨n, hn, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff n).mp hmem
    · rw [h]
      exact hzZ
    · rw [h]
      exact Subgroup.mem_top z
  obtain ⟨n0, hn0N, hn0z⟩ := hzN
  obtain ⟨s, hs2, hsz, hsy⟩ := hlift n0 hn0z
  have hsN : s ∈ N := (Subgroup.zpowers_le.mpr hn0N) hsy
  set K := (Subgroup.zpowers z).comap π with hK
  have hKcard : Nat.card K = Nat.card F * 2 := by
    have h := QuotientGroup.card_preimage_mk F
      ((Subgroup.zpowers z : Subgroup (Q ⧸ F)) : Set (Q ⧸ F))
    rw [SetLike.coe_sort_coe, Nat.card_zpowers, hzo] at h
    exact h
  have hfac : (Nat.card K).factorization 2 = 1 := by
    rw [hKcard, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun h => by
        obtain ⟨m, hm⟩ := hFodd
        omega), Nat.Prime.factorization_self Nat.prime_two]
  have hmemK : ∀ x : Q, π x = z → x ∈ K := fun x hx => by
    rw [hK, Subgroup.mem_comap, hx]
    exact Subgroup.mem_zpowers z
  have hcard2 : ∀ x : Q, x ^ 2 = 1 → π x = z →
      Nat.card ((Subgroup.zpowers x).subgroupOf K) = 2 ^ (Nat.card K).factorization 2 := by
    intro x hx hxz
    have hle : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr (hmemK x hxz)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hfac,
      pow_one]
    exact orderOf_eq_prime hx (fun h => hnotF x hxz (h ▸ F.one_mem))
  let St : Sylow 2 K := Sylow.ofCard _ (hcard2 t ht2 htz)
  let Ss : Sylow 2 K := Sylow.ofCard _ (hcard2 s hs2 hsz)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Ss St
  have htSt : (⟨t, hmemK t htz⟩ : K) ∈ (St : Subgroup K) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers t)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at htSt
  have h3 := Subgroup.mem_subgroupOf.mp htSt
  have heq : (((MulAut.conj g)⁻¹ • (⟨t, hmemK t htz⟩ : K) : K) : Q) = (g : Q)⁻¹ * t * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    simp
  rw [heq] at h3
  have h4 := hN.conj_mem _ ((Subgroup.zpowers_le.mpr hsN) h3) (g : Q)
  rwa [show (g : Q) * ((g : Q)⁻¹ * t * g) * (g : Q)⁻¹ = t by group] at h4

theorem centralizer_oddCore_le (hO2 : CFSG.pCore 2 Q = ⊥)
    (e : Q ⧸ CFSG.oddCore Q ≃* SL(2, ZMod 5)) :
    Subgroup.centralizer (CFSG.oddCore Q : Set Q) ≤ CFSG.oddCore Q := by
  obtain ⟨t, ht2, htF, htc, ht⟩ := exists_involution_mem_normal e
  have hFodd : Odd (Nat.card (CFSG.oddCore Q)) := Sec10.odd_card_oddCore
  by_contra hC
  have hCn : (Subgroup.centralizer (CFSG.oddCore Q : Set Q)).Normal := inferInstance
  have htC : t ∈ Subgroup.centralizer (CFSG.oddCore Q : Set Q) := ht _ hCn hC
  have hcen : ∀ g : Q, g * t * g⁻¹ = t := by
    intro g
    set x := g * t * g⁻¹ with hx
    have hxF : x * t⁻¹ ∈ CFSG.oddCore Q := by
      rw [← QuotientGroup.eq_one_iff (N := CFSG.oddCore Q)]
      change QuotientGroup.mk' (CFSG.oddCore Q) (x * t⁻¹) = 1
      have hc := Subgroup.mem_center_iff.mp htc (QuotientGroup.mk' (CFSG.oddCore Q) g)
      rw [hx, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have hft : (x * t⁻¹) * t = t * (x * t⁻¹) := Subgroup.mem_centralizer_iff.mp htC _ hxF
    have hxt : x * t = t * x := by
      have h1 : x = t * (x * t⁻¹) := by
        calc x = (x * t⁻¹) * t := by group
          _ = t * (x * t⁻¹) := hft
      calc x * t = t * (x * t⁻¹) * t := by rw [← h1]
        _ = t * x := by group
    have hx2 : x ^ 2 = 1 := by
      rw [hx, sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ← sq, ht2]
      group
    have hf2 : (x * t⁻¹) ^ 2 = 1 := by
      have hc : Commute x t⁻¹ := (Commute.inv_right (show Commute x t from hxt))
      rw [hc.mul_pow, hx2, inv_pow, ht2, one_mul, inv_one]
    have hf1 := eq_one_of_mem_of_pow_two_pow hFodd hxF (k := 1) (by simpa using hf2)
    exact mul_inv_eq_one.mp hf1
  have hTn : (Subgroup.zpowers t).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← conj_zpow, hcen g]
    exact Subgroup.zpow_mem_zpowers t k
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht2 (fun h => htF (h ▸ (CFSG.oddCore Q).one_mem))
  have hle : Subgroup.zpowers t ≤ CFSG.pCore 2 Q := le_sSup ⟨hTn, hT2⟩
  rw [hO2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact htF (hle ▸ (CFSG.oddCore Q).one_mem)

theorem exists_prime_centralizer_pCore_le (hO2 : CFSG.pCore 2 Q = ⊥)
    (e : Q ⧸ CFSG.oddCore Q ≃* SL(2, ZMod 5)) (hFfit : CFSG.oddCore Q ≤ fittingSubgroup Q) :
    ∃ p : ℕ, p.Prime ∧ Subgroup.centralizer (CFSG.pCore p Q : Set Q) ≤ CFSG.oddCore Q := by
  obtain ⟨t, -, htF, -, ht⟩ := exists_involution_mem_normal e
  by_contra h
  push Not at h
  have htp : ∀ p : ℕ, p.Prime → t ∈ Subgroup.centralizer (CFSG.pCore p Q : Set Q) :=
    fun p hp => ht _ inferInstance (h p hp)
  have hle : (⨆ p : (Nat.card Q).primeFactors, CFSG.pCore (p : ℕ) Q) ≤
      Subgroup.centralizer ({t} : Set Q) := by
    refine iSup_le fun p y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (htp p (Nat.prime_of_mem_primeFactors p.2)) y hy
  have htC : t ∈ Subgroup.centralizer (CFSG.oddCore Q : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf' := hFfit hf
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore] at hf'
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hf')
  exact htF (centralizer_oddCore_le hO2 e htC)

theorem centralizer_le_of_fixing (e : Q ⧸ CFSG.oddCore Q ≃* SL(2, ZMod 5)) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    (hCp : Subgroup.centralizer (CFSG.pCore p Q : Set Q) ≤ CFSG.oddCore Q)
    {D₀ : Subgroup (CFSG.pCore p Q)}
    (hfix : IsPGroup p (fixingSubgroup (MulAut (CFSG.pCore p Q)) (D₀ : Set (CFSG.pCore p Q))))
    (hDn : (D₀.map (CFSG.pCore p Q).subtype).Normal) :
    Subgroup.centralizer ((D₀.map (CFSG.pCore p Q).subtype : Subgroup Q) : Set Q) ≤
      CFSG.oddCore Q := by
  obtain ⟨t, ht2, htF, -, ht⟩ := exists_involution_mem_normal e
  by_contra h
  have htD := ht _ inferInstance h
  set σ : MulAut (CFSG.pCore p Q) := MulAut.conjNormal t with hσ
  have hσfix : σ ∈ fixingSubgroup (MulAut (CFSG.pCore p Q)) (D₀ : Set (CFSG.pCore p Q)) := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    apply Subtype.ext
    rw [hσ, MulAut.smul_def, MulAut.conjNormal_apply]
    have := Subgroup.mem_centralizer_iff.mp htD (d : Q) ⟨d, hd, rfl⟩
    calc t * (d : Q) * t⁻¹ = (d : Q) * t * t⁻¹ := by rw [this]
      _ = d := by group
  obtain ⟨k, hk⟩ := hfix ⟨σ, hσfix⟩
  have hσk : σ ^ p ^ k = 1 := congrArg Subtype.val hk
  have hodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have htk : t ^ p ^ k = t := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have hσ1 : σ = 1 := by
    rw [← hσk, hσ, ← map_pow, htk]
  have htC : t ∈ Subgroup.centralizer (CFSG.pCore p Q : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg (fun τ : MulAut (CFSG.pCore p Q) => ((τ ⟨x, hx⟩ : CFSG.pCore p Q) : Q)) hσ1
    simp only [hσ, MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc x * t = t * x * t⁻¹ * t := by rw [this]
      _ = t * x := by group
  exact htF (hCp htC)

end Proof152ConfA

end CFSG.RankThree.PartTwo.Sec15
