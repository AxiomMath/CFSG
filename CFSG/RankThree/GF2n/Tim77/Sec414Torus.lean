module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderCount

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  conj_mem_sylowCenter normalizer_transitive_center benderBorel_sylowCenter)

theorem sec414tor_lift {U K : Type} [Group U] [Finite U] [Group K] (π : U →* K)
    (hπ : Function.Surjective π) (T : Subgroup U) (hT : IsPGroup 2 T)
    (hTmax : ∀ T' : Subgroup U, IsPGroup 2 T' → T ≤ T' → T' = T) {δ : K}
    (hδ : δ ∈ Subgroup.normalizer ((T.map π : Subgroup K) : Set K)) :
    ∃ n ∈ Subgroup.normalizer (T : Set U), π n = δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T0 : Sylow 2 U := ⟨T, hT, fun {Q} hQ hle => hTmax Q hQ hle⟩
  obtain ⟨u, hu⟩ := hπ δ
  let P : Subgroup U := (T.map π).comap π
  have hTP : (T0 : Subgroup U) ≤ P := Subgroup.le_comap_map π T
  have hT1P : ((u • T0 : Sylow 2 U) : Subgroup U) ≤ P := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [Subgroup.mem_comap]
    have h1 : π (MulAut.conj u • t) = δ * π t * δ⁻¹ := by
      simp [MulAut.smul_def, hu]
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp hδ (π t)).mp (Subgroup.mem_map_of_mem π ht)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq P ((u • T0).subtype hT1P) (T0.subtype hTP)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hh
  have hn : (h : U) * u ∈ Subgroup.normalizer (T : Set U) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh)
  have hhP : π (h : U) ∈ T.map π := Subgroup.mem_comap.mp h.2
  obtain ⟨s, hs, hsπ⟩ := Subgroup.mem_map.mp hhP
  refine ⟨s⁻¹ * ((h : U) * u), Subgroup.mul_mem _ (Subgroup.inv_mem _
    (Subgroup.le_normalizer hs)) hn, ?_⟩
  rw [map_mul, map_mul, map_inv, hsπ, hu, inv_mul_cancel_left]

theorem sec414tor_torus {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (S : Sylow 2 K) :
    ∃ δ : K, δ ∈ Subgroup.normalizer ((S : Subgroup K) : Set K) ∧ Odd (orderOf δ) ∧
      4 ≤ Nat.card (sylowCenter (S : Subgroup K)) ∧
      ∀ z ∈ sylowCenter (S : Subgroup K), z ≠ 1 →
        ∀ z' ∈ sylowCenter (S : Subgroup K), z' ≠ 1 →
          ∃ i : ℕ, δ ^ i * z * (δ ^ i)⁻¹ = z' := by
  classical
  obtain ⟨q, k, hB, hq4, -⟩ :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_fusionBenderBorel hK
  obtain ⟨hSE, hZ2, hZcard, -⟩ := benderBorel_sylowCenter hB S
  obtain ⟨-, ⟨D, hDcyc, hDodd, -, hsupN⟩, -⟩ := hB S
  haveI := hDcyc
  obtain ⟨δ, hδ⟩ := IsCyclic.exists_generator (α := ↥D)
  have hDN : D ≤ Subgroup.normalizer ((S : Subgroup K) : Set K) := by
    rw [← hsupN]
    exact le_sup_right
  refine ⟨(δ : K), hDN δ.2, ?_, by rw [hZcard]; exact hq4, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hDodd (orderOf_dvd_natCard δ)
  · intro z hz hz1 z' hz' hz'1
    obtain ⟨n, hn, hnz⟩ := normalizer_transitive_center hSE hZ2 hz hz' hz1 hz'1
    have hm : n⁻¹ ∈ Subgroup.normalizer ((S : Subgroup K) : Set K) := Subgroup.inv_mem _ hn
    have hsupS : ((S : Subgroup K).subgroupOf
          (Subgroup.normalizer ((S : Subgroup K) : Set K))) ⊔
        (D.subgroupOf (Subgroup.normalizer ((S : Subgroup K) : Set K))) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup Subgroup.le_normalizer hDN, hsupN, Subgroup.subgroupOf_self]
    have hmem : (⟨n⁻¹, hm⟩ : ↥(Subgroup.normalizer ((S : Subgroup K) : Set K))) ∈
        ((S : Subgroup K).subgroupOf (Subgroup.normalizer ((S : Subgroup K) : Set K))) ⊔
          (D.subgroupOf (Subgroup.normalizer ((S : Subgroup K) : Set K))) := by
      rw [hsupS]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, d, hd, hsd⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hsK : (s : K) ∈ (S : Subgroup K) := hs
    have hdD : (d : K) ∈ D := hd
    have hnd : n⁻¹ = (s : K) * (d : K) := by
      simpa using (congrArg Subtype.val hsd).symm
    have hdz : (d : K) * z * (d : K)⁻¹ ∈ sylowCenter (S : Subgroup K) := by
      have := conj_mem_sylowCenter (Subgroup.inv_mem _ (hDN hdD)) hz
      simpa using this
    have hn' : n = ((s : K) * (d : K))⁻¹ := inv_eq_iff_eq_inv.mp hnd
    have h1 : z' = (s : K) * ((d : K) * z * (d : K)⁻¹) * (s : K)⁻¹ := by
      rw [← hnz, hnd, hn']
      group
    have hc := (mem_sylowCenter.mp hdz).2 (s : K) hsK
    have hzz' : (d : K) * z * (d : K)⁻¹ = z' := by
      rw [h1, hc, mul_inv_cancel_right]
    have hdmem : (⟨(d : K), hdD⟩ : ↥D) ∈ Submonoid.powers δ :=
      mem_powers_iff_mem_zpowers.mpr (hδ _)
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff (⟨(d : K), hdD⟩ : ↥D) δ).mp hdmem
    refine ⟨i, ?_⟩
    have hiK : (δ : K) ^ i = d := congrArg Subtype.val hi
    rw [hiK]
    exact hzz'

theorem sec414_exists_torus {U K : Type} [Group U] [Finite U] [Group K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (π : U →* K) (hπ : Function.Surjective π)
    (T : Subgroup U) (hT : IsPGroup 2 T)
    (hTmax : ∀ T' : Subgroup U, IsPGroup 2 T' → T ≤ T' → T' = T) :
    ∃ n : U, n ∈ Subgroup.normalizer (T : Set U) ∧ Odd (orderOf n) ∧
      4 ≤ Nat.card
        (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T.map π)) ∧
      ∀ z ∈ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T.map π),
        z ≠ 1 →
        ∀ z' ∈ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T.map π),
          z' ≠ 1 → ∃ i : ℕ, π n ^ i * z * (π n ^ i)⁻¹ = z' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := Finite.of_surjective π hπ
  obtain ⟨S, hS⟩ : ∃ S : Sylow 2 K, (S : Subgroup K) = T.map π :=
    ⟨Sylow.mapSurjective hπ (⟨T, hT, fun {Q} hQ hle => hTmax Q hQ hle⟩ : Sylow 2 U), rfl⟩
  obtain ⟨δ, hδN, hδodd, hcard, htrans⟩ := sec414tor_torus hK S
  rw [hS] at hδN hcard htrans
  obtain ⟨n₂, hn₂N, hn₂π⟩ := sec414tor_lift π hπ T hT hTmax hδN
  obtain ⟨a, r, hr, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n₂).ne'
  refine ⟨n₂ ^ (2 ^ a), Subgroup.pow_mem _ hn₂N _, ?_, hcard, ?_⟩
  · rw [orderOf_pow_of_dvd (by positivity) ⟨r, hord⟩, hord,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hr
  · intro z hz hz1 z' hz' hz'1
    obtain ⟨i, hi⟩ := htrans z hz hz1 z' hz' hz'1
    have hcop : Nat.Coprime (2 ^ a) (orderOf δ) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hδodd)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    refine ⟨m * i, ?_⟩
    rw [map_pow, hn₂π, pow_mul, hm]
    exact hi

end CFSG.RankThree.GF2n.Tim77
