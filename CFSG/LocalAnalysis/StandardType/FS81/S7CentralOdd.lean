module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
public import Mathlib.GroupTheory.Sylow
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.StandardType.FS81.S7CentralHall

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.QuasithinUnique

open CFSG.LieType.BorelTits

private theorem pow_two_eq_one_of_mem_odd {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hNodd : ¬ 2 ∣ Nat.card N) :
    ∀ n ∈ N, n ^ 2 = 1 → n = 1 := by
  intro n hn hn2
  have h2 : orderOf n ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hn2
  have hcard : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
  have hcop : Nat.Coprime 2 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hNodd
  have h1 : orderOf n ∣ 1 := by
    have h := Nat.dvd_gcd h2 hcard
    rwa [Nat.coprime_iff_gcd_eq_one.mp hcop] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem charTwoMod_of_central_odd {G : Type} [Group G] [Finite G] (H N : Subgroup G)
    [(N.subgroupOf H).Normal] (hNH : N ≤ H) (hNc : ∀ n ∈ N, ∀ h ∈ H, h * n = n * h)
    (hNodd : ¬ 2 ∣ Nat.card N) {x : G} (hxH : x ∈ H) (hx : orderOf x = 2) {P : Subgroup G}
    (hP : pCoreOf 2 (H ⊓ Subgroup.centralizer ({x} : Set G)) = P)
    (hC : ∀ y ∈ H, y * x = x * y → (∀ p ∈ P, y * p = p * y) → y ∈ P ⊔ N) :
    CharTwoMod H N ⟨x, hxH⟩ := by
  let Q := ↥H ⧸ N.subgroupOf H
  let π : ↥H →* Q := QuotientGroup.mk' (N.subgroupOf H)
  let xH : ↥H := ⟨x, hxH⟩
  let C : Subgroup Q := Subgroup.centralizer ({π xH} : Set Q)
  change CharTwo C
  have hx2 : x ^ 2 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  have hx2' : x * x = 1 := by simpa [pow_two] using hx2
  have hno2 : ∀ n ∈ N, n ^ 2 = 1 → n = 1 := pow_two_eq_one_of_mem_odd hNodd
  have hPX : P ≤ H ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [← hP]; exact pCoreOf_le (r := 2) _
  have hPH : P ≤ H := hPX.trans inf_le_left
  have hP2 : IsPGroup 2 P := by rw [← hP]; exact pCoreOf_isPGroup 2 _
  have hnorm : H ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (P : Set G) := by
    rw [← hP]; exact le_normalizer_pCoreOf 2 _
  have hmem_iff : ∀ y : ↥H, π y ∈ C → (y : G) * x = x * (y : G) := by
    intro y hy
    have hcomm : π xH * π y = π y * π xH :=
      (Subgroup.mem_centralizer_iff.mp hy) (π xH) (by simp)
    have hker : π (y * xH * y⁻¹ * xH⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm.symm]
      group
    have hnN : (y : G) * x * (y : G)⁻¹ * x⁻¹ ∈ N := by
      have hmem :=
        (QuotientGroup.eq_one_iff (N := N.subgroupOf H) (y * xH * y⁻¹ * xH⁻¹)).mp hker
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa [xH] using hmem
    let n : G := (y : G) * x * (y : G)⁻¹ * x⁻¹
    have hnx : (y : G) * x * (y : G)⁻¹ = n * x := by
      simp only [n]; group
    have hxn : x * n = n * x := hNc n hnN x hxH
    have hsq1 : ((y : G) * x * (y : G)⁻¹) ^ 2 = 1 := by
      have h : ((y : G) * x * (y : G)⁻¹) ^ 2 =
          (y : G) * x ^ 2 * (y : G)⁻¹ := by
        rw [pow_two, pow_two]; group
      rw [h, hx2, mul_one, mul_inv_cancel]
    have hn2 : n ^ 2 = 1 := by
      have h1 : ((y : G) * x * (y : G)⁻¹) ^ 2 = (n * x) ^ 2 := by rw [hnx]
      rw [hsq1] at h1
      have h2 : (n * x) ^ 2 = n ^ 2 := by
        calc (n * x) ^ 2 = n * (x * n) * x := by rw [pow_two]; group
          _ = n * (n * x) * x := by rw [hxn]
          _ = (n * n) * (x * x) := by group
          _ = n ^ 2 := by rw [hx2', mul_one, pow_two]
      rw [h2] at h1
      exact h1.symm
    have hn1 : n = 1 := hno2 n hnN hn2
    have hconj : (y : G) * x * (y : G)⁻¹ = x := by
      rw [hnx, hn1, one_mul]
    calc (y : G) * x = (y : G) * x * (y : G)⁻¹ * (y : G) := by group
      _ = x * (y : G) := by rw [hconj]
  have hPsub : IsPGroup 2 (P.subgroupOf H) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  let Pq : Subgroup Q := (P.subgroupOf H).map π
  have hPqP : IsPGroup 2 Pq := hPsub.map π
  have hPq_le_C : Pq ≤ C := by
    intro p hp
    rw [Subgroup.mem_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    rw [Subgroup.mem_subgroupOf] at hp'
    change π p' ∈ Subgroup.centralizer ({π xH} : Set Q)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hcomm : (p' : G) * x = x * (p' : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPX hp').2
    have hcommH : xH * p' = p' * xH := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, xH]
      exact hcomm.symm
    exact (map_mul π xH p').symm.trans ((congrArg π hcommH).trans (map_mul π p' xH))
  have hPq_normal : (Pq.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Q) ∈ Pq := Subgroup.mem_subgroupOf.mp hn
    rw [Subgroup.mem_map] at hn'
    obtain ⟨p, hp, hp_eq⟩ := hn'
    rw [Subgroup.mem_subgroupOf] at hp
    obtain ⟨y, hyπ⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) (g : Q)
    have hyC : π y ∈ C := by rw [hyπ]; exact g.2
    have hyx : (y : G) * x = x * (y : G) := hmem_iff y hyC
    have hyX : (y : G) ∈ H ⊓ Subgroup.centralizer ({x} : Set G) :=
      ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyx⟩
    have hyN : (y : G) ∈ Subgroup.normalizer (P : Set G) := hnorm hyX
    have hyp : (y : G) * (p : G) * (y : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hyN (p : G)).mp hp
    show (g : Q) * (n : Q) * (g : Q)⁻¹ ∈ Pq
    rw [← hyπ, ← hp_eq, ← map_inv]
    rw [← map_mul, ← map_mul]
    exact Subgroup.mem_map.mpr ⟨y * p * y⁻¹, by
      rw [Subgroup.mem_subgroupOf]
      simpa using hyp, rfl⟩
  have hPq_le_pcore : Pq ≤ pCoreOf 2 C :=
    le_pCoreOf (r := 2) hPq_le_C hPq_normal hPqP
  intro c hc
  have hcC : c ∈ C := hc.1
  have hccent : c ∈ Subgroup.centralizer (pCoreOf 2 C : Set Q) := hc.2
  obtain ⟨y, hyπ⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) c
  have hyC : π y ∈ C := by rw [hyπ]; exact hcC
  have hyx : (y : G) * x = x * (y : G) := hmem_iff y hyC
  have hcommP : ∀ p ∈ P, (y : G) * p = p * (y : G) := by
    intro p hpP
    have hpX : p ∈ H ⊓ Subgroup.centralizer ({x} : Set G) := hPX hpP
    let pH : ↥H := ⟨p, hpX.1⟩
    have hπpH : π pH ∈ pCoreOf 2 C := by
      apply hPq_le_pcore
      exact Subgroup.mem_map.mpr
        ⟨pH, by rw [Subgroup.mem_subgroupOf]; exact hpP, rfl⟩
    have hcommc : π pH * c = c * π pH :=
      (Subgroup.mem_centralizer_iff.mp hccent) (π pH) hπpH
    let m : G := (y : G) * p * (y : G)⁻¹ * p⁻¹
    have hmN : m ∈ N := by
      have hker : π (y * pH * y⁻¹ * pH⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv]
        rw [hyπ]
        rw [hcommc.symm]
        group
      have hmem :=
        (QuotientGroup.eq_one_iff (N := N.subgroupOf H) (y * pH * y⁻¹ * pH⁻¹)).mp hker
      rw [Subgroup.mem_subgroupOf] at hmem
      simpa [m, pH] using hmem
    have hmP : m ∈ P := by
      have hyX : (y : G) ∈ H ⊓ Subgroup.centralizer ({x} : Set G) :=
        ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyx⟩
      have hyN : (y : G) ∈ Subgroup.normalizer (P : Set G) := hnorm hyX
      have hyp : (y : G) * p * (y : G)⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hyN p).mp hpP
      simp only [m]
      exact Subgroup.mul_mem P hyp (Subgroup.inv_mem P hpP)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2) (G := P)).mp hP2 ⟨m, hmP⟩
    have hord : orderOf m = 2 ^ k := by simpa using hk
    have hdvd : orderOf m ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmN
    have hk0 : k = 0 := by
      by_contra hkne
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkne
      have h2dvd : 2 ∣ 2 ^ k := by
        have h := pow_dvd_pow 2 hk1
        simpa using h
      exact hNodd (dvd_trans (by rw [hord]; exact h2dvd) hdvd)
    have hm1 : m = 1 := by
      have h : orderOf m = 1 := by rw [hord, hk0, pow_zero]
      exact orderOf_eq_one_iff.mp h
    have hconjP : (y : G) * p * (y : G)⁻¹ = p := by
      have h : (y : G) * p * (y : G)⁻¹ = m * p := by simp only [m]; group
      rw [h, hm1, one_mul]
    calc (y : G) * p = (y : G) * p * (y : G)⁻¹ * (y : G) := by group
      _ = p * (y : G) := by rw [hconjP]
  have hy_sup : (y : G) ∈ P ⊔ N := hC (y : G) y.2 hyx hcommP
  have hsupH : y ∈ (P.subgroupOf H) ⊔ (N.subgroupOf H) := by
    rw [← Subgroup.subgroupOf_sup hPH hNH, Subgroup.mem_subgroupOf]
    exact hy_sup
  rw [Subgroup.mem_sup_of_normal_right] at hsupH
  obtain ⟨p', hp', n', hn', hy_eq⟩ := hsupH
  rw [Subgroup.mem_subgroupOf] at hp'
  have hn'_one : π n' = 1 :=
    (QuotientGroup.eq_one_iff (N := N.subgroupOf H) n').mpr hn'
  have hc_eq : c = π p' := by
    rw [← hyπ, ← hy_eq, map_mul, hn'_one, mul_one]
  exact hPq_le_pcore (by
    rw [hc_eq]
    exact Subgroup.mem_map.mpr
      ⟨p', by rw [Subgroup.mem_subgroupOf]; exact hp', rfl⟩)

theorem exists_normalComplement_of_central_three {G : Type} [Group G] [Finite G] {Z : Subgroup G}
    {β : G} (hβZ : β ∈ Z) (hβ : orderOf β = 3) (hβc : ∀ z ∈ Z, z * β = β * z)
    (hS : ∀ T : Subgroup G, T ≤ Z → IsPGroup 3 T → Nat.card T ≤ 3) :
    ∃ K : Subgroup G, K ≤ Z ∧ (K.subgroupOf Z).Normal ∧ ¬ 3 ∣ Nat.card K ∧
      Z ≤ Subgroup.zpowers β ⊔ K ∧ ∀ z ∈ Z, z ∈ K ↔ ¬ 3 ∣ orderOf z := by
  set N : Subgroup G := Subgroup.zpowers β with hNdef
  have hNZ : N ≤ Z := by rw [hNdef]; exact Subgroup.zpowers_le.mpr hβZ
  have hNcard : Nat.card N = 3 := by rw [hNdef, Nat.card_zpowers, hβ]
  have hNcentral : N ≤ Subgroup.centralizer (Z : Set G) := by
    rw [hNdef, Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr hβc
  have hNcZ : ∀ n ∈ N, ∀ g ∈ Z, g * n = n * g := by
    intro n hn g hg
    exact (Subgroup.mem_centralizer_iff.mp (hNcentral hn)) g hg
  have hNp : IsPGroup 3 N :=
    IsPGroup.of_card (n := 1) (by rw [hNcard, pow_one])
  have hNsub : IsPGroup 3 (N.subgroupOf Z) :=
    hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNZ).symm
  obtain ⟨Q, _hNQ⟩ := hNsub.exists_le_sylow
  have hZne : Nat.card Z ≠ 0 := (Nat.card_pos (α := Z)).ne'
  have h3dvd : 3 ∣ Nat.card Z := by
    have h := Subgroup.orderOf_dvd_natCard Z hβZ
    rwa [hβ] at h
  let e : ℕ := (Nat.card Z).factorization 3
  have hQle3 : Nat.card Q ≤ 3 := by
    have hTle : Q.toSubgroup.map Z.subtype ≤ Z := by
      intro t ht
      rcases Subgroup.mem_map.mp ht with ⟨q, _hq, rfl⟩
      exact q.2
    have hTp : IsPGroup 3 (Q.toSubgroup.map Z.subtype) := Q.isPGroup'.map Z.subtype
    have hcardT : Nat.card (Q.toSubgroup.map Z.subtype) = Nat.card Q.toSubgroup :=
      Subgroup.card_map_of_injective (K := Q.toSubgroup) Subtype.coe_injective
    have h := hS (Q.toSubgroup.map Z.subtype) hTle hTp
    rw [hcardT] at h
    exact h
  have hQcard : Nat.card Q.toSubgroup = 3 ^ e := by
    have h := Sylow.card_eq_multiplicity (p := 3) Q
    simpa [e] using h
  have he_le : e ≤ 1 := by
    have h : 3 ^ e ≤ 3 ^ 1 := by
      have h' : 3 ^ e ≤ 3 := by rw [← hQcard]; exact hQle3
      simpa using h'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have he_ge : 1 ≤ e := by
    have h := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hZne).mp h3dvd
    simpa [e] using h
  have he : e = 1 := le_antisymm he_le he_ge
  let m : ℕ := ordCompl[3] (Nat.card Z)
  have hmul : 3 ^ e * m = Nat.card Z := Nat.ordProj_mul_ordCompl_eq_self (Nat.card Z) 3
  have hm : Nat.card Z = Nat.card N * m := by
    rw [hNcard]
    have h : 3 * m = Nat.card Z := by
      rw [he, pow_one] at hmul
      exact hmul
    exact h.symm
  have hcop : Nat.Coprime (Nat.card N) m := by
    rw [hNcard]
    exact Nat.coprime_ordCompl Nat.prime_three hZne
  obtain ⟨K, hKle, hKnorm, hKcard, hKsup, hKmem⟩ :=
    exists_normal_complement_of_central_hall (X := G) (M := Z) (N := N) hNZ hNcZ hm hcop
  have hcop3 : Nat.Coprime 3 m := by rwa [hNcard] at hcop
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop3
  refine ⟨K, hKle, hKnorm, h3K, ?_, ?_⟩
  · rw [sup_comm]
    exact hKsup
  · intro z hz
    have h := hKmem z hz
    rw [hNcard] at h
    rw [h, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]

end CFSG.StandardType.FrameRoute.FS81

end
