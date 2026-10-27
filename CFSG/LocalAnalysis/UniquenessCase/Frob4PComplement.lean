module

public import CFSG.LocalAnalysis.UniquenessCase.Frob4PNormalCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qzb
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem frob4P_le_normalizer_of_frobenius {p : ℕ} [Fact p.Prime] {M P₀ D : Subgroup G}
    (hP₀ : Nat.card P₀ = p) (hDM : D ≤ M) (hDT : D ⊓ pCoreOf 2 M = ⊥)
    (hV₀ : uniqueFourPrimeCore p (centralizer (P₀ : Set G)) ⊔ P₀ ≤ D)
    (hN : M ≤ normalizer ((uniqueFourPrimeCore p M ⊔ P₀ : Subgroup G) : Set G))
    (hF : uniqueFourIsFrobenius (uniqueFourPrimeCore p M ⊔ P₀) (pCoreOf 2 M)
      (uniqueFourPrimeCore p (centralizer (P₀ : Set G)) ⊔ P₀)) :
    D ≤ normalizer (P₀ : Set G) := by
  classical
  obtain ⟨hT1, hV1, hTR, hTn, hVR, hReq, hTV, hfpf⟩ := hF
  set Q : Subgroup G := uniqueFourPrimeCore p M with hQ
  set T : Subgroup G := pCoreOf 2 M with hT
  set C : Subgroup G := centralizer (P₀ : Set G) with hC
  set Q₀ : Subgroup G := uniqueFourPrimeCore p C with hQ₀
  set V₀ : Subgroup G := Q₀ ⊔ P₀ with hV₀def
  set R : Subgroup G := Q ⊔ P₀ with hR
  haveI hcyc : IsCyclic ↥P₀ := isCyclic_of_prime_card (p := p) hP₀
  have hPcomm : IsMulCommutative ↥P₀ := hcyc.isMulCommutative
  have hP₀C : P₀ ≤ C := fun x hx => mem_centralizer_iff.2 fun y hy =>
    congrArg Subtype.val (hPcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  obtain ⟨hQ₀C, hCQ₀, hcop⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p C
  have hV₀C : V₀ ≤ C := sup_le hQ₀C hP₀C
  have hP₀NQ₀ : P₀ ≤ normalizer (Q₀ : Set G) := hP₀C.trans hCQ₀
  have hQ₀comm : ∀ q ∈ Q₀, ∀ y ∈ P₀, q * y = y * q := fun q hq y hy =>
    ((mem_centralizer_iff.1 (hQ₀C hq)) y hy).symm
  have hP₀pow : ∀ y ∈ P₀, y ^ p = 1 := fun y hy =>
    orderOf_dvd_iff_pow_eq_one.mp (hP₀ ▸ Subgroup.orderOf_dvd_natCard P₀ hy)
  have hRnormT : R ≤ normalizer (T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTR).mp hTn
  have hDinfR : D ⊓ R = V₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxD, hxR⟩ := mem_inf.1 hx
      rw [hReq] at hxR
      change x ∈ (↑(T ⊔ V₀) : Set G) at hxR
      rw [Subgroup.coe_mul_of_right_le_normalizer_left T V₀ (hVR.trans hRnormT)] at hxR
      obtain ⟨t, ht, v, hv, rfl⟩ := hxR
      have hvD : v ∈ D := hV₀ hv
      have htD : t ∈ D := by
        have h1 : t = t * v * v⁻¹ := by rw [mul_inv_cancel_right]
        rw [h1]
        exact D.mul_mem hxD (D.inv_mem hvD)
      have ht1 : t = 1 := by
        have hmem : t ∈ D ⊓ T := mem_inf.2 ⟨htD, ht⟩
        rwa [hDT, mem_bot] at hmem
      simpa [ht1] using hv
    · intro x hx
      exact mem_inf.2 ⟨hV₀ hx, hVR hx⟩
  have hconjV : ∀ d ∈ D, ∀ x ∈ V₀, d * x * d⁻¹ ∈ V₀ := by
    intro d hd x hx
    have hxD : d * x * d⁻¹ ∈ D := D.mul_mem (D.mul_mem hd (hV₀ hx)) (D.inv_mem hd)
    have hxR : d * x * d⁻¹ ∈ R := by
      have hdR : d ∈ normalizer (R : Set G) := hN (hDM hd)
      exact (mem_normalizer_iff.1 hdR x).1 (hVR hx)
    have hmem : d * x * d⁻¹ ∈ D ⊓ R := mem_inf.2 ⟨hxD, hxR⟩
    exact hDinfR ▸ hmem
  have hDV₀ : D ≤ normalizer (V₀ : Set G) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro x
    exact ⟨hconjV d hd x, fun hx => by
      have h := hconjV d⁻¹ (D.inv_mem hd) (d * x * d⁻¹) hx
      simpa [mul_assoc] using h⟩
  have hVp : ∀ z ∈ V₀, z ^ p = 1 → z ∈ P₀ := by
    intro z hz hzp
    have hzR : z ∈ (↑(Q₀ ⊔ P₀) : Set G) := hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q₀ P₀ hP₀NQ₀] at hzR
    obtain ⟨q, hq, y, hy, rfl⟩ := hzR
    have hqy : Commute q y := hQ₀comm q hq y hy
    have hqpow : q ^ p = 1 := by
      rw [hqy.mul_pow, hP₀pow y hy, mul_one] at hzp
      exact hzp
    have hord : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one hqpow
    have hordQ : orderOf q ∣ Nat.card ↥Q₀ := Subgroup.orderOf_dvd_natCard Q₀ hq
    have hone : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop hord hordQ
    have hq1 : q = 1 := orderOf_eq_one_iff.mp hone
    simpa [hq1] using hy
  intro d hd
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact hVp _ (hconjV d hd y ((le_sup_right : P₀ ≤ V₀) hy)) (by
      rw [conj_pow, hP₀pow y hy, mul_one]
      exact mul_inv_cancel d)
  · intro hzP
    have hzV : d * y * d⁻¹ ∈ V₀ := (le_sup_right : P₀ ≤ V₀) hzP
    have hyV : y ∈ V₀ := by
      have h := hconjV d⁻¹ (D.inv_mem hd) (d * y * d⁻¹) hzV
      simpa [mul_assoc] using h
    apply hVp y hyV
    have hzpow : (d * y * d⁻¹) ^ p = 1 := hP₀pow _ hzP
    rw [conj_pow] at hzpow
    have h1 := congrArg (fun w => d⁻¹ * w * d) hzpow
    simpa [mul_assoc] using h1


theorem frob4P_centralizer_layer_le_normalizer (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀) (h5 : 5 ≤ p)
    (hab : IsMulCommutative P)
    (hcl : uniqueFourClauseTwo (UC6.dataOfSetup4 hS hU S).M P P₀ p) :
    centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G) ≤
      normalizer (P₀ : Set G) := by
  classical
  have hcl' := hcl
  obtain ⟨hP₀P, hcard, hwc, ⟨hf, -, -, -⟩, -, -, hfrob, -⟩ := hcl'
  haveI := hf
  have hsolv : Group.IsSolvable ↥(UC6.dataOfSetup4 hS hU S).M :=
    UC6S846.solvable_of_sigmaTwo4 hU S.maxLocal hH.mem_sig2.1 hH.mem_sig2.2
  have hN := frob4P_primeCore_sup_normal hsolv hH.sylow hab hP₀P hwc
  have hE1 := uc22p22qzb_le_centralizer_layer h5 hcl
  have hE2 := uc22p22qzb_centralizer_layer_le hS hU S hH h5 hab hcl
  have hE3 := uc22p22qzb_not_two_dvd hS hU S hH h5 hab hcl
  refine frob4P_le_normalizer_of_frobenius hcard hE2 ?_ hE1 hN hfrob
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [inf_comm]
  have hpg : IsPGroup 2 ↥(pCoreOf 2 (UC6.dataOfSetup4 hS hU S).M ⊓
      centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G)) :=
    (uc22p22qh_isPGroup_pCoreOf _).to_inf_left
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le (inf_le_right (a := pCoreOf 2 (UC6.dataOfSetup4 hS hU S).M)
    (b := centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G)))
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hk ▸ hdvd)) hE3


end CFSG.LocalAnalysis.UniquenessCase.UC22
