module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace QA19

variable {G : Type} [Group G]

theorem exists_pow_eq_mul_pow {N : Subgroup G} {n t : G} (hn : n ∈ N)
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (j : ℕ) :
    ∃ n' ∈ N, (n * t) ^ j = n' * t ^ j := by
  induction j with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨n', hn', h⟩ := ih
    have htj : t ^ j ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ ht j
    refine ⟨n' * (t ^ j * n * (t ^ j)⁻¹),
      N.mul_mem hn' ((Subgroup.mem_normalizer_iff.mp htj n).mp hn), ?_⟩
    rw [pow_succ, h]
    group

theorem oTwoUpper_le_of_le_sup {H N T : Subgroup G} (hT : IsPGroup 2 T) (hTH : T ≤ H)
    (hNH : H ≤ Subgroup.normalizer (N : Set G)) (hH : H ≤ N ⊔ T) : oTwoUpper H ≤ N := by
  apply oTwoUpper_le_of_pow_mem
  intro x hx
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := hTH.trans hNH
  have hx' : x ∈ ((N ⊔ T : Subgroup G) : Set G) := hH hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N T hTN] at hx'
  obtain ⟨n, hn, t, ht, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨n', hn', h⟩ := exists_pow_eq_mul_pow hn (hTN ht) (2 ^ k)
  exact ⟨k, by rw [h, hk', mul_one]; exact hn'⟩

theorem conj_mem_oPrimeResidualOf {p : ℕ} {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ oPrimeResidualOf p K) :
    g * x * g⁻¹ ∈ oPrimeResidualOf p K := by
  have key : oPrimeResidualOf p K ≤
      (oPrimeResidualOf p K).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨hyK, k, hk⟩ := hy
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyK, k, ?_⟩
    rw [← hk]
    exact (MulAut.conj g).orderOf_eq y
  exact key hx

theorem mem_normalizer_oPrimeResidualOf {p : ℕ} {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (oPrimeResidualOf p K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_oPrimeResidualOf hg, fun hx => ?_⟩
  have := conj_mem_oPrimeResidualOf (Subgroup.inv_mem _ hg) hx
  simpa [mul_assoc] using this

theorem oPrimeResidualOf_le {p : ℕ} (K : Subgroup G) : oPrimeResidualOf p K ≤ K :=
  (Subgroup.closure_le K).mpr fun _ hx => hx.1

theorem le_oPrimeResidualOf_of_cComp [Finite G] {K1 X : Subgroup G} (hK1 : K1 ∈ cComp X)
    (hrad : solvRad K1 ≤ pCoreOf 2 K1) (h3 : 3 ∣ Nat.card K1) :
    K1 ≤ oPrimeResidualOf 3 K1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN1 : oPrimeResidualOf 3 K1 ≤ K1 := oPrimeResidualOf_le K1
  have hnorm : (((oPrimeResidualOf 3 K1).subgroupOf K1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN1).mpr
      fun g hg => mem_normalizer_oPrimeResidualOf (Subgroup.le_normalizer hg)
  rcases normal_eq_top_or_map_le_solvRad hK1 ((oPrimeResidualOf 3 K1).subgroupOf K1) with h | h
  · exact Subgroup.subgroupOf_eq_top.mp h
  · exfalso
    rw [Subgroup.map_subgroupOf_eq_of_le hN1] at h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have hxN : (x : G) ∈ oPrimeResidualOf 3 K1 :=
      Subgroup.subset_closure ⟨x.2, 1, by simpa using hxo⟩
    have hxO : (x : G) ∈ pCoreOf 2 K1 := hrad (h hxN)
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K1) ⟨(x : G), hxO⟩
    have h1 : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : 3 ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one h1
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega

theorem oTwoUpper_le_oPrimeResidualOf_of_k1 {H K1 T : Subgroup G} (hT : IsPGroup 2 T)
    (hTH : T ≤ H) (hH : K1 ⊔ T = H)
    (h1 : K1 ≤ oPrimeResidualOf 3 (oTwoUpper H)) :
    oTwoUpper H ≤ oPrimeResidualOf 3 (oTwoUpper H) := by
  have hNH : H ≤ Subgroup.normalizer (oPrimeResidualOf 3 (oTwoUpper H) : Set G) :=
    fun g hg => mem_normalizer_oPrimeResidualOf (le_normalizer_oTwoUpper H hg)
  have hHN : H ≤ oPrimeResidualOf 3 (oTwoUpper H) ⊔ T :=
    calc H = K1 ⊔ T := hH.symm
      _ ≤ oPrimeResidualOf 3 (oTwoUpper H) ⊔ T := sup_le_sup_right h1 T
  exact oTwoUpper_le_of_le_sup hT hTH hNH hHN

end QA19

end CFSG.Quasithin
