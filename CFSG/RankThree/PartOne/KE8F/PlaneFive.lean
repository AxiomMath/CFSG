module

public import CFSG.RankThree.PartOne.KE8F.Stab5
public import CFSG.RankThree.PartOne.KE8F.Toral5
public import CFSG.RankThree.PartOne.KE8F.HV
public import CFSG.RankThree.PartOne.KE8F.PlaneOddRad
public import CFSG.RankThree.PartOne.KE.NativeCyclicLocalCore
public import CFSG.RankThree.PartOne.KE.OrdinaryEOuter
public import CFSG.RankThree.PartOne.KE.NativeCyclicEndpoint

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE (ordinary_E_outer_derived_subgroup_odd localCoreTrivialOn_noninner_E
  OddEndpoint cycloVal oddEndpoint_E8_of_native twistedTorusOf)

set_option linter.unusedSectionVars false


theorem odd_of_dvd_sq_add_one {f : ℕ} (h : 5 ∣ 2 ^ f * 2 ^ f + 1) : Odd f := by
  by_contra hf
  rw [Nat.not_odd_iff_even] at hf
  obtain ⟨k, hk⟩ := hf
  have h1 : 2 ^ f * 2 ^ f + 1 = 16 ^ k + 1 := by
    rw [hk, ← pow_add, show k + k + (k + k) = 4 * k by ring, pow_mul]
    norm_num
  rw [h1] at h
  have h2 : (16 ^ k + 1) % 5 = 2 := by
    rw [Nat.add_mod, Nat.pow_mod]
    norm_num
  omega

theorem planeLocalCoreOdd_E8_phi4_five
    (hC1 : Phi4FiveToral) (K : Type) [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (h5 : 5 ∣ Nat.card K * Nat.card K + 1) :
    PlaneLocalCoreOdd 5 (adjointGroup .E8 K) := by
  classical
  have hℓ : Nat.Prime 2 := Nat.prime_two
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨F, hC1F⟩ := hC1 K f hf hK h5 L
  have hfodd : Odd f := odd_of_dvd_sq_add_one (by rwa [hK] at h5)
  have hout : Odd (Nat.card (Outer (adjointGroup .E8 K))) := by
    have hd := (CFSG.LieType.Chevalley.ordinary_E_outer_order_Cartan_divisor .E8
      (Or.inr (Or.inr rfl)) hℓ hf K hK 1 1 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))).1
    exact Odd.of_dvd_nat hfodd (by simpa using hd)
  have hcore := localCoreTrivialOn_noninner_E .E8 (Or.inr (Or.inr rfl)) K hp5 (by norm_num)
  have hFr : ∀ c : L, iterateFrobenius L 2 f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def 2 f c
  have hgen : StabGen L (iterateFrobenius L 2 f) 5 :=
    stabGen_five hFr h5 (by norm_num)
  refine planeLocalCoreOdd_of_odd_radicals hp5 center_adjointGroup_eq_bot ?_ hout hcore
  intro x hx V hVn hVs hVp
  have hxp : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨c, hc⟩ := hC1F x hx
  have hxpow : ∀ y ∈ Subgroup.zpowers x, y ^ 5 = 1 := by
    rintro y ⟨k, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hxp,
      _root_.one_zpow]
  have hxT : ∀ y ∈ Subgroup.zpowers x, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L 2 f))) := by
    rintro y ⟨k, rfl⟩
    rw [map_zpow]
    refine zpow_mem ?_ k
    rw [psiC_apply]
    exact hc
  obtain ⟨hQA, hcard⟩ := exists_torusData_of_toral F hf hK hp5 (by norm_num) h5 hxpow c hxT
  exact hV_odd_of_toral F rfl hf hK hp5 (by norm_num) hgen h5 c (hQA (Subgroup.mem_zpowers x))
    hcard V hVn hVs hVp

theorem oddEndpoint_E8_phi4_five
    (hC1 : Phi4FiveToral) :
    OddEndpoint .E8 fun p ℓ f => p = 5 ∧ ℓ = 2 ∧ (p : ℤ) ∣ cycloVal 4 ℓ f := by
  refine oddEndpoint_E8_of_native ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  obtain ⟨rfl, rfl, hpc⟩ := hc
  have hpf : 5 ∣ Nat.card K * Nat.card K + 1 := by
    have h : (5 : ℤ) ∣ ((Nat.card K : ℤ) * (Nat.card K : ℤ) + 1) := by
      have h1 : (5 : ℤ) ∣ (exhaustionPhi 4).eval (Nat.card K : ℤ) := by
        simpa [cycloVal, hK] using hpc
      have e4 : (exhaustionPhi 4).eval (Nat.card K : ℤ) = (Nat.card K : ℤ) ^ 2 + 1 := by
        simp only [exhaustionPhi, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one]
      rw [e4] at h1
      simpa [sq] using h1
    exact_mod_cast h
  exact planeLocalCoreOdd_E8_phi4_five hC1 K hf hK hpf

end CFSG.RankThree.PartOne.KE8F
