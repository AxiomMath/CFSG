module

public import CFSG.Milestones.ASVolI.A1
import CFSG.GH74.GLS.Balance.Bender.Aux1
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ASVolI

variable {W : Type} [Group W] [Finite W]

theorem uc22s21rh_le_of_coprime_elements {q : ℕ} [Fact q.Prime] {K : Subgroup W}
    (hK : ⁅K, K⁆ = K) {C : Subgroup W} (hC : ∀ k ∈ K, (orderOf k).Coprime q → k ∈ C) :
    K ≤ C := by
  haveI : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  have htop : CFSG.GH74.GLS.oResidual q ↥K = ⊤ :=
    CFSG.GH74.GLS.Balance.BenderExt.oResidual_eq_top_of_isPerfect inferInstance
  have hle : CFSG.GH74.GLS.oResidual q ↥K ≤ C.subgroupOf K := by
    refine (Subgroup.closure_le _).mpr fun k hk => ?_
    exact hC k k.2 (by simpa [Subgroup.orderOf_coe] using hk)
  rw [htop] at hle
  intro k hk
  exact hle (Subgroup.mem_top ⟨k, hk⟩)

theorem uc22s21rh_comm_of_cyclic {K X : Subgroup W} [X.Normal] (hK : ⁅K, K⁆ = K)
    (hX : IsCyclic X) (k : W) (hk : k ∈ K) (x : W) (hx : x ∈ X) : k * x * k⁻¹ = x := by
  haveI : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  haveI := hX
  let κ : ↥K →* MulAut ↥X := (MulAut.conjNormal (H := X)).comp K.subtype
  have h1 := uc22s21rk_map_eq_one_of_perfect
    ((IsCyclic.mulAutMulEquiv (G := ↥X)).toMonoidHom.comp κ) ⟨k, hk⟩
  have h2 : κ ⟨k, hk⟩ = 1 := by
    simpa using (IsCyclic.mulAutMulEquiv (G := ↥X)).injective
      ((by simpa using h1 : IsCyclic.mulAutMulEquiv (G := ↥X) (κ ⟨k, hk⟩) = 1).trans
        (map_one _).symm)
  have h3 := congrArg (fun a : MulAut ↥X => ((a ⟨x, hx⟩ : ↥X) : W)) h2
  simpa [κ] using h3

theorem uc22s21rh_exists_supercritical {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {P : Subgroup W}
    [P.Normal] (hP : IsPGroup q P) {K : Subgroup W} (hK : ⁅K, K⁆ = K)
    (hKP : ¬ K ≤ Subgroup.centralizer (P : Set W)) :
    ∃ X : Subgroup W, X ≤ P ∧ X.Normal ∧ (ChA.frattiniOf X).Normal ∧ (∀ x ∈ X, x ^ q = 1) ∧
      ⁅⁅X, X⁆, X⁆ = ⊥ ∧ (∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ ChA.frattiniOf X) ∧
      ¬ IsCyclic X := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨⟨X, hXsc, hfaith⟩, hall⟩ := as_A_1_21 W q hq hq2 P hP
  obtain ⟨hcl, -, -⟩ := hall X hXsc
  obtain ⟨hXP, hchar, -, -, hexp, -⟩ := hXsc
  haveI hXn : X.Normal := by
    have := ConjAct.normal_of_characteristic_of_normal (H := P) (K := X.subgroupOf P)
    rwa [Subgroup.map_subgroupOf_eq_of_le hXP] at this
  haveI hfn : (ChA.frattiniOf X).Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := X) (K := frattini ↥X)
  have hnt : ∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ ChA.frattiniOf X := by
    by_contra htriv
    push Not at htriv
    apply hKP
    refine uc22s21rh_le_of_coprime_elements (q := q) hK fun k hk hcop => ?_
    have hα : (MulAut.conjNormal k : MulAut ↥P) = 1 := by
      refine hfaith _ (Nat.Coprime.coprime_dvd_left
        (orderOf_map_dvd (MulAut.conjNormal (H := P)) k) hcop) ?_
      intro x hx
      simpa using htriv k hk x hx
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 := congrArg (fun a : MulAut ↥P => ((a ⟨p, hp⟩ : ↥P) : W)) hα
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  refine ⟨X, hXP, hXn, hfn, hexp, hcl, hnt, fun hcyc => ?_⟩
  obtain ⟨k, hk, x, hx, hne⟩ := hnt
  exact hne (by rw [uc22s21rh_comm_of_cyclic hK hcyc k hk x hx]; simp)

theorem uc22s21rh_exists_prime_not_centralizing {K : Subgroup W} (h2 : CFSG.pCore 2 W = ⊥)
    (hKF : ¬ K ≤ Subgroup.centralizer (CFSG.fittingSubgroup W : Set W)) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ¬ K ≤ Subgroup.centralizer (CFSG.pCore q W : Set W) := by
  by_contra hall
  push Not at hall
  apply hKF
  have hle : CFSG.fittingSubgroup W ≤ Subgroup.centralizer (K : Set W) := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => ?_
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    by_cases hp2 : (p : ℕ) = 2
    · rw [hp2, h2]
      exact bot_le
    · intro x hx k hk
      have := hall p hp hp2 hk x hx
      exact this.symm
  intro k hk x hx
  exact (hle hx k hk).symm

theorem uc22s21rh_exists_supercritical_of_fitting (h2 : CFSG.pCore 2 W = ⊥) {K : Subgroup W}
    (hK : ⁅K, K⁆ = K) (hKF : ¬ K ≤ Subgroup.centralizer (CFSG.fittingSubgroup W : Set W)) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ X : Subgroup W, X ≤ CFSG.pCore q W ∧ X.Normal ∧
      (ChA.frattiniOf X).Normal ∧ (∀ x ∈ X, x ^ q = 1) ∧ ⁅⁅X, X⁆, X⁆ = ⊥ ∧
      (∃ k ∈ K, ∃ x ∈ X, k * x * k⁻¹ * x⁻¹ ∉ ChA.frattiniOf X) ∧ ¬ IsCyclic X := by
  obtain ⟨q, hq, hq2, hKq⟩ := uc22s21rh_exists_prime_not_centralizing h2 hKF
  exact ⟨q, hq, hq2, uc22s21rh_exists_supercritical hq hq2 CFSG.pCore_isPGroup hK hKq⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
