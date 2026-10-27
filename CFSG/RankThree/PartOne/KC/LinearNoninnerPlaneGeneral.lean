module

public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneInner
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.KCLinComm

namespace KCLinPlane

theorem noninner_plane_data {p ℓ f n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime)
    (hℓp : ℓ ≠ p) (hf : 1 ≤ f) (hn : 3 ≤ n) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f)
    (hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)))
    (B : Subgroup (MulAut (projectiveSL n K)))
    (A : Subgroup (MulAut (projectiveSL n K))) (hAB : A ≤ B) [IsElementaryAbelian p A]
    (hAcard : Nat.card A = p ^ 2) (hAH : ¬ A ≤ innSL n K)
    (hcore : ∀ a : MulAut (projectiveSL n K), a ∈ B → a ∈ semilinearAutGroup n K →
      a ∉ linearAutGroup n K → orderOf a = p →
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (projectiveSL n K)))) = ⊥)
    (hodd : 3 < ℓ ^ f → ∀ t ∈ innSL n K, orderOf t = p →
      ∀ A' : Subgroup (MulAut (projectiveSL n K)), A' ≤ B ⊓ Subgroup.centralizer {t} →
        IsPGroup p A' →
        Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer {t}), A'⁆ : Subgroup (MulAut (projectiveSL n K))))) :
    Nat.card (A ⊓ innSL n K : Subgroup (MulAut (projectiveSL n K))) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧ 3 < ℓ ^ f ∧
      (∀ a ∈ A, a ∉ innSL n K →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      ∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧ ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ innSL n K → autPlaneProduct p B A t = ⊥) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hCharP : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hpA : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hAE : A ≤ (semilinPsi n K).range := fun α hα => by
    rw [range_semilinPsi]
    exact KCLinCommOdd.mem_semilinearAutGroup_of_pow_eq_one hn hp2 hp (j := 1)
      (by simpa using hpA α hα)
  have hcyc : IsCyclic (K ≃+* K) := by
    obtain ⟨σ, -, -, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, htop⟩
  have hAcap := card_inf_inner_eq_prime hn hp hcop hcyc hAE hAcard hAH
  obtain ⟨a0, ha0A, ha0H⟩ := IsConcreteLE.not_le_iff_exists.mp hAH
  have ha01 : a0 ≠ 1 := fun h => ha0H (h ▸ one_mem _)
  have ha0ord : orderOf a0 = p := orderOf_eq_prime (hpA a0 ha0A) ha01
  have hnotD : ∀ a ∈ A, a ∉ innSL n K → a ∉ linearAutGroup n K := fun a ha haH haD =>
    haH (inner_of_mem_linearAut_of_pow_eq_one hn hcop haD (hpA a ha))
  have hcoreA : ∀ a ∈ A, a ∉ innSL n K →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
    intro a haA haH
    have ha1 : a ≠ 1 := fun h => haH (h ▸ one_mem _)
    exact hcore a (hAB haA) (by rw [← range_semilinPsi]; exact hAE haA) (hnotD a haA haH)
      (orderOf_eq_prime (hpA a haA) ha1)
  have hpf : p ∣ f := by
    obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
      CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
    exact (hdesc p hp hℓp.symm a0 (by rw [← range_semilinPsi]; exact hAE ha0A)
      (hnotD a0 ha0A ha0H) ha0ord).1
  have hfp : p ≤ f := Nat.le_of_dvd (by omega) hpf
  have hq2 : 2 ^ p ≤ ℓ ^ f :=
    calc 2 ^ p ≤ ℓ ^ p := Nat.pow_le_pow_left hℓ.two_le p
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hfp
  have hq3 : 3 < ℓ ^ f := by
    have : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
    omega
  have hθ : autThetaT p B A = ⊥ := by
    refine eq_bot_iff.mpr ((iInf_le_of_le a0 (iInf_le_of_le ha0A
      (iInf_le_of_le ha01 le_rfl))).trans (hcoreA a0 ha0A ha0H).le)
  have hprod : ∀ t : MulAut (projectiveSL n K), autPlaneProduct p B A t =
      ⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({t} : Set _)), A⁆ := by
    intro t
    rw [autPlaneProduct, hθ, sup_bot_eq]
  have hAp : IsPGroup p A := IsPGroup.of_card hAcard
  refine ⟨hAcap, hpf, hq2, hq3, hcoreA, hθ, fun t htA ht1 => ⟨?_, ?_, ?_⟩⟩
  · unfold PlaneProductIsSubgroup
    rw [hθ, sup_bot_eq, Subgroup.coe_bot, Set.mul_singleton]
    simp
  · by_cases htH : t ∈ innSL n K
    · have htord : orderOf t = p := orderOf_eq_prime (hpA t htA) ht1
      have hAle : A ≤ B ⊓ Subgroup.centralizer {t} := fun a ha =>
        ⟨hAB ha, Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨a, ha⟩ ⟨t, htA⟩))⟩
      have hodd' := hodd hq3 t htH htord A hAle hAp
      rw [hprod]
      exact fun h => (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h)
    · rw [hprod, hcoreA t htA htH, Subgroup.commutator_bot_left]
      simp
  · intro htH
    rw [hprod, hcoreA t htA htH, Subgroup.commutator_bot_left]

end KCLinPlane

end CFSG.RankThree.PartOne
