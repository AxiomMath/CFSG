module

public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveActual
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveAbelianLift
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveFieldActor
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveModelBridge

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCEvenUnitaryFiveBridge CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ComponentClassification.OutcomeLocal

namespace KCEvenUnitaryFive

theorem card_sup_dvd_of_le_normalizer {G : Type*} [Group G] [Finite G] (N I : Subgroup G)
    (hI : I ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ I) ∣ Nat.card ↥N * Nat.card ↥I := by
  set M := N ⊔ I with hM
  have hNM : N ≤ M := le_sup_left
  have hIM : I ≤ M := le_sup_right
  have hMn : M ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hI
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMn
  have htop : N.subgroupOf M ⊔ I.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNM hIM, hM, Subgroup.subgroupOf_self]
  have h1 : (N.subgroupOf M).index = (N.subgroupOf M).relIndex (I.subgroupOf M) := by
    have := Subgroup.relIndex_sup_right (H := I.subgroupOf M) (K := N.subgroupOf M)
    rw [sup_comm, htop, Subgroup.relIndex_top_right] at this
    exact this
  have h2 : (N.subgroupOf M).relIndex (I.subgroupOf M) ∣ Nat.card ↥(I.subgroupOf M) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card ↥(N.subgroupOf M) * (N.subgroupOf M).index = Nat.card ↥M :=
    Subgroup.card_mul_index _
  have hcN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcI : Nat.card ↥(I.subgroupOf M) = Nat.card ↥I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIM).toEquiv
  rw [← h3, hcN, h1]
  rw [hcI] at h2
  exact Nat.mul_dvd_mul_left _ h2

end KCEvenUnitaryFive

open KCEvenUnitaryFive

theorem planeLocalCoreOdd_primeFormP_five {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) :
    PlaneLocalCoreOdd 5 (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) := by
  classical
  intro B hB A hAB hAel hAcard t htA ht1
  have hfin := h.finite
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpow : ∀ a ∈ A, a ^ 5 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 : (⟨a, ha⟩ : A) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      hAel.toIsMulCommutative.is_comm.comm _ _
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have ht5 : orderOf t = 5 := orderOf_eq_prime (hpow t htA) ht1
  have hAC : A ≤ B ⊓ Subgroup.centralizer ({t} : Set _) := fun a ha =>
    ⟨hAB ha, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha t htA)⟩
  set S := inSubgroup (aschbacherSolvableCore 5) (B ⊓ Subgroup.centralizer ({t} : Set _))
    with hS
  have hIS : autThetaT 5 B A ≤ S := by
    intro x hx
    have h1 := Subgroup.mem_iInf.mp hx t
    have h2 := Subgroup.mem_iInf.mp h1 htA
    exact Subgroup.mem_iInf.mp h2 ht1
  have hSnorm : S ≤ Subgroup.normalizer ((⁅S, A⁆ : Subgroup _) : Set _) :=
    Subgroup.normalizer_commutator_ge_left S A
  have hactor : ∀ a ∈ A, a ∉ primeFormD h (idGram K 5) →
      inSubgroup (aschbacherSolvableCore 5) (B ⊓ Subgroup.centralizer ({a} : Set _)) = ⊥ := by
    intro a ha haD
    have ha1 : a ≠ 1 := fun h' => haD (h' ▸ Subgroup.one_mem _)
    exact even_unitary_five_field_actor_solvable_core_trivial h h5 B hB (hAB ha) haD
      (orderOf_eq_prime (hpow a ha) ha1)
  have hN : ¬ 2 ∣ Nat.card ↥⁅S, A⁆ := by
    by_cases htD : t ∈ primeFormD h (idGram K 5)
    · exact (even_unitary_five_matrix_actor_local_core_linear_part_odd h h5 B hB (hAB htA) htD
        ht5).2 A hAC
    · have hSt : S = ⊥ := hactor t htA htD
      rw [hSt, Subgroup.commutator_bot_left]
      simp
  have hW : autPlaneProduct 5 B A t = ⁅S, A⁆ ⊔ autThetaT 5 B A := rfl
  by_cases hAD : A ≤ primeFormD h (idGram K 5)
  · by_cases hab : ∀ x y : primeFormUnitary h (idGram K 5),
        primeFormConjHom h (idGram K 5) x ∈ A → primeFormConjHom h (idGram K 5) y ∈ A →
          x * y = y * x
    · have hI : autThetaT 5 B A = ⊥ :=
        even_unitary_five_abelian_lift_plane_core_intersection_trivial h h5 B hB A hAB hAD hAel
          hAcard hab
      rw [hW, hI, sup_bot_eq]
      exact hN
    · have hodd := odd_card_centralizer_of_nonabelian_lift h h5 A hAD hAel hAcard hab
      have hIcent : autThetaT 5 B A ≤ Subgroup.centralizer (A : Set _) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        by_cases ha1 : a = 1
        · rw [ha1, one_mul, mul_one]
        · have h1 := Subgroup.mem_iInf.mp hx a
          have h2 := Subgroup.mem_iInf.mp h1 ha
          have h3 := Subgroup.mem_iInf.mp h2 ha1
          have h4 := (Subgroup.map_subtype_le _ h3 : x ∈ B ⊓ Subgroup.centralizer ({a} : Set _)).2
          exact (Subgroup.mem_centralizer_singleton_iff.mp h4).symm
      have hIodd : ¬ 2 ∣ Nat.card ↥(autThetaT 5 B A) := by
        have hd := Subgroup.card_dvd_of_le hIcent
        intro h2
        have := (Odd.of_dvd_nat hodd hd)
        rw [Nat.odd_iff] at this
        omega
      have hd := card_sup_dvd_of_le_normalizer ⁅S, A⁆ (autThetaT 5 B A) (hIS.trans hSnorm)
      rw [hW]
      intro h2
      have h3 := h2.trans hd
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h3 with h4 | h4
      · exact hN h4
      · exact hIodd h4
  · obtain ⟨a, haA, haD⟩ : ∃ a ∈ A, a ∉ primeFormD h (idGram K 5) := by
      by_contra hcon
      push Not at hcon
      exact hAD hcon
    have hI : autThetaT 5 B A = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have ha1 : a ≠ 1 := fun h' => haD (h' ▸ Subgroup.one_mem _)
      have h1 := Subgroup.mem_iInf.mp hx a
      have h2 := Subgroup.mem_iInf.mp h1 haA
      have h3 := Subgroup.mem_iInf.mp h2 ha1
      rw [hactor a haA haD] at h3
      exact h3
    rw [hW, hI, sup_bot_eq]
    exact hN

theorem even_unitary_five_all_plane_local_core_product_odd :
    EvenUnitaryFivePlaneLocalCoreOdd := by
  intro f K _ h h5
  have hfinK : Finite K := h.finite
  have : Finite (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) :=
    finite_primeFormP
  have : Finite (unitaryPSU h 5) := Finite.of_equiv _ (primeFormOneEquiv h 5).toEquiv
  exact PlaneLocalCoreOdd.of_mulEquiv Nat.prime_five (primeFormOneEquiv h 5).symm
    (planeLocalCoreOdd_primeFormP_five h h5)

end CFSG.RankThree.PartOne
