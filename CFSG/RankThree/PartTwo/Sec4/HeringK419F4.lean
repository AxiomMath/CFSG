module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419Gen
public import CFSG.LieType.Ree.FixedSubgroupData
import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419.ReeF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.LargeReeInvolution

theorem hasTwoWitness_subtype_of_selfCentralizing {M : Type*} [Group M] {Γ C Q : Subgroup M}
    (hQΓ : Q ≤ Γ) (hQ2 : IsPGroup 2 Q) (hnorm : ∀ g ∈ C, ∀ n ∈ Q, g * n * g⁻¹ ∈ Q)
    (hcen : ∀ g ∈ C, (∀ n ∈ Q, g * n = n * g) → g ∈ Q) {k : Γ} (hkC : (k : M) ∈ C)
    (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) : HasTwoWitness k := by
  refine hasTwoWitness_of_selfCentralizing (C := C.subgroupOf Γ) (Q := Q.subgroupOf Γ)
    (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQΓ).symm) ?_ ?_ hkC hk3 hk1
  · intro g hg n hn
    rw [Subgroup.mem_subgroupOf] at hg hn ⊢
    exact hnorm _ hg _ hn
  · intro g hg hgn
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    refine hcen _ hg fun n hn => ?_
    exact congrArg Subtype.val (hgn ⟨n, hQΓ hn⟩ (by rwa [Subgroup.mem_subgroupOf]))

theorem kernel_data_of_subgroupOf {G : Type*} [Group G] {C N : Subgroup G} (hNC : N ≤ C)
    (hN : (N.subgroupOf C).Normal)
    (hcen : Subgroup.centralizer ((N.subgroupOf C : Subgroup C) : Set C) ≤ N.subgroupOf C) :
    (∀ g ∈ C, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧ (∀ g ∈ C, (∀ n ∈ N, g * n = n * g) → g ∈ N) := by
  refine ⟨fun g hg n hn => ?_, fun g hg hgn => ?_⟩
  · have h := hN.conj_mem ⟨n, hNC hn⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hg⟩
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  · have h : (⟨g, hg⟩ : C) ∈ N.subgroupOf C := hcen (Subgroup.mem_centralizer_iff.2 fun n hn =>
      Subtype.ext (by
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hn
        exact (hgn n hn).symm))
    rwa [Subgroup.mem_subgroupOf] at h

theorem three_dvd_sq_sub_one (a : ℕ) : 3 ∣ (2 ^ (2 * a + 1)) ^ 2 - 1 := by
  have h : (2 ^ (2 * a + 1)) ^ 2 = 4 ^ (2 * a + 1) := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 (2 * a + 1)

section Ree


theorem hasTwoWitness_reeGamma {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : ReeTag.F4.reeGamma K a) (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) : HasTwoWitness k := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL (τ := ReeTag.F4.tag)
  have hCΓ : centralizerT K a ≤ ReeTag.F4.reeGamma K a :=
    (reeGamma_inf_centralizer_tOne_eq hK).symm.le.trans inf_le_left
  obtain ⟨-, -, -, -, -, hN, -, hC, -⟩ := large_Ree_tOne_centralizer ha hK
  obtain ⟨hnorm, hcen⟩ := kernel_data_of_subgroupOf (le_sup_left : _ ≤ centralizerT K a) hN hC
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (G := centralizerT K a) (by
    rw [card_centralizerT_eq hK]
    exact Dvd.dvd.mul_left (three_dvd_sq_sub_one a) _)
  set y₀ : ReeTag.F4.reeGamma K a := ⟨x, hCΓ x.2⟩ with hy₀
  have hy₀ord : orderOf y₀ = 3 := by
    rw [← Subgroup.orderOf_coe y₀]
    exact (Subgroup.orderOf_coe x).trans hx
  have hy₀3 : y₀ ^ 3 = 1 := by
    rw [← hy₀ord]
    exact pow_orderOf_eq_one y₀
  have hy₀1 : y₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy₀ord
    omega
  have hy₀W : HasTwoWitness y₀ :=
    hasTwoWitness_subtype_of_selfCentralizing (C := centralizerT K a) (Q := tKernel K a)
      tKernel_le_reeGamma (tKernel_isPGroup ha hK) hnorm hcen x.2 hy₀3 hy₀1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec8.reeF4OrderThreeConj_holds a K ha hK y₀ k hy₀ord
    (orderOf_eq_prime hk3 hk1)
  exact hasTwoWitness_of_conj g y₀ k hg.symm hy₀W

theorem hasTwoWitness_of_reeTitsModel {X : Type} [Group X] {n : ℕ}
    (h : ReeTitsModel X CFSG.Open.StatedLieTag.twistedF4 2 n) {k : X} (hk3 : k ^ 3 = 1)
    (hk1 : k ≠ 1) : HasTwoWitness k := by
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma h
  exact hasTwoWitness_of_mulEquiv e (hasTwoWitness_reeGamma ha hK (e k)
    (by rw [← map_pow, hk3, map_one]) fun h1 => hk1 (EmbeddingLike.map_eq_one_iff.mp h1))

end Ree

end CFSG.RankThree.PartTwo.Sec4.HeringK419.ReeF4
