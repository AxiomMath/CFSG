module

public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual

public section

namespace CFSG.RankThree.PartOne.Sec9A

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem inf_inSubgroup_theta_le [Finite G] {p : ℕ} (hp : p.Prime) {L M : Subgroup G}
    (hLM : L ≤ M) :
    L ⊓ inSubgroup (aschbacherSolvableCore p) M ≤ inSubgroup (aschbacherSolvableCore p) L := by
  rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
    inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
  exact RankThreeEvenClassification.Helpers.intersection_thetaCoreOf_le p hp L M hLM

theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  exact Subgroup.centralizer_le_normalizer _

theorem inSubgroup_theta_normalizer_le_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {c : G}
    (hc : c ^ p = 1) :
    inSubgroup (aschbacherSolvableCore p) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      Subgroup.centralizer ({c} : Set G) := by
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set S := inSubgroup (aschbacherSolvableCore p) H with hS
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcH : c ∈ H := Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hxH : x ∈ H := Subgroup.map_subtype_le _ hx
  have hnorm : H ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer.trans
      (SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p H)
  have hz1 : x * c * x⁻¹ * c⁻¹ ∈ S := by
    have h1 : c * x⁻¹ * c⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hnorm hcH) x⁻¹).mp (inv_mem hx)
    simpa [mul_assoc] using mul_mem hx h1
  have hz2 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hxH c).mp (Subgroup.mem_zpowers c))
      (inv_mem (Subgroup.mem_zpowers c))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz2
  have hzp : (x * c * x⁻¹ * c⁻¹) ^ p = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  have hdvd1 : orderOf (x * c * x⁻¹ * c⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have hdvd2 : orderOf (x * c * x⁻¹ * c⁻¹) ∣ Nat.card S := Subgroup.orderOf_dvd_natCard _ hz1
  have hnd : ¬ p ∣ Nat.card S := by
    have h := (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := H) hp).2.2.1
    rwa [hS, inSubgroup, Subgroup.card_map_of_injective H.subtype_injective]
  have hord : orderOf (x * c * x⁻¹ * c⁻¹) = 1 := by
    rcases (Nat.dvd_prime hp).mp hdvd1 with h | h
    · exact h
    · exact absurd (h ▸ hdvd2) hnd
  have hone : x * c * x⁻¹ * c⁻¹ = 1 := orderOf_eq_one_iff.mp hord
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hone
  exact hone


theorem inSubgroup_theta_normalizer_le [Finite G] {p : ℕ} (hp : p.Prime) {c : G} (hc : c ^ p = 1) :
    inSubgroup (aschbacherSolvableCore p) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)) :=
  (le_inf (inSubgroup_theta_normalizer_le_centralizer hp hc) le_rfl).trans
    (inf_inSubgroup_theta_le hp (centralizer_le_normalizer_zpowers c))

theorem commutator_sup_eq_of_le_centralizer {R B E : Subgroup G}
    (hBE : B ⊔ E ≤ Subgroup.normalizer (R : Set G))
    (hB : B ≤ Subgroup.centralizer (R : Set G)) : ⁅R, B ⊔ E⁆ = ⁅R, E⁆ := by
  set M := R ⊔ (B ⊔ E) with hM
  have hRM : R ≤ M := le_sup_left
  have hBEM : B ⊔ E ≤ M := le_sup_right
  have hBM : B ≤ M := le_sup_left.trans hBEM
  have hEM : E ≤ M := le_sup_right.trans hBEM
  have hn : (R.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr (sup_le Subgroup.le_normalizer hBE)
  have h1 : ⁅R.subgroupOf M, B.subgroupOf M⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hB hb) r hr).symm
  have h2 := Subgroup.commutator_sup_left (R.subgroupOf M) (B.subgroupOf M) (E.subgroupOf M)
  rw [← Subgroup.subgroupOf_sup hBM hEM, h1, bot_sup_eq] at h2
  have h3 := congrArg (Subgroup.map M.subtype) h2
  rwa [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRM,
    Subgroup.map_subgroupOf_eq_of_le hBEM, Subgroup.map_subgroupOf_eq_of_le hEM] at h3

theorem le_twoPrimeResidual [Finite G] {W X : Subgroup G} (hX : IsPGroup 2 X) (hXW : X ≤ W) :
    X ≤ CFSG.Quasithin.twoPrimeResidual W := by
  unfold CFSG.Quasithin.twoPrimeResidual
  exact le_iInf₂ fun N hN =>
    SteinbergBY.le_of_isPGroup_two_of_odd_relIndex hX hXW hN.1 hN.2.1 hN.2.2

theorem sup_eq_of_card [Finite G] {p : ℕ} (hp : p.Prime) {A B S : Subgroup G} (hBA : B ≤ A)
    (hSA : S ≤ A) (hAcard : Nat.card A = p ^ 3) (hBcard : Nat.card B = p ^ 2) (hSB : ¬ S ≤ B) :
    B ⊔ S = A := by
  have hle : B ⊔ S ≤ A := sup_le hBA hSA
  have hlt : B < B ⊔ S := lt_of_le_of_ne le_sup_left fun h => hSB (h ▸ le_sup_right)
  have h1 : Nat.card B < Nat.card (B ⊔ S : Subgroup G) := Subgroup.card_lt_of_lt hlt
  have h2 : Nat.card (B ⊔ S : Subgroup G) ∣ p ^ 3 := hAcard ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp h2
  rw [hBcard, hkeq] at h1
  have hk2 : 2 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h1
  have hk3 : k = 3 := by omega
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hAcard, hkeq, hk3]

end CFSG.RankThree.PartOne.Sec9A

