module

public import CFSG.RankThree.PartOne.Q1327C.P5Arith
public import CFSG.RankThree.PartOne.N143.SectionGroup
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open scoped commutatorElement

theorem center_eq_bot_of_not_prime {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (h : ¬ (Nat.card Q).Prime) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h0 | h0
  · exact h0
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact h (IsSimpleGroup.prime_card (α := Q))

theorem thirteen_dvd_of_section {G : Type} [Group G] [Finite G] {X N : Subgroup G} (hNX : N ≤ X)
    {f : ℕ} (hf : 2 ≤ f) (h5 : 5 ∣ 2 ^ f + 1)
    (hmod : StatedClassicalModel (↥N ⧸ aschbacherSolvableCore 5 ↥N) .PSU 3 2 f) :
    13 ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
  have hQcard : Nat.card (↥N ⧸ aschbacherSolvableCore 5 ↥N) =
      CFSG.Open.ordTwistedA 2 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  have hsimp : IsSimpleGroup (↥N ⧸ aschbacherSolvableCore 5 ↥N) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 f hmod).2
  have hcen : Subgroup.center (↥N ⧸ aschbacherSolvableCore 5 ↥N) = ⊥ :=
    center_eq_bot_of_not_prime (by rw [hQcard]; exact not_prime_ordTwistedA_two (by omega) h5)
  let ρ : ↥N →* (↥X ⧸ Subgroup.center ↥X) :=
    (QuotientGroup.mk' (Subgroup.center ↥X)).comp (Subgroup.inclusion hNX)
  have hker : ρ.ker ≤ aschbacherSolvableCore 5 ↥N := by
    intro n hn
    have h1 : Subgroup.inclusion hNX n ∈ Subgroup.center ↥X := by
      have := MonoidHom.mem_ker.1 hn
      simpa [ρ, QuotientGroup.eq_one_iff] using this
    have h2 : n ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subgroup.inclusion_injective hNX
      simpa using Subgroup.mem_center_iff.1 h1 (Subgroup.inclusion hNX m)
    have h3 : (QuotientGroup.mk n : ↥N ⧸ aschbacherSolvableCore 5 ↥N) ∈
        Subgroup.center (↥N ⧸ aschbacherSolvableCore 5 ↥N) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 h2 m]
    rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hsurj : Function.Surjective
      (QuotientGroup.map ρ.ker (aschbacherSolvableCore 5 ↥N) (MonoidHom.id ↥N)
        (fun x hx => hker hx)) := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk n, rfl⟩
  have h1 : Nat.card (↥N ⧸ aschbacherSolvableCore 5 ↥N) ∣ Nat.card (↥N ⧸ ρ.ker) :=
    Subgroup.card_dvd_of_surjective hsurj
  have h2 : Nat.card (↥N ⧸ ρ.ker) = Nat.card ρ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  have h3 : Nat.card ρ.range ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hQcard, h2] at h1
  exact (thirteen_dvd_ordTwistedA_two (by omega) h5).trans (h1.trans h3)

theorem section_of_center {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hZ : ¬ 5 ∣ Nat.card (Subgroup.center ↥X)) {A S : Subgroup G} (hAX : A ≤ X) (hSX : S ≤ X)
    (hA : IsElementaryAbelian 5 A) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hN : A ≤ Subgroup.normalizer (S : Set G)) (hC : ⁅S, A⁆ = S) :
    ∃ B T : Subgroup (↥X ⧸ Subgroup.center ↥X), IsElementaryAbelian 5 B ∧
      Nat.card B = Nat.card A ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      B ≤ Subgroup.normalizer (T : Set (↥X ⧸ Subgroup.center ↥X)) ∧ ⁅T, B⁆ = T := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := hA
  let π : ↥X →* (↥X ⧸ Subgroup.center ↥X) := QuotientGroup.mk' (Subgroup.center ↥X)
  have hker : ¬ 5 ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    exact hZ
  let E : Subgroup ↥X := A.subgroupOf X
  let S' : Subgroup ↥X := S.subgroupOf X
  have hE : IsElementaryAbelian 5 E := IsElementaryAbelian.subgroupOf hAX
  have hS2' : IsPGroup 2 S' :=
    hS2.of_injective (Subgroup.subgroupOfEquivOfLe hSX).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSX).injective
  have hN' : E ≤ Subgroup.normalizer (S' : Set ↥X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hax : (a : G) ∈ Subgroup.normalizer (S : Set G) := hN (Subgroup.mem_subgroupOf.1 ha)
    have := (Subgroup.mem_normalizer_iff.1 hax) (x : G)
    exact this
  have hmapS : S'.map X.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSX
  have hmapA : E.map X.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAX
  have hC' : ⁅S', E⁆ = S' := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hmapS, hmapA, hC]
  have hSk : ¬ S' ≤ π.ker := by
    intro hle
    rw [QuotientGroup.ker_mk'] at hle
    have h1 : S' ≤ Subgroup.centralizer (E : Set ↥X) :=
      hle.trans (Subgroup.center_le_centralizer _)
    have h2 : ⁅S', E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 h1
    rw [h2] at hC'
    apply hS1
    rw [← hmapS, ← hC']
    simp
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := N143.section_data π Nat.prime_five hker hE hS2' hN' hC' hSk
  refine ⟨E.map π, S'.map π, h1, ?_, h3, h4, h5, h6⟩
  rw [h2]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv

end CFSG.RankThree.PartOne.Q1327C
