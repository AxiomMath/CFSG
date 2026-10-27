module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.RankThree.LocalRank
open scoped commutatorElement

theorem le_aschbacherSolvableCore_of_map_normal {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) (hS : Group.IsSolvable S) (hSp : ¬ p ∣ Nat.card S)
    (hN : (S.map (QuotientGroup.mk' (aschbacherSolvableCore p X))).Normal) :
    S ≤ aschbacherSolvableCore p X := by
  obtain ⟨hNsol, -, hNp, hmax, -⟩ := solvable_prime_complement_core_characterization (H := X) hp
  set N := aschbacherSolvableCore p X with hNdef
  set π := QuotientGroup.mk' N with hπ
  set W : Subgroup X := (S.map π).comap π with hW
  have hWn : W.Normal := hN.comap π
  have hNW : N ≤ W := fun n hn => by
    show π n ∈ S.map π
    rw [show π n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _
  have hSW : S ≤ W := Subgroup.le_comap_map π S
  have hSmapsol : Group.IsSolvable (S.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective S)
  have hWsol : Group.IsSolvable W := by
    have hNWsol : Group.IsSolvable (N.subgroupOf W) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hNW).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hNW).injective
    let g : W →* S.map π := (π.comp W.subtype).codRestrict (S.map π) fun w => w.2
    refine Group.isSolvable_of_ker_le_range (N.subgroupOf W).subtype g ?_
    intro w hw
    have h1 : π (w : X) = 1 := congrArg Subtype.val hw
    have h2 : (w : X) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨w, h2⟩, rfl⟩
  have hWp : ¬ p ∣ Nat.card W := by
    intro hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨s, hs, hsw⟩ := w.2
    have h1 : orderOf (π (w : X)) ∣ p := by
      refine (orderOf_map_dvd π (w : X)).trans ?_
      rw [Subgroup.orderOf_coe, hw]
    have h2 : orderOf (π (w : X)) ∣ Nat.card S := by
      rw [← hsw]
      exact (orderOf_map_dvd π s).trans (Subgroup.orderOf_dvd_natCard S hs)
    have h3 : orderOf (π (w : X)) = 1 := by
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) hSp
    have h4 : (w : X) ∈ N := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
    refine hNp ?_
    have := Subgroup.orderOf_dvd_natCard N h4
    rwa [Subgroup.orderOf_coe, hw] at this
  exact hSW.trans (hmax W hWn hWsol hWp)

theorem mem_aschbacherSolvableCore_of_commutator_mem {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (z : X) (hz : ¬ p ∣ orderOf z)
    (h : ∀ g : X, ⁅z, g⁆ ∈ aschbacherSolvableCore p X) : z ∈ aschbacherSolvableCore p X := by
  set N := aschbacherSolvableCore p X with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hcen : π z ∈ Subgroup.center (X ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    show (g : X ⧸ N) * π z = π z * (g : X ⧸ N)
    have h1 : π ⁅z, g⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (h g)
    have h2 : z * g = ⁅z, g⁆ * (g * z) := by
      simp only [commutatorElement_def]
      group
    have h3 : π (z * g) = π (g * z) := by rw [h2, map_mul, h1, one_mul]
    simpa [hπ] using h3.symm
  have hS : Group.IsSolvable (Subgroup.zpowers z) := inferInstance
  have hSp : ¬ p ∣ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers]
    exact hz
  refine le_aschbacherSolvableCore_of_map_normal hp _ hS hSp ?_ (Subgroup.mem_zpowers z)
  rw [MonoidHom.map_zpowers]
  exact Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcen)

end CFSG.RankThree.PartOne.F106
