module

public import Mathlib.GroupTheory.OrderOfElement
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

variable {G : Type} [Group G] [Finite G]

theorem mem_inf_centralizer_sup {D K : Subgroup G} {d x : G}
    (hKD : K ≤ D)
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hd3 : orderOf d = 3) (hK3 : ¬ 3 ∣ Nat.card K) (hx : x ∈ D)
    (hxd : x * d * x⁻¹ * d⁻¹ ∈ K) :
    x ∈ (D ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ K := by
  have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hDK hx
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem hxN
  have hc1 : x⁻¹ * d * x * d⁻¹ ∈ K := by
    have hk : x * d * x⁻¹ * d⁻¹ ∈ K := hxd
    have hdx : d * x * d⁻¹ = (x * d * x⁻¹ * d⁻¹)⁻¹ * x := by group
    rw [show x⁻¹ * d * x * d⁻¹ = x⁻¹ * (d * x * d⁻¹) by group, hdx]
    rw [show x⁻¹ * ((x * d * x⁻¹ * d⁻¹)⁻¹ * x) = x⁻¹ * (x * d * x⁻¹ * d⁻¹)⁻¹ * x by
      group]
    simpa using
      (Subgroup.mem_normalizer_iff.mp hxN' ((x * d * x⁻¹ * d⁻¹)⁻¹)).mp (inv_mem hk)
  have hc1' : x⁻¹ * d⁻¹ * x * d ∈ K := by
    have hk : x * d * x⁻¹ * d⁻¹ ∈ K := hxd
    have hdx : d⁻¹ * x * d = (d⁻¹ * (x * d * x⁻¹ * d⁻¹) * d) * x := by group
    rw [show x⁻¹ * d⁻¹ * x * d = x⁻¹ * (d⁻¹ * x * d) by group, hdx]
    rw [show x⁻¹ * ((d⁻¹ * (x * d * x⁻¹ * d⁻¹) * d) * x) =
      (x⁻¹ * (d⁻¹ * (x * d * x⁻¹ * d⁻¹) * d)) * x by group]
    simpa using (Subgroup.mem_normalizer_iff.mp hxN'
      (d⁻¹ * (x * d * x⁻¹ * d⁻¹) * d)).mp
        (by simpa using
          (Subgroup.mem_normalizer_iff.mp (inv_mem hdK) (x * d * x⁻¹ * d⁻¹)).mp hk)
  have hP : ∀ a ∈ Subgroup.zpowers d,
      a ∈ Subgroup.normalizer (K : Set G) ∧ x⁻¹ * (a * x * a⁻¹) ∈ K := by
    intro a ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine zpow_induction_right (P := fun a =>
      a ∈ Subgroup.normalizer (K : Set G) ∧ x⁻¹ * (a * x * a⁻¹) ∈ K) ?_ ?_ ?_ m
    · exact ⟨(Subgroup.normalizer (K : Set G)).one_mem, by simp⟩
    · rintro a ⟨haN, haK⟩
      refine ⟨(Subgroup.normalizer (K : Set G)).mul_mem haN hdK, ?_⟩
      rw [show x⁻¹ * ((a * d) * x * (a * d)⁻¹) =
        (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * d * x * d⁻¹) * a⁻¹) by group]
      exact K.mul_mem haK (by
        simpa using (Subgroup.mem_normalizer_iff.mp haN (x⁻¹ * d * x * d⁻¹)).mp hc1)
    · rintro a ⟨haN, haK⟩
      refine ⟨(Subgroup.normalizer (K : Set G)).mul_mem haN (inv_mem hdK), ?_⟩
      rw [show x⁻¹ * ((a * d⁻¹) * x * (a * d⁻¹)⁻¹) =
        (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * d⁻¹ * x * d) * a⁻¹) by group]
      exact K.mul_mem haK (by
        simpa using (Subgroup.mem_normalizer_iff.mp haN (x⁻¹ * d⁻¹ * x * d)).mp hc1')
  have hS3 : IsPGroup 3 ↥(Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd3, pow_one])
  have hinv : ∀ a : ↥(Subgroup.zpowers d), ∀ y : G, x⁻¹ * y ∈ K →
      x⁻¹ * (MulAut.conj (a : G)) y ∈ K := by
    intro a y hy
    obtain ⟨haN, haK⟩ := hP (a : G) a.2
    rw [MulAut.conj_apply]
    rw [show x⁻¹ * ((a : G) * y * ((a : G))⁻¹) =
      (x⁻¹ * ((a : G) * x * ((a : G))⁻¹)) * ((a : G) * (x⁻¹ * y) * ((a : G))⁻¹) by
        group]
    exact K.mul_mem haK (by
      simpa using (Subgroup.mem_normalizer_iff.mp haN (x⁻¹ * y)).mp hy)
  obtain ⟨c, hcK, hcfix⟩ :=
    ((CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed (A := ↥(Subgroup.zpowers d))
      (G := G) (p := 3) hS3
      ((MulAut.conj : G →* MulAut G).comp (Subgroup.zpowers d).subtype) K hK3 x)).2 hinv
  have hcC : c ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : d * c * d⁻¹ = c := by
      simpa [MulAut.conj_apply] using hcfix ⟨d, Subgroup.mem_zpowers d⟩
    have h2 : d * c = c * d := by
      calc d * c = (d * c * d⁻¹) * d := by group
        _ = c * d := by rw [h1]
    exact h2.symm
  have hcD : c ∈ D := by
    have h1 : x * (x⁻¹ * c) ∈ D := D.mul_mem hx (hKD hcK)
    rwa [show x * (x⁻¹ * c) = c by group] at h1
  rw [show x = c * (x⁻¹ * c)⁻¹ by group]
  exact Subgroup.mul_mem_sup ⟨hcD, hcC⟩ (K.inv_mem hcK)

theorem le_inf_centralizer_sup {D K : Subgroup G} {d : G}
    (hKD : K ≤ D)
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hdK : d ∈ Subgroup.normalizer (K : Set G))
    (hd3 : orderOf d = 3) (hK3 : ¬ 3 ∣ Nat.card K)
    (hcomm : ⁅D, Subgroup.zpowers d⁆ ≤ K) :
    D ≤ (D ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ K := by
  intro x hx
  refine mem_inf_centralizer_sup hKD hDK hdK hd3 hK3 hx ?_
  exact hcomm (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers d))

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
