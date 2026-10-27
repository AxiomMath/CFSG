module

public import CFSG.RankThree.PartOne.K156.Max
public import CFSG.RankThree.PartOne.K133.Union

public section

namespace CFSG.RankThree.PartOne.K156

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.S15K (Sec13Avail)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

@[expose] def Full106Stmt : Prop :=
  SchreierFor InCatalog → TwoActionInputs →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∀ L ∈ sectionTenZero p A, CFSG.IsQuasisimple L

variable {G : Type} [Group G] [Finite G]

theorem theta_le_centralizer_of_quasisimple {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : CFSG.IsQuasisimple ↥X) :
    ∀ t ∈ inSubgroup (aschbacherSolvableCore p) X, ∀ z ∈ X, t * z = z * t := by
  intro t ht z hz
  have hn : (aschbacherSolvableCore p ↥X).Normal := inferInstance
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hX hn with htop | hcen
  · exfalso
    have hsol : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore p) X) :=
      (theta_solvable_and_not_dvd hp X).1
    have hXθ : X ≤ inSubgroup (aschbacherSolvableCore p) X := by
      intro x hx
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [htop]
      exact Subgroup.mem_top _
    have hsolX : Group.IsSolvable ↥X :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXθ)
        (Subgroup.inclusion_injective hXθ)
    have : Nontrivial ↥X := CFSG.LocalCores.isQuasisimple_nontrivial hX
    have : Group.IsPerfect ↥X := hX.1
    exact Group.IsPerfect.not_isSolvable ↥X hsolX
  · obtain ⟨t', ht', rfl⟩ := ht
    have := Subgroup.mem_center_iff.1 (hcen ht') ⟨z, hz⟩
    exact congrArg Subtype.val this.symm

theorem le_of_sectionTenRel_of_quasisimple {p : ℕ} (hp : p.Prime) {X Y : Subgroup G}
    (hX : CFSG.IsQuasisimple ↥X) (hXY : sectionTenRel p X Y) : X ≤ Y := by
  have hcent := theta_le_centralizer_of_quasisimple hp hX
  have hθX : inSubgroup (aschbacherSolvableCore p) X ≤ X := Subgroup.map_subtype_le _
  have hset := sectionTenRel_iff.1 hXY
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ Y := by
    intro x hx y hy
    have hx' : x ∈ ((X ⊓ Y : Subgroup G) : Set G) *
        (inSubgroup (aschbacherSolvableCore p) X : Set G) := by rw [← hset]; exact hx
    have hy' : y ∈ ((X ⊓ Y : Subgroup G) : Set G) *
        (inSubgroup (aschbacherSolvableCore p) X : Set G) := by rw [← hset]; exact hy
    obtain ⟨a, ha, t, ht, rfl⟩ := hx'
    obtain ⟨b, hb, u, hu, rfl⟩ := hy'
    have haX : a ∈ X := (Subgroup.mem_inf.1 ha).1
    have hbX : b ∈ X := (Subgroup.mem_inf.1 hb).1
    have hta : t * a = a * t := hcent t ht a haX
    have htb : t * b = b * t := hcent t ht b hbX
    have htu : t * u = u * t := hcent t ht u (hθX hu)
    have hua : u * a = a * u := hcent u hu a haX
    have hua' : u * a⁻¹ = a⁻¹ * u := (Commute.inv_right (hua : Commute u a)).eq
    have key : ⁅a * t, b * u⁆ = a * b * a⁻¹ * b⁻¹ := by
      rw [commutatorElement_def]
      calc a * t * (b * u) * (a * t)⁻¹ * (b * u)⁻¹
          = a * (t * b) * u * t⁻¹ * a⁻¹ * u⁻¹ * b⁻¹ := by group
        _ = a * (b * t) * u * t⁻¹ * a⁻¹ * u⁻¹ * b⁻¹ := by rw [htb]
        _ = a * b * (t * u) * t⁻¹ * a⁻¹ * u⁻¹ * b⁻¹ := by group
        _ = a * b * (u * t) * t⁻¹ * a⁻¹ * u⁻¹ * b⁻¹ := by rw [htu]
        _ = a * b * (u * a⁻¹) * u⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * u) * u⁻¹ * b⁻¹ := by rw [hua']
        _ = a * b * a⁻¹ * b⁻¹ := by group
    rw [key]
    have haY : a ∈ Y := (Subgroup.mem_inf.1 ha).2
    have hbY : b ∈ Y := (Subgroup.mem_inf.1 hb).2
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem haY hbY) (Y.inv_mem haY)) (Y.inv_mem hbY)
  have hle : ⁅(⊤ : Subgroup ↥X), ⊤⁆ ≤ Y.subgroupOf X := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    exact hcomm x x.2 y y.2
  have htop : Y.subgroupOf X = ⊤ := by
    rw [eq_top_iff]
    have h1 := hX.1.commutator_eq_top
    rw [commutator_def] at h1
    rw [← h1]
    exact hle
  exact Subgroup.subgroupOf_eq_top.1 htop

theorem kf156_of_E_eq_A
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs) (h106 : Full106Stmt)
    (hS13 : Sec13Avail) (h1322 : Node1322) (h1320 : Node1320Struct)
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hEA : E = A) : ∀ X ∈ thetaCompZeroE p E, X ≤ lieGenerated p E := by
  intro X hX
  have h := h15.h12
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨B, hB, hXz⟩ := hX
  have hEB : E = B := (Subgroup.eq_of_le_of_card_ge hB.1 (by rw [hE3, hB.2.2.1])).symm
  have hXE : X ∈ thetaCompE p E := ⟨B, hB, hXz.1⟩
  obtain ⟨Y, hY, hXY⟩ := K133.exists_zeroStar_above_E hS h hXE
    (fun _ hb _ _ _ _ => ⟨B, hB.1, hB.2.2.1, hEB ▸ hb, hXz⟩)
  have hYI := node156_of_E_eq_A hGA hS13 h1322 h1320 h15 hEA Y hY
  have hXq : CFSG.IsQuasisimple ↥X := h106 hS hTwo G p B (h.setup_of_admissible hB) X hXz
  exact (le_of_sectionTenRel_of_quasisimple h.prime hXq hXY).trans hYI

end CFSG.RankThree.PartOne.K156
