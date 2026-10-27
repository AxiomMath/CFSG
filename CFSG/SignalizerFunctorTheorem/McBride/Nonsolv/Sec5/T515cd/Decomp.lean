module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515cd

variable {Γ : Type*} [Group Γ]

theorem conj_mem_sectionCentralizer {R Y : Subgroup Γ} {d g : Γ}
    (hdR : d ∈ Subgroup.normalizer (R : Set Γ)) (hdY : d ∈ Subgroup.normalizer (Y : Set Γ))
    (hg : g ∈ sectionCentralizer R Y) : d * g * d⁻¹ ∈ sectionCentralizer R Y := by
  obtain ⟨hgR, hgY, hg⟩ := mem_sectionCentralizer_iff.mp hg
  refine mem_sectionCentralizer_iff.mpr ⟨mul_mem (mul_mem hdR hgR) (inv_mem hdR),
    mul_mem (mul_mem hdY hgY) (inv_mem hdY), fun y hy => ?_⟩
  have hy' : d⁻¹ * y * d⁻¹⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (inv_mem hdY) y).mp hy
  have h1 := (Subgroup.mem_normalizer_iff.mp hdR _).mp (hg _ hy')
  convert h1 using 1
  simp only [commutatorElement_def]
  group

theorem mem_normalizer_sectionCentralizer {R Y : Subgroup Γ} {d : Γ}
    (hdR : d ∈ Subgroup.normalizer (R : Set Γ)) (hdY : d ∈ Subgroup.normalizer (Y : Set Γ)) :
    d ∈ Subgroup.normalizer (sectionCentralizer R Y : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_sectionCentralizer hdR hdY, fun hg => ?_⟩
  have := conj_mem_sectionCentralizer (inv_mem hdR) (inv_mem hdY) hg
  rwa [show d⁻¹ * (d * g * d⁻¹) * d⁻¹⁻¹ = g by group] at this

@[expose] def secCentralizer (X X₁ : Subgroup Γ) : Subgroup Γ :=
  X ⊓ sectionCentralizer (sol X) X₁

theorem secCentralizer_le (X X₁ : Subgroup Γ) : secCentralizer X X₁ ≤ X := inf_le_left

theorem mem_secCentralizer_iff {X X₁ : Subgroup Γ}
    (hn : X ≤ Subgroup.normalizer (X₁ : Set Γ)) {x : Γ} :
    x ∈ secCentralizer X X₁ ↔ x ∈ X ∧ ∀ y ∈ X₁, ⁅x, y⁆ ∈ sol X := by
  unfold secCentralizer
  rw [Subgroup.mem_inf, mem_sectionCentralizer_iff]
  constructor
  · rintro ⟨hx, -, -, h⟩
    exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, SolQuot.normalizer_le_nrm_sol X (Subgroup.le_normalizer hx), hn hx, h⟩

theorem mem_normalizer_secCentralizer {X X₁ : Subgroup Γ} {d : Γ}
    (hX : d ∈ Subgroup.normalizer (X : Set Γ)) (hX₁ : d ∈ Subgroup.normalizer (X₁ : Set Γ)) :
    d ∈ Subgroup.normalizer (secCentralizer X X₁ : Set Γ) :=
  L514.mem_normalizer_inf hX
    (mem_normalizer_sectionCentralizer (SolQuot.normalizer_le_nrm_sol X hX) hX₁)

theorem commutator_mem_sol_iff {X : Subgroup Γ} (a b : ↥X) :
    ⁅(a : Γ), (b : Γ)⁆ ∈ sol X ↔ ⁅a, b⁆ ∈ CFSG.solvableRadical ↥X := by
  rw [← subgroupOf_sol, Subgroup.mem_subgroupOf]
  rfl

section Finite

variable [Finite Γ]

theorem isDirectPair_map_mk {X X₁ : Subgroup Γ} (hK : kOf X = X) (hX₁ : X₁ ≤ X)
    (hn : X ≤ Subgroup.normalizer (X₁ : Set Γ)) :
    IsDirectPair ((X₁.subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X)))
      (⊤ ⊓ Subgroup.centralizer
        (((X₁.subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) :
          Subgroup (↥X ⧸ CFSG.solvableRadical ↥X)) : Set (↥X ⧸ CFSG.solvableRadical ↥X))) ⊤ := by
  have hS : IsSemisimple (⊤ : Subgroup (↥X ⧸ CFSG.solvableRadical ↥X)) :=
    (isKSubgroup_iff_kOf_eq_self X).mpr hK
  have hN1 : (X₁.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₁).mpr hn
  have hNn : ((X₁.subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X))).Normal :=
    hN1.map _ (QuotientGroup.mk'_surjective _)
  exact hS.isDirectPair_of_normal le_top
    ((Subgroup.normal_subgroupOf_iff le_top).mpr fun n g hn' _ => hNn.conj_mem n hn' g)

theorem exists_mem_of_kOf_eq_self {X X₁ : Subgroup Γ} (hK : kOf X = X) (hX₁ : X₁ ≤ X)
    (hn : X ≤ Subgroup.normalizer (X₁ : Set Γ)) {x : Γ} (hx : x ∈ X) :
    ∃ x₁ ∈ X₁, x₁⁻¹ * x ∈ secCentralizer X X₁ := by
  set π := QuotientGroup.mk' (CFSG.solvableRadical ↥X) with hπ
  have hdp := isDirectPair_map_mk hK hX₁ hn
  obtain ⟨n, hn1, c, hc, hnc⟩ := exists_mul_of_isDirectPair hdp (Subgroup.mem_top (π ⟨x, hx⟩))
  obtain ⟨a, ha, rfl⟩ := hn1
  have hc' := (Subgroup.mem_inf.mp hc).2
  have ha₁ : (a : Γ) ∈ X₁ := ha
  refine ⟨a, ha₁, (mem_secCentralizer_iff hn).mpr ⟨mul_mem (inv_mem (hX₁ ha₁)) hx, fun y hy => ?_⟩⟩
  have hy' : (⟨y, hX₁ hy⟩ : ↥X) ∈ X₁.subgroupOf X := hy
  have hcy := Subgroup.mem_centralizer_iff.mp hc' (π ⟨y, hX₁ hy⟩) ⟨_, hy', rfl⟩
  have hπx : π (a⁻¹ * ⟨x, hx⟩) = c := by
    rw [map_mul, map_inv]
    have : π a * c = π ⟨x, hx⟩ := hnc
    rw [← this]
    group
  have hcomm : π ⁅a⁻¹ * ⟨x, hx⟩, ⟨y, hX₁ hy⟩⁆ = 1 := by
    rw [map_commutatorElement, hπx, commutatorElement_eq_one_iff_mul_comm]
    exact hcy.symm
  exact (commutator_mem_sol_iff (a⁻¹ * ⟨x, hx⟩) ⟨y, hX₁ hy⟩).mpr
    (by rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcomm)

theorem mem_sol_of_mem_secCentralizer {X X₁ : Subgroup Γ} (hK : kOf X = X) (hX₁ : X₁ ≤ X)
    (hn : X ≤ Subgroup.normalizer (X₁ : Set Γ)) {z : Γ} (hz₁ : z ∈ X₁)
    (hz₂ : z ∈ secCentralizer X X₁) : z ∈ sol X := by
  set π := QuotientGroup.mk' (CFSG.solvableRadical ↥X) with hπ
  have hdp := isDirectPair_map_mk hK hX₁ hn
  have hzX : z ∈ X := hX₁ hz₁
  have hmem : π ⟨z, hzX⟩ ∈ ((X₁.subgroupOf X).map π) ⊓ (⊤ ⊓ Subgroup.centralizer
      (((X₁.subgroupOf X).map π : Subgroup (↥X ⧸ CFSG.solvableRadical ↥X)) :
        Set (↥X ⧸ CFSG.solvableRadical ↥X))) := by
    refine Subgroup.mem_inf.mpr ⟨⟨_, hz₁, rfl⟩, Subgroup.mem_inf.mpr ⟨trivial, ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have h2 := (commutator_mem_sol_iff (⟨z, hzX⟩ : ↥X) b).mp
      (((mem_secCentralizer_iff hn).mp hz₂).2 b hb)
    have h3 : π ⁅(⟨z, hzX⟩ : ↥X), b⁆ = 1 := by
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  rw [hdp.inf_eq_bot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    at hmem
  exact ⟨⟨z, hzX⟩, hmem, rfl⟩

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515cd
