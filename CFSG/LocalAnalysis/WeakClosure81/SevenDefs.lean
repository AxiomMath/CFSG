module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type*} [Group G]

@[expose] def Hyp7 (V : Subgroup G) : Prop :=
  IsElemAbelian 2 V ∧ 2 < Nat.card V ∧ IsTI V

@[expose] def omegaSet (V H E : Subgroup G) : Set (Subgroup G) :=
  {U | ∃ g : G, U = conjSubgroup V g ∧ E ⊓ U ≠ ⊥ ∧ ¬ U ≤ pCoreOf 2 H}

@[expose] def kSub (V H E : Subgroup G) : Subgroup G :=
  ⨆ U ∈ omegaSet V H E, U

@[expose] def iSub (V H E : Subgroup G) : Subgroup G :=
  ⨆ U ∈ omegaSet V H E, U ⊓ pCoreOf 2 H

@[expose] def dSet (V H E : Subgroup G) : Set G :=
  {u | ∃ U ∈ omegaSet V H E, u ∈ U ∧ u ∉ pCoreOf 2 H}

@[simp] theorem mem_omegaSet {V H E U : Subgroup G} :
    U ∈ omegaSet V H E ↔
      ∃ g : G, U = conjSubgroup V g ∧ E ⊓ U ≠ ⊥ ∧ ¬ U ≤ pCoreOf 2 H :=
  Iff.rfl

@[simp] theorem mem_dSet {V H E : Subgroup G} {u : G} :
    u ∈ dSet V H E ↔ ∃ U ∈ omegaSet V H E, u ∈ U ∧ u ∉ pCoreOf 2 H :=
  Iff.rfl

theorem le_kSub {V H E U : Subgroup G} (hU : U ∈ omegaSet V H E) : U ≤ kSub V H E :=
  le_iSup₂_of_le U hU le_rfl

theorem inf_pCoreOf_le_iSub {V H E U : Subgroup G} (hU : U ∈ omegaSet V H E) :
    U ⊓ pCoreOf 2 H ≤ iSub V H E :=
  le_iSup₂_of_le U hU le_rfl

theorem dSet_subset_kSub (V H E : Subgroup G) : dSet V H E ⊆ kSub V H E := by
  rintro u ⟨U, hU, huU, -⟩
  exact le_kSub hU huU

theorem mem_kSub_of_mem_dSet {V H E : Subgroup G} {u : G} (hu : u ∈ dSet V H E) :
    u ∈ kSub V H E :=
  dSet_subset_kSub V H E hu

@[expose] def nVSub (V : Subgroup G) (g : G) : Subgroup G :=
  V ⊓ normalizer (conjSubgroup V g)

@[expose] def bSub (V : Subgroup G) (g : G) : Subgroup G :=
  conjSubgroup V g ⊓ normalizer V

@[simp] theorem mem_nVSub {V : Subgroup G} {g x : G} :
    x ∈ nVSub V g ↔ x ∈ V ∧ x ∈ normalizer (conjSubgroup V g : Set G) :=
  Subgroup.mem_inf

@[simp] theorem mem_bSub {V : Subgroup G} {g x : G} :
    x ∈ bSub V g ↔ x ∈ conjSubgroup V g ∧ x ∈ normalizer (V : Set G) :=
  Subgroup.mem_inf

theorem conjSubgroup_normalizer (V : Subgroup G) (g : G) :
    conjSubgroup (normalizer (V : Set G)) g = normalizer (conjSubgroup V g : Set G) := by
  ext x
  constructor
  · intro hx
    rw [mem_conjSubgroup_iff] at hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · intro hy
      rw [mem_conjSubgroup_iff] at hy ⊢
      have e : g * (x * y * x⁻¹) * g⁻¹ =
          (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact (hx (g * y * g⁻¹)).mp hy
    · intro hy
      rw [mem_conjSubgroup_iff] at hy ⊢
      have e : g * (x * y * x⁻¹) * g⁻¹ =
          (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
      rw [e] at hy
      exact (hx (g * y * g⁻¹)).mpr hy
  · intro hx
    rw [Subgroup.mem_normalizer_iff] at hx
    rw [mem_conjSubgroup_iff]
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have hv' : g⁻¹ * v * g ∈ conjSubgroup V g :=
        mem_conjSubgroup_iff.mpr (by rw [show g * (g⁻¹ * v * g) * g⁻¹ = v by group]; exact hv)
      have h := (hx (g⁻¹ * v * g)).mp hv'
      rw [mem_conjSubgroup_iff] at h
      have e : g * (x * (g⁻¹ * v * g) * x⁻¹) * g⁻¹ =
          (g * x * g⁻¹) * v * (g * x * g⁻¹)⁻¹ := by group
      rwa [e] at h
    · intro hv
      have hv' : (g * x * g⁻¹) * v * (g * x * g⁻¹)⁻¹ ∈ V := hv
      have h1 : g⁻¹ * ((g * x * g⁻¹) * v * (g * x * g⁻¹)⁻¹) * g ∈
          conjSubgroup V g :=
        mem_conjSubgroup_iff.mpr
          (by rw [show g * (g⁻¹ * ((g * x * g⁻¹) * v * (g * x * g⁻¹)⁻¹) * g) * g⁻¹ =
            (g * x * g⁻¹) * v * (g * x * g⁻¹)⁻¹ by group]; exact hv')
      have e : g⁻¹ * ((g * x * g⁻¹) * v * (g * x * g⁻¹)⁻¹) * g =
          x * (g⁻¹ * v * g) * x⁻¹ := by group
      rw [e] at h1
      have h2 := (hx (g⁻¹ * v * g)).mpr h1
      rw [mem_conjSubgroup_iff] at h2
      rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v by group] at h2

end CFSG.LocalAnalysis.WeakClosure81
