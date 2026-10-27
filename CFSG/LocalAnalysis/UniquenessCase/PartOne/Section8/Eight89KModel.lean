module

public import Certificates.Data.Eight89KModels
public import CFSG.Certificates.Kernel.Spor.PK.PermOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup

@[expose] noncomputable def tperm (d : ℕ) (t : Array ℕ) : Equiv.Perm (Fin d) :=
  CFSG.KS.PK.permOf d fun x => t.getD x x

@[expose] noncomputable def perm3a : Equiv.Perm (Fin 18) := tperm 18 KData.m3aT

@[expose] noncomputable def perm3b : Equiv.Perm (Fin 18) := tperm 18 KData.m3bT

@[expose] noncomputable def model3 : Subgroup (Equiv.Perm (Fin 18)) := closure {perm3a, perm3b}

@[expose] noncomputable def a3 : model3 := ⟨perm3a, subset_closure (by simp)⟩

@[expose] noncomputable def b3 : model3 := ⟨perm3b, subset_closure (by simp)⟩

@[expose] noncomputable def s3 : model3 := a3 * b3

@[expose] noncomputable def c3 : model3 := s3 ^ 5

@[expose] noncomputable def e3 : model3 := s3 ^ 3

@[expose] noncomputable def perm6a : Equiv.Perm (Fin 162) := tperm 162 KData.m6aT

@[expose] noncomputable def perm6b : Equiv.Perm (Fin 162) := tperm 162 KData.m6bT

@[expose] noncomputable def model6 : Subgroup (Equiv.Perm (Fin 162)) := closure {perm6a, perm6b}

@[expose] noncomputable def a6 : model6 := ⟨perm6a, subset_closure (by simp)⟩

@[expose] noncomputable def b6 : model6 := ⟨perm6b, subset_closure (by simp)⟩

@[expose] noncomputable def s6 : model6 := a6 * b6

@[expose] noncomputable def c6 : model6 := s6 ^ 5

@[expose] noncomputable def e6 : model6 := s6 ^ 6

@[expose] noncomputable def z6 : model6 := c6 ^ 2

theorem closure_pair_subtype_eq_top {G : Type*} [Group G] (x y : G) :
    closure ({⟨x, subset_closure (by simp)⟩, ⟨y, subset_closure (by simp)⟩} :
      Set (closure ({x, y} : Set G))) = ⊤ := by
  have h : ({⟨x, subset_closure (by simp)⟩, ⟨y, subset_closure (by simp)⟩} :
      Set (closure ({x, y} : Set G))) = ((↑) : closure ({x, y} : Set G) → G) ⁻¹' {x, y} := by
    ext ⟨g, hg⟩
    simp [Subtype.ext_iff]
  rw [h, closure_closure_coe_preimage]

theorem closure_gens3 : closure ({a3, b3} : Set model3) = ⊤ :=
  closure_pair_subtype_eq_top perm3a perm3b

theorem closure_gens6 : closure ({a6, b6} : Set model6) = ⊤ :=
  closure_pair_subtype_eq_top perm6a perm6b

@[expose] def IdentC : Prop :=
  ∃ T : List (model3 × model3), ∀ (A : Type) [Ring A], (2 : A) = 0 → ∀ ρ : model3 →* A,
    (T.map fun x => ρ x.1 * (∑ m ∈ Finset.range 5, ρ e3 ^ m) * ρ x.2).sum = ρ c3 + ρ c3 ^ 2

@[expose] def IdentD : Prop :=
  ∃ (T : List (model3 × model3)) (v : List (ℤ × model3)), ∀ (A : Type) [Ring A] (ρ : model3 →* A),
    (T.map fun x => ρ x.1 * (∑ m ∈ Finset.range 5, ρ e3 ^ m) * ρ x.2).sum *
        (v.map fun x => x.1 • ρ x.2).sum = (10800 : A) * (2 - ρ c3 - ρ c3 ^ 2)

@[expose] def IdentE : Prop :=
  ∃ (T : List (model6 × model6)) (v : List (ℤ × model6)), ∀ (A : Type) [Ring A] (ρ : model6 →* A),
    (T.map fun x => ρ x.1 * (∑ m ∈ Finset.range 5, ρ e6 ^ m) * ρ x.2).sum *
        (v.map fun x => x.1 • ρ x.2).sum = (21600 : A) * (2 - ρ z6 - ρ z6 ^ 2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
