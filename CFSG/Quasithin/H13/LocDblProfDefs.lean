module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.LocDbl.M24Prof

open scoped Pointwise

variable {Γ : Type*} [Group Γ] [MulAction Γ (Fin 24)]

open Classical in
@[expose] noncomputable def orbitSet (E : Subgroup Γ) (p : Fin 24) : Finset (Fin 24) :=
  Finset.univ.filter fun q => ∃ f ∈ E, f • p = q

open Classical in
@[expose] noncomputable def ptsOfSize (E : Subgroup Γ) (s : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Fin 24 => (orbitSet E p).card = s).card

@[expose] def ProfileOK (E : Subgroup Γ) : Prop :=
  (0 < ptsOfSize E 2 ∧ ptsOfSize E 2 ≤ 10) ∨ (0 < ptsOfSize E 4 ∧ ptsOfSize E 4 ≤ 20) ∨
    ptsOfSize E 4 = 24 ∨ ptsOfSize E 8 = 24

open Classical in
@[expose] noncomputable def fixCount (g : Γ) : ℕ := (Finset.univ.filter fun p : Fin 24 => g • p = p).card

theorem mem_orbitSet {E : Subgroup Γ} {p q : Fin 24} : q ∈ orbitSet E p ↔ ∃ f ∈ E, f • p = q := by
  classical
  simp [orbitSet]

theorem self_mem_orbitSet (E : Subgroup Γ) (p : Fin 24) : p ∈ orbitSet E p :=
  mem_orbitSet.2 ⟨1, E.one_mem, one_smul _ _⟩

theorem mem_orbitSet_symm {E : Subgroup Γ} {p q : Fin 24} (h : q ∈ orbitSet E p) :
    p ∈ orbitSet E q := by
  obtain ⟨f, hf, rfl⟩ := mem_orbitSet.1 h
  exact mem_orbitSet.2 ⟨f⁻¹, E.inv_mem hf, inv_smul_smul f p⟩

theorem mem_orbitSet_trans {E : Subgroup Γ} {p q r : Fin 24} (h1 : q ∈ orbitSet E p)
    (h2 : r ∈ orbitSet E q) : r ∈ orbitSet E p := by
  obtain ⟨f, hf, rfl⟩ := mem_orbitSet.1 h1
  obtain ⟨f', hf', rfl⟩ := mem_orbitSet.1 h2
  exact mem_orbitSet.2 ⟨f' * f, E.mul_mem hf' hf, mul_smul _ _ _⟩

theorem orbitSet_eq_of_mem {E : Subgroup Γ} {p q : Fin 24} (h : q ∈ orbitSet E p) :
    orbitSet E q = orbitSet E p := by
  ext r
  exact ⟨fun hr => mem_orbitSet_trans h hr, fun hr => mem_orbitSet_trans (mem_orbitSet_symm h) hr⟩

theorem disjoint_orbitSet {E : Subgroup Γ} {p q : Fin 24} (h : orbitSet E p ≠ orbitSet E q) :
    Disjoint (orbitSet E p) (orbitSet E q) := by
  rw [Finset.disjoint_left]
  intro r hrp hrq
  apply h
  rw [← orbitSet_eq_of_mem hrp, ← orbitSet_eq_of_mem hrq]

theorem smul_orbitSet {E : Subgroup Γ} {y : Γ} (hy : y ∈ Subgroup.normalizer (E : Set Γ))
    (p : Fin 24) : y • orbitSet E p = orbitSet E (y • p) := by
  classical
  ext q
  rw [Finset.mem_smul_finset, mem_orbitSet]
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨f, hf, rfl⟩ := mem_orbitSet.1 hr
    refine ⟨y * f * y⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 hy f).1 hf
    · simp [mul_smul]
  · rintro ⟨f, hf, rfl⟩
    refine ⟨(y⁻¹ * f * y) • p, mem_orbitSet.2 ⟨y⁻¹ * f * y, ?_, rfl⟩, ?_⟩
    · refine (Subgroup.mem_normalizer_iff.1 hy (y⁻¹ * f * y)).2 ?_
      simpa [mul_assoc] using hf
    · simp [mul_smul]

theorem orbitSet_map_conj (E : Subgroup Γ) (g : Γ) (p : Fin 24) :
    orbitSet (E.map (MulAut.conj g).toMonoidHom) (g • p) = g • orbitSet E p := by
  classical
  ext q
  rw [Finset.mem_smul_finset, mem_orbitSet]
  constructor
  · rintro ⟨f, ⟨f0, hf0, rfl⟩, rfl⟩
    refine ⟨f0 • p, mem_orbitSet.2 ⟨f0, hf0, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_smul]
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨f0, hf0, rfl⟩ := mem_orbitSet.1 hr
    refine ⟨g * f0 * g⁻¹, ⟨f0, hf0, by simp [MulAut.conj_apply]⟩, ?_⟩
    simp [mul_smul]

theorem ptsOfSize_map_conj (E : Subgroup Γ) (g : Γ) (s : ℕ) :
    ptsOfSize (E.map (MulAut.conj g).toMonoidHom) s = ptsOfSize E s := by
  classical
  unfold ptsOfSize
  refine Finset.card_bij (fun p _ => g⁻¹ • p) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have h := orbitSet_map_conj E g (g⁻¹ • p)
    rw [smul_inv_smul] at h
    rw [← hp, h, Finset.card_smul_finset]
  · intro p _ q _ h
    simpa using h
  · intro q hq
    refine ⟨g • q, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [orbitSet_map_conj E g q, Finset.card_smul_finset]
    exact hq

theorem ProfileOK.of_map_conj {E : Subgroup Γ} {g : Γ}
    (h : ProfileOK (E.map (MulAut.conj g).toMonoidHom)) : ProfileOK E := by
  unfold ProfileOK at h ⊢
  simpa only [ptsOfSize_map_conj] using h

end CFSG.Quasithin.H13.LocDbl.M24Prof
