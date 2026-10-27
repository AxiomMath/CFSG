module

public import CFSG.RankThree.PartOne.KE.E7ThreeNodes
public import CFSG.RankThree.PartOne.KE.A5Interface
public import CFSG.RankThree.PartOne.KE.E7A2NativeModule
public import CFSG.RankThree.PartOne.KE.E7ThreeLatticeInputs

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix Pointwise

@[expose] def e7T3J : ℕ → Set (Fin Tag.E7.rank)
  | 0 => support13
  | 1 => a1Nodes Tag.E7
  | 2 => d4Nodes Tag.E7
  | _ => a5Nodes Tag.E7

@[expose] def e7T3Beta : ℕ → Bool → Equiv.Perm (Fin Tag.E7.rank)
  | 1, false => List.formPerm [1, 4, 6]
  | 1, true => List.formPerm [1, 6, 4]
  | 2, false => List.formPerm [1, 2, 4]
  | 2, true => List.formPerm [1, 4, 2]
  | _, _ => 1

theorem mem_e7T3J_iff {kind : ℕ} (hk : kind < 4) (i : Fin Tag.E7.rank) :
    i ∈ e7T3J kind ↔ i.val ∈ e7T3Nodes kind := by
  obtain ⟨i, hi⟩ := i
  have hi7 : i < 7 := hi
  interval_cases kind
  · rw [e7T3J, mem_support13, Fin.ext_iff, Fin.ext_iff]
    have h0 : (e7Index 0).val = 0 := rfl
    have h2 : (e7Index 2).val = 2 := rfl
    rw [h0, h2]
    simp [e7T3Nodes]
  all_goals
    interval_cases i <;> simp [e7T3J, e7T3Nodes, a1Nodes, d4Nodes, a5Nodes]

theorem permLattice_one {τ : Tag} (x : Fin τ.rank → ℤ) : permLattice (1 : Equiv.Perm (Fin τ.rank)) x = x :=
  rfl

theorem permLattice_cycle_toVec (σ : Equiv.Perm (Fin Tag.E7.rank)) (a b c : ℕ)
    (hσ : ∀ k : Fin Tag.E7.rank, ((σ.symm k : Fin Tag.E7.rank) : ℕ) =
      if k.val = a then c else if k.val = b then a else if k.val = c then b else k.val)
    (l : List ℤ) :
    permLattice σ (toVec Tag.E7.rank l) = toVec Tag.E7.rank (e7perm3 a b c l) := by
  funext k
  simp only [permLattice, Function.comp_apply]
  simp [toVec, vget, e7perm3, hσ k]

theorem e7T3_permLattice {kind : ℕ} (hk : kind < 4) (rot : Bool) (l : List ℤ) :
    permLattice (e7T3Beta kind rot) (toVec Tag.E7.rank l) =
      toVec Tag.E7.rank (e7T3Perm kind rot l) := by
  interval_cases kind
  · simp [e7T3Beta, e7T3Perm, permLattice_one]
  · cases rot
    · simp only [e7T3Beta, e7T3Perm, ite_true, Bool.false_eq_true, ite_false]
      exact permLattice_cycle_toVec _ 1 4 6 (by decide) l
    · simp only [e7T3Beta, e7T3Perm, ite_true]
      exact permLattice_cycle_toVec _ 1 6 4 (by decide) l
  · cases rot
    · simp only [e7T3Beta, e7T3Perm]
      exact permLattice_cycle_toVec _ 1 2 4 (by decide) l
    · simp only [e7T3Beta, e7T3Perm]
      exact permLattice_cycle_toVec _ 1 4 2 (by decide) l
  · simp [e7T3Beta, e7T3Perm, permLattice_one]

theorem parabolicRoots_e7T3J {kind : ℕ} (hk : kind < 4) :
    parabolicRoots Tag.E7 (e7T3J kind) =
      {α | ∃ l ∈ e7StdRoots (e7T3Nodes kind), α = toVec Tag.E7.rank l} := by
  ext α
  constructor
  · rintro ⟨hα, hsupp⟩
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
    refine ⟨l, ?_, rfl⟩
    simp only [e7StdRoots, List.mem_filter]
    refine ⟨hl, ?_⟩
    rw [List.all_eq_true]
    intro k hk7
    have hk7' : k < 7 := List.mem_range.1 hk7
    by_cases hkJ : k ∈ e7T3Nodes kind
    · simp [hkJ]
    · have := hsupp ⟨k, hk7'⟩ (by rwa [mem_e7T3J_iff hk])
      simpa [hkJ, toVec] using this
  · rintro ⟨l, hl, rfl⟩
    simp only [e7StdRoots, List.mem_filter] at hl
    refine ⟨isRoot_toVec hl.1, fun i hi => ?_⟩
    have := (List.all_eq_true.1 hl.2) i.val (List.mem_range.2 i.isLt)
    have hiJ : i.val ∉ e7T3Nodes kind := fun h => hi ((mem_e7T3J_iff hk i).2 h)
    simpa [hiJ, toVec] using this

theorem wordProd_mem_parabolicWeylGroup {J : Set (Fin Tag.E7.rank)} {u : List (Fin Tag.E7.rank)}
    (hu : ∀ x ∈ u, x ∈ J) : (coxeterSystem Tag.E7).wordProd u ∈ parabolicWeylGroup Tag.E7 J := by
  unfold CoxeterSystem.wordProd
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨i, hu i hi, rfl⟩

theorem comp_action {w : List (Fin Tag.E7.rank)} {cm : E7T3Comp}
    (h : cm.Good e7T3Word w) :
    (coxeterSystem Tag.E7).wordProd cm.u ∈ parabolicWeylGroup Tag.E7 (e7T3J cm.kind) ∧
      ∀ α ∈ parabolicRoots Tag.E7 (e7T3J cm.kind),
        (((coxeterSystem Tag.E7).wordProd w)⁻¹ * (coxeterSystem Tag.E7).wordProd e7T3Word *
          (coxeterSystem Tag.E7).wordProd w) • α =
          (coxeterSystem Tag.E7).wordProd cm.u • permLattice (e7T3Beta cm.kind cm.rot) α := by
  obtain ⟨hu, hk, -, hroots⟩ := h
  refine ⟨wordProd_mem_parabolicWeylGroup fun x hx => (mem_e7T3J_iff hk x).2 (hu x hx),
    fun α hα => ?_⟩
  rw [parabolicRoots_e7T3J hk] at hα
  obtain ⟨l, hl, rfl⟩ := hα
  have e : ((coxeterSystem Tag.E7).wordProd w)⁻¹ * (coxeterSystem Tag.E7).wordProd e7T3Word *
      (coxeterSystem Tag.E7).wordProd w =
        (coxeterSystem Tag.E7).wordProd (w.reverse ++ e7T3Word ++ w) := by
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
      CoxeterSystem.wordProd_reverse]
  rw [e, wordProd_smul_toVec7, e7T3_permLattice hk, wordProd_smul_toVec7, hroots l hl]

theorem mem_rootList_iff {c : E7T3Cert}
    (hk : ∀ cm ∈ c.comps, cm.kind < 4) (α : Fin Tag.E7.rank → ℤ) :
    (∃ l ∈ c.rootList, α = toVec Tag.E7.rank l) ↔
      ∃ cm ∈ c.comps, ∃ γ ∈ parabolicRoots Tag.E7 (e7T3J cm.kind),
        α = (coxeterSystem Tag.E7).wordProd c.w • γ := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simp only [E7T3Cert.rootList, List.mem_flatMap, List.mem_map] at hl
    obtain ⟨cm, hcm, l₀, hl₀, rfl⟩ := hl
    refine ⟨cm, hcm, toVec Tag.E7.rank l₀, ?_, (wordProd_smul_toVec7 c.w l₀).symm⟩
    rw [parabolicRoots_e7T3J (hk cm hcm)]
    exact ⟨l₀, hl₀, rfl⟩
  · rintro ⟨cm, hcm, γ, hγ, rfl⟩
    rw [parabolicRoots_e7T3J (hk cm hcm)] at hγ
    obtain ⟨l₀, hl₀, rfl⟩ := hγ
    refine ⟨lmulVec Tag.E7.rank (e7wl c.w) l₀, ?_, (wordProd_smul_toVec7 c.w l₀)⟩
    simp only [E7T3Cert.rootList, List.mem_flatMap, List.mem_map]
    exact ⟨cm, hcm, l₀, hl₀, rfl⟩

end CFSG.RankThree.PartOne.KE
