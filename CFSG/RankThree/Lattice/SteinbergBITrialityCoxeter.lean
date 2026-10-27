module

public import CFSG.RankThree.Lattice.SteinbergBIChecks

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix

@[expose] def trialityPermMat : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]

theorem trialityPermMat_mulVec (v : Fin 4 → ℤ) :
    trialityPermMat *ᵥ v = permLattice TwistTag.D4.perm v := by
  funext a
  fin_cases a <;>
    simp [trialityPermMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, permLattice,
      TwistTag.perm] <;> rfl

@[expose] def d4Refl (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ := reflMat .D4 i

@[expose] def trialityCoxeter : Matrix (Fin 4) (Fin 4) ℤ :=
  d4Refl 2 * d4Refl 0 * trialityPermMat

@[expose] def trialityCoxeterList : List (List ℤ) :=
  [[0, 0, 1, -1], [1, 0, 0, 0], [1, 1, 0, -1], [0, 1, 0, 0]]

theorem trialityCoxeter_eq : trialityCoxeter = toMat 4 trialityCoxeterList := by
  decide +kernel

theorem trialityCoxeter_pow_six : trialityCoxeter ^ 6 = -1 := by
  rw [trialityCoxeter_eq, ← toMat_lpow]
  have h : lpow 4 trialityCoxeterList 6 =
      [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]] := by
    decide +kernel
  rw [h]
  decide +kernel

theorem trialityCoxeter_pow_twelve : trialityCoxeter ^ 12 = 1 := by
  rw [show 12 = 6 * 2 by rfl, pow_mul, trialityCoxeter_pow_six, neg_one_sq]

theorem trialityCoxeter_relation :
    trialityCoxeter ^ 4 - trialityCoxeter ^ 2 + 1 = 0 := by
  rw [trialityCoxeter_eq, ← toMat_lpow, ← toMat_lpow]
  have h4 : lpow 4 trialityCoxeterList 4 =
      [[0, 0, 0, -1], [0, -1, 1, -1], [1, -1, 0, -1], [1, 0, 0, -1]] := by
    decide +kernel
  have h2 : lpow 4 trialityCoxeterList 2 =
      [[1, 0, 0, -1], [0, 0, 1, -1], [1, -1, 1, -1], [1, 0, 0, 0]] := by
    decide +kernel
  rw [h4, h2]
  decide +kernel

theorem orderOf_trialityCoxeter : orderOf trialityCoxeter = 12 := by
  rw [trialityCoxeter_eq]
  exact orderOf_toMat_eq (by norm_num) (by decide +kernel) (by decide +kernel)

theorem det_trialityCoxeter : trialityCoxeter.det = 1 := by
  rw [trialityCoxeter_eq, det_toMat_eq]
  decide +kernel

@[expose] def trialityOrbitOne : List (List ℤ) :=
  lorbit 4 trialityCoxeterList [1, 0, 0, 0] 12

@[expose] def trialityOrbitFour : List (List ℤ) :=
  lorbit 4 trialityCoxeterList [0, 0, 0, 1] 12

theorem toVec_e₁ : toVec 4 [1, 0, 0, 0] = Pi.single (0 : Fin 4) 1 := by
  decide +kernel

theorem toVec_e₄ : toVec 4 [0, 0, 0, 1] = Pi.single (3 : Fin 4) 1 := by
  decide +kernel

theorem trialityOrbit_nodup : trialityOrbitOne.Nodup ∧ trialityOrbitFour.Nodup := by
  decide +kernel

theorem trialityOrbit_disjoint : ∀ l ∈ trialityOrbitOne, l ∉ trialityOrbitFour := by
  decide +kernel

theorem trialityOrbit_cover :
    ∀ l ∈ Tag.D4.artifactRoots, l ∈ trialityOrbitOne ∨ l ∈ trialityOrbitFour := by
  decide +kernel

theorem trialityOrbit_roots :
    (∀ l ∈ trialityOrbitOne, l ∈ Tag.D4.artifactRoots) ∧
      ∀ l ∈ trialityOrbitFour, l ∈ Tag.D4.artifactRoots := by
  decide +kernel

theorem det_orbitMat_trialityOrbit :
    (orbitMat trialityCoxeter (Pi.single (0 : Fin 4) 1) 4).det = 1 ∧
      (orbitMat trialityCoxeter (Pi.single (3 : Fin 4) 1) 4).det = 1 := by
  rw [← toVec_e₁, ← toVec_e₄, trialityCoxeter_eq]
  refine ⟨?_, ?_⟩
  · rw [orbitMat_eq_toMat, det_toMat_eq]
    decide +kernel
  · rw [orbitMat_eq_toMat, det_toMat_eq]
    decide +kernel

theorem mem_lorbit_iff {n : ℕ} {A : List (List ℤ)} {x : List ℤ} {m : ℕ} {l : List ℤ} :
    l ∈ lorbit n A x m ↔ ∃ j < m, l = lmulVec n (lpow n A j) x := by
  simp only [lorbit, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem toVec_mem_lorbit {n : ℕ} {A : List (List ℤ)} {x : List ℤ} {m : ℕ} {l : List ℤ}
    (h : l ∈ lorbit n A x m) : ∃ j < m, toVec n l = (toMat n A ^ j) *ᵥ toVec n x := by
  obtain ⟨j, hj, rfl⟩ := mem_lorbit_iff.1 h
  exact ⟨j, hj, by rw [toVec_lmulVec, toMat_lpow]⟩

theorem triality_twisted_Coxeter_unimodular_root_orbits :
    trialityCoxeter = !![0, 0, 1, -1; 1, 0, 0, 0; 1, 1, 0, -1; 0, 1, 0, 0] ∧
    trialityCoxeter.det = 1 ∧ trialityCoxeter ^ 4 - trialityCoxeter ^ 2 + 1 = 0 ∧
    trialityCoxeter ^ 6 = -1 ∧ orderOf trialityCoxeter = 12 ∧
    {v : Fin 4 → ℤ | IsRoot .D4 v} =
      {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (0 : Fin 4) 1} ∪
        {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (3 : Fin 4) 1} ∧
    Disjoint {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (0 : Fin 4) 1}
      {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (3 : Fin 4) 1} ∧
    {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (0 : Fin 4) 1}.ncard = 12 ∧
    {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (3 : Fin 4) 1}.ncard = 12 ∧
    ∀ α : Fin 4 → ℤ, IsRoot .D4 α →
      (LinearIndependent ℤ (fun j : Fin 4 => (trialityCoxeter ^ (j : ℕ)) *ᵥ α) ∧
        Submodule.span ℤ (Set.range fun j : Fin 4 => (trialityCoxeter ^ (j : ℕ)) *ᵥ α) = ⊤) ∧
      (Matrix.of fun i (j : Fin 4) => ((trialityCoxeter ^ (j : ℕ)) *ᵥ α) i).det = 1 := by
  have hw12 := trialityCoxeter_pow_twelve
  have hO : ∀ (x : List ℤ) (hx : x = [1, 0, 0, 0] ∨ x = [0, 0, 0, 1]) (v : Fin 4 → ℤ),
      (∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ toVec 4 x) ↔
        ∃ l ∈ lorbit 4 trialityCoxeterList x 12, v = toVec 4 l := by
    intro x _ v
    rw [mem_powOrbit_iff (by norm_num) hw12]
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨_, mem_lorbit_iff.2 ⟨j, hj, rfl⟩, ?_⟩
      rw [toVec_lmulVec, toMat_lpow, ← trialityCoxeter_eq]
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨j, hj, hjl⟩ := toVec_mem_lorbit hl
      exact ⟨j, hj, by rw [hjl, ← trialityCoxeter_eq]⟩
  have hO₁ := hO _ (Or.inl rfl)
  have hO₄ := hO _ (Or.inr rfl)
  rw [toVec_e₁] at hO₁
  rw [toVec_e₄] at hO₄
  have hroots : {v : Fin 4 → ℤ | IsRoot .D4 v} =
      {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (0 : Fin 4) 1} ∪
        {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (3 : Fin 4) 1} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_union, hO₁, hO₄]
    constructor
    · intro hv
      obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hv
      rcases trialityOrbit_cover l hl with h | h
      · exact Or.inl ⟨l, h, rfl⟩
      · exact Or.inr ⟨l, h, rfl⟩
    · rintro (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩)
      · exact isRoot_toVec (trialityOrbit_roots.1 l hl)
      · exact isRoot_toVec (trialityOrbit_roots.2 l hl)
  have hlen : ∀ l, l ∈ trialityOrbitOne ∨ l ∈ trialityOrbitFour → l.length = 4 := by
    intro l hl
    rcases hl with hl | hl
    · obtain ⟨j, -, rfl⟩ := mem_lorbit_iff.1 hl
      exact length_lmulVec _ _
    · obtain ⟨j, -, rfl⟩ := mem_lorbit_iff.1 hl
      exact length_lmulVec _ _
  have hdisj : Disjoint {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (0 : Fin 4) 1}
      {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (3 : Fin 4) 1} := by
    rw [Set.disjoint_left]
    intro v hv₁ hv₄
    simp only [Set.mem_ofPred_eq, hO₁, hO₄] at hv₁ hv₄
    obtain ⟨l, hl, rfl⟩ := hv₁
    obtain ⟨l', hl', hll'⟩ := hv₄
    have h := toVec_injective_of_length (hlen l (Or.inl hl)) (hlen l' (Or.inr hl')) hll'
    exact trialityOrbit_disjoint l hl (h ▸ hl')
  have hcard₁ : {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (0 : Fin 4) 1}.ncard = 12 := by
    rw [← toVec_e₁, trialityCoxeter_eq]
    exact ncard_powOrbit (by norm_num) (by rw [← trialityCoxeter_eq]; exact hw12)
      trialityOrbit_nodup.1
  have hcard₄ : {v | ∃ j : ℕ, v = (trialityCoxeter ^ j) *ᵥ Pi.single (3 : Fin 4) 1}.ncard = 12 := by
    rw [← toVec_e₄, trialityCoxeter_eq]
    exact ncard_powOrbit (by norm_num) (by rw [← trialityCoxeter_eq]; exact hw12)
      trialityOrbit_nodup.2
  refine ⟨by rw [trialityCoxeter_eq]; decide +kernel, det_trialityCoxeter, trialityCoxeter_relation,
    trialityCoxeter_pow_six, orderOf_trialityCoxeter, hroots, hdisj, hcard₁, hcard₄,
    fun α hα => ?_⟩
  have hdet : (orbitMat trialityCoxeter α 4).det = 1 := by
    have hα' : α ∈ {v : Fin 4 → ℤ | IsRoot .D4 v} := hα
    rw [hroots] at hα'
    rcases hα' with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [det_orbitMat_pow_mulVec, det_trialityCoxeter, one_pow, one_mul,
        det_orbitMat_trialityOrbit.1]
    · rw [det_orbitMat_pow_mulVec, det_trialityCoxeter, one_pow, one_mul,
        det_orbitMat_trialityOrbit.2]
  refine ⟨(isBasis_iff_isUnit_det trialityCoxeter α).2 (by rw [hdet]; exact isUnit_one), hdet⟩

end CFSG.RankThree.Lattice
