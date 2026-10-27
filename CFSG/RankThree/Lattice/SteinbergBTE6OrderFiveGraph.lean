module

public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFour

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

theorem conj_mem_closure_rootReflection {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α) (a : WeylGroup Tag.E6) {t : WeylGroup Tag.E6}
    (ht : t ∈ Subgroup.closure {s | ∃ β ∈ (a • ·) '' S, s = rootReflection β}) :
    a⁻¹ * t * a ∈ Subgroup.closure {s | ∃ α ∈ S, s = rootReflection α} := by
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, ⟨α, hα, rfl⟩, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨α, hα, ?_⟩
    rw [rootReflection_smul_root a (hS α hα)]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have e : a⁻¹ * (x * y) * a = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : a⁻¹ * x⁻¹ * a = (a⁻¹ * x * a)⁻¹ := by group
    rw [e]
    exact inv_mem hx

section Transport

variable {K : Type*} [CommRing K]

theorem graph_conj_transport (a w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    a • (w • permLattice e6Rho (a⁻¹ • x)) =
      (a * w * e6WeylTwist a⁻¹) • permLattice e6Rho x := by
  rw [mul_smul, mul_smul, e6WeylTwist_smul, permLattice_e6Rho_e6Rho]

theorem graph_fixed_transport {z z' : Fin Tag.E6.rank → K} {a w : WeylGroup Tag.E6}
    (ha : ∀ x, charVal z' (a • x) = charVal z x)
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) :
    ∀ x, charVal z' ((a * w * e6WeylTwist a⁻¹) • permLattice e6Rho x) = charVal z' x := by
  intro x
  rw [← graph_conj_transport, ha, hb, ← ha, smul_inv_smul]

theorem charVal_inv_transport {z z' : Fin Tag.E6.rank → K} {a : WeylGroup Tag.E6}
    (ha : ∀ x, charVal z' (a • x) = charVal z x) : ∀ x, charVal z (a⁻¹ • x) = charVal z' x := by
  intro x
  rw [← ha, smul_inv_smul]

theorem graph_fixed_of_basis {z : Fin Tag.E6.rank → K} {w : WeylGroup Tag.E6}
    (h : ∀ i, charVal z (w • permLattice e6Rho (Pi.single i 1)) = z i) :
    ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x := by
  have e : ∀ y : Fin Tag.E6.rank → ℤ,
      w • permLattice e6Rho y = (weylMatrix w * rhoMatrix).mulVec y := fun y => by
    rw [← Matrix.mulVec_mulVec, ← permLattice_eq_mulVec, weylMatrix_mulVec]
  intro x
  rw [e, charVal_mulVec_eq_sum, charVal]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← h j, e, Matrix.mulVec_single_one]
  rfl

theorem charVal_transport_of_checks {z z' : Fin Tag.E6.rank → K} (ω : List (Fin 6))
    (hχ : ∀ i : Fin Tag.E6.rank,
      charVal z' ((e6Word ω).foldr (reflect Tag.E6) (Pi.single i 1)) = z i) :
    ∀ x, charVal z' ((coxeterSystem Tag.E6).wordProd (e6Word ω) • x) = charVal z x := by
  intro x
  rw [charVal_smul_eq_sum, charVal]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wordProd_e6Word_smul, hχ j]

end Transport

theorem isNegativeTransition_of_eq_neg {z : Fin Tag.E6.rank → ZMod 5} {v w t : WeylGroup Tag.E6}
    (hv : (v • ·) '' rootKernel z = parabolicRoots Tag.E6 support134)
    (ht : t ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α})
    (hbt : ∀ α ∈ rootKernel z, w • permLattice e6Rho α = -(t • α)) :
    IsNegativeTransition (fun x => v • (w • permLattice e6Rho (v⁻¹ • x))) chain134 chain134 := by
  have ht' : v * t * v⁻¹ ∈ Subgroup.closure
      {s | ∃ β ∈ parabolicRoots Tag.E6 support134, s = rootReflection β} := by
    clear hbt
    induction ht using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨α, hα, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨v • α, ?_, ?_⟩
      · rw [← hv]
        exact ⟨α, hα, rfl⟩
      · rw [rootReflection_smul_root v hα.1]
    | one => simp
    | mul x y _ _ hx hy =>
      have e : v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
    | inv x _ hx =>
      have e : v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hx
  obtain ⟨π, hπ⟩ := positive_of_mem_closure_134 ht'
  refine ⟨π, fun i j => ?_⟩
  dsimp only
  by_cases hij : i = j
  · subst hij
    rw [chainRoot_self, chainRoot_self, smul_zero]
    have : permLattice e6Rho (0 : Fin Tag.E6.rank → ℤ) = 0 := rfl
    rw [this, smul_zero, smul_zero]
  · have hc := chainRoot134_mem_parabolicRoots hij
    have hc' : v⁻¹ • chainRoot chain134 i j ∈ rootKernel z := by
      rw [← hv] at hc
      obtain ⟨α, hα, hαc⟩ := hc
      rw [← hαc, inv_smul_smul]
      exact hα
    have hπij := hπ i j
    dsimp only at hπij
    rw [hbt _ hc', smul_neg, chainRoot_swap chain134 (π i) (π j), ← hπij, mul_smul, mul_smul]

@[expose] def e6G5W0Word : List (Fin 6) := [4, 3, 2, 0, 5, 4, 3, 2]

@[expose] def e6G5W0 : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word e6G5W0Word)

@[expose] def e6G5T0Word : List (Fin 6) := [0, 2, 0, 3, 2, 0]

@[expose] def e6G5T0 : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word e6G5T0Word)

theorem e6G5W0_basis : ∀ i : Fin Tag.E6.rank,
    charVal e6F4ZJ ((e6Word e6G5W0Word).foldr (reflect Tag.E6)
      (permLattice e6Rho (Pi.single i 1))) = e6F4ZJ i := by
  decide +kernel

theorem e6G5W0_fixes : ∀ x, charVal e6F4ZJ (e6G5W0 • permLattice e6Rho x) = charVal e6F4ZJ x :=
  graph_fixed_of_basis fun i => by
    rw [e6G5W0, wordProd_e6Word_smul]
    exact e6G5W0_basis i

theorem e6G5W0_roots : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 3) → e6RootVec m i = 0) →
      (e6Word e6G5W0Word).foldr (reflect Tag.E6) (permLattice e6Rho (e6RootVec m)) =
        -((e6Word e6G5T0Word).foldr (reflect Tag.E6) (e6RootVec m)) := by
  decide +kernel

theorem e6G5W0_neg {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ parabolicRoots Tag.E6 support134) :
    e6G5W0 • permLattice e6Rho α = -(e6G5T0 • α) := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
  rw [e6G5W0, e6G5T0, wordProd_e6Word_smul, wordProd_e6Word_smul]
  exact e6G5W0_roots m fun i hi => hα.2 i ((mem_support134 i).not.2 hi)

theorem e6G5T0_mem : e6G5T0 ∈ Subgroup.closure
    {s | ∃ β ∈ parabolicRoots Tag.E6 support134, s = rootReflection β} := by
  have hS : ∀ i ∈ support134, simple Tag.E6 i ∈
      {s | ∃ β ∈ parabolicRoots Tag.E6 support134, s = rootReflection β} := fun i hi =>
    ⟨Pi.single i 1, single_mem_parabolicRoots_E6 hi, by
      rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]⟩
  have h : ∀ ω : List (Fin 6),
      (∀ i ∈ ω, e6Index i = e6Index 0 ∨ e6Index i = e6Index 2 ∨ e6Index i = e6Index 3) →
      (coxeterSystem Tag.E6).wordProd (e6Word ω) ∈ Subgroup.closure
        {s | ∃ β ∈ parabolicRoots Tag.E6 support134, s = rootReflection β} := by
    intro ω
    induction ω with
    | nil => intro _; exact one_mem _
    | cons i ω ih =>
      intro hω
      change (coxeterSystem Tag.E6).wordProd (e6Index i :: e6Word ω) ∈ _
      rw [CoxeterSystem.wordProd_cons]
      exact mul_mem (Subgroup.subset_closure
          (hS _ ((mem_support134 _).2 (hω i List.mem_cons_self))))
        (ih fun j hj => hω j (List.mem_cons_of_mem i hj))
  exact h e6G5T0Word (by decide)

theorem graph_neg_e6F4ZJ {w : WeylGroup Tag.E6}
    (hb : ∀ x, charVal e6F4ZJ (w • permLattice e6Rho x) = charVal e6F4ZJ x) :
    ∃ t ∈ Subgroup.closure {s | ∃ β ∈ parabolicRoots Tag.E6 support134, s = rootReflection β},
      ∀ α ∈ parabolicRoots Tag.E6 support134, w • permLattice e6Rho α = -(t • α) := by
  have hg : w * e6G5W0⁻¹ ∈ dualWeylStabilizer e6F4ZJ := by
    rw [mem_dualWeylStabilizer]
    intro x
    rw [mul_smul, ← permLattice_e6Rho_e6Rho (e6G5W0⁻¹ • x), hb, charVal_graph_inv e6G5W0_fixes]
  obtain ⟨hstab, -⟩ := dualWeylStabilizer_e6F4ZJ
  rw [hstab, rootKernel_e6F4ZJ] at hg
  refine ⟨w * e6G5W0⁻¹ * e6G5T0, mul_mem hg e6G5T0_mem, fun α hα => ?_⟩
  have h1 : w • permLattice e6Rho α = (w * e6G5W0⁻¹) • (e6G5W0 • permLattice e6Rho α) := by
    rw [mul_smul, inv_smul_smul]
  rw [h1, e6G5W0_neg hα, smul_neg]
  simp only [mul_smul]

theorem graph_neg_of_transport {z : Fin Tag.E6.rank → ZMod 5} {a : WeylGroup Tag.E6}
    (ha : ∀ x, charVal e6F4ZJ (a • x) = charVal z x) {w : WeylGroup Tag.E6}
    (hb : ∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) :
    ∃ t ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α},
      ∀ α ∈ rootKernel z, w • permLattice e6Rho α = -(t • α) := by
  have himg : (a • ·) '' rootKernel z = parabolicRoots Tag.E6 support134 := by
    rw [image_rootKernel_of_charVal ha, rootKernel_e6F4ZJ]
  obtain ⟨t', ht', hneg⟩ := graph_neg_e6F4ZJ (graph_fixed_transport ha hb)
  refine ⟨a⁻¹ * t' * a, conj_mem_closure_rootReflection (fun α hα => hα.1) a
    (by rw [himg]; exact ht'), fun α hα => ?_⟩
  have hα' : a • α ∈ parabolicRoots Tag.E6 support134 := by
    rw [← himg]
    exact ⟨α, hα, rfl⟩
  have h1 := hneg (a • α) hα'
  rw [← graph_conj_transport, inv_smul_smul] at h1
  calc w • permLattice e6Rho α = a⁻¹ • (a • (w • permLattice e6Rho α)) := by
        rw [inv_smul_smul]
    _ = a⁻¹ • -(t' • a • α) := by rw [h1]
    _ = -((a⁻¹ * t' * a) • α) := by rw [smul_neg, mul_smul, mul_smul]

@[expose] def E6G5Claims (z : Fin Tag.E6.rank → ZMod 5) : Prop :=
  (∃ v : WeylGroup Tag.E6, (v • ·) '' rootKernel z = parabolicRoots Tag.E6 support134) ∧
  (∀ g : WeylGroup Tag.E6, (dualMatrix (ZMod 5) g⁻¹).mulVec z = z ↔
    g ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) ∧
  Nat.card (Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) = 24 ∧
  (∃ w₀ : WeylGroup Tag.E6,
    (((rhoMatrix * weylMatrix w₀⁻¹).map (Int.cast : ℤ → ZMod 5)).transpose).mulVec z = z ∧
    ∀ w : WeylGroup Tag.E6,
      (((rhoMatrix * weylMatrix w⁻¹).map (Int.cast : ℤ → ZMod 5)).transpose).mulVec z = z ↔
        w * w₀⁻¹ ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) ∧
  ∀ w : WeylGroup Tag.E6,
    (((rhoMatrix * weylMatrix w⁻¹).map (Int.cast : ℤ → ZMod 5)).transpose).mulVec z = z →
      (fun x => w • permLattice e6Rho x) '' rootKernel z = rootKernel z ∧
      (∃ t ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α},
        ∀ α ∈ rootKernel z, w • permLattice e6Rho α = -(t • α)) ∧
      ∀ v : WeylGroup Tag.E6, (v • ·) '' rootKernel z = parabolicRoots Tag.E6 support134 →
        IsNegativeTransition (fun x => v • (w • permLattice e6Rho (v⁻¹ • x))) chain134 chain134

theorem E6G5Claims_smul {z : Fin Tag.E6.rank → ZMod 5} {s : ZMod 5} (hs : s ≠ 0)
    (h : E6G5Claims z) : E6G5Claims (s • z) := by
  have hfix : ∀ M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) (ZMod 5),
      M.mulVec (s • z) = s • z ↔ M.mulVec z = z := fun M => by
    rw [Matrix.mulVec_smul]
    exact (smul_right_injective _ hs).eq_iff
  obtain ⟨h1, h2, h3, ⟨w₀, hw₀, hcos⟩, h5⟩ := h
  refine ⟨by rw [rootKernel_smul hs]; exact h1, fun g => by
    rw [rootKernel_smul hs, hfix]; exact h2 g, by rw [rootKernel_smul hs]; exact h3,
    ⟨w₀, (hfix _).2 hw₀, fun w => by rw [rootKernel_smul hs, hfix]; exact hcos w⟩,
    fun w hw => by rw [rootKernel_smul hs]; exact h5 w ((hfix _).1 hw)⟩

theorem E6G5Claims_of_transport {z : Fin Tag.E6.rank → ZMod 5} {a : WeylGroup Tag.E6}
    (ha : ∀ x, charVal e6F4ZJ (a • x) = charVal z x) (hcl : E6F4Claims z) : E6G5Claims z := by
  obtain ⟨-, hstab, hcard⟩ := hcl
  have himg : (a • ·) '' rootKernel z = parabolicRoots Tag.E6 support134 := by
    rw [image_rootKernel_of_charVal ha, rootKernel_e6F4ZJ]
  set w₀ := a⁻¹ * e6G5W0 * e6WeylTwist a⁻¹⁻¹ with hw₀def
  have hw₀ : ∀ x, charVal z (w₀ • permLattice e6Rho x) = charVal z x :=
    graph_fixed_transport (charVal_inv_transport ha) e6G5W0_fixes
  have hstab' : ∀ g, g ∈ dualWeylStabilizer z ↔
      g ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := fun g => by
    rw [mem_dualWeylStabilizer_iff_dualMatrix, hstab]
  have hcos : ∀ w : WeylGroup Tag.E6,
      (∀ x, charVal z (w • permLattice e6Rho x) = charVal z x) ↔
        w * w₀⁻¹ ∈ dualWeylStabilizer z := by
    intro w
    constructor
    · intro hb x
      rw [mul_smul, ← permLattice_e6Rho_e6Rho (w₀⁻¹ • x), hb, charVal_graph_inv hw₀]
    · intro hg x
      have h1 : w • permLattice e6Rho x = (w * w₀⁻¹) • (w₀ • permLattice e6Rho x) := by
        rw [mul_smul, inv_smul_smul]
      rw [h1, hg, hw₀]
  refine ⟨⟨a, himg⟩, hstab, hcard, ⟨w₀, graph_dual_fixed_iff.2 hw₀, fun w => by
    rw [graph_dual_fixed_iff, hcos, hstab']⟩, fun w hwm => ?_⟩
  have hb := graph_dual_fixed_iff.1 hwm
  obtain ⟨t, ht, hbt⟩ := graph_neg_of_transport ha hb
  exact ⟨image_graph_rootKernel hb, ⟨t, ht, hbt⟩,
    fun v hv => isNegativeTransition_of_eq_neg hv ht hbt⟩

theorem E6G5Claims_of_checks {z : Fin Tag.E6.rank → ZMod 5} (ω : List (Fin 6))
    (hχ : ∀ i : Fin Tag.E6.rank,
      charVal e6F4ZJ ((e6Word ω).foldr (reflect Tag.E6) (Pi.single i 1)) = z i)
    (hcl : E6F4Claims z) : E6G5Claims z :=
  E6G5Claims_of_transport (charVal_transport_of_checks ω hχ) hcl

theorem E6G5Claims_2_1_0 : E6G5Claims (e6F4Z 2 1 0) :=
  E6G5Claims_of_checks [1, 3, 4, 3, 2, 5, 4, 3, 1] (by decide +kernel) e6F4_rep_2_1_0

theorem E6G5Claims_2_1_1 : E6G5Claims (e6F4Z 2 1 1) :=
  E6G5Claims_of_checks [4, 3, 1, 2, 0, 3, 2, 5, 4, 3, 1, 2, 0, 3, 4, 5] (by decide +kernel)
    e6F4_rep_2_1_1

theorem E6G5Claims_2_1_2 : E6G5Claims (e6F4Z 2 1 2) :=
  E6G5Claims_of_checks [4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5] (by decide +kernel)
    e6F4_rep_2_1_2

theorem E6G5Claims_2_1_3 : E6G5Claims (e6F4Z 2 1 3) :=
  E6G5Claims_of_checks [1, 3, 4, 3, 1, 2, 0, 5, 4] (by decide +kernel) e6F4_rep_2_1_3

theorem E6G5Claims_2_1_4 : E6G5Claims (e6F4Z 2 1 4) :=
  E6G5Claims_of_checks [1, 3, 2, 0, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3] (by decide +kernel)
    e6F4_rep_2_1_4

theorem E6G5Claims_2_0_1 : E6G5Claims (e6F4Z 2 0 1) :=
  E6G5Claims_of_checks [1, 3, 2, 4, 3, 1, 2, 5, 4, 3, 2, 0] (by decide +kernel) e6F4_rep_2_0_1

theorem E6G5Claims_3_1_0 : E6G5Claims (e6F4Z 3 1 0) :=
  E6G5Claims_of_checks [1, 3, 4, 3, 2, 5, 4, 3, 1, 2] (by decide +kernel) e6F4_rep_3_1_0

theorem E6G5Claims_3_1_1 : E6G5Claims (e6F4Z 3 1 1) :=
  E6G5Claims_of_checks [4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5] (by decide +kernel)
    e6F4_rep_3_1_1

theorem E6G5Claims_3_1_2 : E6G5Claims (e6F4Z 3 1 2) :=
  E6G5Claims_of_checks [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3]
    (by decide +kernel) e6F4_rep_3_1_2

theorem E6G5Claims_3_1_3 : E6G5Claims (e6F4Z 3 1 3) :=
  E6G5Claims_of_checks [4, 3, 2, 0, 5, 4, 3, 1, 2, 0, 3, 2, 4, 5] (by decide +kernel)
    e6F4_rep_3_1_3

theorem E6G5Claims_3_1_4 : E6G5Claims (e6F4Z 3 1 4) :=
  E6G5Claims_of_checks [1, 3, 4, 3, 5, 4, 3, 1, 2, 0] (by decide +kernel) e6F4_rep_3_1_4

theorem E6G5Claims_3_0_1 : E6G5Claims (e6F4Z 3 0 1) :=
  E6G5Claims_of_checks [1, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3] (by decide +kernel)
    e6F4_rep_3_0_1

theorem E6_order_five_graph_stabilizers_reverse_A3_orientation {r : ZMod 5} (hr : r = 2 ∨ r = 3)
    {z : Fin Tag.E6.rank → ZMod 5} (hz0 : z ≠ 0)
    (hz : (dualMatrix (ZMod 5) e6F4U).mulVec z = r • z) :
    (∃ v : WeylGroup Tag.E6, (v • ·) '' rootKernel z = parabolicRoots Tag.E6 support134) ∧
    (∀ g : WeylGroup Tag.E6, (dualMatrix (ZMod 5) g⁻¹).mulVec z = z ↔
      g ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) ∧
    Nat.card (Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) = 24 ∧
    (∃ w₀ : WeylGroup Tag.E6,
      (((rhoMatrix * weylMatrix w₀⁻¹).map (Int.cast : ℤ → ZMod 5)).transpose).mulVec z = z ∧
      ∀ w : WeylGroup Tag.E6,
        (((rhoMatrix * weylMatrix w⁻¹).map (Int.cast : ℤ → ZMod 5)).transpose).mulVec z = z ↔
          w * w₀⁻¹ ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}) ∧
    ∀ w : WeylGroup Tag.E6,
      (((rhoMatrix * weylMatrix w⁻¹).map (Int.cast : ℤ → ZMod 5)).transpose).mulVec z = z →
        (fun x => w • permLattice e6Rho x) '' rootKernel z = rootKernel z ∧
        (∃ t ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α},
          ∀ α ∈ rootKernel z, w • permLattice e6Rho α = -(t • α)) ∧
        ∀ v : WeylGroup Tag.E6, (v • ·) '' rootKernel z = parabolicRoots Tag.E6 support134 →
          IsNegativeTransition (fun x => v • (w • permLattice e6Rho (v⁻¹ • x)))
            chain134 chain134 := by
  show E6G5Claims z
  obtain ⟨s, hs, hrep⟩ := e6F4_eigen_rep hz0 hz
  rcases hrep with ⟨j, rfl⟩ | rfl
  · refine E6G5Claims_smul hs ?_
    rcases hr with rfl | rfl <;> fin_cases j
    exacts [E6G5Claims_2_1_0, E6G5Claims_2_1_1, E6G5Claims_2_1_2, E6G5Claims_2_1_3,
      E6G5Claims_2_1_4, E6G5Claims_3_1_0, E6G5Claims_3_1_1, E6G5Claims_3_1_2, E6G5Claims_3_1_3,
      E6G5Claims_3_1_4]
  · refine E6G5Claims_smul hs ?_
    rcases hr with rfl | rfl
    exacts [E6G5Claims_2_0_1, E6G5Claims_3_0_1]

end CFSG.RankThree.Lattice
