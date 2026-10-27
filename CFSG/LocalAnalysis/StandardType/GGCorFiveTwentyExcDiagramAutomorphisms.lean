module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcTreeSignGauge

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def tagCartanEntry (τ : Tag) (i j : Fin τ.rank) : ℤ := τ.cartan i j

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
theorem cartan_embedding_E6 :
    ∀ a3 : Fin 6, ∀ a1 : Fin 6, tagCartanEntry .E6 a1 a3 = -1 → ∀ a2 : Fin 6,
    tagCartanEntry .E6 a2 a3 = -1 → tagCartanEntry .E6 a2 a1 = 0 → ∀ a4 : Fin 6,
    tagCartanEntry .E6 a4 a3 = -1 → tagCartanEntry .E6 a4 a1 = 0 → tagCartanEntry .E6 a4 a2 = 0 →
    ∀ a0 : Fin 6, tagCartanEntry .E6 a0 a3 = 0 → tagCartanEntry .E6 a0 a1 = 0 →
    tagCartanEntry .E6 a0 a2 = -1 → tagCartanEntry .E6 a0 a4 = 0 → ∀ a5 : Fin 6,
    tagCartanEntry .E6 a5 a3 = 0 → tagCartanEntry .E6 a5 a1 = 0 → tagCartanEntry .E6 a5 a2 = 0 →
    tagCartanEntry .E6 a5 a4 = -1 → tagCartanEntry .E6 a5 a0 = 0 →
    (a0 = 0 ∧ a1 = 1 ∧ a2 = 2 ∧ a3 = 3 ∧ a4 = 4 ∧ a5 = 5) ∨
      (a0 = 5 ∧ a1 = 1 ∧ a2 = 4 ∧ a3 = 3 ∧ a4 = 2 ∧ a5 = 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
theorem cartan_embedding_E7 :
    ∀ a3 : Fin 7, ∀ a1 : Fin 7, tagCartanEntry .E7 a1 a3 = -1 → ∀ a2 : Fin 7,
    tagCartanEntry .E7 a2 a3 = -1 → tagCartanEntry .E7 a2 a1 = 0 → ∀ a4 : Fin 7,
    tagCartanEntry .E7 a4 a3 = -1 → tagCartanEntry .E7 a4 a1 = 0 → tagCartanEntry .E7 a4 a2 = 0 →
    ∀ a0 : Fin 7, tagCartanEntry .E7 a0 a3 = 0 → tagCartanEntry .E7 a0 a1 = 0 →
    tagCartanEntry .E7 a0 a2 = -1 → tagCartanEntry .E7 a0 a4 = 0 → ∀ a5 : Fin 7,
    tagCartanEntry .E7 a5 a3 = 0 → tagCartanEntry .E7 a5 a1 = 0 → tagCartanEntry .E7 a5 a2 = 0 →
    tagCartanEntry .E7 a5 a4 = -1 → tagCartanEntry .E7 a5 a0 = 0 → ∀ a6 : Fin 7,
    tagCartanEntry .E7 a6 a3 = 0 → tagCartanEntry .E7 a6 a1 = 0 → tagCartanEntry .E7 a6 a2 = 0 →
    tagCartanEntry .E7 a6 a4 = 0 → tagCartanEntry .E7 a6 a0 = 0 → tagCartanEntry .E7 a6 a5 = -1 →
    a0 = 0 ∧ a1 = 1 ∧ a2 = 2 ∧ a3 = 3 ∧ a4 = 4 ∧ a5 = 5 ∧ a6 = 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 100000 in
theorem cartan_embedding_E8 :
    ∀ a3 : Fin 8, ∀ a1 : Fin 8, tagCartanEntry .E8 a1 a3 = -1 → ∀ a2 : Fin 8,
    tagCartanEntry .E8 a2 a3 = -1 → tagCartanEntry .E8 a2 a1 = 0 → ∀ a4 : Fin 8,
    tagCartanEntry .E8 a4 a3 = -1 → tagCartanEntry .E8 a4 a1 = 0 → tagCartanEntry .E8 a4 a2 = 0 →
    ∀ a0 : Fin 8, tagCartanEntry .E8 a0 a3 = 0 → tagCartanEntry .E8 a0 a1 = 0 →
    tagCartanEntry .E8 a0 a2 = -1 → tagCartanEntry .E8 a0 a4 = 0 → ∀ a5 : Fin 8,
    tagCartanEntry .E8 a5 a3 = 0 → tagCartanEntry .E8 a5 a1 = 0 → tagCartanEntry .E8 a5 a2 = 0 →
    tagCartanEntry .E8 a5 a4 = -1 → tagCartanEntry .E8 a5 a0 = 0 → ∀ a6 : Fin 8,
    tagCartanEntry .E8 a6 a3 = 0 → tagCartanEntry .E8 a6 a1 = 0 → tagCartanEntry .E8 a6 a2 = 0 →
    tagCartanEntry .E8 a6 a4 = 0 → tagCartanEntry .E8 a6 a0 = 0 → tagCartanEntry .E8 a6 a5 = -1 →
    ∀ a7 : Fin 8, tagCartanEntry .E8 a7 a3 = 0 → tagCartanEntry .E8 a7 a1 = 0 →
    tagCartanEntry .E8 a7 a2 = 0 → tagCartanEntry .E8 a7 a4 = 0 → tagCartanEntry .E8 a7 a0 = 0 →
    tagCartanEntry .E8 a7 a5 = 0 → tagCartanEntry .E8 a7 a6 = -1 →
    a0 = 0 ∧ a1 = 1 ∧ a2 = 2 ∧ a3 = 3 ∧ a4 = 4 ∧ a5 = 5 ∧ a6 = 6 ∧ a7 = 7 := by
  decide +kernel

@[expose] def excDiagramSigmaE6 : Equiv.Perm (Fin Tag.E6.rank) :=
  Equiv.swap (0 : Fin 6) 5 * Equiv.swap (2 : Fin 6) 4

theorem perm_eq_one_of_cartan_E7 (π : Equiv.Perm (Fin Tag.E7.rank))
    (h : ∀ i j, Tag.E7.cartan (π i) (π j) = Tag.E7.cartan i j) : π = 1 := by
  have hh : ∀ i j, tagCartanEntry .E7 (π i) (π j) = tagCartanEntry .E7 i j := h
  obtain ⟨k0, k1, k2, k3, k4, k5, k6⟩ :=
    cartan_embedding_E7 (π (3 : Fin 7)) (π (1 : Fin 7)) ((hh _ _).trans (by decide)) (π (2 : Fin 7))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) (π (4 : Fin 7))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    (π (0 : Fin 7)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) (π (5 : Fin 7))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) (π (6 : Fin 7))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
  refine Equiv.ext fun i => ?_
  fin_cases i <;> first | exact k0 | exact k1 | exact k2 | exact k3 | exact k4 | exact k5 | exact k6

theorem perm_eq_one_of_cartan_E8 (π : Equiv.Perm (Fin Tag.E8.rank))
    (h : ∀ i j, Tag.E8.cartan (π i) (π j) = Tag.E8.cartan i j) : π = 1 := by
  have hh : ∀ i j, tagCartanEntry .E8 (π i) (π j) = tagCartanEntry .E8 i j := h
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7⟩ :=
    cartan_embedding_E8 (π (3 : Fin 8)) (π (1 : Fin 8)) ((hh _ _).trans (by decide)) (π (2 : Fin 8))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) (π (4 : Fin 8))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    (π (0 : Fin 8)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) (π (5 : Fin 8))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) (π (6 : Fin 8))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    (π (7 : Fin 8)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
  refine Equiv.ext fun i => ?_
  fin_cases i <;>
    first | exact k0 | exact k1 | exact k2 | exact k3 | exact k4 | exact k5 | exact k6 | exact k7

theorem perm_eq_one_or_eq_sigma_of_cartan_E6 (π : Equiv.Perm (Fin Tag.E6.rank))
    (h : ∀ i j, Tag.E6.cartan (π i) (π j) = Tag.E6.cartan i j) : π = 1 ∨ π = excDiagramSigmaE6 := by
  have hh : ∀ i j, tagCartanEntry .E6 (π i) (π j) = tagCartanEntry .E6 i j := h
  rcases cartan_embedding_E6 (π (3 : Fin 6)) (π (1 : Fin 6)) ((hh _ _).trans (by decide))
    (π (2 : Fin 6)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) (π (4 : Fin 6))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    (π (0 : Fin 6)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) (π (5 : Fin 6))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
    ((hh _ _).trans (by decide)) ((hh _ _).trans (by decide))
      with ⟨k0, k1, k2, k3, k4, k5⟩ | ⟨k0, k1, k2, k3, k4, k5⟩
  · left
    refine Equiv.ext fun i => ?_
    fin_cases i <;> first | exact k0 | exact k1 | exact k2 | exact k3 | exact k4 | exact k5
  · right
    refine Equiv.ext fun i => ?_
    fin_cases i <;> first | exact k0 | exact k1 | exact k2 | exact k3 | exact k4 | exact k5

theorem prod_map_simple_smul {ι : Type*} (τ : Tag) (f : ι → Fin τ.rank) (l : List ι)
    (v : Fin τ.rank → ℤ) :
    (l.map fun a => simple τ (f a)).prod • v = l.foldr (fun a w => reflect τ (f a) w) v := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.prod_cons, mul_smul, simple_smul, ih, List.foldr_cons]

@[expose] def excNodeE6 (n : ℕ) : Fin Tag.E6.rank := Fin.ofNat 6 n

@[expose] def excLongestWordE6 : List ℕ :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
    4, 3, 2, 0]

@[expose] noncomputable def excLongestElementE6 : WeylGroup Tag.E6 :=
  (excLongestWordE6.map fun n => simple Tag.E6 (excNodeE6 n)).prod

theorem excLongestElementE6_smul_single (i : Fin Tag.E6.rank) :
    excLongestElementE6 • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      -Pi.single (excDiagramSigmaE6 i) 1 := by
  rw [excLongestElementE6, prod_map_simple_smul]
  fin_cases i <;> decide +kernel

theorem exists_conj_simple_of_cartan_perm_E6 (π : Equiv.Perm (Fin Tag.E6.rank))
    (h : ∀ i j, Tag.E6.cartan (π i) (π j) = Tag.E6.cartan i j) :
    ∃ g : WeylGroup Tag.E6, ∀ i, g * simple Tag.E6 i * g⁻¹ = simple Tag.E6 (π i) := by
  rcases perm_eq_one_or_eq_sigma_of_cartan_E6 π h with rfl | rfl
  · exact ⟨1, fun i => by simp⟩
  · refine ⟨excLongestElementE6, fun i => ?_⟩
    have h1 : rootReflection (-(Pi.single (excDiagramSigmaE6 i) 1 : Fin Tag.E6.rank → ℤ)) =
        excLongestElementE6 * simple Tag.E6 i * excLongestElementE6⁻¹ :=
      rootReflection_eq_conj (excLongestElementE6_smul_single i)
    have h2 : rootReflection (Pi.single (excDiagramSigmaE6 i) 1 : Fin Tag.E6.rank → ℤ) =
        simple Tag.E6 (excDiagramSigmaE6 i) := by
      rw [rootReflection_eq_conj (w := 1) (j := excDiagramSigmaE6 i) (one_smul _ _), one_mul,
        inv_one, mul_one]
    rw [← h1, rootReflection_neg (isRoot_single Tag.E6 (excDiagramSigmaE6 i)), h2]

theorem exists_conj_simple_of_cartan_perm_E7 (π : Equiv.Perm (Fin Tag.E7.rank))
    (h : ∀ i j, Tag.E7.cartan (π i) (π j) = Tag.E7.cartan i j) :
    ∃ g : WeylGroup Tag.E7, ∀ i, g * simple Tag.E7 i * g⁻¹ = simple Tag.E7 (π i) := by
  rw [perm_eq_one_of_cartan_E7 π h]
  exact ⟨1, fun i => by simp⟩

theorem exists_conj_simple_of_cartan_perm_E8 (π : Equiv.Perm (Fin Tag.E8.rank))
    (h : ∀ i j, Tag.E8.cartan (π i) (π j) = Tag.E8.cartan i j) :
    ∃ g : WeylGroup Tag.E8, ∀ i, g * simple Tag.E8 i * g⁻¹ = simple Tag.E8 (π i) := by
  rw [perm_eq_one_of_cartan_E8 π h]
  exact ⟨1, fun i => by simp⟩

@[expose] def excTreeParentNat (n : ℕ) : ℕ := if n = 0 then 2 else if n ≤ 4 then 3 else n - 1

@[expose] def excTreeDepthNat (n : ℕ) : ℕ :=
  if n = 3 then 0 else if n = 1 ∨ n = 2 ∨ n = 4 then 1 else if n = 0 then 2 else n - 3

@[expose] def excTreeParentE6 (i : Fin Tag.E6.rank) : Fin Tag.E6.rank :=
  Fin.ofNat 6 (excTreeParentNat i.val)

@[expose] def excTreeRootE6 : Fin Tag.E6.rank := Fin.ofNat 6 3

@[expose] def excTreeParentE7 (i : Fin Tag.E7.rank) : Fin Tag.E7.rank :=
  Fin.ofNat 7 (excTreeParentNat i.val)

@[expose] def excTreeRootE7 : Fin Tag.E7.rank := Fin.ofNat 7 3

@[expose] def excTreeParentE8 (i : Fin Tag.E8.rank) : Fin Tag.E8.rank :=
  Fin.ofNat 8 (excTreeParentNat i.val)

@[expose] def excTreeRootE8 : Fin Tag.E8.rank := Fin.ofNat 8 3

theorem exists_sign_gauge_E6 (c : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ)
    (hcsymm : ∀ i j, c i j = c j i) (hcdiag : ∀ i, c i i = 2)
    (hc0 : ∀ i j, i ≠ j → Tag.E6.cartan i j = 0 → c i j = 0)
    (hc1 : ∀ i j, Tag.E6.cartan i j = -1 → c i j = 1 ∨ c i j = -1) :
    ∃ ε : Fin Tag.E6.rank → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ i j, ε i * ε j * c i j = Tag.E6.cartan i j :=
  exists_sign_gauge_of_tree (tagCartanEntry .E6) c excTreeParentE6 excTreeRootE6
    (fun i => excTreeDepthNat i.val) hcsymm hcdiag (by decide +kernel) (by decide +kernel) hc0 hc1
    (by decide +kernel) (by decide +kernel)

theorem exists_sign_gauge_E7 (c : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ)
    (hcsymm : ∀ i j, c i j = c j i) (hcdiag : ∀ i, c i i = 2)
    (hc0 : ∀ i j, i ≠ j → Tag.E7.cartan i j = 0 → c i j = 0)
    (hc1 : ∀ i j, Tag.E7.cartan i j = -1 → c i j = 1 ∨ c i j = -1) :
    ∃ ε : Fin Tag.E7.rank → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ i j, ε i * ε j * c i j = Tag.E7.cartan i j :=
  exists_sign_gauge_of_tree (tagCartanEntry .E7) c excTreeParentE7 excTreeRootE7
    (fun i => excTreeDepthNat i.val) hcsymm hcdiag (by decide +kernel) (by decide +kernel) hc0 hc1
    (by decide +kernel) (by decide +kernel)

theorem exists_sign_gauge_E8 (c : Fin Tag.E8.rank → Fin Tag.E8.rank → ℤ)
    (hcsymm : ∀ i j, c i j = c j i) (hcdiag : ∀ i, c i i = 2)
    (hc0 : ∀ i j, i ≠ j → Tag.E8.cartan i j = 0 → c i j = 0)
    (hc1 : ∀ i j, Tag.E8.cartan i j = -1 → c i j = 1 ∨ c i j = -1) :
    ∃ ε : Fin Tag.E8.rank → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ i j, ε i * ε j * c i j = Tag.E8.cartan i j :=
  exists_sign_gauge_of_tree (tagCartanEntry .E8) c excTreeParentE8 excTreeRootE8
    (fun i => excTreeDepthNat i.val) hcsymm hcdiag (by decide +kernel) (by decide +kernel) hc0 hc1
    (by decide +kernel) (by decide +kernel)

end CFSG.StandardType

end
