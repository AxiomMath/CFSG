module

public import CFSG.RankThree.PartOne.KE.E7ClassLists

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal charVal_add charVal_neg charVal_smul charVal_smul_col
  charVal_single charVal_dualMatrix dualMatrix weylMatrix weylMatrix_apply weylMatrix_mulVec
  eq_of_smul_single_eq)

section Transport

variable {τ : Tag} {K : Type*} [Field K]

theorem image_rootKernel_of_charVal {z z' : Fin τ.rank → K} {a : WeylGroup τ}
    (h : ∀ x, charVal z' (a • x) = charVal z x) :
    (a • ·) '' rootKernel z = rootKernel z' := by
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul hα.1 a, by rw [h]; exact hα.2⟩
  · intro hβ
    refine ⟨a⁻¹ • β, ⟨IsRoot.smul hβ.1 a⁻¹, ?_⟩, smul_inv_smul a β⟩
    rw [← h, smul_inv_smul]
    exact hβ.2

theorem mem_dualWeylStabilizer_conj {z z' : Fin τ.rank → K} {a : WeylGroup τ}
    (h : ∀ x, charVal z' (a • x) = charVal z x) (g : WeylGroup τ) :
    g ∈ dualWeylStabilizer z ↔ a * g * a⁻¹ ∈ dualWeylStabilizer z' := by
  simp only [mem_dualWeylStabilizer]
  constructor
  · intro hg x
    rw [mul_smul, mul_smul, h, hg, ← h, smul_inv_smul]
  · intro hg x
    have := hg (a • x)
    rw [mul_smul, mul_smul, inv_smul_smul, h, h] at this
    exact this

theorem mem_closure_rootKernel_conj
    {z z' : Fin τ.rank → K} {a : WeylGroup τ}
    (h : ∀ x, charVal z' (a • x) = charVal z x) (g : WeylGroup τ) :
    g ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} ↔
      a * g * a⁻¹ ∈ Subgroup.closure {s | ∃ α ∈ rootKernel z', s = rootReflection α} := by
  have himg := image_rootKernel_of_charVal h
  have hmap : (Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α}).map
      (MulAut.conj a).toMonoidHom =
      Subgroup.closure {s | ∃ α ∈ rootKernel z', s = rootReflection α} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext s
    simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
      exact ⟨a • α, himg ▸ ⟨α, hα, rfl⟩, (rootReflection_smul_root a hα.1).symm⟩
    · rintro ⟨β, hβ, rfl⟩
      rw [← himg] at hβ
      obtain ⟨α, hα, rfl⟩ := hβ
      exact ⟨rootReflection α, ⟨α, hα, rfl⟩, (rootReflection_smul_root a hα.1).symm⟩
  rw [← hmap, Subgroup.mem_map_equiv,
    show (MulAut.conj a).symm (a * g * a⁻¹) = g by rw [MulAut.conj_symm_apply]; group]

theorem rootKernel_col_smul {z : Fin τ.rank → K} {s : K} (hs : s ≠ 0) :
    rootKernel (s • z) = rootKernel z := by
  ext α
  simp only [mem_rootKernel, charVal_smul_col, mul_eq_zero, hs, false_or]

theorem dualWeylStabilizer_col_smul {z : Fin τ.rank → K} {s : K} (hs : s ≠ 0) :
    dualWeylStabilizer (s • z) = dualWeylStabilizer z := by
  ext g
  simp only [mem_dualWeylStabilizer, charVal_smul_col, mul_right_inj' hs]

theorem simple_eq_rootReflection_single
    (i : Fin τ.rank) : simple τ i = rootReflection (Pi.single i 1 : Fin τ.rank → ℤ) := by
  rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]

theorem wordProd_mem_closure_of_single_mem
    {S : Set (Fin τ.rank → ℤ)} : ∀ ω : List (Fin τ.rank),
    (∀ i ∈ ω, (Pi.single i 1 : Fin τ.rank → ℤ) ∈ S) →
    (coxeterSystem τ).wordProd ω ∈
      Subgroup.closure {s | ∃ α ∈ S, s = rootReflection α}
  | [], _ => by
    rw [CoxeterSystem.wordProd_nil]
    exact one_mem _
  | i :: ω, h => by
    rw [CoxeterSystem.wordProd_cons]
    exact mul_mem (Subgroup.subset_closure ⟨Pi.single i 1, h i List.mem_cons_self,
      simple_eq_rootReflection_single i⟩)
      (wordProd_mem_closure_of_single_mem ω fun j hj => h j (List.mem_cons_of_mem _ hj))

end Transport

@[expose] def e7S5Z : Fin Tag.E7.rank → ZMod 5 := ![1, 0, 0, 0, 0, 1, 0]

theorem charVal_e7S5Z (x : Fin Tag.E7.rank → ℤ) :
    charVal e7S5Z x = ((x (0 : Fin 7) + x (5 : Fin 7) : ℤ) : ZMod 5) := by
  rw [charVal]
  show ∑ i : Fin 7, ((x i : ℤ) : ZMod 5) * e7S5Z i = _
  rw [Fin.sum_univ_seven]
  simp [e7S5Z]

theorem ofFn_seven {α : Type*} (f : Fin Tag.E7.rank → α) :
    List.ofFn f = [f (0 : Fin 7), f (1 : Fin 7), f (2 : Fin 7), f (3 : Fin 7), f (4 : Fin 7),
      f (5 : Fin 7), f (6 : Fin 7)] :=
  rfl

@[expose] def lz5 : List ℤ → ℤ
  | [x0, _, _, _, _, x5, _] => (x0 + x5) % 5
  | _ => 0

@[expose] def lform7 : List ℤ → List ℤ → ℤ
  | [x0, x1, x2, x3, x4, x5, x6], [y0, y1, y2, y3, y4, y5, y6] =>
    x0 * (2 * y0 - y2) + x1 * (2 * y1 - y3) + x2 * (2 * y2 - y0 - y3) +
    x3 * (2 * y3 - y1 - y2 - y4) + x4 * (2 * y4 - y3 - y5) + x5 * (2 * y5 - y4 - y6) +
    x6 * (2 * y6 - y5)
  | _, _ => 0

theorem lz5_ofFn (x : Fin Tag.E7.rank → ℤ) :
    ((lz5 (List.ofFn x) : ℤ) : ZMod 5) = charVal e7S5Z x := by
  rw [charVal_e7S5Z, ofFn_seven]
  exact ZMod.intCast_mod _ 5

theorem lz5_eq_of_charVal {x : Fin Tag.E7.rank → ℤ} {c : ℤ} (hc0 : 0 ≤ c) (hc5 : c < 5)
    (h : charVal e7S5Z x = (c : ZMod 5)) : lz5 (List.ofFn x) = c := by
  have h' := lz5_ofFn x
  rw [h, ZMod.intCast_eq_intCast_iff' _ _ 5] at h'
  have h'' : lz5 (List.ofFn x) % 5 = c % 5 := by exact_mod_cast h'
  have e1 : lz5 (List.ofFn x) % 5 = lz5 (List.ofFn x) := by
    rw [ofFn_seven, lz5, Int.emod_emod_of_dvd _ (dvd_refl _)]
  rw [e1, Int.emod_eq_of_lt hc0 hc5] at h''
  exact h''

theorem symmetrizedCartan_E7 : Tag.E7.symmetrizedCartan = Tag.E7.cartan := by
  rw [Tag.symmetrizedCartan, Tag.symmetrizer, one_mul]

theorem cartan_E7_apply : ∀ i j : Fin 7, Tag.E7.cartan i j =
    ![![2, 0, -1, 0, 0, 0, 0], ![0, 2, 0, -1, 0, 0, 0], ![-1, 0, 2, -1, 0, 0, 0],
      ![0, -1, -1, 2, -1, 0, 0], ![0, 0, 0, -1, 2, -1, 0], ![0, 0, 0, 0, -1, 2, -1],
      ![0, 0, 0, 0, 0, -1, 2]] i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem lform7_ofFn7 (x y : Fin 7 → ℤ) :
    lform7 (List.ofFn x) (List.ofFn y) =
      ∑ i : Fin 7, ∑ j : Fin 7, x i * Tag.E7.cartan i j * y j := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := rfl
  have hy : List.ofFn y = [y 0, y 1, y 2, y 3, y 4, y 5, y 6] := rfl
  rw [hx, hy, lform7]
  simp only [Fin.sum_univ_seven, cartan_E7_apply]
  simp
  ring

theorem iform_eq_sum7 (x y : Fin Tag.E7.rank → ℤ) :
    iform x y = ∑ i : Fin 7, ∑ j : Fin 7, x i * Tag.E7.cartan i j * y j := by
  rw [iform, symmetrizedCartan_E7]
  rfl

theorem lform7_ofFn (x y : Fin Tag.E7.rank → ℤ) :
    lform7 (List.ofFn x) (List.ofFn y) = iform x y :=
  (lform7_ofFn7 x y).trans (iform_eq_sum7 x y).symm

theorem iform_single_single (i j : Fin Tag.E7.rank) :
    iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ) (Pi.single j 1) = Tag.E7.cartan i j := by
  rw [iform_single_left]
  simp [Tag.symmetrizer, Pi.single_apply]

@[expose] def e7S5R1 : List (List ℤ) := Tag.E7.artifactRoots.filter fun l => lz5 l == 1

@[expose] def e7S5R0 : List (List ℤ) := Tag.E7.artifactRoots.filter fun l => lz5 l == 0

@[expose] def e7S5Search : List (List (List ℤ)) :=
  e7S5R1.flatMap fun a₀ =>
  (e7S5R0.filter fun a₁ => lform7 a₀ a₁ == 0).flatMap fun a₁ =>
  (e7S5R0.filter fun a₂ => lform7 a₀ a₂ == -1 && lform7 a₁ a₂ == 0).flatMap fun a₂ =>
  (e7S5R0.filter fun a₃ => lform7 a₀ a₃ == 0 && lform7 a₁ a₃ == -1 &&
    lform7 a₂ a₃ == -1).flatMap fun a₃ =>
  (e7S5R0.filter fun a₄ => lform7 a₀ a₄ == 0 && lform7 a₁ a₄ == 0 && lform7 a₂ a₄ == 0 &&
    lform7 a₃ a₄ == -1).flatMap fun a₄ =>
  (e7S5R1.filter fun a₅ => lform7 a₀ a₅ == 0 && lform7 a₁ a₅ == 0 && lform7 a₂ a₅ == 0 &&
    lform7 a₃ a₅ == 0 && lform7 a₄ a₅ == -1).flatMap fun a₅ =>
  (e7S5R0.filter fun a₆ => lform7 a₀ a₆ == 0 && lform7 a₁ a₆ == 0 && lform7 a₂ a₆ == 0 &&
    lform7 a₃ a₆ == 0 && lform7 a₄ a₆ == 0 && lform7 a₅ a₆ == -1).map fun a₆ =>
  [a₀, a₁, a₂, a₃, a₄, a₅, a₆]

theorem e7S5Search_length : e7S5Search.length = 384 := by
  decide +kernel

@[expose] def e7S5T (g : WeylGroup Tag.E7) : List (List ℤ) :=
  List.ofFn fun i : Fin Tag.E7.rank => List.ofFn (g • (Pi.single i 1 : Fin Tag.E7.rank → ℤ))

theorem e7S5T_injective : Function.Injective e7S5T := by
  intro g h hgh
  refine eq_of_smul_single_eq fun j => ?_
  exact List.ofFn_injective (congrFun (List.ofFn_injective hgh) j)

theorem mem_e7S5Search {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : List ℤ}
    (h₀ : a₀ ∈ Tag.E7.artifactRoots) (h₁ : a₁ ∈ Tag.E7.artifactRoots)
    (h₂ : a₂ ∈ Tag.E7.artifactRoots) (h₃ : a₃ ∈ Tag.E7.artifactRoots)
    (h₄ : a₄ ∈ Tag.E7.artifactRoots) (h₅ : a₅ ∈ Tag.E7.artifactRoots)
    (h₆ : a₆ ∈ Tag.E7.artifactRoots)
    (z₀ : lz5 a₀ = 1) (z₁ : lz5 a₁ = 0) (z₂ : lz5 a₂ = 0) (z₃ : lz5 a₃ = 0) (z₄ : lz5 a₄ = 0)
    (z₅ : lz5 a₅ = 1) (z₆ : lz5 a₆ = 0)
    (c₁ : lform7 a₀ a₁ = 0)
    (c₂ : lform7 a₀ a₂ = -1 ∧ lform7 a₁ a₂ = 0)
    (c₃ : lform7 a₀ a₃ = 0 ∧ lform7 a₁ a₃ = -1 ∧ lform7 a₂ a₃ = -1)
    (c₄ : lform7 a₀ a₄ = 0 ∧ lform7 a₁ a₄ = 0 ∧ lform7 a₂ a₄ = 0 ∧ lform7 a₃ a₄ = -1)
    (c₅ : lform7 a₀ a₅ = 0 ∧ lform7 a₁ a₅ = 0 ∧ lform7 a₂ a₅ = 0 ∧ lform7 a₃ a₅ = 0 ∧
      lform7 a₄ a₅ = -1)
    (c₆ : lform7 a₀ a₆ = 0 ∧ lform7 a₁ a₆ = 0 ∧ lform7 a₂ a₆ = 0 ∧ lform7 a₃ a₆ = 0 ∧
      lform7 a₄ a₆ = 0 ∧ lform7 a₅ a₆ = -1) :
    [a₀, a₁, a₂, a₃, a₄, a₅, a₆] ∈ e7S5Search := by
  simp only [e7S5Search, List.mem_flatMap, List.mem_filter, List.mem_map, e7S5R1, e7S5R0,
    beq_iff_eq, Bool.and_eq_true, and_assoc]
  exact ⟨a₀, h₀, z₀, a₁, h₁, z₁, c₁, a₂, h₂, z₂, c₂.1, c₂.2, a₃, h₃, z₃, c₃.1, c₃.2.1, c₃.2.2,
    a₄, h₄, z₄, c₄.1, c₄.2.1, c₄.2.2.1, c₄.2.2.2, a₅, h₅, z₅, c₅.1, c₅.2.1, c₅.2.2.1,
    c₅.2.2.2.1, c₅.2.2.2.2, a₆, h₆, z₆, c₆.1, c₆.2.1, c₆.2.2.1, c₆.2.2.2.1, c₆.2.2.2.2.1,
    c₆.2.2.2.2.2, rfl⟩

@[expose] def e7S5ZInt : List ℤ := [1, 0, 0, 0, 0, 1, 0]

theorem e7S5Z_eq (i : Fin Tag.E7.rank) : e7S5Z i = ((vget e7S5ZInt i : ℤ) : ZMod 5) := by
  fin_cases i <;> rfl

theorem e7S5T_mem_search {g : WeylGroup Tag.E7} (hg : g ∈ dualWeylStabilizer e7S5Z) :
    e7S5T g ∈ e7S5Search := by
  have hr : ∀ i, List.ofFn (g • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) ∈ Tag.E7.artifactRoots :=
    fun i => isRoot_iff_mem_artifactRoots.1 (IsRoot.smul (isRoot_single Tag.E7 i) g)
  have hz : ∀ i, charVal e7S5Z (g • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) =
      ((vget e7S5ZInt i : ℤ) : ZMod 5) := fun i => by
    rw [mem_dualWeylStabilizer.1 hg, charVal_single, e7S5Z_eq]
  have hv : ∀ i, lz5 (List.ofFn (g • (Pi.single i 1 : Fin Tag.E7.rank → ℤ))) =
      vget e7S5ZInt i := fun i =>
    lz5_eq_of_charVal (by fin_cases i <;> decide) (by fin_cases i <;> decide) (hz i)
  have hf : ∀ (i j : Fin Tag.E7.rank) (c : ℤ), Tag.E7.cartan i j = c →
      lform7 (List.ofFn (g • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)))
        (List.ofFn (g • (Pi.single j 1 : Fin Tag.E7.rank → ℤ))) = c :=
    fun i j c hc => by rw [lform7_ofFn, iform_smul, iform_single_single, hc]
  rw [e7S5T, ofFn_seven]
  refine mem_e7S5Search (hr 0) (hr 1) (hr 2) (hr 3) (hr 4) (hr 5) (hr 6) (hv 0) (hv 1) (hv 2)
    (hv 3) (hv 4) (hv 5) (hv 6) (hf _ _ _ (by decide)) ⟨hf _ _ _ (by decide), hf _ _ _ (by decide)⟩
    ⟨hf _ _ _ (by decide), hf _ _ _ (by decide), hf _ _ _ (by decide)⟩
    ⟨hf _ _ _ (by decide), hf _ _ _ (by decide), hf _ _ _ (by decide), hf _ _ _ (by decide)⟩
    ⟨hf _ _ _ (by decide), hf _ _ _ (by decide), hf _ _ _ (by decide), hf _ _ _ (by decide),
      hf _ _ _ (by decide)⟩
    ⟨hf _ _ _ (by decide), hf _ _ _ (by decide), hf _ _ _ (by decide), hf _ _ _ (by decide),
      hf _ _ _ (by decide), hf _ _ _ (by decide)⟩

theorem card_dualWeylStabilizer_e7S5Z_le : Nat.card (dualWeylStabilizer e7S5Z) ≤ 384 := by
  classical
  let φ : dualWeylStabilizer e7S5Z → {t // t ∈ e7S5Search.toFinset} :=
    fun g => ⟨e7S5T g, List.mem_toFinset.2 (e7S5T_mem_search g.2)⟩
  have hφ : Function.Injective φ := fun g h hgh =>
    Subtype.ext (e7S5T_injective (congrArg Subtype.val hgh))
  calc Nat.card (dualWeylStabilizer e7S5Z)
      ≤ Nat.card {t // t ∈ e7S5Search.toFinset} := Nat.card_le_card_of_injective φ hφ
    _ = e7S5Search.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ e7S5Search.length := List.toFinset_card_le _
    _ = 384 := e7S5Search_length

theorem single_mem_rootKernel_e7S5Z {i : Fin Tag.E7.rank}
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6) :
    (Pi.single i 1 : Fin Tag.E7.rank → ℤ) ∈ rootKernel e7S5Z := by
  refine ⟨isRoot_single Tag.E7 i, ?_⟩
  rw [charVal_single]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide

@[expose] def e7S5WJWords : List (List (Fin Tag.E7.rank)) :=
  [[], [1], [2], [3], [4], [6], [1, 2], [1, 3], [1, 4], [1, 6], [2, 3], [2, 4], [2, 6], [3, 1],
  [3, 2], [3, 4], [3, 6], [4, 3], [4, 6], [1, 2, 3], [1, 2, 4], [1, 2, 6], [1, 3, 1], [1, 3, 2],
  [1, 3, 4], [1, 3, 6], [1, 4, 3], [1, 4, 6], [2, 3, 1], [2, 3, 2], [2, 3, 4], [2, 3, 6],
  [2, 4, 3], [2, 4, 6], [3, 1, 2], [3, 1, 4], [3, 1, 6], [3, 2, 4], [3, 2, 6], [3, 4, 3],
  [3, 4, 6], [4, 3, 1], [4, 3, 2], [4, 3, 6], [1, 2, 3, 1], [1, 2, 3, 2], [1, 2, 3, 4],
  [1, 2, 3, 6], [1, 2, 4, 3], [1, 2, 4, 6], [1, 3, 1, 2], [1, 3, 1, 4], [1, 3, 1, 6], [1, 3, 2, 4],
  [1, 3, 2, 6], [1, 3, 4, 3], [1, 3, 4, 6], [1, 4, 3, 1], [1, 4, 3, 2], [1, 4, 3, 6], [2, 3, 1, 2],
  [2, 3, 1, 4], [2, 3, 1, 6], [2, 3, 2, 4], [2, 3, 2, 6], [2, 3, 4, 3], [2, 3, 4, 6], [2, 4, 3, 1],
  [2, 4, 3, 2], [2, 4, 3, 6], [3, 1, 2, 3], [3, 1, 2, 4], [3, 1, 2, 6], [3, 1, 4, 3], [3, 1, 4, 6],
  [3, 2, 4, 3], [3, 2, 4, 6], [3, 4, 3, 1], [3, 4, 3, 2], [3, 4, 3, 6], [4, 3, 1, 2], [4, 3, 1, 6],
  [4, 3, 2, 6], [1, 2, 3, 1, 2], [1, 2, 3, 1, 4], [1, 2, 3, 1, 6], [1, 2, 3, 2, 4],
  [1, 2, 3, 2, 6], [1, 2, 3, 4, 3], [1, 2, 3, 4, 6], [1, 2, 4, 3, 1], [1, 2, 4, 3, 2],
  [1, 2, 4, 3, 6], [1, 3, 1, 2, 3], [1, 3, 1, 2, 4], [1, 3, 1, 2, 6], [1, 3, 1, 4, 3],
  [1, 3, 1, 4, 6], [1, 3, 2, 4, 3], [1, 3, 2, 4, 6], [1, 3, 4, 3, 1], [1, 3, 4, 3, 2],
  [1, 3, 4, 3, 6], [1, 4, 3, 1, 2], [1, 4, 3, 1, 6], [1, 4, 3, 2, 6], [2, 3, 1, 2, 3],
  [2, 3, 1, 2, 4], [2, 3, 1, 2, 6], [2, 3, 1, 4, 3], [2, 3, 1, 4, 6], [2, 3, 2, 4, 3],
  [2, 3, 2, 4, 6], [2, 3, 4, 3, 1], [2, 3, 4, 3, 2], [2, 3, 4, 3, 6], [2, 4, 3, 1, 2],
  [2, 4, 3, 1, 6], [2, 4, 3, 2, 6], [3, 1, 2, 3, 4], [3, 1, 2, 3, 6], [3, 1, 2, 4, 3],
  [3, 1, 2, 4, 6], [3, 1, 4, 3, 1], [3, 1, 4, 3, 2], [3, 1, 4, 3, 6], [3, 2, 4, 3, 1],
  [3, 2, 4, 3, 2], [3, 2, 4, 3, 6], [3, 4, 3, 1, 2], [3, 4, 3, 1, 6], [3, 4, 3, 2, 6],
  [4, 3, 1, 2, 3], [4, 3, 1, 2, 6], [1, 2, 3, 1, 2, 3], [1, 2, 3, 1, 2, 4], [1, 2, 3, 1, 2, 6],
  [1, 2, 3, 1, 4, 3], [1, 2, 3, 1, 4, 6], [1, 2, 3, 2, 4, 3], [1, 2, 3, 2, 4, 6],
  [1, 2, 3, 4, 3, 1], [1, 2, 3, 4, 3, 2], [1, 2, 3, 4, 3, 6], [1, 2, 4, 3, 1, 2],
  [1, 2, 4, 3, 1, 6], [1, 2, 4, 3, 2, 6], [1, 3, 1, 2, 3, 4], [1, 3, 1, 2, 3, 6],
  [1, 3, 1, 2, 4, 3], [1, 3, 1, 2, 4, 6], [1, 3, 1, 4, 3, 1], [1, 3, 1, 4, 3, 2],
  [1, 3, 1, 4, 3, 6], [1, 3, 2, 4, 3, 1], [1, 3, 2, 4, 3, 2], [1, 3, 2, 4, 3, 6],
  [1, 3, 4, 3, 1, 2], [1, 3, 4, 3, 1, 6], [1, 3, 4, 3, 2, 6], [1, 4, 3, 1, 2, 3],
  [1, 4, 3, 1, 2, 6], [2, 3, 1, 2, 3, 4], [2, 3, 1, 2, 3, 6], [2, 3, 1, 2, 4, 3],
  [2, 3, 1, 2, 4, 6], [2, 3, 1, 4, 3, 1], [2, 3, 1, 4, 3, 2], [2, 3, 1, 4, 3, 6],
  [2, 3, 2, 4, 3, 1], [2, 3, 2, 4, 3, 2], [2, 3, 2, 4, 3, 6], [2, 3, 4, 3, 1, 2],
  [2, 3, 4, 3, 1, 6], [2, 3, 4, 3, 2, 6], [2, 4, 3, 1, 2, 3], [2, 4, 3, 1, 2, 6],
  [3, 1, 2, 3, 4, 3], [3, 1, 2, 3, 4, 6], [3, 1, 2, 4, 3, 1], [3, 1, 2, 4, 3, 2],
  [3, 1, 2, 4, 3, 6], [3, 1, 4, 3, 1, 2], [3, 1, 4, 3, 1, 6], [3, 1, 4, 3, 2, 6],
  [3, 2, 4, 3, 1, 2], [3, 2, 4, 3, 1, 6], [3, 2, 4, 3, 2, 6], [3, 4, 3, 1, 2, 3],
  [3, 4, 3, 1, 2, 6], [4, 3, 1, 2, 3, 4], [4, 3, 1, 2, 3, 6], [1, 2, 3, 1, 2, 3, 4],
  [1, 2, 3, 1, 2, 3, 6], [1, 2, 3, 1, 2, 4, 3], [1, 2, 3, 1, 2, 4, 6], [1, 2, 3, 1, 4, 3, 1],
  [1, 2, 3, 1, 4, 3, 2], [1, 2, 3, 1, 4, 3, 6], [1, 2, 3, 2, 4, 3, 1], [1, 2, 3, 2, 4, 3, 2],
  [1, 2, 3, 2, 4, 3, 6], [1, 2, 3, 4, 3, 1, 2], [1, 2, 3, 4, 3, 1, 6], [1, 2, 3, 4, 3, 2, 6],
  [1, 2, 4, 3, 1, 2, 3], [1, 2, 4, 3, 1, 2, 6], [1, 3, 1, 2, 3, 4, 3], [1, 3, 1, 2, 3, 4, 6],
  [1, 3, 1, 2, 4, 3, 1], [1, 3, 1, 2, 4, 3, 2], [1, 3, 1, 2, 4, 3, 6], [1, 3, 1, 4, 3, 1, 2],
  [1, 3, 1, 4, 3, 1, 6], [1, 3, 1, 4, 3, 2, 6], [1, 3, 2, 4, 3, 1, 2], [1, 3, 2, 4, 3, 1, 6],
  [1, 3, 2, 4, 3, 2, 6], [1, 3, 4, 3, 1, 2, 3], [1, 3, 4, 3, 1, 2, 6], [1, 4, 3, 1, 2, 3, 4],
  [1, 4, 3, 1, 2, 3, 6], [2, 3, 1, 2, 3, 4, 3], [2, 3, 1, 2, 3, 4, 6], [2, 3, 1, 2, 4, 3, 1],
  [2, 3, 1, 2, 4, 3, 2], [2, 3, 1, 2, 4, 3, 6], [2, 3, 1, 4, 3, 1, 2], [2, 3, 1, 4, 3, 1, 6],
  [2, 3, 1, 4, 3, 2, 6], [2, 3, 2, 4, 3, 1, 2], [2, 3, 2, 4, 3, 1, 6], [2, 3, 2, 4, 3, 2, 6],
  [2, 3, 4, 3, 1, 2, 3], [2, 3, 4, 3, 1, 2, 6], [2, 4, 3, 1, 2, 3, 4], [2, 4, 3, 1, 2, 3, 6],
  [3, 1, 2, 3, 4, 3, 1], [3, 1, 2, 3, 4, 3, 2], [3, 1, 2, 3, 4, 3, 6], [3, 1, 2, 4, 3, 1, 2],
  [3, 1, 2, 4, 3, 1, 6], [3, 1, 2, 4, 3, 2, 6], [3, 1, 4, 3, 1, 2, 3], [3, 1, 4, 3, 1, 2, 6],
  [3, 2, 4, 3, 1, 2, 3], [3, 2, 4, 3, 1, 2, 6], [3, 4, 3, 1, 2, 3, 4], [3, 4, 3, 1, 2, 3, 6],
  [4, 3, 1, 2, 3, 4, 6], [1, 2, 3, 1, 2, 3, 4, 3], [1, 2, 3, 1, 2, 3, 4, 6],
  [1, 2, 3, 1, 2, 4, 3, 1], [1, 2, 3, 1, 2, 4, 3, 2], [1, 2, 3, 1, 2, 4, 3, 6],
  [1, 2, 3, 1, 4, 3, 1, 2], [1, 2, 3, 1, 4, 3, 1, 6], [1, 2, 3, 1, 4, 3, 2, 6],
  [1, 2, 3, 2, 4, 3, 1, 2], [1, 2, 3, 2, 4, 3, 1, 6], [1, 2, 3, 2, 4, 3, 2, 6],
  [1, 2, 3, 4, 3, 1, 2, 3], [1, 2, 3, 4, 3, 1, 2, 6], [1, 2, 4, 3, 1, 2, 3, 4],
  [1, 2, 4, 3, 1, 2, 3, 6], [1, 3, 1, 2, 3, 4, 3, 1], [1, 3, 1, 2, 3, 4, 3, 2],
  [1, 3, 1, 2, 3, 4, 3, 6], [1, 3, 1, 2, 4, 3, 1, 2], [1, 3, 1, 2, 4, 3, 1, 6],
  [1, 3, 1, 2, 4, 3, 2, 6], [1, 3, 1, 4, 3, 1, 2, 3], [1, 3, 1, 4, 3, 1, 2, 6],
  [1, 3, 2, 4, 3, 1, 2, 3], [1, 3, 2, 4, 3, 1, 2, 6], [1, 3, 4, 3, 1, 2, 3, 4],
  [1, 3, 4, 3, 1, 2, 3, 6], [1, 4, 3, 1, 2, 3, 4, 6], [2, 3, 1, 2, 3, 4, 3, 1],
  [2, 3, 1, 2, 3, 4, 3, 2], [2, 3, 1, 2, 3, 4, 3, 6], [2, 3, 1, 2, 4, 3, 1, 2],
  [2, 3, 1, 2, 4, 3, 1, 6], [2, 3, 1, 2, 4, 3, 2, 6], [2, 3, 1, 4, 3, 1, 2, 3],
  [2, 3, 1, 4, 3, 1, 2, 6], [2, 3, 2, 4, 3, 1, 2, 3], [2, 3, 2, 4, 3, 1, 2, 6],
  [2, 3, 4, 3, 1, 2, 3, 4], [2, 3, 4, 3, 1, 2, 3, 6], [2, 4, 3, 1, 2, 3, 4, 6],
  [3, 1, 2, 3, 4, 3, 1, 2], [3, 1, 2, 3, 4, 3, 1, 6], [3, 1, 2, 3, 4, 3, 2, 6],
  [3, 1, 2, 4, 3, 1, 2, 3], [3, 1, 2, 4, 3, 1, 2, 6], [3, 1, 4, 3, 1, 2, 3, 4],
  [3, 1, 4, 3, 1, 2, 3, 6], [3, 2, 4, 3, 1, 2, 3, 4], [3, 2, 4, 3, 1, 2, 3, 6],
  [3, 4, 3, 1, 2, 3, 4, 6], [1, 2, 3, 1, 2, 3, 4, 3, 1], [1, 2, 3, 1, 2, 3, 4, 3, 2],
  [1, 2, 3, 1, 2, 3, 4, 3, 6], [1, 2, 3, 1, 2, 4, 3, 1, 2], [1, 2, 3, 1, 2, 4, 3, 1, 6],
  [1, 2, 3, 1, 2, 4, 3, 2, 6], [1, 2, 3, 1, 4, 3, 1, 2, 3], [1, 2, 3, 1, 4, 3, 1, 2, 6],
  [1, 2, 3, 2, 4, 3, 1, 2, 3], [1, 2, 3, 2, 4, 3, 1, 2, 6], [1, 2, 3, 4, 3, 1, 2, 3, 4],
  [1, 2, 3, 4, 3, 1, 2, 3, 6], [1, 2, 4, 3, 1, 2, 3, 4, 6], [1, 3, 1, 2, 3, 4, 3, 1, 2],
  [1, 3, 1, 2, 3, 4, 3, 1, 6], [1, 3, 1, 2, 3, 4, 3, 2, 6], [1, 3, 1, 2, 4, 3, 1, 2, 3],
  [1, 3, 1, 2, 4, 3, 1, 2, 6], [1, 3, 1, 4, 3, 1, 2, 3, 4], [1, 3, 1, 4, 3, 1, 2, 3, 6],
  [1, 3, 2, 4, 3, 1, 2, 3, 4], [1, 3, 2, 4, 3, 1, 2, 3, 6], [1, 3, 4, 3, 1, 2, 3, 4, 6],
  [2, 3, 1, 2, 3, 4, 3, 1, 2], [2, 3, 1, 2, 3, 4, 3, 1, 6], [2, 3, 1, 2, 3, 4, 3, 2, 6],
  [2, 3, 1, 2, 4, 3, 1, 2, 3], [2, 3, 1, 2, 4, 3, 1, 2, 6], [2, 3, 1, 4, 3, 1, 2, 3, 4],
  [2, 3, 1, 4, 3, 1, 2, 3, 6], [2, 3, 2, 4, 3, 1, 2, 3, 4], [2, 3, 2, 4, 3, 1, 2, 3, 6],
  [2, 3, 4, 3, 1, 2, 3, 4, 6], [3, 1, 2, 3, 4, 3, 1, 2, 3], [3, 1, 2, 3, 4, 3, 1, 2, 6],
  [3, 1, 2, 4, 3, 1, 2, 3, 4], [3, 1, 2, 4, 3, 1, 2, 3, 6], [3, 1, 4, 3, 1, 2, 3, 4, 6],
  [3, 2, 4, 3, 1, 2, 3, 4, 6], [1, 2, 3, 1, 2, 3, 4, 3, 1, 2], [1, 2, 3, 1, 2, 3, 4, 3, 1, 6],
  [1, 2, 3, 1, 2, 3, 4, 3, 2, 6], [1, 2, 3, 1, 2, 4, 3, 1, 2, 3], [1, 2, 3, 1, 2, 4, 3, 1, 2, 6],
  [1, 2, 3, 1, 4, 3, 1, 2, 3, 4], [1, 2, 3, 1, 4, 3, 1, 2, 3, 6], [1, 2, 3, 2, 4, 3, 1, 2, 3, 4],
  [1, 2, 3, 2, 4, 3, 1, 2, 3, 6], [1, 2, 3, 4, 3, 1, 2, 3, 4, 6], [1, 3, 1, 2, 3, 4, 3, 1, 2, 3],
  [1, 3, 1, 2, 3, 4, 3, 1, 2, 6], [1, 3, 1, 2, 4, 3, 1, 2, 3, 4], [1, 3, 1, 2, 4, 3, 1, 2, 3, 6],
  [1, 3, 1, 4, 3, 1, 2, 3, 4, 6], [1, 3, 2, 4, 3, 1, 2, 3, 4, 6], [2, 3, 1, 2, 3, 4, 3, 1, 2, 3],
  [2, 3, 1, 2, 3, 4, 3, 1, 2, 6], [2, 3, 1, 2, 4, 3, 1, 2, 3, 4], [2, 3, 1, 2, 4, 3, 1, 2, 3, 6],
  [2, 3, 1, 4, 3, 1, 2, 3, 4, 6], [2, 3, 2, 4, 3, 1, 2, 3, 4, 6], [3, 1, 2, 3, 4, 3, 1, 2, 3, 4],
  [3, 1, 2, 3, 4, 3, 1, 2, 3, 6], [3, 1, 2, 4, 3, 1, 2, 3, 4, 6],
  [1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 3], [1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 6],
  [1, 2, 3, 1, 2, 4, 3, 1, 2, 3, 4], [1, 2, 3, 1, 2, 4, 3, 1, 2, 3, 6],
  [1, 2, 3, 1, 4, 3, 1, 2, 3, 4, 6], [1, 2, 3, 2, 4, 3, 1, 2, 3, 4, 6],
  [1, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4], [1, 3, 1, 2, 3, 4, 3, 1, 2, 3, 6],
  [1, 3, 1, 2, 4, 3, 1, 2, 3, 4, 6], [2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4],
  [2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 6], [2, 3, 1, 2, 4, 3, 1, 2, 3, 4, 6],
  [3, 1, 2, 3, 4, 3, 1, 2, 3, 4, 6], [1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4],
  [1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 6], [1, 2, 3, 1, 2, 4, 3, 1, 2, 3, 4, 6],
  [1, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4, 6], [2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4, 6],
  [1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4, 6]]

theorem e7S5WJ_letters : ∀ ω ∈ e7S5WJWords, ∀ i ∈ ω, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 6 := by
  decide +kernel

@[expose] def e7S5V0 : List ℤ := [0, 1, 0, 3, 0, 0, 1]

@[expose] def e7S5Key (ω : List (Fin Tag.E7.rank)) : List ℤ :=
  lmulVec Tag.E7.rank (e7wl ω) e7S5V0

@[expose] def e7S5Code (l : List ℤ) : ℕ := (l.map fun x => (x + 8).toNat).foldr (fun d acc => d + 16 * acc) 0

@[expose] def e7S5WJCodes : List ℕ :=
  [159955096, 159955112, 159955864, 159934616, 160151704, 126400664, 159955880, 159934552,
  160151720, 126400680, 159934104, 160152472, 126401432, 159938728, 159947672, 160143512,
  126380184, 159803544, 126597272, 159934040, 160152488, 126401448, 159938648, 159947656,
  160143496, 126380120, 159803480, 126597288, 159938472, 159946392, 160143768, 126379672,
  159803032, 126598040, 159951784, 160147624, 126384296, 160156568, 126393240, 159815832,
  126589080, 159873192, 160013208, 126249112, 159938392, 159946376, 160143752, 126379608,
  159802968, 126598056, 159951752, 160147592, 126384216, 160156600, 126393224, 159815816,
  126589064, 159873112, 160013192, 126249048, 159950760, 160148136, 126384040, 160156056,
  126391960, 159816088, 126589336, 159872936, 160011928, 126248600, 159929944, 160160680,
  126397352, 159799384, 126593192, 159807128, 126602136, 159885480, 160025496, 126261400,
  160082856, 126318760, 126458776, 159950728, 160148104, 126383960, 160156088, 126391944,
  159816072, 126589320, 159872856, 160011912, 126248536, 159929992, 160160696, 126397320,
  159799432, 126593160, 159807080, 126602168, 159885448, 160025528, 126261384, 160082824,
  126318680, 126458760, 159930200, 160160424, 126396328, 159798616, 126593704, 159807896,
  126601624, 159885992, 160024984, 126261656, 160081832, 126318504, 126457496, 160151944,
  126375512, 159790680, 126606248, 159864920, 160021384, 126244952, 159881128, 160003736,
  126252696, 160095144, 126331048, 126471064, 159733336, 126528424, 159930248, 160160440,
  126396296, 159798664, 126593672, 159807848, 126601656, 159885960, 160025016, 126261640,
  160081800, 126318424, 126457480, 160151992, 126375560, 159790696, 126606264, 159864968,
  160021432, 126245000, 159881080, 160003688, 126252648, 160095160, 126331016, 126471096,
  159733384, 126528392, 160152200, 126375768, 159790424, 126605992, 159864152, 160020616,
  126244184, 159881896, 160004504, 126253464, 160094888, 126331560, 126470552, 159733592,
  126527400, 159803784, 126597512, 159860568, 159999624, 126236248, 160086920, 126310488,
  126466952, 160077736, 126326696, 126449304, 159725144, 126540712, 159955336, 126178904,
  160152248, 126375816, 159790440, 126606008, 159864200, 160020664, 126244232, 159881848,
  160004456, 126253416, 160094904, 126331528, 126470584, 159733640, 126527368, 159803752,
  126597560, 159860600, 159999592, 126236264, 160086968, 126310536, 126467000, 160077688,
  126326648, 126449256, 159725160, 126540728, 159955384, 126178952, 159802760, 126597768,
  159860056, 160000136, 126235992, 160086152, 126309720, 126466184, 160078504, 126327464,
  126450072, 159724888, 126540456, 159955592, 126179160, 159873672, 160012728, 126249352,
  160069512, 126306136, 126445192, 159737480, 126532488, 159729496, 126523304, 159934856,
  126170712, 126400904, 159802728, 126597816, 159860088, 160000104, 126236008, 160086200,
  126309768, 126466232, 160078456, 126327416, 126450024, 159724904, 126540472, 159955640,
  126179208, 159873656, 160012648, 126249320, 160069496, 126306168, 126445160, 159737448,
  126532536, 159729528, 126523256, 159934824, 126170728, 126400952, 159872392, 160012472,
  126248328, 160069768, 126305624, 126445704, 159737992, 126531720, 159728984, 126524072,
  159933832, 126170456, 126401160, 160082616, 126319240, 126458296, 159741832, 126515080,
  159947192, 126183048, 159939208, 126175064, 126380424, 159872376, 160012392, 126248296,
  160069752, 126305656, 126445672, 159737960, 126531768, 159729016, 126524024, 159933800,
  126170472, 126401208, 160082552, 126319224, 126458216, 159741816, 126515064, 159947112,
  126183016, 159939192, 126175096, 126380392, 160082104, 126317960, 126458040, 159742088,
  126515336, 159946936, 126183560, 159937928, 126174552, 126379400, 159733096, 126528184,
  159951544, 126187400, 126392760, 126384776, 160082040, 126317944, 126457960, 159742072,
  126515320, 159946856, 126183528, 159937912, 126174584, 126379368, 159733112, 126528120,
  159951480, 126187384, 126392680, 126384760, 159733864, 126527672, 159951032, 126187656,
  126392504, 126383496, 159929704, 126178664, 126397112, 159733880, 126527608, 159950968,
  126187640, 126392424, 126383480, 159929720, 126178680, 126397048, 159930472, 126179432,
  126396600, 126375272, 159930488, 126179448, 126396536, 126375288, 126376040, 126376056]

theorem e7S5WJ_codes : e7S5WJWords.map (fun ω => e7S5Code (e7S5Key ω)) = e7S5WJCodes := by
  decide +kernel

theorem e7S5WJCodes_nodup : e7S5WJCodes.Nodup := by
  decide +kernel

theorem e7S5WJ_length : e7S5WJWords.length = 384 := by
  decide +kernel

@[expose] def e7S5Img (g : WeylGroup Tag.E7) : List ℤ :=
  List.ofFn (g • toVec Tag.E7.rank e7S5V0)

theorem e7S5Img_wordProd (ω : List (Fin Tag.E7.rank)) :
    e7S5Img ((coxeterSystem Tag.E7).wordProd ω) = e7S5Key ω := by
  rw [e7S5Img, wordProd_smul_toVec7, e7S5Key, lmulVec, toVec_vofFn]
  rfl

theorem card_closure_e7S5Z_ge :
    384 ≤ Nat.card (Subgroup.closure {s | ∃ α ∈ rootKernel e7S5Z, s = rootReflection α}) := by
  classical
  set P : List (WeylGroup Tag.E7) :=
    e7S5WJWords.map (coxeterSystem Tag.E7).wordProd with hP
  have hnd : P.Nodup := by
    refine List.Nodup.of_map e7S5Img ?_
    rw [hP, List.map_map]
    have : (e7S5Img ∘ (coxeterSystem Tag.E7).wordProd) = e7S5Key := funext e7S5Img_wordProd
    rw [this]
    refine List.Nodup.of_map e7S5Code ?_
    rw [List.map_map]
    show (e7S5WJWords.map fun ω => e7S5Code (e7S5Key ω)).Nodup
    rw [e7S5WJ_codes]
    exact e7S5WJCodes_nodup
  have hsub : ∀ g ∈ P.toFinset, g ∈ Subgroup.closure
      {s | ∃ α ∈ rootKernel e7S5Z, s = rootReflection α} := by
    intro g hg
    rw [List.mem_toFinset, hP, List.mem_map] at hg
    obtain ⟨ω, hω, rfl⟩ := hg
    exact wordProd_mem_closure_of_single_mem ω fun i hi =>
      single_mem_rootKernel_e7S5Z (e7S5WJ_letters ω hω i hi)
  let ι : P.toFinset → Subgroup.closure {s | ∃ α ∈ rootKernel e7S5Z, s = rootReflection α} :=
    fun g => ⟨g, hsub g g.2⟩
  have hι : Function.Injective ι := fun g h hgh => by
    have := congrArg (fun x : Subgroup.closure
      {s | ∃ α ∈ rootKernel e7S5Z, s = rootReflection α} => (x : WeylGroup Tag.E7)) hgh
    exact Subtype.ext this
  have := Nat.card_le_card_of_injective ι hι
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd, hP,
    List.length_map, e7S5WJ_length] at this
  exact this

theorem dualWeylStabilizer_e7S5Z :
    dualWeylStabilizer e7S5Z =
        Subgroup.closure {s | ∃ α ∈ rootKernel e7S5Z, s = rootReflection α} ∧
      Nat.card (dualWeylStabilizer e7S5Z) = 384 := by
  have hle := closure_rootReflection_le (z := e7S5Z)
  have h1 := card_dualWeylStabilizer_e7S5Z_le
  have h2 := card_closure_e7S5Z_ge
  have heq := Subgroup.eq_of_le_of_card_ge hle (h1.trans h2)
  refine ⟨heq.symm, le_antisymm h1 ?_⟩
  rw [← heq]
  exact h2

theorem dualWeylStabilizer_e7S5Z_le :
    dualWeylStabilizer e7S5Z ≤ Subgroup.closure {s | ∃ α ∈ rootKernel e7S5Z, s = rootReflection α} :=
  dualWeylStabilizer_e7S5Z.1.le

end CFSG.RankThree.PartOne.KE
