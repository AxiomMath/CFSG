module

public import CFSG.RankThree.E6.LargePrimeStabilizers
public import CFSG.RankThree.Lattice.SteinbergBIRoots

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LieType.Steinberg.Adjoint

section Transport

variable {K : Type*} [Field K]

theorem image_rootKernel_of_charVal {z z' : Fin Tag.E6.rank → K} {a : WeylGroup Tag.E6}
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

theorem mem_dualWeylStabilizer_conj {z z' : Fin Tag.E6.rank → K} {a : WeylGroup Tag.E6}
    (h : ∀ x, charVal z' (a • x) = charVal z x) (g : WeylGroup Tag.E6) :
    g ∈ dualWeylStabilizer z ↔ a * g * a⁻¹ ∈ dualWeylStabilizer z' := by
  simp only [mem_dualWeylStabilizer]
  constructor
  · intro hg x
    rw [mul_smul, mul_smul, h, hg, ← h, smul_inv_smul]
  · intro hg x
    have := hg (a • x)
    rw [mul_smul, mul_smul, inv_smul_smul, h, h] at this
    exact this

theorem mem_closure_rootKernel_conj {z z' : Fin Tag.E6.rank → K} {a : WeylGroup Tag.E6}
    (h : ∀ x, charVal z' (a • x) = charVal z x) (g : WeylGroup Tag.E6) :
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

theorem rootKernel_smul {z : Fin Tag.E6.rank → K} {s : K} (hs : s ≠ 0) :
    rootKernel (s • z) = rootKernel z := by
  ext α
  simp only [mem_rootKernel, charVal_smul_col, mul_eq_zero, hs, false_or]

theorem dualWeylStabilizer_smul {z : Fin Tag.E6.rank → K} {s : K} (hs : s ≠ 0) :
    dualWeylStabilizer (s • z) = dualWeylStabilizer z := by
  ext g
  simp only [mem_dualWeylStabilizer, charVal_smul_col, mul_right_inj' hs]

end Transport

@[expose] def e6F4ZJInt : List ℤ := [0, 4, 0, 0, 3, 4]

@[expose] def e6F4ZJ : Fin Tag.E6.rank → ZMod 5 := fun i => (vget e6F4ZJInt i : ZMod 5)

@[expose] def lzv (l : List ℤ) : ℤ := (∑ i : Fin Tag.E6.rank, vget l i * vget e6F4ZJInt i) % 5

@[expose] def lform (l l' : List ℤ) : ℤ :=
  ∑ i : Fin Tag.E6.rank, vget l i * ∑ j : Fin Tag.E6.rank, Tag.E6.cartan i j * vget l' j

@[expose] def lcomb (cs : List ℤ) (vs : List (List ℤ)) : List ℤ :=
  List.ofFn fun t : Fin Tag.E6.rank => ∑ k : Fin Tag.E6.rank, vget cs k * vget (vs.getD k []) t

@[expose] def e6F4Tuples : List (List (List ℤ)) := [
  [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[-1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[1, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0], [0, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[1, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, -1, 0, 0],
   [0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [-1, 0, -1, 0, 0, 0], [1, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[-1, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0], [0, 0, 0, -1, 0, 0],
   [0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[-1, 0, -1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[1, 0, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 0, 0],
   [0, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[1, 0, 1, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, -1, -1, 0, 0], [0, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, -1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, 1, 0, 0, 0], [1, 1, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, -1, 0, 0],
   [1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, 1, 1, 0, 0], [0, 1, 0, 1, 0, 0], [-1, 0, -1, -1, 0, 0], [1, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[-1, 0, -1, 0, 0, 0], [0, 1, 1, 1, 0, 0], [1, 0, 1, 1, 0, 0], [0, 0, -1, -1, 0, 0],
   [0, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[1, 0, 1, 1, 0, 0], [0, 1, 1, 1, 0, 0], [0, 0, 0, -1, 0, 0], [0, 0, -1, 0, 0, 0],
   [0, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[-1, 0, -1, -1, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, -1, 0, 0, 0], [1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 0, 0], [-1, 0, -1, -1, 0, 0],
   [1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, 1, 1, 0, 0], [1, 1, 1, 1, 0, 0], [0, 0, 0, -1, 0, 0], [-1, 0, -1, 0, 0, 0],
   [1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, -1, -1, 0, 0], [0, 1, 0, 1, 0, 0], [-1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0], [-1, 0, -1, -1, 0, 0], [1, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[-1, 0, -1, -1, 0, 0], [0, 1, 1, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 0, -1, 0, 0, 0],
   [0, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, 0, 1, 0, 0], [1, 1, 1, 1, 0, 0], [0, 0, -1, -1, 0, 0], [-1, 0, 0, 0, 0, 0],
   [1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, -1, -1, 0, 0], [1, 1, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0], [-1, 0, -1, 0, 0, 0],
   [1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, 0, -1, 0, 0], [0, 1, 1, 1, 0, 0], [-1, 0, -1, 0, 0, 0], [1, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]],
  [[0, 0, 0, -1, 0, 0], [1, 1, 1, 1, 0, 0], [0, 0, -1, 0, 0, 0], [-1, 0, 0, 0, 0, 0],
   [1, 0, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1]]]

@[expose] def e6F4WJWords : List (List (Fin 6)) :=
  [[], [0], [2], [3], [0, 2], [0, 3], [2, 0], [2, 3], [3, 2], [0, 2, 0], [0, 2, 3], [0, 3, 2],
   [2, 0, 3], [2, 3, 2], [3, 2, 0], [0, 2, 0, 3], [0, 2, 3, 2], [0, 3, 2, 0], [2, 0, 3, 2],
   [2, 3, 2, 0], [0, 2, 0, 3, 2], [0, 2, 3, 2, 0], [2, 0, 3, 2, 0], [0, 2, 0, 3, 2, 0]]

@[expose] def e6F4S27 : List (List ℤ) :=
  [[-2, -3, -4, -6, -5, -4], [-2, -3, -4, -6, -5, -1], [-2, -3, -4, -6, -2, -1],
   [-2, -3, -4, -3, -2, -1], [-2, -3, -1, -3, -2, -1], [-2, 0, -4, -3, -2, -1],
   [-2, 0, -1, -3, -2, -1], [-2, 0, -1, 0, -2, -1], [-2, 0, -1, 0, 1, -1], [-2, 0, -1, 0, 1, 2],
   [1, -3, -1, -3, -2, -1], [1, 0, -1, -3, -2, -1], [1, 0, -1, 0, -2, -1], [1, 0, -1, 0, 1, -1],
   [1, 0, -1, 0, 1, 2], [1, 0, 2, 0, -2, -1], [1, 0, 2, 0, 1, -1], [1, 0, 2, 0, 1, 2],
   [1, 0, 2, 3, 1, -1], [1, 0, 2, 3, 1, 2], [1, 0, 2, 3, 4, 2], [1, 3, 2, 3, 1, -1],
   [1, 3, 2, 3, 1, 2], [1, 3, 2, 3, 4, 2], [1, 3, 2, 6, 4, 2], [1, 3, 5, 6, 4, 2],
   [4, 3, 5, 6, 4, 2]]


@[expose] def e6F4X1 : Fin Tag.E6.rank → ℤ := toVec 6 [4, 3, 5, 6, 4, 2]

theorem e6F4_S27_closed : ∀ l ∈ e6F4S27, ∀ i : Fin Tag.E6.rank,
    List.ofFn (reflect Tag.E6 i (toVec Tag.E6.rank l)) ∈ e6F4S27 := by
  decide +kernel

theorem e6F4_S27_mem (g : WeylGroup Tag.E6) : List.ofFn (g • e6F4X1) ∈ e6F4S27 := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem Tag.E6).wordProd_surjective g
  rw [wordProd_smul]
  induction ω with
  | nil => decide +kernel
  | cons i ω ih =>
    rw [List.foldr_cons]
    have h := e6F4_S27_closed _ ih i
    rwa [toVec_ofFn] at h

@[expose] def e6F4SearchOK : Bool :=
  Tag.E6.artifactRoots.all fun a₀ => !(lzv a₀ == 0) ||
  Tag.E6.artifactRoots.all fun a₁ => !(lzv a₁ == 4 && lform a₀ a₁ == 0) ||
  Tag.E6.artifactRoots.all fun a₂ => !(lzv a₂ == 0 && lform a₀ a₂ == -1 && lform a₁ a₂ == 0) ||
  Tag.E6.artifactRoots.all fun a₃ => !(lzv a₃ == 0 && lform a₀ a₃ == 0 && lform a₁ a₃ == -1 &&
    lform a₂ a₃ == -1) ||
  Tag.E6.artifactRoots.all fun a₄ => !(lzv a₄ == 3 && lform a₀ a₄ == 0 && lform a₁ a₄ == 0 &&
    lform a₂ a₄ == 0 && lform a₃ a₄ == -1) ||
  Tag.E6.artifactRoots.all fun a₅ => !(lzv a₅ == 4 && lform a₀ a₅ == 0 && lform a₁ a₅ == 0 &&
    lform a₂ a₅ == 0 && lform a₃ a₅ == 0 && lform a₄ a₅ == -1 &&
    decide (lcomb [4, 3, 5, 6, 4, 2] [a₀, a₁, a₂, a₃, a₄, a₅] ∈ e6F4S27)) ||
  decide ([a₀, a₁, a₂, a₃, a₄, a₅] ∈ e6F4Tuples)

theorem e6F4SearchOK_eq : e6F4SearchOK = true := by
  decide +kernel

theorem bor_of_not {c r : Bool} (h : (!c || r) = true) (hc : c = true) : r = true := by
  rw [hc] at h
  simpa using h

theorem e6F4_search {a₀ a₁ a₂ a₃ a₄ a₅ : List ℤ} (h₀ : a₀ ∈ Tag.E6.artifactRoots)
    (h₁ : a₁ ∈ Tag.E6.artifactRoots) (h₂ : a₂ ∈ Tag.E6.artifactRoots)
    (h₃ : a₃ ∈ Tag.E6.artifactRoots) (h₄ : a₄ ∈ Tag.E6.artifactRoots)
    (h₅ : a₅ ∈ Tag.E6.artifactRoots)
    (c₀ : lzv a₀ = 0) (c₁ : lzv a₁ = 4 ∧ lform a₀ a₁ = 0)
    (c₂ : lzv a₂ = 0 ∧ lform a₀ a₂ = -1 ∧ lform a₁ a₂ = 0)
    (c₃ : lzv a₃ = 0 ∧ lform a₀ a₃ = 0 ∧ lform a₁ a₃ = -1 ∧ lform a₂ a₃ = -1)
    (c₄ : lzv a₄ = 3 ∧ lform a₀ a₄ = 0 ∧ lform a₁ a₄ = 0 ∧ lform a₂ a₄ = 0 ∧ lform a₃ a₄ = -1)
    (c₅ : lzv a₅ = 4 ∧ lform a₀ a₅ = 0 ∧ lform a₁ a₅ = 0 ∧ lform a₂ a₅ = 0 ∧
      lform a₃ a₅ = 0 ∧ lform a₄ a₅ = -1)
    (c₆ : lcomb [4, 3, 5, 6, 4, 2] [a₀, a₁, a₂, a₃, a₄, a₅] ∈ e6F4S27) :
    [a₀, a₁, a₂, a₃, a₄, a₅] ∈ e6F4Tuples := by
  have h := e6F4SearchOK_eq
  rw [e6F4SearchOK] at h
  have g₀ := bor_of_not (List.all_eq_true.1 h a₀ h₀) (by simp [c₀])
  have g₁ := bor_of_not (List.all_eq_true.1 g₀ a₁ h₁) (by simp [c₁])
  have g₂ := bor_of_not (List.all_eq_true.1 g₁ a₂ h₂) (by simp [c₂])
  have g₃ := bor_of_not (List.all_eq_true.1 g₂ a₃ h₃) (by simp [c₃])
  have g₄ := bor_of_not (List.all_eq_true.1 g₃ a₄ h₄) (by simp [c₄])
  have g₅ := bor_of_not (List.all_eq_true.1 g₄ a₅ h₅) (by simp [c₅, c₆])
  simpa using g₅

@[expose] def gTuple (g : WeylGroup Tag.E6) : List (List ℤ) :=
  List.ofFn fun i : Fin Tag.E6.rank => List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))

@[expose] def wordTuple (ω : List (Fin 6)) : List (List ℤ) :=
  List.ofFn fun i : Fin Tag.E6.rank =>
    List.ofFn ((e6Word ω).foldr (reflect Tag.E6) (Pi.single i 1 : Fin Tag.E6.rank → ℤ))

theorem gTuple_wordProd (ω : List (Fin 6)) :
    gTuple ((coxeterSystem Tag.E6).wordProd (e6Word ω)) = wordTuple ω := by
  simp only [gTuple, wordTuple, wordProd_smul]

theorem gTuple_injective : Function.Injective gTuple := by
  intro g h hgh
  refine eq_of_smul_single_eq fun j => ?_
  have := congrArg (fun L : List (List ℤ) => L.getD j []) hgh
  simp only [gTuple, List.getD_eq_getElem _ _ (by simp : (j : ℕ) < (List.ofFn
    fun i : Fin Tag.E6.rank => List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))).length),
    List.getElem_ofFn] at this
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn] at this
  exact List.ofFn_injective this

theorem ofFn_six {α : Type*} (f : Fin Tag.E6.rank → α) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5] :=
  rfl

theorem lzv_ofFn (x : Fin Tag.E6.rank → ℤ) :
    ((lzv (List.ofFn x) : ℤ) : ZMod 5) = charVal e6F4ZJ x := by
  have e : ((lzv (List.ofFn x) : ℤ) : ZMod 5) =
      ((∑ i : Fin Tag.E6.rank, vget (List.ofFn x) i * vget e6F4ZJInt i : ℤ) : ZMod 5) :=
    ZMod.intCast_mod _ 5
  rw [e, charVal]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show List.ofFn x = vofFn Tag.E6.rank x from rfl, vget_vofFn]
  rfl

theorem lzv_eq_of_charVal {x : Fin Tag.E6.rank → ℤ} {c : ℤ} (hc0 : 0 ≤ c) (hc5 : c < 5)
    (h : charVal e6F4ZJ x = (c : ZMod 5)) : lzv (List.ofFn x) = c := by
  have h' := lzv_ofFn x
  rw [h, ZMod.intCast_eq_intCast_iff' _ _ 5] at h'
  have h'' : lzv (List.ofFn x) % 5 = c % 5 := by exact_mod_cast h'
  have e1 : lzv (List.ofFn x) % 5 = lzv (List.ofFn x) := by
    rw [lzv, Int.emod_emod_of_dvd _ (dvd_refl _)]
  rw [e1, Int.emod_eq_of_lt hc0 hc5] at h''
  exact h''

theorem lform_ofFn (x y : Fin Tag.E6.rank → ℤ) :
    lform (List.ofFn x) (List.ofFn y) = e6Form x y := by
  simp only [lform, e6Form, show List.ofFn x = vofFn Tag.E6.rank x from rfl,
    show List.ofFn y = vofFn Tag.E6.rank y from rfl, vget_vofFn]

theorem e6Form_single (i j : Fin Tag.E6.rank) :
    e6Form (Pi.single i 1) (Pi.single j 1) = Tag.E6.cartan i j := by
  simp [e6Form, Pi.single_apply]

theorem e6Form_smul (g : WeylGroup Tag.E6) (x y : Fin Tag.E6.rank → ℤ) :
    e6Form (g • x) (g • y) = e6Form x y := by
  rw [← iform_eq_e6Form, ← iform_eq_e6Form, iform_smul]

theorem lcomb_gTuple (g : WeylGroup Tag.E6) :
    lcomb [4, 3, 5, 6, 4, 2] (gTuple g) = List.ofFn (g • e6F4X1) := by
  rw [lcomb]
  congr 1
  funext t
  rw [← weylMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct, weylMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gTuple, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn,
    show List.ofFn (g • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) =
      vofFn Tag.E6.rank (g • (Pi.single k 1 : Fin Tag.E6.rank → ℤ)) from rfl, vget_vofFn,
    mul_comm]
  rfl

theorem gTuple_mem {g : WeylGroup Tag.E6} (hg : g ∈ dualWeylStabilizer e6F4ZJ) :
    gTuple g ∈ e6F4Tuples := by
  have hr : ∀ i, List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ∈
      Tag.E6.artifactRoots := fun i =>
    isRoot_iff_mem_artifactRoots.1 (IsRoot.smul (isRoot_single Tag.E6 i) g)
  have hz : ∀ i, charVal e6F4ZJ (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
      ((vget e6F4ZJInt i : ℤ) : ZMod 5) := fun i => by
    rw [mem_dualWeylStabilizer.1 hg, charVal_single]
    rfl
  have hv : ∀ i, lzv (List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) =
      vget e6F4ZJInt i := fun i =>
    lzv_eq_of_charVal (by fin_cases i <;> decide) (by fin_cases i <;> decide) (hz i)
  have hf : ∀ i j, lform (List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)))
      (List.ofFn (g • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) = Tag.E6.cartan i j := fun i j => by
    rw [lform_ofFn, e6Form_smul, e6Form_single]
  have hc := lcomb_gTuple g
  rw [gTuple, ofFn_six] at hc ⊢
  refine e6F4_search (hr 0) (hr 1) (hr 2) (hr 3) (hr 4) (hr 5) (hv 0) ⟨hv 1, hf 0 1⟩
    ⟨hv 2, hf 0 2, hf 1 2⟩ ⟨hv 3, hf 0 3, hf 1 3, hf 2 3⟩
    ⟨hv 4, hf 0 4, hf 1 4, hf 2 4, hf 3 4⟩ ⟨hv 5, hf 0 5, hf 1 5, hf 2 5, hf 3 5, hf 4 5⟩ ?_
  rw [hc]
  exact e6F4_S27_mem g

theorem card_dualWeylStabilizer_e6F4ZJ_le : Nat.card (dualWeylStabilizer e6F4ZJ) ≤ 24 := by
  classical
  let φ : dualWeylStabilizer e6F4ZJ → {t // t ∈ e6F4Tuples.toFinset} :=
    fun g => ⟨gTuple g, List.mem_toFinset.2 (gTuple_mem g.2)⟩
  have hφ : Function.Injective φ := fun g h hgh =>
    Subtype.ext (gTuple_injective (congrArg Subtype.val hgh))
  calc Nat.card (dualWeylStabilizer e6F4ZJ)
      ≤ Nat.card {t // t ∈ e6F4Tuples.toFinset} := Nat.card_le_card_of_injective φ hφ
    _ = e6F4Tuples.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ e6F4Tuples.length := List.toFinset_card_le _
    _ = 24 := by decide

theorem single_mem_rootKernel_e6F4ZJ {i : Fin Tag.E6.rank} (hi : i = 0 ∨ i = 2 ∨ i = 3) :
    (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootKernel e6F4ZJ := by
  refine ⟨isRoot_single Tag.E6 i, ?_⟩
  rw [charVal_single]
  rcases hi with rfl | rfl | rfl <;> decide

theorem simple_eq_rootReflection (i : Fin Tag.E6.rank) :
    simple Tag.E6 i = rootReflection (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
  rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]

theorem wordProd_mem_closure_e6F4ZJ : ∀ ω : List (Fin Tag.E6.rank),
    (∀ i ∈ ω, i = 0 ∨ i = 2 ∨ i = 3) →
    (coxeterSystem Tag.E6).wordProd ω ∈
      Subgroup.closure {s | ∃ α ∈ rootKernel e6F4ZJ, s = rootReflection α}
  | [], _ => by
    rw [CoxeterSystem.wordProd_nil]
    exact one_mem _
  | i :: ω, h => by
    rw [CoxeterSystem.wordProd_cons]
    refine mul_mem (Subgroup.subset_closure ⟨Pi.single i 1, single_mem_rootKernel_e6F4ZJ ?_, ?_⟩)
      (wordProd_mem_closure_e6F4ZJ ω fun j hj => h j (List.mem_cons_of_mem _ hj))
    · rcases h i List.mem_cons_self with h | h | h <;> [left; (right; left); (right; right)] <;>
        exact h
    · exact simple_eq_rootReflection i

theorem e6F4WJ_letters : ∀ ω ∈ e6F4WJWords, ∀ i ∈ e6Word ω, i = 0 ∨ i = 2 ∨ i = 3 := by
  decide +kernel

theorem e6F4WJ_tuples : ∀ k : Fin 24, wordTuple (e6F4WJWords.getD k []) = e6F4Tuples.getD k [] := by
  decide +kernel

theorem e6F4Tuples_getD_inj : ∀ k k' : Fin 24,
    e6F4Tuples.getD k [] = e6F4Tuples.getD k' [] → k = k' := by
  decide +kernel

theorem card_closure_e6F4ZJ_ge :
    24 ≤ Nat.card (Subgroup.closure {s | ∃ α ∈ rootKernel e6F4ZJ, s = rootReflection α}) := by
  have hmem : ∀ k : Fin 24, (coxeterSystem Tag.E6).wordProd (e6Word (e6F4WJWords.getD k [])) ∈
      Subgroup.closure {s | ∃ α ∈ rootKernel e6F4ZJ, s = rootReflection α} := fun k =>
    wordProd_mem_closure_e6F4ZJ _ (e6F4WJ_letters _ (by
      rw [List.getD_eq_getElem _ _ (by simp [e6F4WJWords])]
      exact List.getElem_mem _))
  let f : Fin 24 → Subgroup.closure {s | ∃ α ∈ rootKernel e6F4ZJ, s = rootReflection α} :=
    fun k => ⟨_, hmem k⟩
  have hf : Function.Injective f := by
    intro k k' h
    have h' : gTuple (f k : WeylGroup Tag.E6) = gTuple (f k') := by rw [h]
    simp only [f, gTuple_wordProd, e6F4WJ_tuples] at h'
    exact e6F4Tuples_getD_inj k k' h'
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem rootKernel_e6F4ZJ : rootKernel e6F4ZJ = parabolicRoots Tag.E6 support134 := by
  have h : ∀ m : Fin 72, charVal e6F4ZJ (e6RootVec m) = 0 ↔
      ∀ i : Fin Tag.E6.rank, ¬(i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 3) →
        e6RootVec m i = 0 := by
    decide +kernel
  ext α
  rw [mem_rootKernel, mem_parabolicRoots_iff]
  constructor
  · rintro ⟨hα, h0⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
    exact ⟨hα, fun i hi => (h m).1 h0 i ((mem_support134 i).not.1 hi)⟩
  · rintro ⟨hα, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
    exact ⟨hα, (h m).2 fun i hi => hs i ((mem_support134 i).not.2 hi)⟩

theorem dualWeylStabilizer_e6F4ZJ :
    dualWeylStabilizer e6F4ZJ =
        Subgroup.closure {s | ∃ α ∈ rootKernel e6F4ZJ, s = rootReflection α} ∧
      Nat.card (dualWeylStabilizer e6F4ZJ) = 24 := by
  have hle := closure_rootReflection_le (z := e6F4ZJ)
  have h1 := card_dualWeylStabilizer_e6F4ZJ_le
  have h2 := card_closure_e6F4ZJ_ge
  have heq := Subgroup.eq_of_le_of_card_ge hle (h1.trans h2)
  refine ⟨heq.symm, le_antisymm h1 ?_⟩
  rw [← heq]
  exact h2

end CFSG.RankThree.Lattice
