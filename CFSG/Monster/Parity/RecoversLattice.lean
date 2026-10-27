module

public import CFSG.Monster.Parity.ShortLines
public import CFSG.Monster.Visible.Pair
import CFSG.Monster.Code.LatticeGen

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Parity

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible Matrix Module

@[expose] def intVec (K : Type*) [Field K] (u : Fin 24 → ℤ) : Fin 24 → K := fun i => (u i : K)

variable {K : Type*} [Field K]

theorem intVec_zero : intVec K 0 = 0 := by
  funext i
  simp [intVec]

theorem intVec_add (u v : Fin 24 → ℤ) : intVec K (u + v) = intVec K u + intVec K v := by
  funext i
  simp [intVec]

theorem intVec_neg (u : Fin 24 → ℤ) : intVec K (-u) = -intVec K u := by
  funext i
  simp [intVec]

theorem intVec_rat (u : Fin 24 → ℤ) : intVec ℚ u = ratVec u := rfl

theorem uQ_eq_intVec (c : ShortIdx) : uQ c = intVec ℚ (uvec c) := rfl

@[expose] def latPre (M : Matrix (Fin 24) (Fin 24) K) : AddSubgroup (Fin 24 → ℤ) where
  carrier := {v | ∃ w ∈ codeLattice C, intVec K v ᵥ* M = intVec K w}
  zero_mem' := ⟨0, zero_mem_codeLattice, by rw [intVec_zero, zero_vecMul]⟩
  add_mem' := by
    rintro a b ⟨w, hw, h⟩ ⟨w', hw', h'⟩
    exact ⟨w + w', add_mem_codeLattice allOnes_mem_C hw hw', by
      rw [intVec_add, add_vecMul, h, h', intVec_add]⟩
  neg_mem' := by
    rintro a ⟨w, hw, h⟩
    exact ⟨-w, neg_mem_codeLattice allOnes_mem_C hw, by rw [intVec_neg, neg_vecMul, h, intVec_neg]⟩

theorem forall_mem_codeLattice_of_minVecs (M : Matrix (Fin 24) (Fin 24) K)
    (h : ∀ u ∈ minVecs, ∃ w ∈ codeLattice C, intVec K u ᵥ* M = intVec K w)
    {v : Fin 24 → ℤ} (hv : v ∈ codeLattice C) :
    ∃ w ∈ codeLattice C, intVec K v ᵥ* M = intVec K w := by
  have hle : AddSubgroup.closure latticeGens ≤ latPre M := by
    rw [AddSubgroup.closure_le]
    intro u hu
    exact h u (mem_minVecs_iff.2 (latticeGens_mem hu))
  have hv' : v ∈ AddSubgroup.closure latticeGens := by
    rw [closure_latticeGens]
    exact hv
  exact hle hv'

theorem exists_shortIdx_of_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    ∃ c : ShortIdx, u = uvec c ∨ u = -uvec c := by
  obtain ⟨p, hp⟩ := SpinLattice.phi0_bijective.2 (classOf u)
  have hc : IsShortCoord p := ⟨u, hu, hp.symm⟩
  exact ⟨⟨p, hc⟩, (classOf_eq_iff (uvec_mem _) hu).1 ((classOf_uvec _).trans hp)⟩

theorem minVecs_of_uvec (M : Matrix (Fin 24) (Fin 24) K)
    (h : ∀ c : ShortIdx, ∃ c' : ShortIdx, intVec K (uvec c) ᵥ* M = intVec K (uvec c') ∨
      intVec K (uvec c) ᵥ* M = -intVec K (uvec c')) :
    ∀ u ∈ minVecs, ∃ w ∈ codeLattice C, intVec K u ᵥ* M = intVec K w := by
  intro u hu
  obtain ⟨c, hc⟩ := exists_shortIdx_of_minVecs hu
  obtain ⟨c', hc'⟩ := h c
  have hmem : uvec c' ∈ codeLattice C := (uvec_mem c').1
  have hmem' : -uvec c' ∈ codeLattice C := neg_mem_codeLattice allOnes_mem_C hmem
  rcases hc with rfl | rfl <;> rcases hc' with h1 | h1
  · exact ⟨_, hmem, h1⟩
  · exact ⟨_, hmem', by rw [h1, intVec_neg]⟩
  · exact ⟨_, hmem', by rw [intVec_neg, neg_vecMul, h1, intVec_neg]⟩
  · exact ⟨_, hmem, by rw [intVec_neg, neg_vecMul, h1, neg_neg]⟩

@[expose] def castVec (x : Fin 24 → ℚ) : Fin 24 → ℝ := fun i => (x i : ℝ)

theorem castVec_injective : Function.Injective castVec := fun _ _ h =>
  funext fun i => Rat.cast_injective (congrFun h i)

theorem castVec_intVec (u : Fin 24 → ℤ) : castVec (intVec ℚ u) = intVec ℝ u := by
  funext i
  simp [castVec, intVec]

theorem castVec_neg (x : Fin 24 → ℚ) : castVec (-x) = -castVec x := by
  funext i
  simp [castVec]

theorem castVec_vecMul (x : Fin 24 → ℚ) (g : Matrix (Fin 24) (Fin 24) ℚ) :
    castVec (x ᵥ* g) = castVec x ᵥ* castR g := by
  funext j
  simp [castVec, vecMul, dotProduct, castR_apply, Rat.cast_sum, Rat.cast_mul]

theorem castR_Umat (c : ShortIdx) :
    castR (Umat c) = vecMulVec (intVec ℝ (uvec c)) (intVec ℝ (uvec c)) := by
  ext i j
  simp [castR_apply, Umat, uQ, vecMulVec_apply, intVec]

theorem conj_vecMulVec (G : Matrix (Fin 24) (Fin 24) ℝ) (a : Fin 24 → ℝ) :
    Gᵀ * vecMulVec a a * G = vecMulVec (a ᵥ* G) (a ᵥ* G) := by
  rw [mul_vecMulVec, mulVec_transpose, vecMulVec_mul]

section Real

variable {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsParityAut f) {G : Matrix (Fin 24) (Fin 24) ℝ}
  (hG : ∀ A : symMat, castR (resA f A) = Gᵀ * castR A * G)
include hf hG

theorem realVec_uvec_mul (c : ShortIdx) :
    intVec ℝ (uvec c) ᵥ* G = intVec ℝ (uvec (hf.lineMap c)) ∨
      intVec ℝ (uvec c) ᵥ* G = -intVec ℝ (uvec (hf.lineMap c)) := by
  have h := hG (UmatS c)
  rw [hf.resA_UmatS, coe_UmatS, coe_UmatS, castR_Umat, castR_Umat, conj_vecMulVec] at h
  exact eq_or_eq_neg_of_vecMulVec_eq h

theorem real_mem_codeLattice {v : Fin 24 → ℤ} (hv : v ∈ codeLattice C) :
    ∃ w ∈ codeLattice C, intVec ℝ v ᵥ* G = intVec ℝ w :=
  forall_mem_codeLattice_of_minVecs G
    (minVecs_of_uvec G fun c => ⟨hf.lineMap c, realVec_uvec_mul hf hG c⟩) hv

theorem exists_row (i : Fin 24) : ∃ w ∈ codeLattice C, ∀ j, G i j = (w j : ℝ) / 8 := by
  obtain ⟨w, hw, h⟩ := real_mem_codeLattice hf hG
    (smul_eight_mem_codeLattice (C := C) (Pi.single i 1 : Fin 24 → ℤ))
  refine ⟨w, hw, fun j => ?_⟩
  have e : intVec ℝ ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ)) = (8 : ℝ) • Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [intVec]
    · simp [intVec, hk]
  have hj := congrFun h j
  rw [e, smul_vecMul, single_one_vecMul] at hj
  simp only [Pi.smul_apply, Matrix.row, smul_eq_mul, intVec] at hj
  linarith

theorem exists_rat_of_real :
    ∃ g : Matrix (Fin 24) (Fin 24) ℚ, castR g = G ∧ ∀ i j, ∃ k : ℤ, g i j = k / 8 := by
  choose w _ hwG using exists_row hf hG
  refine ⟨Matrix.of fun i j => (w i j : ℚ) / 8, ?_, fun i j => ⟨w i j, rfl⟩⟩
  ext i j
  rw [castR_apply, hwG i j, of_apply]
  push_cast
  rfl

end Real

namespace IsParityAut

variable {f : SpaceB ≃ₗ[ℚ] SpaceB}

theorem exists_rat_matrix (hf : IsParityAut f) :
    ∃ g : Matrix (Fin 24) (Fin 24) ℚ, g * gᵀ = 1 ∧
      (∀ A : symMat, (resA f A : Matrix (Fin 24) (Fin 24) ℚ) =
        gᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * g) ∧
      (∀ c : ShortIdx, uQ c ᵥ* g = uQ (hf.lineMap c) ∨ uQ c ᵥ* g = -uQ (hf.lineMap c)) ∧
      ∀ i j, ∃ k : ℤ, g i j = k / 8 := by
  obtain ⟨G, hGo, hG⟩ := exists_real_orthogonal_conj (resA f) hf.resA_jordanQ hf.resA_trace
  obtain ⟨g, hgG, hg8⟩ := exists_rat_of_real hf hG
  refine ⟨g, ?_, fun A => ?_, fun c => ?_, hg8⟩
  · apply castR_injective
    rw [map_mul, castR_transpose, hgG, map_one]
    exact (mem_orthogonalGroup_iff _ _).1 hGo
  · apply castR_injective
    rw [hG, map_mul, map_mul, castR_transpose, hgG]
  · rcases realVec_uvec_mul hf hG c with h | h
    · left
      apply castVec_injective
      rw [castVec_vecMul, hgG, uQ_eq_intVec, uQ_eq_intVec, castVec_intVec, castVec_intVec, h]
    · right
      apply castVec_injective
      rw [castVec_vecMul, hgG, uQ_eq_intVec, uQ_eq_intVec, castVec_neg, castVec_intVec,
        castVec_intVec, h]

theorem image_latticeQ_eq (hf : IsParityAut f) {g : Matrix (Fin 24) (Fin 24) ℚ}
    (hg : g * gᵀ = 1)
    (hu : ∀ c : ShortIdx, uQ c ᵥ* g = uQ (hf.lineMap c) ∨ uQ c ᵥ* g = -uQ (hf.lineMap c)) :
    (fun x => x ᵥ* g) '' latticeQ = latticeQ := by
  have hgt : gᵀ * g = 1 := mul_eq_one_comm.1 hg
  have h1 : ∀ v ∈ codeLattice C, ∃ w ∈ codeLattice C, intVec ℚ v ᵥ* g = intVec ℚ w :=
    fun v hv => forall_mem_codeLattice_of_minVecs g
      (minVecs_of_uvec g fun c => ⟨hf.lineMap c, hu c⟩) hv
  have hut : ∀ d : ShortIdx, ∃ c : ShortIdx, intVec ℚ (uvec d) ᵥ* gᵀ = intVec ℚ (uvec c) ∨
      intVec ℚ (uvec d) ᵥ* gᵀ = -intVec ℚ (uvec c) := by
    intro d
    obtain ⟨c, rfl⟩ := hf.lineMap_bijective.2 d
    refine ⟨c, ?_⟩
    have hback : ∀ x : Fin 24 → ℚ, (x ᵥ* g) ᵥ* gᵀ = x := fun x => by
      rw [vecMul_vecMul, hg, vecMul_one]
    rcases hu c with h | h
    · left
      rw [← uQ_eq_intVec, ← uQ_eq_intVec, ← h, hback]
    · right
      have h' : uQ (hf.lineMap c) = -(uQ c ᵥ* g) := by rw [h, neg_neg]
      rw [← uQ_eq_intVec, ← uQ_eq_intVec, h', neg_vecMul, hback]
  have h2 : ∀ w ∈ codeLattice C, ∃ v ∈ codeLattice C, intVec ℚ w ᵥ* gᵀ = intVec ℚ v :=
    fun w hw => forall_mem_codeLattice_of_minVecs gᵀ (minVecs_of_uvec gᵀ hut) hw
  ext y
  constructor
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨w, hw, h⟩ := h1 v hv
    exact ⟨w, hw, h.symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, h⟩ := h2 w hw
    refine ⟨ratVec v, ⟨v, hv, rfl⟩, ?_⟩
    change intVec ℚ v ᵥ* g = intVec ℚ w
    rw [← h, vecMul_vecMul, hgt, vecMul_one]

theorem exists_latticeO (hf : IsParityAut f) :
    ∃ g : latticeO, (∀ A : symMat, resA f A = thetaA (mat g) A) ∧
      (∀ c : ShortIdx, uQ c ᵥ* mat g = uQ (hf.lineMap c) ∨
        uQ c ᵥ* mat g = -uQ (hf.lineMap c)) ∧
      ∀ i j, ∃ k : ℤ, mat g i j = k / 8 := by
  obtain ⟨g, hg, hA, hu, h8⟩ := hf.exists_rat_matrix
  refine ⟨mkO g hg (hf.image_latticeQ_eq hg hu), fun A => Subtype.ext ?_, ?_, ?_⟩
  · rw [hA, coe_thetaA, mat_mkO]
  · rw [mat_mkO]
    exact hu
  · rw [mat_mkO]
    exact h8

end IsParityAut

theorem sgn_eq_one_or_neg_one (t : ZMod 2) : sgn t = 1 ∨ sgn t = -1 := by
  unfold sgn
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem parity_centralizer_recovers_lattice (f : SpaceB ≃ₗ[ℚ] SpaceB)
    (hmul : ∀ u v, f (gmul u v) = gmul (f u) (f v))
    (hiso : ∀ u v, bform (f u) (f v) = bform u v) (hcomm : ∀ u, f (xB u) = xB (f u)) :
    ∃ g : latticeO,
      (∀ A : symMat, f (A, 0, 0) = (thetaA (mat g) A, 0, 0)) ∧
      (∀ (r : Q) (hr : IsShortCoord (coordOf r)), ∃ (t : Q) (ht : IsShortCoord (coordOf t)) (ε : ℚ),
        (ε = 1 ∨ ε = -1) ∧ f (0, Xlift r, 0) = (0, ε • Xlift t, 0) ∧
        (uQ ⟨coordOf r, hr⟩ ᵥ* mat g = uQ ⟨coordOf t, ht⟩ ∨
          uQ ⟨coordOf r, hr⟩ ᵥ* mat g = -uQ ⟨coordOf t, ht⟩)) ∧
      (∀ g' : Matrix (Fin 24) (Fin 24) ℚ, g' ∈ orthogonalGroup (Fin 24) ℚ →
        (∀ A : symMat, f (A, 0, 0) = (thetaA g' A, 0, 0)) → g' = mat g ∨ g' = -mat g) ∧
      ∀ i j, ∃ k : ℤ, mat g i j = k / 8 := by
  have hf : IsParityAut f := ⟨hmul, hiso, hcomm⟩
  obtain ⟨g, hA, hu, h8⟩ := hf.exists_latticeO
  have hfA : ∀ A : symMat, f (A, 0, 0) = (thetaA (mat g) A, 0, 0) := fun A => by
    rw [← hA]
    exact hf.apply_inA A
  refine ⟨g, hfA, fun r hr => ?_, fun g' hg' h' => ?_, h8⟩
  · set c : ShortIdx := ⟨coordOf r, hr⟩
    have ht : IsShortCoord (coordOf (rep (hf.lineMap c).1)) := isShortCoord_rep _
    have e : (⟨coordOf (rep (hf.lineMap c).1), ht⟩ : ShortIdx) = hf.lineMap c :=
      Subtype.ext (coordOf_rep _)
    refine ⟨rep (hf.lineMap c).1, ht, sgn (centralCoord r) * hf.lineSign c, ?_,
      hf.apply_Xlift hr, ?_⟩
    · rcases sgn_eq_one_or_neg_one (centralCoord r) with h1 | h1 <;>
        rcases hf.lineSign_eq c with h2 | h2 <;> rw [h1, h2] <;> norm_num
    · rw [e]
      exact hu c
  · have hg'' : g' * g'ᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hg'
    refine eq_or_eq_neg_of_conj_eq_rat (mat_mul_transpose g) hg'' fun A => ?_
    have h1 := congrArg (fun w : SpaceB => ((w.1 : symMat) : Matrix (Fin 24) (Fin 24) ℚ))
      ((hfA A).symm.trans (h' A))
    simpa only [coe_thetaA] using h1

end CFSG.Monster.Parity
