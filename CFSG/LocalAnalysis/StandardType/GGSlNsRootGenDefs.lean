module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBlock

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane

section Defs

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r : ℕ}

@[expose] def IsBlockTorusModel {L' : Type} [Group L']
    (φ : SpecialLinearGroup (Fin n) K →* L') (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (hC : (rootMat g).det = 1) (A : Subgroup (MulAut L')) : Prop :=
  ∀ a : MulAut L', a ∈ A ↔ ∃ t : Fin s → ℕ, a = MulAut.conj (φ (SLNS.nsSL ε hC t))

variable (g) in
@[expose] noncomputable def pairBlock (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i j : Fin s) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map (theta g ε)

@[expose] def blockCoords (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i : Fin s) :
    Finset (Fin n) :=
  Finset.univ.filter fun x =>
    Sum.elim (fun ai => decide (ai.2 = i)) (fun _ => true) (ε x) = true

variable (g) in
@[expose] noncomputable def zeroBlock (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  coordBlockSL K (blockCoords ε i)

theorem mem_blockCoords_inl {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {i : Fin s}
    {x : Fin n} {a : Fin (rootPB g).dim} {m : Fin s} (hx : ε x = Sum.inl (a, m)) :
    x ∈ blockCoords ε i ↔ m = i := by
  simp [blockCoords, hx]

theorem mem_blockCoords_inr {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {i : Fin s}
    {x : Fin n} {z : Fin r} (hx : ε x = Sum.inr z) : x ∈ blockCoords ε i := by
  simp [blockCoords, hx]

end Defs

section Torus

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [NeZero p]

variable (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hC : (rootMat g).det = 1) in
@[expose] noncomputable def torusSL (hCp : rootMat g ^ p = 1) :
    Multiplicative (Fin s → ZMod p) →* SpecialLinearGroup (Fin n) K :=
  frameHom (MonoidHom.id _) 1 ε hC hCp

variable {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}

theorem torusSL_apply (hCp : rootMat g ^ p = 1) (t : Fin s → ZMod p) :
    torusSL ε hC hCp (Multiplicative.ofAdd t) = SLNS.nsSL ε hC fun i => (t i).val := by
  rw [torusSL, frameHom_apply, MonoidHom.id_apply, one_mul, inv_one, mul_one]

theorem torusSL_natCast (hCp : rootMat g ^ p = 1) (k : Fin s → ℕ) :
    torusSL ε hC hCp (Multiplicative.ofAdd fun i => (k i : ZMod p)) = SLNS.nsSL ε hC k := by
  rw [torusSL_apply]
  exact SLNS.nsSL_congr ε hC hCp fun i => by rw [ZMod.val_natCast, Nat.mod_mod]

theorem IsBlockTorusModel.mem_iff {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin n) K →* L'}
    {A : Subgroup (MulAut L')} (hM : IsBlockTorusModel φ ε hC A) (hCp : rootMat g ^ p = 1)
    {a : MulAut L'} :
    a ∈ A ↔
      ∃ t : Fin s → ZMod p, a = MulAut.conj (φ (torusSL ε hC hCp (Multiplicative.ofAdd t))) := by
  rw [hM a]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨fun i => (k i : ZMod p), by rw [torusSL_natCast]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨fun i => (t i).val, by rw [torusSL_apply]⟩

end Torus

section Vec

variable {s p : ℕ}

@[expose] def blockVec (i : Fin s) : Fin s → ZMod p := fun m => if m = i then 0 else 1

@[expose] def pairVec (i j : Fin s) : Fin s → ZMod p :=
  fun m => if m = i ∨ m = j then 1 else 0

theorem blockVec_eq_zero_iff [Fact (1 < p)] {i m : Fin s} :
    blockVec (p := p) i m = 0 ↔ m = i := by
  by_cases h : m = i <;> simp [blockVec, h]

theorem zeroCoords_blockVec {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n r : ℕ}
    [Fact (1 < p)] (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i : Fin s) :
    zeroCoords ε (blockVec (p := p) i) = blockCoords ε i := by
  ext x
  rcases hx : ε x with ⟨a, m⟩ | z
  · rw [mem_zeroCoords_inl hx, mem_blockCoords_inl hx, blockVec_eq_zero_iff]
  · simp only [mem_zeroCoords_inr hx, mem_blockCoords_inr hx]

theorem classSet_pairVec [Fact (1 < p)] (i j : Fin s) :
    classSet (pairVec (p := p) i j) 1 = {i, j} := by
  ext m
  rw [mem_classSet, Finset.mem_insert, Finset.mem_singleton]
  by_cases h : m = i ∨ m = j <;> simp [pairVec, h]

@[expose] def swapMap (i j : Fin s) (t : Fin s → ZMod p) : Fin s → ZMod p := t ∘ Equiv.swap i j

@[expose] def negMap (i : Fin s) (t : Fin s → ZMod p) : Fin s → ZMod p :=
  Function.update t i (-t i)

theorem aligned_of_eq_zero_or_one {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    [Fact p.Prime] {hζ : AdjoinRoot.root g ^ p = 1} {β : Fin s → ZMod p}
    (hβ : ∀ m, β m = 0 ∨ β m = 1) : Aligned hζ β := by
  intro i j hj u _ hij
  rcases hβ j with h | h
  · exact absurd h hj
  rcases hβ i with h' | h'
  · rw [h', h, mul_one] at hij
    exact absurd hij.symm u.ne_zero
  · rw [h, h']

end Vec

end CFSG.StandardType.SlNsRootGen

end
