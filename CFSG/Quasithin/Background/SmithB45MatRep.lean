module

public import CFSG.CharacterTheory.SteinbergBYModularRealization
public import Mathlib.Algebra.Module.ZMod
public import CFSG.CharacterTheory.SteinbergBYFieldFour
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.B45Mat

open Matrix
open scoped Kronecker

@[expose] noncomputable def mulAutMat (n : ℕ) :
    MulAut (Multiplicative (Fin n → ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2) where
  toFun f := LinearMap.toMatrix'
    (AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.toMultiplicative.symm f.toMonoidHom))
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
  map_mul' f g := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1

theorem mulAutMat_apply (n : ℕ) (f : MulAut (Multiplicative (Fin n → ZMod 2))) (i j : Fin n) :
    mulAutMat n f i j =
      Multiplicative.toAdd (f (Multiplicative.ofAdd (Pi.single j 1))) i := by
  simp only [mulAutMat, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix'_apply]
  rfl

section Kron

variable {G F : Type*} [Group G] [CommRing F] {m n : ℕ}

@[expose] def kronRep (M : G →* Matrix (Fin m) (Fin m) F) (N : G →* Matrix (Fin n) (Fin n) F) :
    G →* Matrix (Fin (m * n)) (Fin (m * n)) F where
  toFun g := Matrix.reindex finProdFinEquiv finProdFinEquiv (M g ⊗ₖ N g)
  map_one' := by
    rw [map_one, map_one, Matrix.one_kronecker_one]
    exact Matrix.submatrix_one_equiv _
  map_mul' g h := by
    rw [map_mul, map_mul, Matrix.mul_kronecker_mul]
    simp only [Matrix.reindex_apply]
    exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

theorem kronRep_apply (M : G →* Matrix (Fin m) (Fin m) F) (N : G →* Matrix (Fin n) (Fin n) F)
    (g : G) : kronRep M N g = Matrix.reindex finProdFinEquiv finProdFinEquiv (M g ⊗ₖ N g) :=
  rfl

end Kron

theorem forall_of_closure {G : Type*} [Group G] [Finite G] {S : Set G}
    (hS : Subgroup.closure S = ⊤) (p : G → Prop) (h1 : p 1) (hS' : ∀ s ∈ S, p s)
    (hmul : ∀ g h, p g → p h → p (g * h)) : ∀ g, p g := by
  have hpow : ∀ g, p g → ∀ k : ℕ, p (g ^ k) := by
    intro g hg k
    induction k with
    | zero => rw [pow_zero]; exact h1
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hg
  intro g
  have hg : g ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS' x hx
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx =>
    have hfin : orderOf x ≠ 0 := (orderOf_pos x).ne'
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hfin),
        pow_orderOf_eq_one]
    rw [this]
    exact hpow x hx _

section Sub

variable {G F : Type*} [Group G] [Field F] {n d : ℕ}

@[expose] def subRep (K : G →* Matrix (Fin n) (Fin n) F) (B : Matrix (Fin n) (Fin d) F)
    (P : Matrix (Fin d) (Fin n) F) (hPB : P * B = 1)
    (hinv : ∀ g, K g * B = B * (P * K g * B)) : G →* Matrix (Fin d) (Fin d) F where
  toFun g := P * K g * B
  map_one' := by rw [map_one, Matrix.mul_one, hPB]
  map_mul' g h := by
    rw [map_mul]
    calc P * (K g * K h) * B = P * K g * (K h * B) := by simp only [Matrix.mul_assoc]
      _ = P * K g * (B * (P * K h * B)) := by rw [hinv h]
      _ = P * K g * B * (P * K h * B) := by simp only [Matrix.mul_assoc]

theorem subRep_apply (K : G →* Matrix (Fin n) (Fin n) F) (B : Matrix (Fin n) (Fin d) F)
    (P : Matrix (Fin d) (Fin n) F) (hPB : P * B = 1)
    (hinv : ∀ g, K g * B = B * (P * K g * B)) (g : G) :
    subRep K B P hPB hinv g = P * K g * B :=
  rfl

theorem subInv_of_closure [Finite G] {S : Set G} (hS : Subgroup.closure S = ⊤)
    (K : G →* Matrix (Fin n) (Fin n) F) (B : Matrix (Fin n) (Fin d) F)
    (P : Matrix (Fin d) (Fin n) F) (hPB : P * B = 1)
    (hgen : ∀ s ∈ S, K s * B = B * (P * K s * B)) : ∀ g, K g * B = B * (P * K g * B) := by
  refine forall_of_closure hS _ (by rw [map_one, Matrix.one_mul, Matrix.mul_one, hPB,
    Matrix.mul_one]) hgen fun g h hg hh => ?_
  have h1 : K (g * h) * B = B * ((P * K g * B) * (P * K h * B)) := by
    rw [map_mul, Matrix.mul_assoc, hh, ← Matrix.mul_assoc, hg, Matrix.mul_assoc]
  have h2 : P * K (g * h) * B = (P * K g * B) * (P * K h * B) := by
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, hPB, Matrix.one_mul]
  rw [h2]
  exact h1

@[expose] def quotRep (K : G →* Matrix (Fin n) (Fin n) F) (B : Matrix (Fin n) (Fin d) F)
    (P : Matrix (Fin d) (Fin n) F) (hPB : P * B = 1)
    (hinv : ∀ g, P * K g = P * K g * B * P) : G →* Matrix (Fin d) (Fin d) F where
  toFun g := P * K g * B
  map_one' := by rw [map_one, Matrix.mul_one, hPB]
  map_mul' g h := by
    rw [map_mul]
    calc P * (K g * K h) * B = (P * K g) * K h * B := by simp only [Matrix.mul_assoc]
      _ = (P * K g * B * P) * K h * B := by rw [← hinv g]
      _ = P * K g * B * (P * K h * B) := by simp only [Matrix.mul_assoc]

theorem quotRep_apply (K : G →* Matrix (Fin n) (Fin n) F) (B : Matrix (Fin n) (Fin d) F)
    (P : Matrix (Fin d) (Fin n) F) (hPB : P * B = 1)
    (hinv : ∀ g, P * K g = P * K g * B * P) (g : G) :
    quotRep K B P hPB hinv g = P * K g * B :=
  rfl

theorem quotInv_of_closure [Finite G] {S : Set G} (hS : Subgroup.closure S = ⊤)
    (K : G →* Matrix (Fin n) (Fin n) F) (B : Matrix (Fin n) (Fin d) F)
    (P : Matrix (Fin d) (Fin n) F) (hPB : P * B = 1)
    (hgen : ∀ s ∈ S, P * K s = P * K s * B * P) : ∀ g, P * K g = P * K g * B * P := by
  refine forall_of_closure hS (fun g => P * K g = P * K g * B * P) ?_ hgen fun g h hg hh => ?_
  · rw [map_one, Matrix.mul_one, hPB, Matrix.one_mul]
  · calc P * K (g * h) = (P * K g) * K h := by rw [map_mul, Matrix.mul_assoc]
      _ = (P * K g * B * P) * K h := by rw [← hg]
      _ = P * K g * B * (P * K h) := by simp only [Matrix.mul_assoc]
      _ = P * K g * B * (P * K h * B * P) := by rw [← hh]
      _ = (P * K g * B * P) * K h * B * P := by simp only [Matrix.mul_assoc]
      _ = (P * K g) * K h * B * P := by rw [← hg]
      _ = P * K (g * h) * B * P := by rw [map_mul, Matrix.mul_assoc P]

end Sub

section Descent

open CFSG.CharacterTheory.SteinbergBY Module FieldFour

variable {G : Type} [Group G]

theorem nonempty_equiv_of_intertwining_binary {K : Type*} [Field K] {d m : ℕ}
    (M : G →* Matrix (Fin d) (Fin d) (ZMod 2)) (N : G →* Matrix (Fin m) (Fin m) (ZMod 2))
    (hM : (matrixBaseChange (RingHom.id (ZMod 2)) M).IsIrreducible)
    (hN : (matrixBaseChange (RingHom.id (ZMod 2)) N).IsIrreducible) (ψ : ZMod 2 →+* K)
    (f : (matrixBaseChange ψ M).IntertwiningMap (matrixBaseChange ψ N)) (hf : f ≠ 0) :
    Nonempty ((matrixBaseChange (RingHom.id (ZMod 2)) N).Equiv
      (matrixBaseChange (RingHom.id (ZMod 2)) M)) := by
  have hT0 : LinearMap.toMatrix' f.toLinearMap ≠ 0 := by
    intro h
    apply hf
    apply Representation.IntertwiningMap.ext
    exact LinearMap.toMatrix'.injective (h.trans (map_zero _).symm)
  obtain ⟨T, hT, hTM⟩ := exists_ne_zero_mul_eq_mul_of_map ψ (fun g => M g) (fun g => N g) _ hT0
    (toMatrix'_mul_map_eq ψ M N f)
  obtain ⟨e⟩ := nonempty_equiv_of_ne_zero (intertwiningMapOfMatrix (RingHom.id (ZMod 2)) M N T hTM)
    (intertwiningMapOfMatrix_ne_zero _ M N T hTM hT)
  exact ⟨e.symm⟩

theorem exists_binary_equiv {ι : Type} {d : ι → ℕ}
    (M : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) (ZMod 2))
    (hM : ∀ i, (matrixBaseChange (RingHom.id (ZMod 2)) (M i)).IsIrreducible) (D : ℕ)
    (hsmall : ∀ (U : Type) [AddCommGroup U] [Module (AlgebraicClosure (ZMod 2)) U]
      [FiniteDimensional (AlgebraicClosure (ZMod 2)) U]
      (σ : Representation (AlgebraicClosure (ZMod 2)) G U), σ.IsIrreducible →
        finrank (AlgebraicClosure (ZMod 2)) U ≤ D →
        ∃ i, Nonempty (σ.Equiv (matrixBaseChange
          ((toField (AlgebraicClosure (ZMod 2))).comp ofPrime) (M i))))
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (τ : Representation (ZMod 2) G W) (hτ : τ.IsIrreducible) (hW : finrank (ZMod 2) W ≤ D) :
    ∃ i, Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) (M i))) := by
  classical
  have hnt := nontrivial_of_isIrreducible τ
  let eW := (Module.finBasis (ZMod 2) W).equivFun
  let τ' := transportRep eW τ
  have hτ' : τ'.IsIrreducible := isIrreducible_of_equiv (transportRepEquiv eW τ) hτ
  let N := repMatrix τ'
  have hN : matrixBaseChange (RingHom.id (ZMod 2)) N = τ' := matrixBaseChange_repMatrix τ'
  have hNirr : (matrixBaseChange (RingHom.id (ZMod 2)) N).IsIrreducible := by rw [hN]; exact hτ'
  have hτN : Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) N)) := by
    rw [hN]
    exact ⟨transportRepEquiv eW τ⟩
  obtain ⟨eτ⟩ := hτN
  let k := AlgebraicClosure (ZMod 2)
  let ψ : ZMod 2 →+* k := (toField k).comp ofPrime
  have hm : 0 < finrank (ZMod 2) W := Module.finrank_pos
  have : Nonempty (Fin (finrank (ZMod 2) W)) := ⟨⟨0, hm⟩⟩
  obtain ⟨U, hU0, hUirr⟩ := exists_isIrreducible_subrepresentation (matrixBaseChange ψ N)
  have hUdim : finrank k U.toSubmodule ≤ D := by
    have h1 := Submodule.finrank_le U.toSubmodule
    rw [Module.finrank_fin_fun] at h1
    exact h1.trans hW
  obtain ⟨i, ⟨e⟩⟩ := hsmall U.toSubmodule U.toRepresentation hUirr hUdim
  let incl : U.toRepresentation.IntertwiningMap (matrixBaseChange ψ N) :=
    ⟨U.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  let f := incl.comp e.symm.toIntertwiningMap
  have hf : f ≠ 0 := by
    obtain ⟨u, huU, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hU0
      ext x
      exact ⟨fun hx => (Submodule.mem_bot k).mpr (hcon x hx),
        fun hx => (Submodule.mem_bot k).mp hx ▸ Submodule.zero_mem _⟩
    intro h0
    apply hu0
    have h1 : f (e ⟨u, huU⟩) = u := by
      change U.toSubmodule.subtype (e.symm (e ⟨u, huU⟩)) = u
      rw [Representation.Equiv.symm_apply_apply]
      rfl
    rw [← h1, h0]
    rfl
  obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_binary (M i) N (hM i) hNirr ψ f hf
  exact ⟨i, ⟨eτ.trans e'⟩⟩

end Descent

end CFSG.Quasithin.B45Mat
