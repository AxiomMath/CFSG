module

public import CFSG.LocalAnalysis.StandardType.GGLatDefs
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.RootSystem.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

public section

namespace CFSG.StandardType.LatPerp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

open scoped Matrix

section Generic

variable {N : ℕ}

theorem latGram_eq_dotProduct (S : Matrix (Fin N) (Fin N) ℤ) (a b : Fin N → ℤ) :
    latGram S a b = a ⬝ᵥ S *ᵥ b := by
  simp only [latGram, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem latGram_eq_vecMul_dotProduct (S : Matrix (Fin N) (Fin N) ℤ) (hS : Sᵀ = S)
    (a b : Fin N → ℤ) : latGram S a b = (S *ᵥ a) ⬝ᵥ b := by
  rw [latGram_eq_dotProduct, ← hS, Matrix.dotProduct_transpose_mulVec, dotProduct_comm, hS]

theorem latGram_conj (S : Matrix (Fin N) (Fin N) ℤ) (hS : Sᵀ = S)
    (R : Matrix (Fin N) (Fin N) ℤ) (hR : Rᵀ * S * R = S) (a b : Fin N → ℤ) :
    latGram S (R *ᵥ a) (R *ᵥ b) = latGram S a b := by
  rw [latGram_eq_vecMul_dotProduct S hS, latGram_eq_vecMul_dotProduct S hS,
    Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h1 : (((S * R) *ᵥ a) ᵥ* R) = S *ᵥ a := by
    rw [Matrix.vecMul_mulVec, Matrix.transpose_mul, hS, hR]
    rw [show a ᵥ* S = a ᵥ* Sᵀ by rw [hS]]
    exact Matrix.vecMul_transpose S a
  rw [h1]

end Generic

@[expose] def reflMat (τ : Tag) (i : Fin τ.rank) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  1 - Matrix.of fun m j => if m = i then τ.cartan i j else 0

theorem reflMat_mulVec (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflMat τ i *ᵥ v = reflect τ i v := by
  have hM : (Matrix.of fun m j => if m = i then τ.cartan i j else 0) *ᵥ v
      = (∑ j, τ.cartan i j * v j) • Pi.single i 1 := by
    ext k
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [reflMat, Matrix.sub_mulVec, Matrix.one_mulVec, hM, reflect]

theorem symmetrizedCartan_transpose (τ : Tag) :
    (Tag.symmetrizedCartan τ)ᵀ = Tag.symmetrizedCartan τ := by
  cases τ <;> decide +kernel

theorem reflMat_conj (τ : Tag) (i : Fin τ.rank) :
    (reflMat τ i)ᵀ * Tag.symmetrizedCartan τ * reflMat τ i = Tag.symmetrizedCartan τ := by
  cases τ <;> fin_cases i <;> decide +kernel

theorem latGram_reflect (τ : Tag) (i : Fin τ.rank) (a b : Fin τ.rank → ℤ) :
    latGram (Tag.symmetrizedCartan τ) (reflect τ i a) (reflect τ i b)
      = latGram (Tag.symmetrizedCartan τ) a b := by
  rw [← reflMat_mulVec, ← reflMat_mulVec]
  exact latGram_conj _ (symmetrizedCartan_transpose τ) _ (reflMat_conj τ i) a b

theorem reflect_invol (τ : Tag) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ i (reflect τ i v) = v := by
  rw [← CFSG.LieType.Chevalley.reflection_cartan τ i,
    ← CFSG.LieType.Chevalley.reflection_cartan τ i]
  have hmul := CFSG.LieType.RootSystem.reflection_mul_self (A := Tag.cartan τ) (i := i)
    (Tag.cartan_self τ i)
  have h2 : (CFSG.LieType.RootSystem.reflection (Tag.cartan τ) i *
      CFSG.LieType.RootSystem.reflection (Tag.cartan τ) i) v = v := by
    rw [hmul, Module.End.one_apply]
  rwa [Module.End.mul_apply] at h2

theorem perp_reflect (τ : Tag) (i : Fin τ.rank) {v : Fin τ.rank → ℤ} :
    perp {w | IsRoot τ w} (Tag.symmetrizedCartan τ) (reflect τ i v)
      = reflect τ i '' perp {w | IsRoot τ w} (Tag.symmetrizedCartan τ) v := by
  ext β
  constructor
  · rintro ⟨hβ, hg⟩
    refine ⟨reflect τ i β, ⟨IsRoot.reflect i hβ, ?_⟩, reflect_invol τ i β⟩
    rw [← latGram_reflect τ i v (reflect τ i β), reflect_invol]
    exact hg
  · rintro ⟨β', ⟨hβ', hg'⟩, rfl⟩
    exact ⟨IsRoot.reflect i hβ', by rw [latGram_reflect]; exact hg'⟩

theorem latLinked_image_iff {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ)
    (s : (Fin N → ℤ) → (Fin N → ℤ)) (hs : Function.Injective s)
    (hs2 : ∀ x, s (s x) = x) {Φ Ψ : Set (Fin N → ℤ)} (hΨ : Ψ = s '' Φ)
    (hgram : ∀ a b, latGram S (s a) (s b) = latGram S a b) {a b : Fin N → ℤ} :
    latLinked S Ψ (s a) (s b) ↔ latLinked S Φ a b := by
  unfold latLinked
  constructor
  · intro h
    let rΦ : (Fin N → ℤ) → (Fin N → ℤ) → Prop :=
      fun x y => x ∈ Φ ∧ y ∈ Φ ∧ latGram S x y ≠ 0
    haveI : IsEquiv _ (fun x y => Relation.EqvGen rΦ (s x) (s y)) :=
      IsEquiv.comap (r := Relation.EqvGen rΦ) s
    have hle : (fun x y => x ∈ Ψ ∧ y ∈ Ψ ∧ latGram S x y ≠ 0) ≤
        fun x y => Relation.EqvGen rΦ (s x) (s y) := by
      intro x y hxy
      obtain ⟨hx, hy, hg⟩ := hxy
      rw [hΨ] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      change Relation.EqvGen rΦ (s (s x')) (s (s y'))
      rw [hs2 x', hs2 y']
      exact Relation.EqvGen.rel _ _ ⟨hx', hy', by rw [← hgram]; exact hg⟩
    have h' := (Relation.EqvGen.eqvGen_le hle) (s a) (s b) h
    simpa [rΦ, hs2] using h'
  · intro h
    let rΨ : (Fin N → ℤ) → (Fin N → ℤ) → Prop :=
      fun x y => x ∈ Ψ ∧ y ∈ Ψ ∧ latGram S x y ≠ 0
    haveI : IsEquiv _ (fun x y => Relation.EqvGen rΨ (s x) (s y)) :=
      IsEquiv.comap (r := Relation.EqvGen rΨ) s
    have hle : (fun x y => x ∈ Φ ∧ y ∈ Φ ∧ latGram S x y ≠ 0) ≤
        fun x y => Relation.EqvGen rΨ (s x) (s y) := by
      intro x y hxy
      exact Relation.EqvGen.rel _ _ ⟨by rw [hΨ]; exact ⟨x, hxy.1, rfl⟩,
        by rw [hΨ]; exact ⟨y, hxy.2.1, rfl⟩, by rw [hgram]; exact hxy.2.2⟩
    have h' := (Relation.EqvGen.eqvGen_le hle) a b h
    simpa [rΨ, hs2] using h'

@[expose] def reflChar (τ : Tag) (i : Fin τ.rank) (p : ℕ) (f : Fin τ.rank → ZMod p) :
    Fin τ.rank → ZMod p :=
  fun l => latChar p f (reflect τ i (Pi.single l 1))

theorem latChar_smul {N : ℕ} (p : ℕ) (c : ZMod p) (f : Fin N → ZMod p)
    (α : Fin N → ℤ) : latChar p (c • f) α = c * latChar p f α := by
  simp only [latChar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem latChar_sum {N : ℕ} (p : ℕ) (f : Fin N → ZMod p) (c : Fin N → ℤ)
    (g : Fin N → Fin N → ℤ) :
    latChar p f (∑ l, c l • g l) = ∑ l, (c l : ZMod p) * latChar p f (g l) := by
  simp only [latChar, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

theorem reflect_sum_single (τ : Tag) (i : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    reflect τ i α = ∑ l, α l • reflect τ i (Pi.single l 1) := by
  have hsum : (∑ l, α l • (Pi.single l 1 : Fin τ.rank → ℤ)) = α := by
    rw [← Finset.univ_sum_single α]
    exact Finset.sum_congr rfl fun l _ => by
      funext j
      by_cases h : j = l <;> simp [Pi.single_apply, h]
  calc reflect τ i α
      = reflect τ i (∑ l, α l • (Pi.single l 1 : Fin τ.rank → ℤ)) := by rw [hsum]
    _ = ∑ l, α l • reflect τ i (Pi.single l 1) := by
          rw [← CFSG.LieType.Chevalley.reflection_cartan τ i, map_sum]
          exact Finset.sum_congr rfl fun l _ => by
            rw [map_smul, CFSG.LieType.Chevalley.reflection_cartan]

theorem latChar_reflChar (τ : Tag) (i : Fin τ.rank) (p : ℕ) (f : Fin τ.rank → ZMod p)
    (α : Fin τ.rank → ℤ) :
    latChar p (reflChar τ i p f) α = latChar p f (reflect τ i α) := by
  rw [reflect_sum_single τ i α, latChar_sum]
  rfl

theorem reflChar_invol (τ : Tag) (i : Fin τ.rank) (p : ℕ) (f : Fin τ.rank → ZMod p) :
    reflChar τ i p (reflChar τ i p f) = f := by
  ext l
  change latChar p (reflChar τ i p f) (reflect τ i (Pi.single l 1)) = f l
  rw [latChar_reflChar, reflect_invol]
  simp [latChar, Pi.single_apply]

section Gram

variable {N : ℕ}

theorem latGram_single_left (S : Matrix (Fin N) (Fin N) ℤ) (i : Fin N) (b : Fin N → ℤ) :
    latGram S (Pi.single i 1) b = (S *ᵥ b) i := by
  rw [latGram_eq_dotProduct]
  simp [dotProduct, Pi.single_apply]

theorem latGram_left_sum (S : Matrix (Fin N) (Fin N) ℤ) (β α : Fin N → ℤ) :
    latGram S β α = ∑ i, β i * latGram S (Pi.single i 1) α := by
  have h : ∀ i, latGram S (Pi.single i 1) α = (S *ᵥ α) i := fun i => latGram_single_left S i α
  simp only [h]
  rw [latGram_eq_dotProduct]
  simp only [dotProduct]

theorem latGram_sub_smul_left (S : Matrix (Fin N) (Fin N) ℤ) (a b x : Fin N → ℤ) (c : ℤ) :
    latGram S (a - c • b) x = latGram S a x - c * latGram S b x := by
  simp only [latGram_eq_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]

@[expose] def cartInt (S : Matrix (Fin N) (Fin N) ℤ) (α β : Fin N → ℤ) : ℤ :=
  ∑ i, β i * (2 * latGram S (Pi.single i 1) α / latGram S α α)

@[expose] def DivInv (S : Matrix (Fin N) (Fin N) ℤ) (α : Fin N → ℤ) : Prop :=
  latGram S α α ≠ 0 ∧ ∀ i, latGram S α α ∣ 2 * latGram S (Pi.single i 1) α

theorem latGram_mul_cartInt (S : Matrix (Fin N) (Fin N) ℤ) {α : Fin N → ℤ} (h : DivInv S α)
    (β : Fin N → ℤ) : latGram S α α * cartInt S α β = 2 * latGram S β α := by
  rw [cartInt, Finset.mul_sum, latGram_left_sum S β α, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc := Int.mul_ediv_cancel' (h.2 i)
  calc latGram S α α * (β i * (2 * latGram S (Pi.single i 1) α / latGram S α α))
      = β i * (latGram S α α * (2 * latGram S (Pi.single i 1) α / latGram S α α)) := by ring
    _ = β i * (2 * latGram S (Pi.single i 1) α) := by rw [hc]
    _ = 2 * (β i * latGram S (Pi.single i 1) α) := by ring

theorem divInv_transport (S : Matrix (Fin N) (Fin N) ℤ) (s : (Fin N → ℤ) → (Fin N → ℤ))
    (hs2 : ∀ x, s (s x) = x) (hgram : ∀ a b, latGram S (s a) (s b) = latGram S a b) (i : Fin N)
    (hsl : ∀ l, ∃ c : ℤ, s (Pi.single l 1) = Pi.single l 1 - c • Pi.single i 1)
    {α : Fin N → ℤ} (h : DivInv S α) : DivInv S (s α) := by
  have hd : latGram S (s α) (s α) = latGram S α α := hgram α α
  refine ⟨by rw [hd]; exact h.1, fun l => ?_⟩
  rw [hd]
  obtain ⟨c, hc⟩ := hsl l
  have h1 : latGram S (Pi.single l 1) (s α) = latGram S (s (Pi.single l 1)) α := by
    have := hgram (s (Pi.single l 1)) α
    rwa [hs2] at this
  rw [h1, hc, latGram_sub_smul_left, mul_sub, ← mul_assoc, mul_comm 2 c, mul_assoc]
  exact dvd_sub (h.2 l) (Dvd.dvd.mul_left (h.2 i) c)

theorem cartInt_transport (S : Matrix (Fin N) (Fin N) ℤ) (s : (Fin N → ℤ) → (Fin N → ℤ))
    (hs2 : ∀ x, s (s x) = x) (hgram : ∀ a b, latGram S (s a) (s b) = latGram S a b)
    {α : Fin N → ℤ} (h : DivInv S α) (h' : DivInv S (s α)) (β : Fin N → ℤ) :
    cartInt S (s α) β = cartInt S α (s β) := by
  have hd : latGram S (s α) (s α) = latGram S α α := hgram α α
  have e1 := latGram_mul_cartInt S h' β
  have e2 := latGram_mul_cartInt S h (s β)
  have hb : latGram S β (s α) = latGram S (s β) α := by
    have := hgram (s β) α
    rwa [hs2] at this
  rw [hd, hb] at e1
  exact mul_left_cancel₀ h.1 (e1.trans e2.symm)

end Gram

theorem reflect_single (τ : Tag) (i l : Fin τ.rank) :
    reflect τ i (Pi.single l 1) = Pi.single l 1 - (τ.cartan i l) • Pi.single i 1 := by
  have h : ∑ j, τ.cartan i j * (Pi.single l (1 : ℤ) : Fin τ.rank → ℤ) j = τ.cartan i l := by
    rw [Finset.sum_eq_single l]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  simp only [reflect, h]

theorem reflect_injective (τ : Tag) (i : Fin τ.rank) : Function.Injective (reflect τ i) :=
  Function.LeftInverse.injective (reflect_invol τ i)


end CFSG.StandardType.LatPerp
