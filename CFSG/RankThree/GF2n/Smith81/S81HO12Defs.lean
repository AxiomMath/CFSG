module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthGraph

open Module QuadraticMap

abbrev PIdx (n : ℕ) : Type := Fin n ⊕ Fin 2 ⊕ Fin n

variable {n : ℕ}

@[expose] def pdual : PIdx n → PIdx n
  | .inl i => .inr (.inr i)
  | .inr (.inl j) => .inr (.inl j.rev)
  | .inr (.inr i) => .inl i

@[simp] theorem pdual_inl (i : Fin n) : pdual (.inl i : PIdx n) = .inr (.inr i) := rfl

@[simp] theorem pdual_inr_inl (j : Fin 2) : pdual (.inr (.inl j) : PIdx n) = .inr (.inl j.rev) :=
  rfl

@[simp] theorem pdual_inr_inr (i : Fin n) : pdual (.inr (.inr i) : PIdx n) = .inl i := rfl

@[simp] theorem pdual_pdual (p : PIdx n) : pdual (pdual p) = p := by
  rcases p with i | j | i <;> simp

@[expose] def prank : PIdx n → ℕ
  | .inl i => i
  | .inr (.inl j) => n + j
  | .inr (.inr i) => 2 * n + 1 - i

@[simp] theorem prank_inl (i : Fin n) : prank (.inl i : PIdx n) = i := rfl

@[simp] theorem prank_inr_inl (j : Fin 2) : prank (.inr (.inl j) : PIdx n) = n + j := rfl

@[simp] theorem prank_inr_inr (i : Fin n) : prank (.inr (.inr i) : PIdx n) = 2 * n + 1 - i := rfl

theorem prank_lt (p : PIdx n) : prank p < 2 * n + 2 := by
  rcases p with i | j | i
  · have := i.isLt
    simp only [prank_inl]
    omega
  · have := j.isLt
    simp only [prank_inr_inl]
    omega
  · simp only [prank_inr_inr]
    omega

variable {K : Type*} [Field K]

@[expose] def pchar (c : Fin n → Kˣ) : PIdx n → Kˣ
  | .inl i => c i
  | .inr (.inl _) => 1
  | .inr (.inr i) => (c i)⁻¹

@[simp] theorem pchar_inl (c : Fin n → Kˣ) (i : Fin n) : pchar c (.inl i) = c i := rfl

@[simp] theorem pchar_inr_inl (c : Fin n → Kˣ) (j : Fin 2) : pchar c (.inr (.inl j)) = 1 := rfl

@[simp] theorem pchar_inr_inr (c : Fin n → Kˣ) (i : Fin n) : pchar c (.inr (.inr i)) = (c i)⁻¹ :=
  rfl

theorem pchar_mul (c d : Fin n → Kˣ) (p : PIdx n) : pchar (c * d) p = pchar c p * pchar d p := by
  rcases p with i | j | i
  · rfl
  · simp
  · simp only [pchar_inr_inr, Pi.mul_apply, mul_inv_rev]
    exact mul_comm _ _

@[simp] theorem pchar_one (p : PIdx n) : pchar (1 : Fin n → Kˣ) p = 1 := by
  rcases p with i | j | i <;> simp [pchar]

theorem pchar_pdual (c : Fin n → Kˣ) (p : PIdx n) : pchar c (pdual p) = (pchar c p)⁻¹ := by
  rcases p with i | j | i <;> simp

variable {V : Type*} [AddCommGroup V] [Module K V]

structure IsPairBasis (Q : QuadraticForm K V) (b : Basis (PIdx n) K V) : Prop where
  polar_eq : ∀ p q, polar Q (b p) (b q) = if q = pdual p then 1 else 0
  sing_v : ∀ i, Q (b (.inl i)) = 0
  sing_w : ∀ i, Q (b (.inr (.inr i))) = 0

theorem IsPairBasis.repr_apply {Q : QuadraticForm K V} {b : Basis (PIdx n) K V}
    (hb : IsPairBasis Q b) (x : V) (p : PIdx n) : b.repr x p = polar Q x (b (pdual p)) := by
  have key : ∀ y : V, polar Q y (b (pdual p)) = b.repr y p := by
    intro y
    have h1 : polar Q y (b (pdual p)) = Q.polarBilin y (b (pdual p)) := rfl
    have h2 : b.repr y p = (b.coord p) y := rfl
    rw [h1, h2]
    have hlin : (Q.polarBilin.flip (b (pdual p))) = b.coord p := by
      refine b.ext fun q => ?_
      rw [LinearMap.flip_apply, polarBilin_apply_apply, hb.polar_eq, Basis.coord_apply,
        Basis.repr_self, Finsupp.single_apply]
      by_cases hqp : q = p
      · subst hqp
        simp
      · have : ¬ pdual p = pdual q := fun h => hqp (by simpa using congrArg pdual h.symm)
        simp [this, hqp]
    exact congrArg (fun φ : V →ₗ[K] K => φ y) hlin
  exact (key x).symm

theorem mem_orthogonalGroup_of_basis {ι : Type*} (b : Basis ι K V) {Q : QuadraticForm K V}
    (g : V ≃ₗ[K] V) (hQ : ∀ p, Q (g (b p)) = Q (b p))
    (hpol : ∀ p q, polar Q (g (b p)) (g (b q)) = polar Q (b p) (b q)) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  have hB : Q.polarBilin.compl₁₂ (g : V →ₗ[K] V) (g : V →ₗ[K] V) = Q.polarBilin :=
    LinearMap.ext_basis b b fun p q => by
      rw [LinearMap.compl₁₂_apply, polarBilin_apply_apply, polarBilin_apply_apply]
      exact hpol p q
  have hB' : ∀ x y, polar Q (g x) (g y) = polar Q x y := fun x y => by
    have := congrArg (fun B : LinearMap.BilinForm K V => B x y) hB
    simpa [polarBilin_apply_apply] using this
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  have hx : x ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := hy
    exact hQ p
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, QuadraticMap.map_add (Q : V → K), QuadraticMap.map_add (Q : V → K), hy, hz, hB']
  | smul c y _ hy => rw [map_smul, QuadraticMap.map_smul, QuadraticMap.map_smul, hy]

@[expose] noncomputable def basisMat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) : (V ≃ₗ[K] V) ≃* GL ι K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

theorem basisMat_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (g : V ≃ₗ[K] V) (p q : ι) :
    ((basisMat b g : GL ι K) : Matrix ι ι K) p q = b.repr (g (b q)) p := by
  change LinearMap.toMatrixAlgEquiv b (g : V →ₗ[K] V) p q = _
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

end CFSG.RankThree.GF2n.Smith81.OrthGraph
