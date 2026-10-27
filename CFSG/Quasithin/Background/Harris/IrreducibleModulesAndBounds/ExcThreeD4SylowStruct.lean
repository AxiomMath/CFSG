module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped commutatorElement

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

structure D4Syl (K : Type) [Field K] (σ : K ≃+* K) (k : Subfield K) (P : Type) [Group P] where
  Tr : K → k
  Nm : K → k
  x1 : K → P
  x3 : K → P
  x4 : K → P
  x2 : k → P
  x5 : k → P
  x6 : k → P
  two_eq_zero : (2 : K) = 0
  hσ3 : ∀ s, σ (σ (σ s)) = s
  hk : ∀ c : K, c ∈ k ↔ σ c = c
  hTr : ∀ s, (Tr s : K) = s + σ s + σ (σ s)
  hNm : ∀ s, (Nm s : K) = s * σ s * σ (σ s)
  x1_add : ∀ a b, x1 (a + b) = x1 a * x1 b
  x2_add : ∀ a b, x2 (a + b) = x2 a * x2 b
  x3_add : ∀ a b, x3 (a + b) = x3 a * x3 b
  x4_add : ∀ a b, x4 (a + b) = x4 a * x4 b
  x5_add : ∀ a b, x5 (a + b) = x5 a * x5 b
  x6_add : ∀ a b, x6 (a + b) = x6 a * x6 b
  bij : Function.Bijective fun p : K × k × K × K × k × k =>
    x1 p.1 * (x2 p.2.1 * (x3 p.2.2.1 * (x4 p.2.2.2.1 * (x5 p.2.2.2.2.1 * x6 p.2.2.2.2.2))))
  c15 : ∀ a b, Commute (x1 a) (x5 b)
  c16 : ∀ a b, Commute (x1 a) (x6 b)
  c23 : ∀ a b, Commute (x2 a) (x3 b)
  c24 : ∀ a b, Commute (x2 a) (x4 b)
  c26 : ∀ a b, Commute (x2 a) (x6 b)
  c35 : ∀ a b, Commute (x3 a) (x5 b)
  c36 : ∀ a b, Commute (x3 a) (x6 b)
  c45 : ∀ a b, Commute (x4 a) (x5 b)
  c46 : ∀ a b, Commute (x4 a) (x6 b)
  c56 : ∀ a b, Commute (x5 a) (x6 b)
  r14 : ∀ s t, ⁅x1 s, x4 t⁆ = x5 (Tr (s * t))
  r34 : ∀ s t, ⁅x3 s, x4 t⁆ = x6 (Tr (s * t))
  r25 : ∀ b e, ⁅x2 b, x5 e⁆ = x6 (b * e)
  r21 : ∀ (β : k) s, ⁅x2 β, x1 s⁆ = x3 ((β : K) * s) * x4 ((β : K) * (σ s * σ (σ s))) *
    x5 (β * Nm s) * x6 (β * β * Nm s)
  r13 : ∀ s t, ⁅x1 s, x3 t⁆ = x4 (σ s * σ (σ t) + σ (σ s) * σ t) *
    x5 (Tr (s * σ s * σ (σ t))) * x6 (Tr (s * σ t * σ (σ t)))

theorem swap_of_comm_root {P : Type} [Group P] {a b z : P} (h : ⁅a, b⁆ = z) :
    b * a = z⁻¹ * (a * b) := by
  rw [← h, commutatorElement_def]
  group

namespace D4Syl

variable {K : Type} [Field K] {σ : K ≃+* K} {k : Subfield K} {P : Type} [Group P]
  (D : D4Syl K σ k P)

include D in
theorem add_self (a : K) : a + a = 0 := by
  rw [← two_mul, D.two_eq_zero, zero_mul]

include D in
theorem add_self_k (a : k) : a + a = 0 := by
  apply Subtype.ext
  simp [D.add_self]

theorem x1_zero : D.x1 0 = 1 := by
  have h := D.x1_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)
theorem x2_zero : D.x2 0 = 1 := by
  have h := D.x2_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)
theorem x3_zero : D.x3 0 = 1 := by
  have h := D.x3_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)
theorem x4_zero : D.x4 0 = 1 := by
  have h := D.x4_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)
theorem x5_zero : D.x5 0 = 1 := by
  have h := D.x5_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)
theorem x6_zero : D.x6 0 = 1 := by
  have h := D.x6_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem x1_sq (a : K) : D.x1 a * D.x1 a = 1 := by
  rw [← D.x1_add, D.add_self, D.x1_zero]
theorem x2_sq (a : k) : D.x2 a * D.x2 a = 1 := by
  rw [← D.x2_add, D.add_self_k, D.x2_zero]
theorem x3_sq (a : K) : D.x3 a * D.x3 a = 1 := by
  rw [← D.x3_add, D.add_self, D.x3_zero]
theorem x4_sq (a : K) : D.x4 a * D.x4 a = 1 := by
  rw [← D.x4_add, D.add_self, D.x4_zero]
theorem x5_sq (a : k) : D.x5 a * D.x5 a = 1 := by
  rw [← D.x5_add, D.add_self_k, D.x5_zero]
theorem x6_sq (a : k) : D.x6 a * D.x6 a = 1 := by
  rw [← D.x6_add, D.add_self_k, D.x6_zero]

theorem x1_inv (a : K) : (D.x1 a)⁻¹ = D.x1 a := inv_eq_of_mul_eq_one_right (D.x1_sq a)
theorem x2_inv (a : k) : (D.x2 a)⁻¹ = D.x2 a := inv_eq_of_mul_eq_one_right (D.x2_sq a)
theorem x3_inv (a : K) : (D.x3 a)⁻¹ = D.x3 a := inv_eq_of_mul_eq_one_right (D.x3_sq a)
theorem x4_inv (a : K) : (D.x4 a)⁻¹ = D.x4 a := inv_eq_of_mul_eq_one_right (D.x4_sq a)
theorem x5_inv (a : k) : (D.x5 a)⁻¹ = D.x5 a := inv_eq_of_mul_eq_one_right (D.x5_sq a)
theorem x6_inv (a : k) : (D.x6 a)⁻¹ = D.x6 a := inv_eq_of_mul_eq_one_right (D.x6_sq a)

@[expose] def nf (b : k) (u v : K) (e g : k) : P :=
  D.x2 b * (D.x3 u * (D.x4 v * (D.x5 e * D.x6 g)))

theorem L2 (a b : k) (u v : K) (e g : k) : D.x2 a * D.nf b u v e g = D.nf (a + b) u v e g := by
  rw [nf, nf, D.x2_add, mul_assoc]

theorem L3 (a : K) (b : k) (u v : K) (e g : k) :
    D.x3 a * D.nf b u v e g = D.nf b (a + u) v e g := by
  rw [nf, nf, (D.c23 b a).symm.left_comm, D.x3_add, mul_assoc]

theorem L6 (a : k) (b : k) (u v : K) (e g : k) :
    D.x6 a * D.nf b u v e g = D.nf b u v e (a + g) := by
  rw [nf, nf, (D.c26 b a).symm.left_comm, (D.c36 u a).symm.left_comm, (D.c46 v a).symm.left_comm,
    (D.c56 e a).symm.left_comm, D.x6_add]

theorem L4 (a : K) (b : k) (u v : K) (e g : k) :
    D.x4 a * D.nf b u v e g = D.nf b u (a + v) e (g + D.Tr (u * a)) := by
  have h := swap_of_comm_root (D.r34 u a)
  rw [D.x6_inv] at h
  calc D.x4 a * D.nf b u v e g
      = D.x2 b * (D.x4 a * (D.x3 u * (D.x4 v * (D.x5 e * D.x6 g)))) := by
        rw [nf, (D.c24 b a).symm.left_comm]
    _ = D.x2 b * (D.x6 (D.Tr (u * a)) * (D.x3 u * (D.x4 (a + v) * (D.x5 e * D.x6 g)))) := by
        rw [D.x4_add, ← mul_assoc (D.x4 a) (D.x3 u), h, mul_assoc, mul_assoc, mul_assoc,
          ← mul_assoc (D.x4 a)]
    _ = D.x6 (D.Tr (u * a)) * D.nf b u (a + v) e g := by
        rw [nf, (D.c26 b _).left_comm]
    _ = D.nf b u (a + v) e (g + D.Tr (u * a)) := by rw [D.L6, add_comm (D.Tr (u * a)) g]

theorem L5 (a : k) (b : k) (u v : K) (e g : k) :
    D.x5 a * D.nf b u v e g = D.nf b u v (a + e) (g + b * a) := by
  have h := swap_of_comm_root (D.r25 b a)
  rw [D.x6_inv] at h
  calc D.x5 a * D.nf b u v e g
      = (D.x5 a * D.x2 b) * (D.x3 u * (D.x4 v * (D.x5 e * D.x6 g))) := by rw [nf, ← mul_assoc]
    _ = D.x6 (b * a) * (D.x2 b * (D.x3 u * (D.x4 v * (D.x5 (a + e) * D.x6 g)))) := by
        rw [h, mul_assoc, mul_assoc (D.x2 b), (D.c35 u a).symm.left_comm,
          (D.c45 v a).symm.left_comm, D.x5_add, mul_assoc]
    _ = D.x6 (b * a) * D.nf b u v (a + e) g := by rw [nf]
    _ = D.nf b u v (a + e) (g + b * a) := by rw [D.L6, add_comm (b * a) g]

theorem nf_mul_nf (b b' : k) (u u' v v' : K) (e e' g g' : k) :
    D.nf b u v e g * D.nf b' u' v' e' g' =
      D.nf (b + b') (u + u') (v + v') (e + e') (g + g' + b' * e + D.Tr (u' * v)) := by
  calc D.nf b u v e g * D.nf b' u' v' e' g'
      = D.x2 b * (D.x3 u * (D.x4 v * (D.x5 e * (D.x6 g * D.nf b' u' v' e' g')))) := by
        simp only [nf, mul_assoc]
    _ = _ := by rw [D.L6, D.L5, D.L4, D.L3, D.L2]

@[expose] def gens : Set P :=
  Set.range D.x2 ∪ Set.range D.x3 ∪ Set.range D.x4 ∪ Set.range D.x5 ∪ Set.range D.x6

@[expose] def N : Subgroup P := Subgroup.closure D.gens

theorem nf_mem_N (b : k) (u v : K) (e g : k) : D.nf b u v e g ∈ D.N := by
  have h2 : D.x2 b ∈ D.N := Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inl ⟨b, rfl⟩))))
  have h3 : D.x3 u ∈ D.N := Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨u, rfl⟩))))
  have h4 : D.x4 v ∈ D.N := Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨v, rfl⟩)))
  have h5 : D.x5 e ∈ D.N := Subgroup.subset_closure (Or.inl (Or.inr ⟨e, rfl⟩))
  have h6 : D.x6 g ∈ D.N := Subgroup.subset_closure (Or.inr ⟨g, rfl⟩)
  exact Subgroup.mul_mem _ h2 (Subgroup.mul_mem _ h3 (Subgroup.mul_mem _ h4
    (Subgroup.mul_mem _ h5 h6)))

theorem gen_inv {y : P} (hy : y ∈ D.gens) : y⁻¹ = y := by
  rcases hy with (((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩
  · exact D.x2_inv a
  · exact D.x3_inv a
  · exact D.x4_inv a
  · exact D.x5_inv a
  · exact D.x6_inv a

theorem mem_N_iff {g : P} : g ∈ D.N ↔ ∃ b u v e g', g = D.nf b u v e g' := by
  constructor
  · intro hg
    refine Subgroup.closure_induction_left (p := fun g _ => ∃ b u v e g', g = D.nf b u v e g')
      ⟨0, 0, 0, 0, 0, ?_⟩ ?_ ?_ hg
    · simp [nf, D.x2_zero, D.x3_zero, D.x4_zero, D.x5_zero, D.x6_zero]
    · intro y hy z _ hz
      obtain ⟨b, u, v, e, g', rfl⟩ := hz
      rcases hy with (((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩
      · exact ⟨_, _, _, _, _, D.L2 a b u v e g'⟩
      · exact ⟨_, _, _, _, _, D.L3 a b u v e g'⟩
      · exact ⟨_, _, _, _, _, D.L4 a b u v e g'⟩
      · exact ⟨_, _, _, _, _, D.L5 a b u v e g'⟩
      · exact ⟨_, _, _, _, _, D.L6 a b u v e g'⟩
    · intro y hy z _ hz
      obtain ⟨b, u, v, e, g', rfl⟩ := hz
      rw [D.gen_inv hy]
      rcases hy with (((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩
      · exact ⟨_, _, _, _, _, D.L2 a b u v e g'⟩
      · exact ⟨_, _, _, _, _, D.L3 a b u v e g'⟩
      · exact ⟨_, _, _, _, _, D.L4 a b u v e g'⟩
      · exact ⟨_, _, _, _, _, D.L5 a b u v e g'⟩
      · exact ⟨_, _, _, _, _, D.L6 a b u v e g'⟩
  · rintro ⟨b, u, v, e, g', rfl⟩
    exact D.nf_mem_N b u v e g'

theorem x2_mem_N (b : k) : D.x2 b ∈ D.N :=
  Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inl ⟨b, rfl⟩))))
theorem x3_mem_N (b : K) : D.x3 b ∈ D.N :=
  Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨b, rfl⟩))))
theorem x4_mem_N (b : K) : D.x4 b ∈ D.N :=
  Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨b, rfl⟩)))
theorem x5_mem_N (b : k) : D.x5 b ∈ D.N :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨b, rfl⟩))
theorem x6_mem_N (b : k) : D.x6 b ∈ D.N :=
  Subgroup.subset_closure (Or.inr ⟨b, rfl⟩)

@[expose] noncomputable def Φ : (K × k × K × K × k × k) ≃ P := Equiv.ofBijective _ D.bij

theorem Φ_symm_x1_nf (a : K) (b : k) (u v : K) (e g : k) :
    D.Φ.symm (D.x1 a * D.nf b u v e g) = (a, b, u, v, e, g) := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem Φ_symm_nf (b : k) (u v : K) (e g : k) :
    D.Φ.symm (D.nf b u v e g) = (0, b, u, v, e, g) := by
  rw [← one_mul (D.nf b u v e g), ← D.x1_zero, Φ_symm_x1_nf]

@[expose] noncomputable def π1f (g : P) : K := (D.Φ.symm g).1

@[expose] noncomputable def ρf (g : P) : k × K × K × k :=
  ((D.Φ.symm g).2.1, (D.Φ.symm g).2.2.1, (D.Φ.symm g).2.2.2.1, (D.Φ.symm g).2.2.2.2.1)

@[expose] noncomputable def c6f (g : P) : k := (D.Φ.symm g).2.2.2.2.2

theorem π1f_x1_nf (a : K) (b : k) (u v : K) (e g : k) :
    D.π1f (D.x1 a * D.nf b u v e g) = a := by
  rw [π1f, Φ_symm_x1_nf]

theorem ρf_nf (b : k) (u v : K) (e g : k) : D.ρf (D.nf b u v e g) = (b, u, v, e) := by
  rw [ρf, Φ_symm_nf]

theorem c6f_nf (b : k) (u v : K) (e g : k) : D.c6f (D.nf b u v e g) = g := by
  rw [c6f, Φ_symm_nf]

theorem exists_x1_mul (g : P) : ∃ a : K, ∃ n ∈ D.N, g = D.x1 a * n := by
  obtain ⟨a, b, u, v, e, g', hg⟩ : ∃ a b u v e g', g = D.x1 a * D.nf b u v e g' :=
    ⟨(D.Φ.symm g).1, (D.Φ.symm g).2.1, (D.Φ.symm g).2.2.1, (D.Φ.symm g).2.2.2.1,
      (D.Φ.symm g).2.2.2.2.1, (D.Φ.symm g).2.2.2.2.2, by
        conv_lhs => rw [← D.Φ.apply_symm_apply g]
        rfl⟩
  exact ⟨a, _, D.nf_mem_N b u v e g', hg⟩

theorem π1f_x1_mul {n : P} (hn : n ∈ D.N) (a : K) : D.π1f (D.x1 a * n) = a := by
  obtain ⟨b, u, v, e, g, rfl⟩ := D.mem_N_iff.1 hn
  exact D.π1f_x1_nf a b u v e g

theorem mem_N_of_π1f {g : P} (h : D.π1f g = 0) : g ∈ D.N := by
  obtain ⟨a, n, hn, rfl⟩ := D.exists_x1_mul g
  rw [D.π1f_x1_mul hn] at h
  rw [h, D.x1_zero, one_mul]
  exact hn

theorem ρf_mul {n n' : P} (hn : n ∈ D.N) (hn' : n' ∈ D.N) :
    D.ρf (n * n') = D.ρf n + D.ρf n' := by
  obtain ⟨b, u, v, e, g, rfl⟩ := D.mem_N_iff.1 hn
  obtain ⟨b', u', v', e', g', rfl⟩ := D.mem_N_iff.1 hn'
  rw [D.nf_mul_nf, D.ρf_nf, D.ρf_nf, D.ρf_nf]
  rfl

theorem c6f_mul {n n' : P} (hn : n ∈ D.N) (hn' : n' ∈ D.N) :
    D.c6f (n * n') = D.c6f n + D.c6f n' + (D.ρf n').1 * (D.ρf n).2.2.2 +
      D.Tr ((D.ρf n').2.1 * (D.ρf n).2.2.1) := by
  obtain ⟨b, u, v, e, g, rfl⟩ := D.mem_N_iff.1 hn
  obtain ⟨b', u', v', e', g', rfl⟩ := D.mem_N_iff.1 hn'
  rw [D.nf_mul_nf, D.c6f_nf, D.c6f_nf, D.c6f_nf, D.ρf_nf, D.ρf_nf]

theorem ρf_one : D.ρf 1 = 0 := by
  have h : (1 : P) = D.nf 0 0 0 0 0 := by
    simp [nf, D.x2_zero, D.x3_zero, D.x4_zero, D.x5_zero, D.x6_zero]
  rw [h, D.ρf_nf]
  rfl

theorem ρf_inv {n : P} (hn : n ∈ D.N) : D.ρf n⁻¹ = - D.ρf n := by
  have h := D.ρf_mul hn (Subgroup.inv_mem _ hn)
  rw [mul_inv_cancel, D.ρf_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem ρf_conj_N {m n : P} (hm : m ∈ D.N) (hn : n ∈ D.N) : D.ρf (m * n * m⁻¹) = D.ρf n := by
  rw [D.ρf_mul (Subgroup.mul_mem _ hm hn) (Subgroup.inv_mem _ hm), D.ρf_mul hm hn,
    D.ρf_inv hm]
  abel

theorem cj2 (β : k) (s : K) :
    D.x1 s * D.x2 β * D.x1 s = D.nf β ((β : K) * s) ((β : K) * (σ s * σ (σ s))) (β * D.Nm s)
      (β * β * D.Nm s) := by
  have h := D.r21 β s
  rw [commutatorElement_def, D.x2_inv, D.x1_inv] at h
  have h2 := congrArg (D.x2 β * ·) h
  simp only [← mul_assoc, D.x2_sq, one_mul] at h2
  rw [h2]
  simp only [nf, mul_assoc]

theorem cj3 (s t : K) :
    D.x1 s * D.x3 t * D.x1 s = D.x4 (σ s * σ (σ t) + σ (σ s) * σ t) *
      D.x5 (D.Tr (s * σ s * σ (σ t))) * D.x6 (D.Tr (s * σ t * σ (σ t))) * D.x3 t := by
  rw [← D.r13]
  rw [commutatorElement_def, D.x1_inv]
  group

theorem cj4 (s t : K) : D.x1 s * D.x4 t * D.x1 s = D.x5 (D.Tr (s * t)) * D.x4 t := by
  rw [← D.r14, commutatorElement_def, D.x1_inv]
  group

theorem cj5 (s : K) (e : k) : D.x1 s * D.x5 e * D.x1 s = D.x5 e := by
  rw [(D.c15 s e).eq, mul_assoc, D.x1_sq, mul_one]

theorem cj6 (s : K) (e : k) : D.x1 s * D.x6 e * D.x1 s = D.x6 e := by
  rw [(D.c16 s e).eq, mul_assoc, D.x1_sq, mul_one]

theorem conj_nf (s : K) (b : k) (u v : K) (e g : k) :
    D.x1 s * D.nf b u v e g * D.x1 s =
      (D.x1 s * D.x2 b * D.x1 s) * ((D.x1 s * D.x3 u * D.x1 s) *
        ((D.x1 s * D.x4 v * D.x1 s) * ((D.x1 s * D.x5 e * D.x1 s) * (D.x1 s * D.x6 g * D.x1 s)))) := by
  have h := D.x1_sq s
  simp only [nf]
  calc D.x1 s * (D.x2 b * (D.x3 u * (D.x4 v * (D.x5 e * D.x6 g)))) * D.x1 s
      = D.x1 s * D.x2 b * (D.x1 s * D.x1 s) * D.x3 u * (D.x1 s * D.x1 s) * D.x4 v *
        (D.x1 s * D.x1 s) * D.x5 e * (D.x1 s * D.x1 s) * D.x6 g * D.x1 s := by
        rw [h]; simp only [mul_one, mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem conj_mem (s : K) {n : P} (hn : n ∈ D.N) : D.x1 s * n * D.x1 s ∈ D.N := by
  obtain ⟨b, u, v, e, g, rfl⟩ := D.mem_N_iff.1 hn
  rw [D.conj_nf, D.cj2, D.cj3, D.cj4, D.cj5, D.cj6]
  refine Subgroup.mul_mem _ (D.nf_mem_N _ _ _ _ _) (Subgroup.mul_mem _ ?_ (Subgroup.mul_mem _ ?_
    (Subgroup.mul_mem _ (D.x5_mem_N e) (D.x6_mem_N g))))
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (D.x4_mem_N _)
      (D.x5_mem_N _)) (D.x6_mem_N _)) (D.x3_mem_N u)
  · exact Subgroup.mul_mem _ (D.x5_mem_N _) (D.x4_mem_N v)

theorem π1f_mul (g h : P) : D.π1f (g * h) = D.π1f g + D.π1f h := by
  obtain ⟨a, n, hn, rfl⟩ := D.exists_x1_mul g
  obtain ⟨a', n', hn', rfl⟩ := D.exists_x1_mul h
  have e : D.x1 a * n * (D.x1 a' * n') =
      D.x1 (a + a') * ((D.x1 a' * n * D.x1 a') * n') := by
    rw [D.x1_add]
    calc D.x1 a * n * (D.x1 a' * n')
        = D.x1 a * (D.x1 a' * (D.x1 a' * n * D.x1 a')) * n' := by
          simp only [← mul_assoc, D.x1_sq, one_mul]
      _ = _ := by simp only [mul_assoc]
  rw [e, D.π1f_x1_mul (Subgroup.mul_mem _ (D.conj_mem a' hn) hn'), D.π1f_x1_mul hn,
    D.π1f_x1_mul hn']

@[expose] noncomputable def π1hom : P →* Multiplicative K :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (D.π1f g)) fun g h => by
    rw [D.π1f_mul]; rfl

@[expose] def Mfun (s : K) (w : k × K × K × k) : k × K × K × k :=
  (w.1, w.2.1 + (w.1 : K) * s,
    w.2.2.1 + (σ s * σ (σ w.2.1) + σ (σ s) * σ w.2.1) + (w.1 : K) * (σ s * σ (σ s)),
    w.2.2.2 + D.Tr (s * w.2.2.1) + D.Tr (s * σ s * σ (σ w.2.1)) + w.1 * D.Nm s)

theorem ρf_x3 (b : K) : D.ρf (D.x3 b) = (0, b, 0, 0) := by
  have h : D.x3 b = D.nf 0 b 0 0 0 := by
    simp [nf, D.x2_zero, D.x4_zero, D.x5_zero, D.x6_zero]
  rw [h, D.ρf_nf]
theorem ρf_x4 (b : K) : D.ρf (D.x4 b) = (0, 0, b, 0) := by
  have h : D.x4 b = D.nf 0 0 b 0 0 := by
    simp [nf, D.x2_zero, D.x3_zero, D.x5_zero, D.x6_zero]
  rw [h, D.ρf_nf]
theorem ρf_x5 (b : k) : D.ρf (D.x5 b) = (0, 0, 0, b) := by
  have h : D.x5 b = D.nf 0 0 0 b 0 := by
    simp [nf, D.x2_zero, D.x3_zero, D.x4_zero, D.x6_zero]
  rw [h, D.ρf_nf]
theorem ρf_x6 (b : k) : D.ρf (D.x6 b) = 0 := by
  have h : D.x6 b = D.nf 0 0 0 0 b := by
    simp [nf, D.x2_zero, D.x3_zero, D.x4_zero, D.x5_zero]
  rw [h, D.ρf_nf]
  rfl

theorem ρf_conj_nf (s : K) (b : k) (u v : K) (e g : k) :
    D.ρf (D.x1 s * D.nf b u v e g * D.x1 s) = D.Mfun s (b, u, v, e) := by
  rw [D.conj_nf, D.cj2, D.cj3, D.cj4, D.cj5, D.cj6]
  have m2 := D.x2_mem_N; have m3 := D.x3_mem_N; have m4 := D.x4_mem_N
  have m5 := D.x5_mem_N; have m6 := D.x6_mem_N
  have hB : D.x4 (σ s * σ (σ u) + σ (σ s) * σ u) * D.x5 (D.Tr (s * σ s * σ (σ u))) *
      D.x6 (D.Tr (s * σ u * σ (σ u))) * D.x3 u ∈ D.N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (m4 _) (m5 _)) (m6 _)) (m3 _)
  have hC : D.x5 (D.Tr (s * v)) * D.x4 v ∈ D.N := Subgroup.mul_mem _ (m5 _) (m4 _)
  have hE : D.x5 e * D.x6 g ∈ D.N := Subgroup.mul_mem _ (m5 _) (m6 _)
  have hCE : (D.x5 (D.Tr (s * v)) * D.x4 v) * (D.x5 e * D.x6 g) ∈ D.N :=
    Subgroup.mul_mem _ hC hE
  have hBCE : D.x4 (σ s * σ (σ u) + σ (σ s) * σ u) * D.x5 (D.Tr (s * σ s * σ (σ u))) *
      D.x6 (D.Tr (s * σ u * σ (σ u))) * D.x3 u * ((D.x5 (D.Tr (s * v)) * D.x4 v) *
        (D.x5 e * D.x6 g)) ∈ D.N := Subgroup.mul_mem _ hB hCE
  rw [D.ρf_mul (D.nf_mem_N _ _ _ _ _) hBCE, D.ρf_mul hB hCE, D.ρf_mul hC hE,
    D.ρf_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ (m4 _) (m5 _)) (m6 _)) (m3 _),
    D.ρf_mul (Subgroup.mul_mem _ (m4 _) (m5 _)) (m6 _), D.ρf_mul (m4 _) (m5 _),
    D.ρf_mul (m5 _) (m4 _), D.ρf_mul (m5 _) (m6 _), D.ρf_nf, D.ρf_x4, D.ρf_x5, D.ρf_x6,
    D.ρf_x3, D.ρf_x4, D.ρf_x5, D.ρf_x5, D.ρf_x6]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    simp only [Mfun, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.fst_zero, Prod.snd_zero] <;>
    ring

theorem ρf_conj_gen {g n : P} (hn : n ∈ D.N) :
    D.ρf (g * n * g⁻¹) = D.Mfun (D.π1f g) (D.ρf n) := by
  obtain ⟨a, m, hm, rfl⟩ := D.exists_x1_mul g
  have h : D.x1 a * m * n * (D.x1 a * m)⁻¹ = D.x1 a * (m * n * m⁻¹) * D.x1 a := by
    rw [mul_inv_rev, D.x1_inv]
    group
  rw [h, D.π1f_x1_mul hm]
  have hn' : m * n * m⁻¹ ∈ D.N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hn) (Subgroup.inv_mem _ hm)
  obtain ⟨b, u, v, e, g', hnf⟩ := D.mem_N_iff.1 hn'
  rw [hnf, D.ρf_conj_nf, ← D.ρf_conj_N hm hn, hnf, D.ρf_nf]

end D4Syl

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
