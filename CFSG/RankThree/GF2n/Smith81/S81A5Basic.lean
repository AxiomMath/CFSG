module

public import TauCeti.RepresentationTheory.ClassicalGroups.ExteriorPower
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open exteriorPower Matrix

variable (K : Type*) [Field K]

abbrev Cube : Type _ := ⋀[K]^3 (Fin 6 → K)

abbrev rho (g : GL (Fin 6) K) : Cube K →ₗ[K] Cube K := TauCeti.extPowerRep K 6 3 g

@[expose] def cubeBasis : Module.Basis (Set.powersetCard (Fin 6) 3) K (Cube K) :=
  (Pi.basisFun K (Fin 6)).exteriorPower 3

@[expose] def coord (ξ : Cube K) (I : Set.powersetCard (Fin 6) 3) : K := (cubeBasis K).repr ξ I

abbrev enum (I : Set.powersetCard (Fin 6) 3) : Fin 3 ↪o Fin 6 :=
  Set.powersetCard.ofFinEmbEquiv.symm I

@[expose] def tau (I : Set.powersetCard (Fin 6) 3) : ℕ := (I.val.filter (fun i => i.val < 2)).card

@[expose] def IsPure (ξ : Cube K) : Prop := ∃ v : Fin 3 → Fin 6 → K, ξ = ιMulti K 3 v

abbrev e (i : Fin 6) : Fin 6 → K := Pi.single i 1

@[expose] def W2 : Submodule K (Fin 6 → K) where
  carrier := {n | ∀ j : Fin 6, 2 ≤ j.val → n j = 0}
  add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ ha j hj => by simp [ha j hj]

@[expose] def W4 : Submodule K (Fin 6 → K) where
  carrier := {n | n 0 = 0 ∧ n 1 = 0}
  add_mem' := fun ha hb => by simp [ha.1, hb.1, ha.2, hb.2]
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c _ ha => by simp [ha.1, ha.2]

theorem rho_ιMulti (g : GL (Fin 6) K) (v : Fin 3 → Fin 6 → K) :
    rho K g (ιMulti K 3 v) =
      ιMulti K 3 (fun i => (g : Matrix (Fin 6) (Fin 6) K).mulVec (v i)) := by
  rw [rho, Representation.exteriorPower_apply, TauCeti.stdRep_apply,
    exteriorPower.map_apply_ιMulti]
  rfl

theorem coord_ιMulti (v : Fin 3 → Fin 6 → K) (I : Set.powersetCard (Fin 6) 3) :
    coord K (ιMulti K 3 v) I = (Matrix.of fun i j => v i (enum I j)).det := by
  have h := congrArg (fun f => f (ιMulti K 3 v))
    (exteriorPower.basis_coord K 3 (Pi.basisFun K (Fin 6)) I)
  simp only [Module.Basis.coord_apply] at h
  unfold coord cubeBasis
  rw [h, exteriorPower.ιMultiDual_apply_ιMulti]
  simp

variable {K}

@[expose] def minor3 (v : Fin 3 → Fin 6 → K) (i j k : Fin 6) : K :=
  (Matrix.of fun r (s : Fin 3) => v r (![i, j, k] s)).det

theorem IsPure.rho {ξ : Cube K} (h : IsPure K ξ) (g : GL (Fin 6) K) : IsPure K (rho K g ξ) := by
  obtain ⟨v, rfl⟩ := h
  exact ⟨_, rho_ιMulti K g v⟩

theorem isPure_zero : IsPure K (0 : Cube K) :=
  ⟨fun _ => 0, ((ιMulti K 3).map_coord_zero (0 : Fin 3) rfl).symm⟩

theorem mem_W2_iff {a : Fin 6 → K} : a ∈ W2 K ↔ ∀ j : Fin 6, 2 ≤ j.val → a j = 0 := Iff.rfl

theorem e_mem_W2 {i : Fin 6} (hi : i.val < 2) : e K i ∈ W2 K := by
  intro j hj
  have : j ≠ i := fun h => by subst h; omega
  simp [Pi.single_apply, this]

theorem e_mem_W4 {i : Fin 6} (hi : 2 ≤ i.val) : e K i ∈ W4 K := by
  have h0 : (0 : Fin 6) ≠ i := fun h => by subst h; simp at hi
  have h1 : (1 : Fin 6) ≠ i := fun h => by subst h; simp at hi
  exact ⟨by simp [Pi.single_apply, h0], by simp [Pi.single_apply, h1]⟩

theorem coord_add (a b : Cube K) (I : Set.powersetCard (Fin 6) 3) :
    coord K (a + b) I = coord K a I + coord K b I := by simp [coord]

theorem coord_smul (c : K) (a : Cube K) (I : Set.powersetCard (Fin 6) 3) :
    coord K (c • a) I = c * coord K a I := by simp [coord]

theorem coord_zero (I : Set.powersetCard (Fin 6) 3) : coord K (0 : Cube K) I = 0 := by
  simp [coord]

theorem sumExtend_inl_apply {ι V : Type*} [AddCommGroup V] [Module K V] {v : ι → V}
    (hs : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend hs (Sum.inl i) = v i := by
  simp only [Module.Basis.sumExtend, Module.Basis.reindex_apply, Equiv.symm_symm,
    Module.Basis.extend_apply_self]
  rfl

theorem exists_sl_of_linearIndependent {n k : ℕ} (hk : k < n) {v w : Fin k → Fin n → K}
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    ∃ g : Matrix (Fin n) (Fin n) K, g.det = 1 ∧ ∀ i, g.mulVec (v i) = w i := by
  classical
  have hf₁ : Finite (Fin k ⊕ Module.Basis.sumExtendIndex hv) :=
    Module.Finite.finite_basis (Module.Basis.sumExtend hv)
  have hf₂ : Finite (Fin k ⊕ Module.Basis.sumExtendIndex hw) :=
    Module.Finite.finite_basis (Module.Basis.sumExtend hw)
  haveI : Finite (Module.Basis.sumExtendIndex hv) :=
    Finite.of_injective (Sum.inr : Module.Basis.sumExtendIndex hv → Fin k ⊕ _) Sum.inr_injective
  haveI : Finite (Module.Basis.sumExtendIndex hw) :=
    Finite.of_injective (Sum.inr : Module.Basis.sumExtendIndex hw → Fin k ⊕ _) Sum.inr_injective
  letI := Fintype.ofFinite (Module.Basis.sumExtendIndex hv)
  letI := Fintype.ofFinite (Module.Basis.sumExtendIndex hw)
  have h₁ := Module.finrank_eq_card_basis (Module.Basis.sumExtend hv)
  have h₂ := Module.finrank_eq_card_basis (Module.Basis.sumExtend hw)
  rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h₁ h₂
  have hcard : Fintype.card (Module.Basis.sumExtendIndex hv) =
      Fintype.card (Module.Basis.sumExtendIndex hw) := by omega
  let σ : Module.Basis.sumExtendIndex hv ≃ Module.Basis.sumExtendIndex hw :=
    Fintype.equivOfCardEq hcard
  let e : (Fin k ⊕ Module.Basis.sumExtendIndex hv) ≃ (Fin k ⊕ Module.Basis.sumExtendIndex hw) :=
    Equiv.sumCongr (Equiv.refl _) σ
  let g₁ : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Module.Basis.sumExtend hv).equiv (Module.Basis.sumExtend hw) e
  have hg₁ : ∀ i, (g₁ : (Fin n → K) →ₗ[K] (Fin n → K)) (v i) = w i := by
    intro i
    rw [← sumExtend_inl_apply hv i, ← sumExtend_inl_apply hw i]
    simp [g₁, e]
  have hne : Nonempty (Module.Basis.sumExtendIndex hw) := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨j₀⟩ := hne
  have hunit : IsUnit (LinearMap.det (g₁ : (Fin n → K) →ₗ[K] (Fin n → K))) :=
    LinearEquiv.isUnit_det' g₁
  obtain ⟨c, hc⟩ : ∃ c : K, c * LinearMap.det (g₁ : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 :=
    ⟨_, inv_mul_cancel₀ hunit.ne_zero⟩
  let φ : Fin k ⊕ Module.Basis.sumExtendIndex hw → K := fun j => if j = Sum.inr j₀ then c else 1
  let h : (Fin n → K) →ₗ[K] (Fin n → K) :=
    (Module.Basis.sumExtend hw).constr K (fun j => φ j • (Module.Basis.sumExtend hw) j)
  have hh : ∀ i, h (w i) = w i := by
    intro i
    rw [← sumExtend_inl_apply hw i]
    simp [h, φ, Module.Basis.constr_basis]
  have hdet : LinearMap.det h = c := by
    rw [← LinearMap.det_toMatrix (Module.Basis.sumExtend hw) h]
    have hhb : ∀ j, h ((Module.Basis.sumExtend hw) j) = φ j • (Module.Basis.sumExtend hw) j := by
      intro j
      simp only [h, Module.Basis.constr_basis]
    have hM : LinearMap.toMatrix (Module.Basis.sumExtend hw) (Module.Basis.sumExtend hw) h =
        Matrix.diagonal φ := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [LinearMap.toMatrix_apply, hhb, Module.Basis.repr_self, Finsupp.single_apply,
          Matrix.diagonal_apply]
      · simp [LinearMap.toMatrix_apply, hhb, Module.Basis.repr_self, Finsupp.single_apply,
          Matrix.diagonal_apply, hij, Ne.symm hij]
    rw [hM, Matrix.det_diagonal]
    simp [φ, Finset.prod_ite_eq']
  refine ⟨LinearMap.toMatrix' h * LinearMap.toMatrix' (g₁ : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩
  · rw [Matrix.det_mul, LinearMap.det_toMatrix', LinearMap.det_toMatrix', hdet]
    exact hc
  · intro i
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hg₁ i, hh i]

theorem linearIndependent_of_ιMulti_ne_zero {v : Fin 3 → Fin 6 → K} (h : ιMulti K 3 v ≠ 0) :
    LinearIndependent K v := by
  by_contra hdep
  exact h (AlternatingMap.map_linearDependent (ιMulti K 3) v hdep)

theorem isPure_transitive {ξ η : Cube K} (hξ : IsPure K ξ) (hη : IsPure K η) (hξ0 : ξ ≠ 0)
    (hη0 : η ≠ 0) :
    ∃ g : GL (Fin 6) K, (g : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ rho K g ξ = η := by
  obtain ⟨v, rfl⟩ := hξ
  obtain ⟨u, rfl⟩ := hη
  obtain ⟨g, hdet, hgv⟩ := exists_sl_of_linearIndependent (by norm_num : 3 < 6)
    (linearIndependent_of_ιMulti_ne_zero hξ0) (linearIndependent_of_ιMulti_ne_zero hη0)
  have hg0 : g.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg0, ?_, ?_⟩
  · show g.det = 1
    exact hdet
  · rw [rho_ιMulti]
    congr 1
    funext i
    show g.mulVec (v i) = u i
    exact hgv i

theorem ι3_add_fst (x x' y w : Fin 6 → K) :
    ιMulti K 3 ![x + x', y, w] = ιMulti K 3 ![x, y, w] + ιMulti K 3 ![x', y, w] := by
  have h := (ιMulti K 3).map_update_add ![x, y, w] 0 x x'
  have h1 : Function.update ![x, y, w] 0 (x + x') = ![x + x', y, w] := by
    funext i; fin_cases i <;> simp
  have h2 : Function.update ![x, y, w] 0 x = ![x, y, w] := by
    funext i; fin_cases i <;> simp
  have h3 : Function.update ![x, y, w] 0 x' = ![x', y, w] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2, h3] at h
  exact h

theorem ι3_smul_fst (c : K) (x y w : Fin 6 → K) :
    ιMulti K 3 ![c • x, y, w] = c • ιMulti K 3 ![x, y, w] := by
  have h := (ιMulti K 3).map_update_smul ![x, y, w] 0 c x
  have h1 : Function.update ![x, y, w] 0 (c • x) = ![c • x, y, w] := by
    funext i; fin_cases i <;> simp
  have h2 : Function.update ![x, y, w] 0 x = ![x, y, w] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2] at h
  exact h

theorem ι3_add_snd (x y y' w : Fin 6 → K) :
    ιMulti K 3 ![x, y + y', w] = ιMulti K 3 ![x, y, w] + ιMulti K 3 ![x, y', w] := by
  have h := (ιMulti K 3).map_update_add ![x, y, w] 1 y y'
  have h1 : Function.update ![x, y, w] 1 (y + y') = ![x, y + y', w] := by
    funext i; fin_cases i <;> simp
  have h2 : Function.update ![x, y, w] 1 y = ![x, y, w] := by
    funext i; fin_cases i <;> simp
  have h3 : Function.update ![x, y, w] 1 y' = ![x, y', w] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2, h3] at h
  exact h

theorem ι3_smul_snd (c : K) (x y w : Fin 6 → K) :
    ιMulti K 3 ![x, c • y, w] = c • ιMulti K 3 ![x, y, w] := by
  have h := (ιMulti K 3).map_update_smul ![x, y, w] 1 c y
  have h1 : Function.update ![x, y, w] 1 (c • y) = ![x, c • y, w] := by
    funext i; fin_cases i <;> simp
  have h2 : Function.update ![x, y, w] 1 y = ![x, y, w] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2] at h
  exact h

theorem ι3_add_thd (x y w w' : Fin 6 → K) :
    ιMulti K 3 ![x, y, w + w'] = ιMulti K 3 ![x, y, w] + ιMulti K 3 ![x, y, w'] := by
  have h := (ιMulti K 3).map_update_add ![x, y, w] 2 w w'
  have h1 : Function.update ![x, y, w] 2 (w + w') = ![x, y, w + w'] := by
    funext i; fin_cases i <;> simp
  have h2 : Function.update ![x, y, w] 2 w = ![x, y, w] := by
    funext i; fin_cases i <;> simp
  have h3 : Function.update ![x, y, w] 2 w' = ![x, y, w'] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2, h3] at h
  exact h

theorem ι3_smul_thd (c : K) (x y w : Fin 6 → K) :
    ιMulti K 3 ![x, y, c • w] = c • ιMulti K 3 ![x, y, w] := by
  have h := (ιMulti K 3).map_update_smul ![x, y, w] 2 c w
  have h1 : Function.update ![x, y, w] 2 (c • w) = ![x, y, c • w] := by
    funext i; fin_cases i <;> simp
  have h2 : Function.update ![x, y, w] 2 w = ![x, y, w] := by
    funext i; fin_cases i <;> simp
  rw [h1, h2] at h
  exact h

theorem ι3_eq_fst_snd (x z : Fin 6 → K) : ιMulti K 3 ![x, x, z] = 0 :=
  (ιMulti K 3).map_eq_zero_of_eq _ (i := 0) (j := 1) (by simp) (by decide)

theorem ι3_eq_fst_thd (x y : Fin 6 → K) : ιMulti K 3 ![x, y, x] = 0 :=
  (ιMulti K 3).map_eq_zero_of_eq _ (i := 0) (j := 2) (by simp) (by decide)

theorem ι3_eq_snd_thd (x z : Fin 6 → K) : ιMulti K 3 ![z, x, x] = 0 :=
  (ιMulti K 3).map_eq_zero_of_eq _ (i := 1) (j := 2) (by simp) (by decide)

theorem ι3_swap_e01 (w : Fin 6 → K) :
    ιMulti K 3 ![e K 1, e K 0, w] = -ιMulti K 3 ![e K 0, e K 1, w] := by
  have h := (ιMulti K 3).map_swap ![e K 0, e K 1, w] (i := 0) (j := 1) (by decide)
  have h' : (![e K 0, e K 1, w] ∘ Equiv.swap (0 : Fin 3) 1) = ![e K 1, e K 0, w] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [h'] at h
  exact h

theorem ι3_bilin (p q r s : K) (w : Fin 6 → K) :
    ιMulti K 3 ![p • e K 0 + q • e K 1, r • e K 0 + s • e K 1, w] =
      (p * s - q * r) • ιMulti K 3 ![e K 0, e K 1, w] := by
  simp only [ι3_add_fst, ι3_add_snd, ι3_smul_fst, ι3_smul_snd, ι3_eq_fst_snd, ι3_swap_e01,
    smul_zero, add_zero, zero_add]
  module

theorem eq_smul_e_add_smul_e_of_mem_W2 {a : Fin 6 → K} (ha : a ∈ W2 K) :
    a = a 0 • e K 0 + a 1 • e K 1 := by
  funext j
  obtain ⟨k, hk⟩ := j
  rcases (show k < 2 ∨ 2 ≤ k by omega) with h | h
  · interval_cases k <;> simp [e, Pi.single_apply]
  · have hj : a ⟨k, hk⟩ = 0 := (mem_W2_iff.mp ha) ⟨k, hk⟩ h
    have h0 : (⟨k, hk⟩ : Fin 6) ≠ 0 := fun h' => by
      rw [Fin.ext_iff] at h'; simp at h'; omega
    have h1 : (⟨k, hk⟩ : Fin 6) ≠ 1 := fun h' => by
      rw [Fin.ext_iff] at h'; simp at h'; omega
    simp [e, Pi.single_apply, hj, h0, h1]

theorem ιMulti_W2_two {a b : Fin 6 → K} (ha : a ∈ W2 K) (hb : b ∈ W2 K) (w : Fin 6 → K) :
    ιMulti K 3 ![a, b, w] = (a 0 * b 1 - a 1 * b 0) • ιMulti K 3 ![e K 0, e K 1, w] := by
  have key := ι3_bilin (a 0) (a 1) (b 0) (b 1) w
  rw [← eq_smul_e_add_smul_e_of_mem_W2 ha, ← eq_smul_e_add_smul_e_of_mem_W2 hb] at key
  exact key

end CFSG.RankThree.GF2n.Smith81.A5Cube
