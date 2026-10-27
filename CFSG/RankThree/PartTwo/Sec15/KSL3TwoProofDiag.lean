module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiEigen
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.PartTwo.Sec15.KSL3Two

open Matrix

variable {L : Type} [Field L]

@[expose] noncomputable def eigProj (p : ℕ) (ζ : L) (a : Matrix (Fin 3) (Fin 3) L) (k : ℕ) :
    Matrix (Fin 3) (Fin 3) L :=
  (p : L)⁻¹ • ∑ i ∈ Finset.range p, ((ζ ^ k)⁻¹ • a) ^ i

theorem mul_eigProj {p : ℕ} {ζ : L} (hζ : ζ ^ p = 1) (hp : 0 < p)
    {a : Matrix (Fin 3) (Fin 3) L} (ha : a ^ p = 1) (k : ℕ) :
    a * eigProj p ζ a k = ζ ^ k • eigProj p ζ a k := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hζ
    exact zero_ne_one hζ
  set x := (ζ ^ k)⁻¹ • a with hx
  have hxp : x ^ p = 1 := by
    rw [hx, smul_pow, ha, inv_pow, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, inv_one, one_smul]
  have hgeom := mul_geom_sum x p
  rw [hxp, sub_self, sub_mul, one_mul, sub_eq_zero] at hgeom
  have h1 : a = ζ ^ k • x := by
    rw [hx, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hζ0), one_smul]
  have haS : a * (∑ i ∈ Finset.range p, x ^ i) = ζ ^ k • ∑ i ∈ Finset.range p, x ^ i := by
    conv_lhs => rw [h1]
    rw [Matrix.smul_mul, hgeom]
  unfold eigProj
  rw [Matrix.mul_smul, haS, smul_comm]

theorem sum_eigProj {p : ℕ} (hp0 : (p : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (a : Matrix (Fin 3) (Fin 3) L) : ∑ k ∈ Finset.range p, eigProj p ζ a k = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 :=
    ⟨p - 1, by have : p ≠ 0 := fun h => hp0 (by rw [h, Nat.cast_zero]); omega⟩
  unfold eigProj
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [smul_pow, ← Finset.sum_smul]
  rw [Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range n,
      (∑ k ∈ Finset.range (n + 1), ((ζ ^ k)⁻¹) ^ (i + 1)) = 0 := by
    intro i hi
    have e : ∀ k, ((ζ ^ k)⁻¹) ^ (i + 1) = ((ζ ^ (i + 1))⁻¹) ^ k := by
      intro k
      rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
    simp_rw [e]
    have hy1 : (ζ ^ (i + 1))⁻¹ ≠ 1 := by
      rw [Ne, inv_eq_one]
      exact hζ.pow_ne_one_of_pos_of_lt (by omega) (by simp at hi; omega)
    rw [geom_sum_eq hy1, inv_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, inv_one,
      sub_self, zero_div]
  rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, zero_smul]), zero_add]
  simp only [pow_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_smul]
  rw [inv_mul_cancel₀ hp0, one_smul]

theorem commute_eigProj {p : ℕ} {ζ : L} {a b : Matrix (Fin 3) (Fin 3) L} (hab : Commute a b)
    (k : ℕ) : Commute (eigProj p ζ a k) b := by
  unfold eigProj
  refine Commute.smul_left (Commute.sum_left _ _ _ fun i _ => ?_) _
  exact (hab.smul_left _).pow_left i

theorem exists_joint_eigenbasis {p : ℕ} (hp0 : (p : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    {a b : Matrix (Fin 3) (Fin 3) L} (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : Commute a b) :
    ∃ v : Fin 3 → (Fin 3 → L), LinearIndependent L v ∧
      ∀ i, ∃ α β : L, a *ᵥ v i = α • v i ∧ b *ᵥ v i = β • v i := by
  classical
  have hp : 0 < p := Nat.pos_of_ne_zero fun h => hp0 (by rw [h, Nat.cast_zero])
  set S : Set (Fin 3 → L) := Set.range fun x : ℕ × ℕ × Fin 3 =>
    (eigProj p ζ a x.1 * eigProj p ζ b x.2.1) *ᵥ Pi.single x.2.2 1 with hS
  have hSeig : ∀ w ∈ S, ∃ α β : L, a *ᵥ w = α • w ∧ b *ᵥ w = β • w := by
    rintro _ ⟨⟨k, l, j⟩, rfl⟩
    refine ⟨ζ ^ k, ζ ^ l, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, mul_eigProj hζ.pow_eq_one hp ha,
        Matrix.smul_mul, Matrix.smul_mulVec]
    · rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← (commute_eigProj hab k).eq,
        Matrix.mul_assoc, mul_eigProj hζ.pow_eq_one hp hb, Matrix.mul_smul, Matrix.smul_mulVec]
  have hspan : Submodule.span L S = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ j, v j • (Pi.single j (1 : L) : Fin 3 → L) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    have h1 : (∑ k ∈ Finset.range p, eigProj p ζ a k) *
        (∑ l ∈ Finset.range p, eigProj p ζ b l) = 1 := by
      rw [sum_eigProj hp0 hζ, sum_eigProj hp0 hζ, Matrix.one_mul]
    have hj : (Pi.single j (1 : L) : Fin 3 → L) = ∑ k ∈ Finset.range p,
        ∑ l ∈ Finset.range p, (eigProj p ζ a k * eigProj p ζ b l) *ᵥ
          (Pi.single j 1 : Fin 3 → L) := by
      calc (Pi.single j (1 : L) : Fin 3 → L) = (1 : Matrix (Fin 3) (Fin 3) L) *ᵥ
            (Pi.single j 1 : Fin 3 → L) := (Matrix.one_mulVec _).symm
        _ = _ := by
          rw [← h1, Finset.sum_mul, Matrix.sum_mulVec]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum, Matrix.sum_mulVec]
    rw [hj]
    exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
      Submodule.subset_span ⟨(k, l, j), rfl⟩
  obtain ⟨B, hBS, hBspan, hBli⟩ := exists_linearIndependent L S
  have hBtop : ⊤ ≤ Submodule.span L (Set.range ((↑) : B → Fin 3 → L)) := by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hBspan, hspan]
  set B' := Module.Basis.mk hBli hBtop
  have hfin : Finite B := Module.Finite.finite_basis B'
  have : Fintype B := Fintype.ofFinite B
  have hcard : Fintype.card B = 3 := by
    rw [← Module.finrank_eq_card_basis B', Module.finrank_fin_fun]
  set B'' := B'.reindex (Fintype.equivFinOfCardEq hcard)
  refine ⟨B'', B''.linearIndependent, fun i => ?_⟩
  have hmem : B'' i ∈ S := by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact hBS (Subtype.mem _)
  exact hSeig _ hmem

theorem exists_conj_diag {p : ℕ} (hp0 : (p : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    {a b : Matrix (Fin 3) (Fin 3) L} (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : Commute a b) :
    ∃ Q : Matrix (Fin 3) (Fin 3) L, IsUnit Q ∧ ∃ α β : Fin 3 → L,
      a * Q = Q * diagonal α ∧ b * Q = Q * diagonal β := by
  obtain ⟨v, hv, hab'⟩ := exists_joint_eigenbasis hp0 hζ ha hb hab
  choose α β hα hβ using hab'
  exact ⟨Sec4.colMat v, Sec4.isUnit_colMat hv, α, β, Sec4.mul_colMat_eq hα,
    Sec4.mul_colMat_eq hβ⟩

theorem mul_apply_self_of_isDiag {A B : Matrix (Fin 3) (Fin 3) L} (hA : A.IsDiag)
    (i : Fin 3) : (A * B) i i = A i i * B i i := by
  conv_lhs => rw [← hA.diagonal_diag]
  rw [Matrix.diagonal_mul]
  rfl

theorem exists_ne_diag_of_not_isCyclic {H : Subgroup (GL (Fin 3) L)} [Finite H]
    (hH : ¬ IsCyclic H) (hdiag : ∀ u ∈ H, (u : Matrix (Fin 3) (Fin 3) L).IsDiag)
    (hdet : ∀ u ∈ H, (u : Matrix (Fin 3) (Fin 3) L).det = 1) {i j : Fin 3} (hij : i ≠ j) :
    ∃ u ∈ H, (u : Matrix (Fin 3) (Fin 3) L) i i ≠ (u : Matrix (Fin 3) (Fin 3) L) j j := by
  by_contra hall
  push Not at hall
  let χ : H →* L :=
    { toFun := fun u => ((u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i i
      map_one' := by simp
      map_mul' := fun u v => by
        simp only [Subgroup.coe_mul, Units.val_mul]
        exact mul_apply_self_of_isDiag (hdiag u u.2) i }
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hi : ((u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i i = 1 := hu
    have hj : ((u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) j j = 1 := by
      rw [← hall _ u.2, hi]
    have hD := (hdiag u u.2).diagonal_diag
    have hd := hdet u u.2
    rw [← hD, det_diagonal, Fin.prod_univ_three] at hd
    simp only [Matrix.diag_apply] at hd
    have hall1 : ∀ k, ((u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) k k = 1 := by
      intro k
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_one, Units.val_one, ← hD]
    rw [← Matrix.diagonal_one]
    congr 1
    funext k
    exact hall1 k
  exact hH (isCyclic_of_injective_ringHom χ hinj)

theorem isDiag_of_commute {H : Subgroup (GL (Fin 3) L)}
    (hdiag : ∀ u ∈ H, (u : Matrix (Fin 3) (Fin 3) L).IsDiag)
    (hsep : ∀ i j : Fin 3, i ≠ j →
      ∃ u ∈ H, (u : Matrix (Fin 3) (Fin 3) L) i i ≠ (u : Matrix (Fin 3) (Fin 3) L) j j)
    {M : Matrix (Fin 3) (Fin 3) L}
    (hM : ∀ u ∈ H, (u : Matrix (Fin 3) (Fin 3) L) * M = M * u) : M.IsDiag := by
  intro i j hij
  obtain ⟨u, hu, hne⟩ := hsep i j hij
  have h := congrFun (congrFun (hM u hu) i) j
  rw [← (hdiag u hu).diagonal_diag, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  simp only [Matrix.diag_apply] at h
  have h' : (((u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i i -
      ((u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) j j) * M i j = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)

theorem commute_of_isDiag {A B : Matrix (Fin 3) (Fin 3) L} (hA : A.IsDiag) (hB : B.IsDiag) :
    A * B = B * A := by
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

@[expose] def IsMonomialWith (G : Matrix (Fin 3) (Fin 3) L) (σ : Fin 3 → Fin 3) : Prop :=
  ∀ i j, G j i ≠ 0 ↔ j = σ i

theorem IsMonomialWith.unique {G : Matrix (Fin 3) (Fin 3) L} {σ σ' : Fin 3 → Fin 3}
    (h : IsMonomialWith G σ) (h' : IsMonomialWith G σ') : σ = σ' := by
  funext i
  exact (h' i (σ i)).mp ((h i (σ i)).mpr rfl)

theorem IsMonomialWith.mul {G G' : Matrix (Fin 3) (Fin 3) L} {σ σ' : Fin 3 → Fin 3}
    (h : IsMonomialWith G σ) (h' : IsMonomialWith G' σ') : IsMonomialWith (G * G') (σ ∘ σ') := by
  intro i j
  have hsum : (G * G') j i = G j (σ' i) * G' (σ' i) i := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ' i)]
    · intro k _ hk
      have : G' k i = 0 := by
        by_contra h0
        exact hk ((h' i k).mp h0)
      rw [this, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  have hG' : G' (σ' i) i ≠ 0 := (h' i (σ' i)).mpr rfl
  rw [hsum, Function.comp_apply]
  constructor
  · intro hne
    exact (h (σ' i) j).mp (left_ne_zero_of_mul hne)
  · intro hj
    exact mul_ne_zero ((h (σ' i) j).mpr hj) hG'

theorem isMonomialWith_smul_one {c : L} (hc : c ≠ 0) :
    IsMonomialWith (c • (1 : Matrix (Fin 3) (Fin 3) L)) id := by
  intro i j
  rw [Matrix.smul_apply, Matrix.one_apply, id]
  by_cases hji : j = i
  · simp [hji, hc]
  · simp [hji]

theorem IsMonomialWith.isDiag {G : Matrix (Fin 3) (Fin 3) L} (h : IsMonomialWith G id) :
    G.IsDiag := by
  intro j i hji
  by_contra h0
  exact hji ((h i j).mp h0)

theorem exists_monomial_of_normalizes {H : Subgroup (GL (Fin 3) L)}
    (hdiag : ∀ u ∈ H, (u : Matrix (Fin 3) (Fin 3) L).IsDiag)
    (hsep : ∀ i j : Fin 3, i ≠ j →
      ∃ u ∈ H, (u : Matrix (Fin 3) (Fin 3) L) i i ≠ (u : Matrix (Fin 3) (Fin 3) L) j j)
    {G : GL (Fin 3) L} (hG : ∀ u ∈ H, G⁻¹ * u * G ∈ H) :
    ∃ σ : Fin 3 → Fin 3, IsMonomialWith (G : Matrix (Fin 3) (Fin 3) L) σ := by
  have hcol : ∀ i, ∃ j, (G : Matrix (Fin 3) (Fin 3) L) j i ≠ 0 := by
    intro i
    by_contra hall
    push Not at hall
    have h0 : (G : Matrix (Fin 3) (Fin 3) L).det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero i hall
    exact (G.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) L →* L)).ne_zero h0
  have key : ∀ u ∈ H, ∀ i j, (G : Matrix (Fin 3) (Fin 3) L) j i ≠ 0 →
      (u : Matrix (Fin 3) (Fin 3) L) j j =
        ((G⁻¹ * u * G : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i i := by
    intro u hu i j hji
    obtain ⟨u', hu'⟩ : ∃ u', u' = G⁻¹ * u * G := ⟨_, rfl⟩
    rw [← hu']
    have hu'H : u' ∈ H := hu' ▸ hG u hu
    have hc : u * G = G * u' := by rw [hu']; group
    have hm := congrArg (fun A : GL (Fin 3) L => (A : Matrix (Fin 3) (Fin 3) L) j i) hc
    simp only [Units.val_mul] at hm
    have hud : (u : Matrix (Fin 3) (Fin 3) L) = diagonal (u : Matrix (Fin 3) (Fin 3) L).diag :=
      (hdiag u hu).diagonal_diag.symm
    have hu'd : (u' : Matrix (Fin 3) (Fin 3) L) =
        diagonal (u' : Matrix (Fin 3) (Fin 3) L).diag := (hdiag u' hu'H).diagonal_diag.symm
    rw [hud, hu'd, Matrix.diagonal_mul, Matrix.mul_diagonal] at hm
    simp only [Matrix.diag_apply] at hm
    have hm' : (G : Matrix (Fin 3) (Fin 3) L) j i * ((u : Matrix (Fin 3) (Fin 3) L) j j -
        (u' : Matrix (Fin 3) (Fin 3) L) i i) = 0 := by
      linear_combination hm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm').resolve_left hji)
  choose σ hσ using hcol
  refine ⟨σ, fun i j => ⟨fun hji => ?_, fun hj => hj ▸ hσ i⟩⟩
  by_contra hne
  obtain ⟨u, hu, hne'⟩ := hsep j (σ i) hne
  exact hne' ((key u hu i j hji).trans (key u hu i (σ i) (hσ i)).symm)

end CFSG.RankThree.PartTwo.Sec15.KSL3Two
