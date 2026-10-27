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
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
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

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix

section Diag

variable {n : ℕ} {K : Type} [Field K]

@[expose] def diagU (d : Fin n → Kˣ) : GL (Fin n) K where
  val := Matrix.diagonal fun i => (d i : K)
  inv := Matrix.diagonal fun i => (((d i)⁻¹ : Kˣ) : K)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => (d i : K) * (((d i)⁻¹ : Kˣ) : K)) = fun _ => 1 := funext fun i => by simp
    rw [this, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => (((d i)⁻¹ : Kˣ) : K) * (d i : K)) = fun _ => 1 := funext fun i => by simp
    rw [this, Matrix.diagonal_one]

theorem diagU_val (d : Fin n → Kˣ) :
    ((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun i => (d i : K) :=
  rfl

theorem diagU_mul (d e : Fin n → Kˣ) : (diagU d : GL (Fin n) K) * diagU e = diagU (d * e) := by
  apply Units.ext
  simp [diagU_val, Matrix.diagonal_mul_diagonal]

theorem diagU_one : (diagU (1 : Fin n → Kˣ) : GL (Fin n) K) = 1 := by
  apply Units.ext
  simp [diagU_val]

theorem diagU_pow (d : Fin n → Kˣ) (m : ℕ) :
    (diagU d : GL (Fin n) K) ^ m = diagU (d ^ m) := by
  induction m with
  | zero => simp [diagU_one]
  | succ m ih => rw [pow_succ, ih, diagU_mul, pow_succ]

@[expose] def diagUHom : (Fin n → Kˣ) →* GL (Fin n) K where
  toFun := diagU
  map_one' := diagU_one
  map_mul' d e := (diagU_mul d e).symm

theorem diagU_injective : Function.Injective (diagU : (Fin n → Kˣ) → GL (Fin n) K) := by
  intro d e hde
  funext i
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i i) hde
  simp only [diagU_val, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

theorem isDiag_diagU (d : Fin n → Kˣ) :
    ((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag :=
  Matrix.isDiag_diagonal _

theorem diagU_apply_same (d : Fin n → Kˣ) (i : Fin n) :
    ((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = (d i : K) := by
  simp [diagU_val]

theorem det_diagU (d : Fin n → Kˣ) :
    ((diagU d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ∏ i, (d i : K) := by
  simp [diagU_val, Matrix.det_diagonal]

theorem exists_diagU_of_isDiag {g : GL (Fin n) K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag) :
    ∃ d : Fin n → Kˣ, diagU d = g := by
  classical
  have hdet : IsUnit ((g : Matrix (Fin n) (Fin n) K).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hne : ∀ i, (g : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
    intro i h0
    have : (g : Matrix (Fin n) (Fin n) K).det = 0 := by
      rw [← hg.diagonal_diag, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using h0)
    rw [this] at hdet
    exact not_isUnit_zero hdet
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  rw [diagU_val]
  simp only [Units.val_mk0]
  exact hg.diagonal_diag

end Diag

section Torus

variable {K : Type} [Field K]

@[expose] def torusVec (p n : ℕ) (K : Type) [Field K] : Subgroup (Fin n → Kˣ) where
  carrier := {d | (∀ i, d i ^ p = 1) ∧ ∏ i, d i = 1}
  mul_mem' := fun {a b} ha hb => ⟨fun i => by simp [mul_pow, ha.1 i, hb.1 i],
    by simp [Finset.prod_mul_distrib, ha.2, hb.2]⟩
  one_mem' := ⟨fun i => by simp, by simp⟩
  inv_mem' := fun {a} ha => ⟨fun i => by simp [inv_pow, ha.1 i],
    by simp [Finset.prod_inv_distrib, ha.2]⟩

@[expose] def torusSU (p n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  (torusVec p n K).map diagUHom

theorem mem_torusSU_iff {p n : ℕ} {g : GL (Fin n) K} :
    g ∈ torusSU p n K ↔ ∃ d : Fin n → Kˣ, (∀ i, d i ^ p = 1) ∧ ∏ i, d i = 1 ∧ diagU d = g := by
  constructor
  · rintro ⟨d, ⟨h1, h2⟩, rfl⟩
    exact ⟨d, h1, h2, rfl⟩
  · rintro ⟨d, h1, h2, rfl⟩
    exact ⟨d, ⟨h1, h2⟩, rfl⟩

theorem card_torusVec_le [Finite K] {p : ℕ} (hp : 0 < p) (m : ℕ) :
    Nat.card (torusVec p (m + 1) K) ≤ p ^ m := by
  classical
  have : NeZero p := ⟨hp.ne'⟩
  have : Fintype K := Fintype.ofFinite K
  let φ : torusVec p (m + 1) K → (Fin m → rootsOfUnity p K) := fun d i =>
    ⟨d.1 (Fin.castSucc i), (mem_rootsOfUnity p _).mpr (d.2.1 _)⟩
  have hφ : Function.Injective φ := by
    intro d e hde
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h1 := d.2.2
      have h2 := e.2.2
      rw [Fin.prod_univ_castSucc] at h1 h2
      have : ∏ j : Fin m, d.1 (Fin.castSucc j) = ∏ j : Fin m, e.1 (Fin.castSucc j) :=
        Finset.prod_congr rfl fun j _ => by
          have := congrFun hde j
          exact congrArg (fun x : rootsOfUnity p K => (x : Kˣ)) this
      rw [this] at h1
      exact mul_left_cancel (h1.trans h2.symm)
    · exact congrArg (fun x : rootsOfUnity p K => (x : Kˣ)) (congrFun hde j)
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card (Fin m → rootsOfUnity p K) = Nat.card (rootsOfUnity p K) ^ m := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h3 : Nat.card (rootsOfUnity p K) ≤ p := card_rootsOfUnity K p
  calc Nat.card (torusVec p (m + 1) K) ≤ Nat.card (Fin m → rootsOfUnity p K) := h1
    _ = Nat.card (rootsOfUnity p K) ^ m := h2
    _ ≤ p ^ m := Nat.pow_le_pow_left h3 m

theorem card_torusSU_le [Finite K] {p : ℕ} (hp : 0 < p) (m : ℕ) :
    Nat.card (torusSU p (m + 1) K) ≤ p ^ m := by
  rw [torusSU, Subgroup.card_map_of_injective diagU_injective]
  exact card_torusVec_le hp m

variable {n : ℕ}

@[expose] def torusElt (i j : Fin n) (u : Kˣ) : Fin n → Kˣ := Pi.mulSingle i u * Pi.mulSingle j u⁻¹

theorem torusElt_apply_left {i j : Fin n} (hij : i ≠ j) (u : Kˣ) : torusElt i j u i = u := by
  simp [torusElt, hij]

theorem torusElt_apply_right {i j : Fin n} (hij : i ≠ j) (u : Kˣ) : torusElt i j u j = u⁻¹ := by
  simp [torusElt, hij.symm]

theorem torusElt_apply_other {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (u : Kˣ) :
    torusElt i j u k = 1 := by
  simp [torusElt, hki, hkj]

theorem prod_torusElt (i j : Fin n) (u : Kˣ) : ∏ k, torusElt i j u k = 1 := by
  have h1 : ∏ k, torusElt i j u k = (∏ k, Pi.mulSingle i u k) * ∏ k, Pi.mulSingle j u⁻¹ k := by
    rw [← Finset.prod_mul_distrib]; rfl
  rw [h1]
  simp

theorem torusElt_mem {p : ℕ} {i j : Fin n} (hij : i ≠ j) {u : Kˣ} (hu : u ^ p = 1) :
    torusElt i j u ∈ torusVec p n K := by
  refine ⟨fun k => ?_, prod_torusElt i j u⟩
  by_cases hki : k = i
  · subst hki; rw [torusElt_apply_left hij]; exact hu
  · by_cases hkj : k = j
    · subst hkj; rw [torusElt_apply_right hij, inv_pow, hu, inv_one]
    · rw [torusElt_apply_other hki hkj]; exact one_pow _

theorem torusSU_char_distinct {p : ℕ} {u : Kˣ} (hu : u ^ p = 1) (hu2 : u ^ 2 ≠ 1)
    {i j : Fin n} (hij : i ≠ j) :
    ∃ g ∈ torusSU p n K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i ≠
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j := by
  refine ⟨diagU (torusElt i j u),
    mem_torusSU_iff.mpr ⟨_, fun k => ?_, prod_torusElt i j u, rfl⟩, ?_⟩
  · exact ((torusElt_mem hij hu : torusElt i j u ∈ torusVec p n K).1 k)
  · rw [diagU_apply_same, diagU_apply_same, torusElt_apply_left hij, torusElt_apply_right hij]
    intro h
    apply hu2
    have : u = u⁻¹ := Units.ext h
    calc u ^ 2 = u * u := sq u
      _ = u * u⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel u

end Torus

section Normalizer

variable {n : ℕ} {K : Type} [Field K]

abbrev ent (g : GL (Fin n) K) (i j : Fin n) : K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j

theorem ent_mul_isDiag_left {g h : GL (Fin n) K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag) (k i : Fin n) :
    ent (g * h) k i = ent g k k * ent h k i := by
  change (((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)) k i) = _
  rw [← hg.diagonal_diag, Matrix.diagonal_mul]
  simp [Matrix.diag]

theorem ent_mul_isDiag_right {g h : GL (Fin n) K}
    (hh : ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag) (k i : Fin n) :
    ent (g * h) k i = ent g k i * ent h i i := by
  change (((g : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)) k i) = _
  rw [← hh.diagonal_diag, Matrix.mul_diagonal]
  simp [Matrix.diag]

theorem exists_ent_ne_zero (w : GL (Fin n) K) (i : Fin n) : ∃ k, ent w k i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : ent (w⁻¹ * w) i i = 1 := by simp [ent]
  have h2 : ent (w⁻¹ * w) i i = 0 := by
    change (((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (w : Matrix (Fin n) (Fin n) K)) i i = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have := hcon k
    simp only [ent] at this
    rw [this, mul_zero]
  rw [h1] at h2
  exact one_ne_zero h2

theorem exists_perm_of_normalizes (T : Subgroup (GL (Fin n) K))
    (hdiag : ∀ g ∈ T, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hdist : ∀ i j : Fin n, i ≠ j → ∃ g ∈ T, ent g i i ≠ ent g j j)
    {w : GL (Fin n) K} (hw : ∀ g ∈ T, w * g * w⁻¹ ∈ T) (hinv : ∀ g ∈ T, w⁻¹ * g * w ∈ T) :
    ∃ σ : Equiv.Perm (Fin n), (∀ i, ent w (σ i) i ≠ 0) ∧ (∀ i k, ent w k i ≠ 0 → k = σ i) ∧
      ∀ g ∈ T, ∀ i, ent (w * g * w⁻¹) (σ i) (σ i) = ent g i i := by
  classical
  have hcol : ∀ i k l, ent w k i ≠ 0 → ent w l i ≠ 0 → k = l := by
    intro i k l hk hl
    by_contra hkl
    obtain ⟨g, hgT, hg⟩ := hdist k l hkl
    have hg' := hinv g hgT
    have hid : g * w = w * (w⁻¹ * g * w) := by group
    have h1 := congrArg (fun x : GL (Fin n) K => ent x k i) hid
    have h2 := congrArg (fun x : GL (Fin n) K => ent x l i) hid
    rw [ent_mul_isDiag_left (hdiag g hgT), ent_mul_isDiag_right (hdiag _ hg')] at h1 h2
    have e1 : ent g k k = ent (w⁻¹ * g * w) i i := mul_right_cancel₀ hk (h1.trans (mul_comm _ _))
    have e2 : ent g l l = ent (w⁻¹ * g * w) i i := mul_right_cancel₀ hl (h2.trans (mul_comm _ _))
    exact hg (e1.trans e2.symm)
  choose σf hσf using exists_ent_ne_zero w
  have hσ : ∀ i k, ent w k i ≠ 0 → k = σf i := fun i k hk => hcol i k (σf i) hk (hσf i)
  have hinj : Function.Injective σf := by
    intro i j hij
    by_contra hne
    have hi : ∀ l, l ≠ σf i → ent w l i = 0 := fun l hl => by
      by_contra h0; exact hl (hσ i l h0)
    have hj : ∀ l, l ≠ σf i → ent w l j = 0 := fun l hl => by
      by_contra h0; exact hl ((hσ j l h0).trans hij.symm)
    have h1 : ent (w⁻¹ * w) i i = 1 := by simp [ent]
    have h2 : ent (w⁻¹ * w) i j = 0 := by
      simp [ent, hne]
    have e1 : ent (w⁻¹ * w) i i = ent w⁻¹ i (σf i) * ent w (σf i) i := by
      change (((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (w : Matrix (Fin n) (Fin n) K)) i i = _
      rw [Matrix.mul_apply, Finset.sum_eq_single (σf i)]
      · intro l _ hl
        have := hi l hl
        simp only [ent] at this
        rw [this, mul_zero]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have e2 : ent (w⁻¹ * w) i j = ent w⁻¹ i (σf i) * ent w (σf i) j := by
      change (((w⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (w : Matrix (Fin n) (Fin n) K)) i j = _
      rw [Matrix.mul_apply, Finset.sum_eq_single (σf i)]
      · intro l _ hl
        have := hj l hl
        simp only [ent] at this
        rw [this, mul_zero]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    have hne0 : ent w⁻¹ i (σf i) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at e1; rw [h1] at e1; exact one_ne_zero e1
    rw [h2] at e2
    have : ent w (σf i) j = 0 := by
      rcases mul_eq_zero.mp e2.symm with h | h
      · exact absurd h hne0
      · exact h
    exact hσf j (by rw [← hij]; exact this)
  refine ⟨Equiv.ofBijective σf (Finite.injective_iff_bijective.mp hinj), hσf, hσ, ?_⟩
  intro g hg i
  have hg'' := hw g hg
  have hid : (w * g * w⁻¹) * w = w * g := by group
  have h1 := congrArg (fun x : GL (Fin n) K => ent x (σf i) i) hid
  rw [ent_mul_isDiag_left (hdiag _ hg''), ent_mul_isDiag_right (hdiag g hg)] at h1
  exact mul_right_cancel₀ (hσf i) (h1.trans (mul_comm _ _))

end Normalizer

section Prime

theorem card_ne_prime_of_two_independent {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (M : Subgroup G) {u w : G} (hu : u ∈ M) (hw : w ∈ M) (hu1 : u ≠ 1)
    (hw' : w ∉ Subgroup.zpowers u) : Nat.card M ≠ p := by
  intro hcard
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite M := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hle : Subgroup.zpowers u ≤ M := (Subgroup.zpowers_le).mpr hu
  have hdvd : Nat.card (Subgroup.zpowers u) ∣ p := by
    rw [← hcard]; exact Subgroup.card_dvd_of_le hle
  have hne1 : Nat.card (Subgroup.zpowers u) ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rw [h1, Subgroup.mem_bot] at this
    exact hu1 this
  have hp' : Nat.card (Subgroup.zpowers u) = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have heq : Subgroup.zpowers u = M := Subgroup.eq_of_le_of_card_ge hle (by rw [hp', hcard])
  exact hw' (heq ▸ hw)

theorem perm_four_cases : ∀ σ : Equiv.Perm (Fin 4), σ * σ = 1 → σ ≠ 1 →
    (∃ a b : Fin 4, a ≠ b ∧ σ = Equiv.swap a b) ∨ ∀ i, σ i ≠ i := by decide

end Prime

end CFSG.RankThree.PartOne.KFU
