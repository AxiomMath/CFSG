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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Sporadic.Ly.Omega

open Matrix MulAction

section RowSpace

variable {K : Type*} [Field K] {d : ℕ}

@[expose] def rs {m : Type*} (M : Matrix m (Fin d) K) : Submodule K (Fin d → K) :=
  Submodule.span K (Set.range fun i c => M i c)

theorem row_mul {m k : Type*} [Fintype k] (A : Matrix m k K) (M : Matrix k (Fin d) K) (i : m) :
    (fun c => (A * M) i c) = ∑ j, A i j • fun c => M j c := by
  funext c
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem rs_mul_le {m k : Type*} [Fintype k] (A : Matrix m k K) (M : Matrix k (Fin d) K) :
    rs (A * M) ≤ rs M := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  change (fun c => (A * M) i c) ∈ rs M
  rw [row_mul]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_mul_of_le {m k : Type*} [Fintype k] {N : Matrix m (Fin d) K}
    {M : Matrix k (Fin d) K} (h : rs N ≤ rs M) : ∃ A : Matrix m k K, N = A * M := by
  have : ∀ i, ∃ c : k → K, ∑ j, c j • (fun x => M j x) = fun x => N i x := fun i =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  choose c hc using this
  refine ⟨Matrix.of c, ?_⟩
  ext i x
  have e := congrFun (row_mul (Matrix.of c) M i) x
  rw [e]
  exact (congrFun (hc i) x).symm

theorem rs_mul_unit {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m m K)
    (hA : IsUnit A.det) (M : Matrix m (Fin d) K) : rs (A * M) = rs M := by
  refine le_antisymm (rs_mul_le A M) ?_
  have e : M = A⁻¹ * (A * M) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA, Matrix.one_mul]
  calc rs M = rs (A⁻¹ * (A * M)) := by rw [← e]
    _ ≤ rs (A * M) := rs_mul_le _ _

theorem rs_mul_right {m : Type*} (M : Matrix m (Fin d) K) (P : Matrix (Fin d) (Fin d) K) :
    rs (M * P) = (rs M).map (Matrix.vecMulLinear P) := by
  unfold rs
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

theorem submatrix_mul {m k : Type*} [Fintype k] (A : Matrix m k K) (M : Matrix k (Fin d) K)
    {r : Type*} (σ : r → Fin d) : (A * M).submatrix id σ = A * M.submatrix id σ := by
  funext i j
  simp [Matrix.mul_apply]

theorem mul_comm_one {k : Type*} [Fintype k] [DecidableEq k] {A B : Matrix k k K}
    (h : A * B = 1) : B * A = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (A := A) (B := B) (eq := rfl)).1 h

theorem rs_eq_of_right_inv {k : Type*} [Fintype k] [DecidableEq k] {A B : Matrix k (Fin d) K}
    {M : Matrix k k K} {Z : Matrix (Fin d) k K} (hA : A * Z = 1) (h : A = M * B) :
    rs A = rs B := by
  have e : M * (B * Z) = 1 := by rw [← Matrix.mul_assoc, ← h, hA]
  rw [h, rs_mul_unit M (Matrix.isUnit_det_of_right_inverse e)]

theorem eq_of_rs_le {k : Type*} [Fintype k] [DecidableEq k] {N N' : Matrix k (Fin d) K}
    (σ : k → Fin d) (hN : N.submatrix id σ = 1) (hN' : N'.submatrix id σ = 1)
    (h : rs N' ≤ rs N) : N' = N := by
  obtain ⟨A, rfl⟩ := exists_mul_of_le h
  rw [submatrix_mul, hN, Matrix.mul_one] at hN'
  rw [hN', Matrix.one_mul]

theorem step_eq {k : Type*} [Fintype k] [DecidableEq k] {Np Ni : Matrix k (Fin d) K}
    {G G' : Matrix (Fin d) (Fin d) K} {M : Matrix k k K} (σ : k → Fin d)
    (hNp : Np.submatrix id σ = 1) (hG : G * G' = 1) (h : Np * G = M * Ni) :
    IsUnit M.det ∧ Ni = M⁻¹ * (Np * G) := by
  have e : Np = M * (Ni * G') := by
    rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, hG, Matrix.mul_one]
  have e1 : M * (Ni * G').submatrix id σ = 1 := by
    rw [← submatrix_mul, ← e, hNp]
  have hM : IsUnit M.det := Matrix.isUnit_det_of_right_inverse e1
  refine ⟨hM, ?_⟩
  rw [h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.one_mul]

theorem chart_spaces {k : Type*} [Fintype k] [DecidableEq k] {n nc : ℕ}
    {N : ℕ → Matrix k (Fin d) K} {ch par lab : ℕ → ℕ}
    {PI PJ GT WC G Gi : ℕ → Matrix (Fin d) (Fin d) K} {T TI : Matrix (Fin d) (Fin d) K}
    (σ : k → Fin d)
    (hPI : ∀ c < nc, PI c * PJ c = 1)
    (hGT : ∀ s < 2, ∀ c < nc, ∀ c' < nc, PI c * GT (s + 2 * c + 16 * c') = G s * PI c')
    (hWC : ∀ e c, e < c → c < nc → PI c * WC (c + 8 * e) = PI e)
    (hG : ∀ s < 2, G s * Gi s = 1) (hT : T * TI = 1)
    (hnode : ∀ i < n, ch i < nc ∧ (N i).submatrix id σ = 1 ∧
      (∀ e < ch i, ¬ IsUnit ((N i * WC (ch i + 8 * e)).submatrix id σ).det) ∧
      (0 < i → par i < i ∧ lab i < 2 ∧
        ∃ M : Matrix k k K, N (par i) * GT (lab i + 2 * ch (par i) + 16 * ch i) = M * N i))
    (hinj : ∀ i < n, ∀ j < n, N i = N j → ch i = ch j → i = j) :
    (∀ i < n, 0 < i → rs (N i * PJ (ch i) * TI) =
      (rs (N (par i) * PJ (ch (par i)) * TI)).map (Matrix.vecMulLinear (T * G (lab i) * TI))) ∧
    (∀ i < n, ∀ j < n, rs (N i * PJ (ch i) * TI) = rs (N j * PJ (ch j) * TI) → i = j) := by
  have hJI : ∀ c < nc, PJ c * PI c = 1 := fun c hc => mul_comm_one (hPI c hc)
  have hTI : TI * T = 1 := mul_comm_one hT
  have hGi : ∀ s < 2, Gi s * G s = 1 := fun s hs => mul_comm_one (hG s hs)
  refine ⟨fun i hi hi0 => ?_, fun i hi j hj e => ?_⟩
  · obtain ⟨hci, -, -, hstep⟩ := hnode i hi
    obtain ⟨hp, hl, M, hM⟩ := hstep hi0
    obtain ⟨hcp, hNp, -, -⟩ := hnode (par i) (by omega)
    set s := lab i
    set g := GT (s + 2 * ch (par i) + 16 * ch i)
    have hg : PI (ch (par i)) * g = G s * PI (ch i) := hGT s hl _ hcp _ hci
    have hg' : g = PJ (ch (par i)) * G s * PI (ch i) := by
      rw [Matrix.mul_assoc, ← hg, ← Matrix.mul_assoc, hJI _ hcp, Matrix.one_mul]
    have hgg : g * (PJ (ch i) * Gi s * PI (ch (par i))) = 1 := by
      rw [hg']
      calc PJ (ch (par i)) * G s * PI (ch i) * (PJ (ch i) * Gi s * PI (ch (par i)))
          = PJ (ch (par i)) * G s * (PI (ch i) * PJ (ch i)) * Gi s * PI (ch (par i)) := by
            simp only [Matrix.mul_assoc]
        _ = PJ (ch (par i)) * (G s * Gi s) * PI (ch (par i)) := by
            rw [hPI _ hci, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hG s hl, Matrix.mul_one, hJI _ hcp]
    obtain ⟨hMu, hNi⟩ := step_eq σ hNp hgg hM
    have key : N i * PJ (ch i) * TI =
        M⁻¹ * (N (par i) * PJ (ch (par i)) * TI * (T * G s * TI)) := by
      rw [hNi, hg']
      calc M⁻¹ * (N (par i) * (PJ (ch (par i)) * G s * PI (ch i))) * PJ (ch i) * TI
          = M⁻¹ * (N (par i) * PJ (ch (par i)) * G s * (PI (ch i) * PJ (ch i)) * TI) := by
            simp only [Matrix.mul_assoc]
        _ = M⁻¹ * (N (par i) * PJ (ch (par i)) * (TI * T) * G s * TI) := by
            rw [hPI _ hci, hTI]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [key, rs_mul_unit _ (Matrix.isUnit_nonsing_inv_det M hMu), rs_mul_right]
  ·
    obtain ⟨hci, hNi, hWi, -⟩ := hnode i hi
    obtain ⟨hcj, hNj, hWj, -⟩ := hnode j hj
    have hB : ∀ a < n, rs (N a * PJ (ch a)) = (rs (N a * PJ (ch a) * TI)).map
        (Matrix.vecMulLinear T) := by
      intro a _
      rw [← rs_mul_right, Matrix.mul_assoc, hTI, Matrix.mul_one]
    have e' : rs (N i * PJ (ch i)) = rs (N j * PJ (ch j)) := by rw [hB i hi, hB j hj, e]
    have hlow : ∀ a < n, ∀ b < n, rs (N a * PJ (ch a)) ≤ rs (N b * PJ (ch b)) →
        ¬ ch a < ch b := by
      intro a ha b hb hab hlt
      obtain ⟨hca, hNa, -, -⟩ := hnode a ha
      obtain ⟨hcb, -, hWb, -⟩ := hnode b hb
      obtain ⟨A, hA⟩ := exists_mul_of_le hab
      have hw : WC (ch b + 8 * ch a) = PJ (ch b) * PI (ch a) := by
        rw [← hWC _ _ hlt hcb, ← Matrix.mul_assoc, hJI _ hcb, Matrix.one_mul]
      have eN : N a = A * (N b * WC (ch b + 8 * ch a)) := by
        rw [hw]
        calc N a = N a * PJ (ch a) * PI (ch a) := by
              rw [Matrix.mul_assoc, hJI _ hca, Matrix.mul_one]
          _ = A * (N b * PJ (ch b)) * PI (ch a) := by rw [hA]
          _ = A * (N b * (PJ (ch b) * PI (ch a))) := by simp only [Matrix.mul_assoc]
      have e1 : A * (N b * WC (ch b + 8 * ch a)).submatrix id σ = 1 := by
        rw [← submatrix_mul, ← eN, hNa]
      exact hWb _ hlt (Matrix.isUnit_det_of_left_inverse e1)
    have hc : ch i = ch j := by
      rcases lt_trichotomy (ch i) (ch j) with h | h | h
      · exact absurd h (hlow i hi j hj e'.le)
      · exact h
      · exact absurd h (hlow j hj i hi e'.ge)
    have hNN : rs (N i) = rs (N j) := by
      have hb : ∀ a < n, rs (N a) = (rs (N a * PJ (ch a))).map (Matrix.vecMulLinear (PI (ch a))) := by
        intro a ha
        rw [← rs_mul_right, Matrix.mul_assoc, hJI _ (hnode a ha).1, Matrix.mul_one]
      rw [hb i hi, hb j hj, e', hc]
    exact hinj i hi j hj (eq_of_rs_le σ hNj hNi hNN.le) hc

end RowSpace

section Sorted

theorem sorted_inj {α : Type*} [LinearOrder α] {n : ℕ} (key : ℕ → α) (σ : ℕ → ℕ)
    (hσ : ∀ k < n, σ k < n) (hsort : ∀ k, k + 1 < n → key (σ k) < key (σ (k + 1))) :
    ∀ i < n, ∀ j < n, key i = key j → i = j := by
  have hmono : ∀ a b, a < b → b < n → key (σ a) < key (σ b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact (ih h (by omega)).trans (hsort b hb)
      · exact hsort a hb
  have hinj : Set.InjOn σ (Set.Iio n) := by
    intro a ha b hb e
    simp only [Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · exact absurd (congrArg key e) (hmono a b h hb).ne
    · exact h
    · exact absurd (congrArg key e).symm (hmono b a h ha).ne
  have hsurj : Set.SurjOn σ (Set.Iio n) (Set.Iio n) := by
    have hmaps : Set.MapsTo σ (Set.Iio n) (Set.Iio n) := fun a ha => hσ a ha
    have hfin : (Set.Iio n).Finite := Set.finite_Iio n
    exact (Set.Finite.injOn_iff_bijOn_of_mapsTo hfin hmaps).1 hinj |>.surjOn
  intro i hi j hj e
  obtain ⟨a, ha, rfl⟩ := hsurj (Set.mem_Iio.2 hi)
  obtain ⟨b, hb, rfl⟩ := hsurj (Set.mem_Iio.2 hj)
  simp only [Set.mem_Iio] at ha hb
  rcases lt_trichotomy a b with h | h | h
  · exact absurd e (hmono a b h hb).ne
  · rw [h]
  · exact absurd e.symm (hmono b a h ha).ne

end Sorted

section Orbit

variable {G X Z : Type*} [Group G] [MulAction G X] [MulAction G Z]

theorem mem_orbit_of_tree (p : X) (key : ℕ → X) (par : ℕ → ℕ) (n : ℕ) (h0 : key 0 = p)
    (hs : ∀ i, 0 < i → i < n → par i < i ∧ ∃ s : G, key i = s • key (par i)) :
    ∀ i < n, key i ∈ orbit G p := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [h0]
      exact mem_orbit_self p
    · obtain ⟨hp, s, hk⟩ := hs i hpos hi
      obtain ⟨g, hg⟩ := ih (par i) hp (lt_trans hp hi)
      refine ⟨s * g, ?_⟩
      change (s * g) • p = key i
      rw [mul_smul, hk]
      exact congrArg (s • ·) hg

theorem card_orbit_le_of_map [Finite X] (Y : X → Z) (hY : ∀ (g : G) (x : X), Y (g • x) = g • Y x)
    (p : X) : Nat.card (orbit G (Y p)) ≤ Nat.card (orbit G p) := by
  have : Finite (orbit G p) := Set.finite_coe_iff.2 (Set.toFinite _)
  refine Nat.card_le_card_of_surjective (fun x : orbit G p => (⟨Y x.1, ?_⟩ : orbit G (Y p))) ?_
  · obtain ⟨g, hg⟩ := x.2
    exact ⟨g, by rw [← hg]; exact (hY g p).symm⟩
  · rintro ⟨z, g, rfl⟩
    exact ⟨⟨g • p, g, rfl⟩, Subtype.ext (hY g p)⟩

theorem card_le_orbit_of_inj [Finite X] [Finite Z] (Y : X → Z)
    (hY : ∀ (g : G) (x : X), Y (g • x) = g • Y x) (p : X) (n : ℕ) (sp : ℕ → Z)
    (hmem : ∀ i < n, sp i ∈ orbit G (Y p)) (hinj : ∀ i < n, ∀ j < n, sp i = sp j → i = j) :
    n ≤ Nat.card (orbit G p) := by
  classical
  refine le_trans ?_ (card_orbit_le_of_map Y hY p)
  have hsub : (((Finset.range n).image sp : Finset Z) : Set Z) ⊆ orbit G (Y p) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hmem i hi
  have hcard : ((Finset.range n).image sp).card = n := by
    rw [Finset.card_image_of_injOn (fun i hi j hj e => hinj i (Finset.mem_range.1 hi) j
      (Finset.mem_range.1 hj) e), Finset.card_range]
  rw [Nat.card_coe_set_eq]
  calc n = ((Finset.range n).image sp).card := hcard.symm
    _ = (((Finset.range n).image sp : Finset Z) : Set Z).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (orbit G (Y p)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem fiber_set (S : Subgroup G) (Y : X → Z) (hY : ∀ (g : G) (x : X), Y (g • x) = g • Y x)
    (p : X) (n : ℕ) (sp : ℕ → Z) (hmem : ∀ i < n, sp i ∈ orbit S (Y p))
    (hinj : ∀ i < n, ∀ j < n, sp i = sp j → i = j) :
    ∃ B : Set X, B ⊆ orbit S p ∧ B.ncard = n := by
  classical
  have : ∀ i : Fin n, ∃ s : S, s • Y p = sp i := fun i => hmem i i.2
  choose s hs using this
  refine ⟨Set.range fun i : Fin n => (s i : G) • p, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨s i, rfl⟩
  · rw [Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro i j e
    have e1 := congrArg Y e
    simp only at e1
    rw [hY, hY] at e1
    have e2 : sp i = sp j := by
      rw [← hs i, ← hs j]
      exact e1
    exact Fin.ext (hinj i i.2 j j.2 e2)

end Orbit

end CFSG.Sporadic.Ly.Omega

end
