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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Geometry

open Module Submodule

variable (k : Type*) [Field k]

@[ext]
structure PlaneFlag where
  pt : Submodule k (Fin 3 → k)
  line : Submodule k (Fin 3 → k)
  finrank_pt : finrank k pt = 1
  finrank_line : finrank k line = 2
  pt_le_line : pt ≤ line

@[expose] def planeTypeAut : Subgroup (Equiv.Perm (PlaneFlag k)) where
  carrier := {g | ∀ x y, ((g x).pt = (g y).pt ↔ x.pt = y.pt) ∧
    ((g x).line = (g y).line ↔ x.line = y.line)}
  mul_mem' {g h} hg hh x y :=
    ⟨(hg (h x) (h y)).1.trans (hh x y).1, (hg (h x) (h y)).2.trans (hh x y).2⟩
  one_mem' _ _ := ⟨Iff.rfl, Iff.rfl⟩
  inv_mem' {g} hg x y := by
    have := hg (g⁻¹ x) (g⁻¹ y)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at this
    exact ⟨this.1.symm, this.2.symm⟩

variable {k}

theorem mem_planeTypeAut {g : Equiv.Perm (PlaneFlag k)} :
    g ∈ planeTypeAut k ↔ ∀ x y, ((g x).pt = (g y).pt ↔ x.pt = y.pt) ∧
      ((g x).line = (g y).line ↔ x.line = y.line) :=
  Iff.rfl

theorem mem_planeTypeAut_iff_adj {g : Equiv.Perm (PlaneFlag k)} :
    g ∈ planeTypeAut k ↔ ∀ x y,
      (g x ≠ g y ∧ (g x).pt = (g y).pt ↔ x ≠ y ∧ x.pt = y.pt) ∧
      (g x ≠ g y ∧ (g x).line = (g y).line ↔ x ≠ y ∧ x.line = y.line) := by
  have hne : ∀ x y, g x ≠ g y ↔ x ≠ y := fun x y => g.injective.ne_iff
  constructor
  · intro hg x y
    rw [hne]
    exact ⟨and_congr_right fun _ => (hg x y).1, and_congr_right fun _ => (hg x y).2⟩
  · intro h x y
    refine ⟨⟨fun hxy => ?_, fun hxy => ?_⟩, ⟨fun hxy => ?_, fun hxy => ?_⟩⟩
    · by_cases e : x = y
      · rw [e]
      · exact ((h x y).1.mp ⟨(hne x y).mpr e, hxy⟩).2
    · by_cases e : x = y
      · rw [e]
      · exact ((h x y).1.mpr ⟨e, hxy⟩).2
    · by_cases e : x = y
      · rw [e]
      · exact ((h x y).2.mp ⟨(hne x y).mpr e, hxy⟩).2
    · by_cases e : x = y
      · rw [e]
      · exact ((h x y).2.mpr ⟨e, hxy⟩).2

namespace PlaneFlag

@[expose] def pointPanel (x : PlaneFlag k) : Set (PlaneFlag k) := {y | y.pt = x.pt}

@[expose] def linePanel (x : PlaneFlag k) : Set (PlaneFlag k) := {y | y.line = x.line}

@[expose] def IsOpposite (x y : PlaneFlag k) : Prop := ¬ x.pt ≤ y.line ∧ ¬ y.pt ≤ x.line

theorem IsOpposite.symm {x y : PlaneFlag k} (h : x.IsOpposite y) : y.IsOpposite x :=
  ⟨h.2, h.1⟩

end PlaneFlag

namespace ProjPlane

@[expose] def linForm (α β γ : k) : Module.Dual k (Fin 3 → k) where
  toFun v := α * v 0 + β * v 1 + γ * v 2
  map_add' v w := by simp only [Pi.add_apply]; ring
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[expose] def kerLine (α β γ : k) : Submodule k (Fin 3 → k) := LinearMap.ker (linForm α β γ)

theorem mem_kerLine {α β γ : k} {v : Fin 3 → k} :
    v ∈ kerLine α β γ ↔ α * v 0 + β * v 1 + γ * v 2 = 0 :=
  Iff.rfl

theorem span_le_kerLine {α β γ : k} {v : Fin 3 → k} :
    k ∙ v ≤ kerLine α β γ ↔ α * v 0 + β * v 1 + γ * v 2 = 0 := by
  rw [span_singleton_le_iff_mem, mem_kerLine]

theorem vec_le_kerLine {α β γ x y z : k} :
    k ∙ (![x, y, z] : Fin 3 → k) ≤ kerLine α β γ ↔ α * x + β * y + γ * z = 0 := by
  rw [span_le_kerLine]
  simp

theorem finrank_kerLine {α β γ : k} (h : α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) :
    finrank k (kerLine α β γ) = 2 := by
  have hf : linForm α β γ ≠ 0 := by
    intro hf
    have h0 := LinearMap.congr_fun hf (Pi.single 0 1)
    have h1 := LinearMap.congr_fun hf (Pi.single 1 1)
    have h2 := LinearMap.congr_fun hf (Pi.single 2 1)
    simp [linForm] at h0 h1 h2
    tauto
  have := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [Module.finrank_fin_fun] at this
  unfold kerLine
  omega

theorem kerLine_smul {α β γ c : k} (hc : c ≠ 0) :
    kerLine (c * α) (c * β) (c * γ) = kerLine α β γ := by
  ext v
  simp only [mem_kerLine]
  constructor
  · intro h
    have : c * (α * v 0 + β * v 1 + γ * v 2) = 0 := by rw [← h]; ring
    exact (mul_eq_zero.mp this).resolve_left hc
  · intro h
    linear_combination c * h

theorem vec_ne_zero_of_two {x y z : k} (h : z ≠ 0) : (![x, y, z] : Fin 3 → k) ≠ 0 := by
  intro h'
  exact h (by simpa using congrFun h' 2)

theorem vec_ne_zero_of_one {x y z : k} (h : y ≠ 0) : (![x, y, z] : Fin 3 → k) ≠ 0 := by
  intro h'
  exact h (by simpa using congrFun h' 1)

theorem vec_ne_zero_of_zero {x y z : k} (h : x ≠ 0) : (![x, y, z] : Fin 3 → k) ≠ 0 := by
  intro h'
  exact h (by simpa using congrFun h' 0)

theorem eta_vec {R : Type*} (v : Fin 3 → R) : v = ![v 0, v 1, v 2] := by
  ext i
  fin_cases i <;> rfl

theorem span_eq_span_of_eq_smul {v w : Fin 3 → k} {c : k} (hc : c ≠ 0) (h : w = c • v) :
    k ∙ w = k ∙ v := by
  rw [h, span_singleton_smul_eq (IsUnit.mk0 c hc)]

theorem vec_eq_of_span_eq {x y z x' y' : k} (hz : z ≠ 0)
    (h : k ∙ (![x, y, z] : Fin 3 → k) = k ∙ ![x', y', z]) : x = x' ∧ y = y' := by
  obtain ⟨u, hu⟩ := (span_singleton_eq_span_singleton).mp h
  have h0 := congrFun hu 0
  have h1 := congrFun hu 1
  have h2 := congrFun hu 2
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at h0 h1 h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2
  have hu1 : (u : k) = 1 := by
    have : ((u : k) - 1) * z = 0 := by rw [sub_mul, h2]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hz)
  rw [hu1, one_mul] at h0 h1
  exact ⟨h0, h1⟩

theorem vec_eq_of_span_eq' {x y z y' z' : k} (hx : x ≠ 0)
    (h : k ∙ (![x, y, z] : Fin 3 → k) = k ∙ ![x, y', z']) : y = y' ∧ z = z' := by
  obtain ⟨u, hu⟩ := (span_singleton_eq_span_singleton).mp h
  have h0 := congrFun hu 0
  have h1 := congrFun hu 1
  have h2 := congrFun hu 2
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at h0 h1 h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2
  have hu1 : (u : k) = 1 := by
    have : ((u : k) - 1) * x = 0 := by rw [sub_mul, h0]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hx)
  rw [hu1, one_mul] at h1 h2
  exact ⟨h1, h2⟩

variable {P Q L M : Submodule k (Fin 3 → k)}

theorem exists_eq_span (hP : finrank k P = 1) : ∃ v : Fin 3 → k, v ≠ 0 ∧ P = k ∙ v := by
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hP
    exact zero_ne_one hP
  obtain ⟨v, hv, hv0⟩ := exists_mem_ne_zero_of_ne_bot hne
  exact ⟨v, hv0, eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0⟩

theorem finrank_sup_of_ne (hP : finrank k P = 1) (hQ : finrank k Q = 1) (hne : P ≠ Q) :
    finrank k ↥(P ⊔ Q) = 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have hle : finrank k ↥(P ⊓ Q) ≤ 1 := hP ▸ Submodule.finrank_mono inf_le_left
  have hne' : finrank k ↥(P ⊓ Q) ≠ 1 := by
    intro h1
    have h₁ : P ⊓ Q = P := Submodule.eq_of_le_of_finrank_eq inf_le_left (h1.trans hP.symm)
    have h₂ : P ⊓ Q = Q := Submodule.eq_of_le_of_finrank_eq inf_le_right (h1.trans hQ.symm)
    exact hne (h₁.symm.trans h₂)
  omega

theorem sup_eq_of_ne (hP : finrank k P = 1) (hQ : finrank k Q = 1) (hL : finrank k L = 2)
    (hne : P ≠ Q) (hPL : P ≤ L) (hQL : Q ≤ L) : P ⊔ Q = L :=
  Submodule.eq_of_le_of_finrank_eq (sup_le hPL hQL) ((finrank_sup_of_ne hP hQ hne).trans hL.symm)

theorem line_eq_of_ne (hP : finrank k P = 1) (hQ : finrank k Q = 1) (hL : finrank k L = 2)
    (hM : finrank k M = 2) (hne : P ≠ Q) (hPL : P ≤ L) (hQL : Q ≤ L) (hPM : P ≤ M)
    (hQM : Q ≤ M) : L = M :=
  (sup_eq_of_ne hP hQ hL hne hPL hQL).symm.trans (sup_eq_of_ne hP hQ hM hne hPM hQM)

theorem pt_eq_of_ne (hP : finrank k P = 1) (hQ : finrank k Q = 1) (hL : finrank k L = 2)
    (hM : finrank k M = 2) (hne : L ≠ M) (hPL : P ≤ L) (hPM : P ≤ M) (hQL : Q ≤ L)
    (hQM : Q ≤ M) : P = Q := by
  by_contra h
  exact hne (line_eq_of_ne hP hQ hL hM h hPL hQL hPM hQM)

theorem exists_mem_inf (hL : finrank k L = 2) (hM : finrank k M = 2) :
    ∃ w : Fin 3 → k, w ≠ 0 ∧ w ∈ L ∧ w ∈ M := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq L M
  have h3 : finrank k ↥(L ⊔ M) ≤ 3 := (Submodule.finrank_le _).trans (by simp)
  have hpos : finrank k ↥(L ⊓ M) ≠ 0 := by omega
  rw [Ne, Submodule.finrank_eq_zero] at hpos
  obtain ⟨w, hw, hw0⟩ := exists_mem_ne_zero_of_ne_bot hpos
  exact ⟨w, hw0, (Submodule.mem_inf.mp hw).1, (Submodule.mem_inf.mp hw).2⟩

theorem exists_two_pts (hL : finrank k L = 2) :
    ∃ P Q : Submodule k (Fin 3 → k), finrank k P = 1 ∧ finrank k Q = 1 ∧ P ≠ Q ∧ P ≤ L ∧
      Q ≤ L := by
  have hne : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hL
    exact absurd hL (by norm_num)
  obtain ⟨u, hu, hu0⟩ := exists_mem_ne_zero_of_ne_bot hne
  have hlt : k ∙ u < L := by
    refine lt_of_le_of_ne ((span_singleton_le_iff_mem u L).mpr hu) fun h => ?_
    have := finrank_span_singleton (K := k) hu0
    rw [h, hL] at this
    exact absurd this (by norm_num)
  obtain ⟨w, hw, hwu⟩ := IsConcreteLE.exists_of_lt hlt
  have hw0 : w ≠ 0 := fun h => hwu (h ▸ zero_mem _)
  refine ⟨k ∙ u, k ∙ w, finrank_span_singleton hu0, finrank_span_singleton hw0, fun h => ?_,
    (span_singleton_le_iff_mem u L).mpr hu, (span_singleton_le_iff_mem w L).mpr hw⟩
  exact hwu (h ▸ mem_span_singleton_self w)

theorem exists_eq_kerLine (hL : finrank k L = 2) :
    ∃ α β γ : k, (α ≠ 0 ∨ β ≠ 0 ∨ γ ≠ 0) ∧ L = kerLine α β γ := by
  have hlt : L < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    rw [h, finrank_top, Module.finrank_fin_fun] at hL
    exact absurd hL (by norm_num)
  obtain ⟨f, hf0, hLf⟩ := Submodule.exists_le_ker_of_lt_top L hlt
  have hfv : ∀ v : Fin 3 → k, f v = f (Pi.single 0 1) * v 0 + f (Pi.single 1 1) * v 1 +
      f (Pi.single 2 1) * v 2 := by
    intro v
    have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hker : LinearMap.ker f = kerLine (f (Pi.single 0 1)) (f (Pi.single 1 1))
      (f (Pi.single 2 1)) := by
    ext v
    rw [LinearMap.mem_ker, mem_kerLine, hfv]
  have hcoef : f (Pi.single 0 1) ≠ 0 ∨ f (Pi.single 1 1) ≠ 0 ∨ f (Pi.single 2 1) ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_or, not_not] at hcon
    apply hf0
    refine LinearMap.ext fun v => ?_
    rw [hfv, hcon.1, hcon.2.1, hcon.2.2]
    simp
  refine ⟨_, _, _, hcoef, ?_⟩
  rw [← hker]
  refine Submodule.eq_of_le_of_finrank_eq hLf ?_
  rw [hL, hker, finrank_kerLine hcoef]

theorem exists_flag_pt (hP : finrank k P = 1) : ∃ x : PlaneFlag k, x.pt = P := by
  obtain ⟨v, hv0, rfl⟩ := exists_eq_span hP
  by_cases h0 : v 0 = 0
  · exact ⟨⟨_, kerLine 1 0 0, hP, finrank_kerLine (Or.inl one_ne_zero),
      span_le_kerLine.mpr (by simp [h0])⟩, rfl⟩
  · exact ⟨⟨_, kerLine (-v 1) (v 0) 0, hP, finrank_kerLine (Or.inr (Or.inl h0)),
      span_le_kerLine.mpr (by ring)⟩, rfl⟩

theorem exists_flag_line (hL : finrank k L = 2) : ∃ x : PlaneFlag k, x.line = L := by
  obtain ⟨P, -, hP, -, -, hPL, -⟩ := exists_two_pts hL
  exact ⟨⟨P, L, hP, hL, hPL⟩, rfl⟩

end ProjPlane

open ProjPlane

namespace PlaneFlag

theorem single_zero : (Pi.single 0 1 : Fin 3 → k) = ![1, 0, 0] := by
  ext i
  fin_cases i <;> simp

theorem single_one : (Pi.single 1 1 : Fin 3 → k) = ![0, 1, 0] := by
  ext i
  fin_cases i <;> simp

theorem single_two : (Pi.single 2 1 : Fin 3 → k) = ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp

theorem span_vec_pair_eq_kerLine_001 {x y : Fin 3 → k} (hx : x = ![1, 0, 0])
    (hy : y = ![0, 1, 0]) : span k {x, y} = kerLine 0 0 1 := by
  ext v
  rw [mem_span_pair, mem_kerLine, hx, hy]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp
  · intro h
    refine ⟨v 0, v 1, ?_⟩
    ext i
    fin_cases i <;> simp_all

theorem span_vec_pair_eq_kerLine_100 {x y : Fin 3 → k} (hx : x = ![0, 1, 0])
    (hy : y = ![0, 0, 1]) : span k {x, y} = kerLine 1 0 0 := by
  ext v
  rw [mem_span_pair, mem_kerLine, hx, hy]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp
  · intro h
    refine ⟨v 1, v 2, ?_⟩
    ext i
    fin_cases i <;> simp_all

theorem span_vec_pair_eq_kerLine_010 {x y : Fin 3 → k} (hx : x = ![1, 0, 0])
    (hy : y = ![0, 0, 1]) : span k {x, y} = kerLine 0 1 0 := by
  ext v
  rw [mem_span_pair, mem_kerLine, hx, hy]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp
  · intro h
    refine ⟨v 0, v 2, ?_⟩
    ext i
    fin_cases i <;> simp_all

theorem span_e01 : span k {(Pi.single 0 1 : Fin 3 → k), Pi.single 1 1} = kerLine 0 0 1 :=
  span_vec_pair_eq_kerLine_001 single_zero single_one

theorem span_e12 : span k {(Pi.single 1 1 : Fin 3 → k), Pi.single 2 1} = kerLine 1 0 0 :=
  span_vec_pair_eq_kerLine_100 single_one single_two

theorem span_e02 : span k {(Pi.single 0 1 : Fin 3 → k), Pi.single 2 1} = kerLine 0 1 0 :=
  span_vec_pair_eq_kerLine_010 single_zero single_two

variable (k) in
@[expose] def c : PlaneFlag k where
  pt := k ∙ Pi.single 0 1
  line := span k {Pi.single 0 1, Pi.single 1 1}
  finrank_pt := finrank_span_singleton (by simp)
  finrank_line := by rw [span_e01]; exact finrank_kerLine (Or.inr (Or.inr one_ne_zero))
  pt_le_line := span_mono (by simp)

variable (k) in
@[expose] def d : PlaneFlag k where
  pt := k ∙ Pi.single 2 1
  line := span k {Pi.single 1 1, Pi.single 2 1}
  finrank_pt := finrank_span_singleton (by simp)
  finrank_line := by rw [span_e12]; exact finrank_kerLine (Or.inl one_ne_zero)
  pt_le_line := span_mono (by simp)

theorem c_pt : (c k).pt = k ∙ ![1, 0, 0] := by rw [← single_zero]; rfl

theorem c_line : (c k).line = kerLine 0 0 1 := span_e01

theorem d_pt : (d k).pt = k ∙ ![0, 0, 1] := by rw [← single_two]; rfl

theorem d_line : (d k).line = kerLine 1 0 0 := span_e12

theorem isOpposite_c_d : (c k).IsOpposite (d k) := by
  refine ⟨?_, ?_⟩
  · rw [c_pt, d_line, span_le_kerLine]
    simp
  · rw [d_pt, c_line, span_le_kerLine]
    simp

instance : Nonempty (PlaneFlag k) := ⟨c k⟩

end PlaneFlag

variable (k) in
@[expose] def planeApartment : Set (PlaneFlag k) :=
  {x | ∃ i j : Fin 3, i ≠ j ∧ x.pt = k ∙ Pi.single i 1 ∧
    x.line = span k {Pi.single i 1, Pi.single j 1}}

variable (k) in
@[expose] def planePairStab (x y : PlaneFlag k) : Subgroup (Equiv.Perm (PlaneFlag k)) where
  carrier := {g | g ∈ planeTypeAut k ∧ g x = x ∧ g y = y}
  mul_mem' {g h} hg hh := ⟨mul_mem hg.1 hh.1, by simp [hh.2.1, hg.2.1], by simp [hh.2.2, hg.2.2]⟩
  one_mem' := ⟨one_mem _, rfl, rfl⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact hg.2.1.symm, by
    rw [Equiv.Perm.inv_eq_iff_eq]; exact hg.2.2.symm⟩

theorem mem_planePairStab {x y : PlaneFlag k} {g : Equiv.Perm (PlaneFlag k)} :
    g ∈ planePairStab k x y ↔ g ∈ planeTypeAut k ∧ g x = x ∧ g y = y :=
  Iff.rfl

variable (k) in
abbrev planeOppStab : Subgroup (Equiv.Perm (PlaneFlag k)) :=
  planePairStab k (PlaneFlag.c k) (PlaneFlag.d k)

namespace ProjPlane

variable {P Q L M : Submodule k (Fin 3 → k)}

noncomputable def ptMap (g : Equiv.Perm (PlaneFlag k)) (P : Submodule k (Fin 3 → k)) :
    Submodule k (Fin 3 → k) :=
  (g (Classical.epsilon fun x : PlaneFlag k => x.pt = P)).pt

noncomputable def lnMap (g : Equiv.Perm (PlaneFlag k)) (L : Submodule k (Fin 3 → k)) :
    Submodule k (Fin 3 → k) :=
  (g (Classical.epsilon fun x : PlaneFlag k => x.line = L)).line

variable {g : Equiv.Perm (PlaneFlag k)}

theorem ptMap_pt (hg : g ∈ planeTypeAut k) (x : PlaneFlag k) : ptMap g x.pt = (g x).pt := by
  have hx : (Classical.epsilon fun y : PlaneFlag k => y.pt = x.pt).pt = x.pt :=
    Classical.epsilon_spec (p := fun y : PlaneFlag k => y.pt = x.pt) ⟨x, rfl⟩
  exact ((hg _ x).1).mpr hx

theorem lnMap_line (hg : g ∈ planeTypeAut k) (x : PlaneFlag k) :
    lnMap g x.line = (g x).line := by
  have hx : (Classical.epsilon fun y : PlaneFlag k => y.line = x.line).line = x.line :=
    Classical.epsilon_spec (p := fun y : PlaneFlag k => y.line = x.line) ⟨x, rfl⟩
  exact ((hg _ x).2).mpr hx

theorem finrank_ptMap (hg : g ∈ planeTypeAut k) (hP : finrank k P = 1) :
    finrank k (ptMap g P) = 1 := by
  obtain ⟨x, rfl⟩ := exists_flag_pt hP
  rw [ptMap_pt hg]
  exact (g x).finrank_pt

theorem finrank_lnMap (hg : g ∈ planeTypeAut k) (hL : finrank k L = 2) :
    finrank k (lnMap g L) = 2 := by
  obtain ⟨x, rfl⟩ := exists_flag_line hL
  rw [lnMap_line hg]
  exact (g x).finrank_line

theorem ptMap_inj (hg : g ∈ planeTypeAut k) (hP : finrank k P = 1) (hQ : finrank k Q = 1) :
    ptMap g P = ptMap g Q ↔ P = Q := by
  obtain ⟨x, rfl⟩ := exists_flag_pt hP
  obtain ⟨y, rfl⟩ := exists_flag_pt hQ
  rw [ptMap_pt hg, ptMap_pt hg]
  exact (hg x y).1

theorem lnMap_inj (hg : g ∈ planeTypeAut k) (hL : finrank k L = 2) (hM : finrank k M = 2) :
    lnMap g L = lnMap g M ↔ L = M := by
  obtain ⟨x, rfl⟩ := exists_flag_line hL
  obtain ⟨y, rfl⟩ := exists_flag_line hM
  rw [lnMap_line hg, lnMap_line hg]
  exact (hg x y).2

theorem ptMap_le_lnMap_iff (hg : g ∈ planeTypeAut k) (hP : finrank k P = 1)
    (hL : finrank k L = 2) : ptMap g P ≤ lnMap g L ↔ P ≤ L := by
  obtain ⟨xP, rfl⟩ := exists_flag_pt hP
  obtain ⟨xL, rfl⟩ := exists_flag_line hL
  constructor
  · intro h
    let z : PlaneFlag k := ⟨ptMap g xP.pt, lnMap g xL.line, finrank_ptMap hg hP,
      finrank_lnMap hg hL, h⟩
    have hz := g.apply_symm_apply z
    have h1 : (g (g.symm z)).pt = (g xP).pt := by rw [hz, ← ptMap_pt hg]
    have h2 : (g (g.symm z)).line = (g xL).line := by rw [hz, ← lnMap_line hg]
    rw [← ((hg _ _).1.mp h1), ← ((hg _ _).2.mp h2)]
    exact (g.symm z).pt_le_line
  · intro h
    let z : PlaneFlag k := ⟨xP.pt, xL.line, hP, hL, h⟩
    have h1 : ptMap g xP.pt = (g z).pt := ptMap_pt hg z
    have h2 : lnMap g xL.line = (g z).line := lnMap_line hg z
    rw [h1, h2]
    exact (g z).pt_le_line

theorem exists_ptMap_eq (hg : g ∈ planeTypeAut k) (hP : finrank k P = 1) :
    ∃ Q : Submodule k (Fin 3 → k), finrank k Q = 1 ∧ ptMap g Q = P := by
  obtain ⟨y, rfl⟩ := exists_flag_pt hP
  refine ⟨(g.symm y).pt, (g.symm y).finrank_pt, ?_⟩
  rw [ptMap_pt hg, Equiv.apply_symm_apply]

theorem apply_eq (hg : g ∈ planeTypeAut k) (x : PlaneFlag k) :
    (g x).pt = ptMap g x.pt ∧ (g x).line = lnMap g x.line :=
  ⟨(ptMap_pt hg x).symm, (lnMap_line hg x).symm⟩

theorem eq_of_ptMap_eq {g h : Equiv.Perm (PlaneFlag k)} (hg : g ∈ planeTypeAut k)
    (hh : h ∈ planeTypeAut k)
    (hgh : ∀ P : Submodule k (Fin 3 → k), finrank k P = 1 → ptMap g P = ptMap h P) :
    g = h := by
  ext1 x
  refine PlaneFlag.ext ?_ ?_
  · rw [← ptMap_pt hg, ← ptMap_pt hh, hgh _ x.finrank_pt]
  · obtain ⟨P, Q, hP, hQ, hPQ, hPL, hQL⟩ := exists_two_pts x.finrank_line
    rw [← lnMap_line hg, ← lnMap_line hh]
    have hP' := finrank_ptMap hg hP
    have hQ' := finrank_ptMap hg hQ
    refine line_eq_of_ne hP' hQ' (finrank_lnMap hg x.finrank_line)
      (finrank_lnMap hh x.finrank_line) (fun e => hPQ ((ptMap_inj hg hP hQ).mp e))
      ((ptMap_le_lnMap_iff hg hP x.finrank_line).mpr hPL)
      ((ptMap_le_lnMap_iff hg hQ x.finrank_line).mpr hQL) ?_ ?_
    · rw [hgh P hP]
      exact (ptMap_le_lnMap_iff hh hP x.finrank_line).mpr hPL
    · rw [hgh Q hQ]
      exact (ptMap_le_lnMap_iff hh hQ x.finrank_line).mpr hQL

theorem isOpposite_apply_iff (hg : g ∈ planeTypeAut k) (x y : PlaneFlag k) :
    (g x).IsOpposite (g y) ↔ x.IsOpposite y := by
  unfold PlaneFlag.IsOpposite
  rw [← ptMap_pt hg, ← lnMap_line hg, ← ptMap_pt hg, ← lnMap_line hg,
    ptMap_le_lnMap_iff hg x.finrank_pt y.finrank_line,
    ptMap_le_lnMap_iff hg y.finrank_pt x.finrank_line]

end ProjPlane

section Semilinear

variable {σ : k →+* k} [RingHomSurjective σ] {P : Submodule k (Fin 3 → k)}

namespace ProjPlane

theorem finrank_map_semilinear (φ : (Fin 3 → k) →ₛₗ[σ] (Fin 3 → k))
    (hφ : Function.Injective φ) (P : Submodule k (Fin 3 → k)) :
    finrank k (P.map φ) = finrank k P := by
  have hσ : Function.Bijective σ := ⟨σ.injective, RingHomSurjective.is_surjective⟩
  let j : P ≃+ P.map φ := AddEquiv.ofBijective (φ.submoduleMap P).toAddMonoidHom
    ⟨fun a b h => Subtype.ext (hφ (congrArg Subtype.val h)), φ.submoduleMap_surjective P⟩
  have h := rank_eq_of_equiv_equiv σ j hσ (fun r m => (φ.submoduleMap P).map_smulₛₗ r m)
  simp only [Module.finrank, h]

end ProjPlane

@[expose] def PlaneFlag.map (φ : (Fin 3 → k) →ₛₗ[σ] (Fin 3 → k)) (hφ : Function.Injective φ)
    (x : PlaneFlag k) : PlaneFlag k where
  pt := x.pt.map φ
  line := x.line.map φ
  finrank_pt := (finrank_map_semilinear φ hφ _).trans x.finrank_pt
  finrank_line := (finrank_map_semilinear φ hφ _).trans x.finrank_line
  pt_le_line := Submodule.map_mono x.pt_le_line

theorem PlaneFlag.map_bijective (φ : (Fin 3 → k) →ₛₗ[σ] (Fin 3 → k))
    (hφ : Function.Bijective φ) : Function.Bijective (PlaneFlag.map φ hφ.1) := by
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h1 : x.pt.map φ = y.pt.map φ := congrArg PlaneFlag.pt h
    have h2 : x.line.map φ = y.line.map φ := congrArg PlaneFlag.line h
    exact PlaneFlag.ext (Submodule.map_injective_of_injective hφ.1 h1)
      (Submodule.map_injective_of_injective hφ.1 h2)
  · have hpt : (y.pt.comap φ).map φ = y.pt := Submodule.map_comap_eq_of_surjective hφ.2 _
    have hline : (y.line.comap φ).map φ = y.line := Submodule.map_comap_eq_of_surjective hφ.2 _
    refine ⟨⟨y.pt.comap φ, y.line.comap φ, ?_, ?_, Submodule.comap_mono y.pt_le_line⟩, ?_⟩
    · rw [← finrank_map_semilinear φ hφ.1, hpt, y.finrank_pt]
    · rw [← finrank_map_semilinear φ hφ.1, hline, y.finrank_line]
    · exact PlaneFlag.ext hpt hline

@[expose] noncomputable def planeFlagPerm (φ : (Fin 3 → k) →ₛₗ[σ] (Fin 3 → k))
    (hφ : Function.Bijective φ) : Equiv.Perm (PlaneFlag k) :=
  Equiv.ofBijective _ (PlaneFlag.map_bijective φ hφ)

variable (φ : (Fin 3 → k) →ₛₗ[σ] (Fin 3 → k)) (hφ : Function.Bijective φ)

@[simp] theorem planeFlagPerm_pt (x : PlaneFlag k) :
    (planeFlagPerm φ hφ x).pt = x.pt.map φ := rfl

@[simp] theorem planeFlagPerm_line (x : PlaneFlag k) :
    (planeFlagPerm φ hφ x).line = x.line.map φ := rfl

theorem planeFlagPerm_mem_planeTypeAut : planeFlagPerm φ hφ ∈ planeTypeAut k := fun _ _ =>
  ⟨(Submodule.map_injective_of_injective hφ.1).eq_iff,
    (Submodule.map_injective_of_injective hφ.1).eq_iff⟩

theorem ptMap_planeFlagPerm (hP : finrank k P = 1) :
    ptMap (planeFlagPerm φ hφ) P = P.map φ := by
  obtain ⟨x, rfl⟩ := exists_flag_pt hP
  rw [ptMap_pt (planeFlagPerm_mem_planeTypeAut φ hφ), planeFlagPerm_pt]

theorem ProjPlane.map_span_singleton (v : Fin 3 → k) : (k ∙ v).map φ = k ∙ φ v := by
  rw [Submodule.map_span, Set.image_singleton]

end Semilinear

@[expose] def planeDiagFun (a b : kˣ) (σ : k ≃+* k) (v : Fin 3 → k) : Fin 3 → k :=
  ![a * σ (v 0), b * σ (v 1), σ (v 2)]

@[simp] theorem planeDiagFun_vec (a b : kˣ) (σ : k ≃+* k) (x y z : k) :
    planeDiagFun a b σ ![x, y, z] = ![a * σ x, b * σ y, σ z] := rfl

@[expose] def planeDiagSemilin (a b : kˣ) (σ : k ≃+* k) :
    (Fin 3 → k) →ₛₗ[(σ : k →+* k)] (Fin 3 → k) where
  toFun := planeDiagFun a b σ
  map_add' v w := by
    ext i
    fin_cases i <;> simp [planeDiagFun] <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [planeDiagFun] <;> ring

@[simp] theorem planeDiagSemilin_apply (a b : kˣ) (σ : k ≃+* k) (v : Fin 3 → k) :
    planeDiagSemilin a b σ v = planeDiagFun a b σ v := rfl

theorem planeDiagSemilin_bijective (a b : kˣ) (σ : k ≃+* k) :
    Function.Bijective (planeDiagSemilin a b σ) := by
  refine ⟨fun v w h => ?_, fun w => ?_⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [planeDiagSemilin_apply, planeDiagFun, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    ext i
    fin_cases i
    · exact σ.injective (mul_left_cancel₀ a.ne_zero h0)
    · exact σ.injective (mul_left_cancel₀ b.ne_zero h1)
    · exact σ.injective h2
  · refine ⟨![σ.symm (a⁻¹ * w 0), σ.symm (b⁻¹ * w 1), σ.symm (w 2)], ?_⟩
    ext i
    fin_cases i <;> simp [planeDiagFun]

@[expose] noncomputable def planeDiagPerm (a b : kˣ) (σ : k ≃+* k) : Equiv.Perm (PlaneFlag k) :=
  planeFlagPerm (planeDiagSemilin a b σ) (planeDiagSemilin_bijective a b σ)

@[simp] theorem planeDiagPerm_pt (a b : kˣ) (σ : k ≃+* k) (x : PlaneFlag k) :
    (planeDiagPerm a b σ x).pt = x.pt.map (planeDiagSemilin a b σ) := rfl

@[simp] theorem planeDiagPerm_line (a b : kˣ) (σ : k ≃+* k) (x : PlaneFlag k) :
    (planeDiagPerm a b σ x).line = x.line.map (planeDiagSemilin a b σ) := rfl

theorem planeDiagPerm_mem_planeTypeAut (a b : kˣ) (σ : k ≃+* k) :
    planeDiagPerm a b σ ∈ planeTypeAut k :=
  planeFlagPerm_mem_planeTypeAut _ _

theorem ptMap_planeDiagPerm (a b : kˣ) (σ : k ≃+* k) {v : Fin 3 → k} (hv : v ≠ 0) :
    ptMap (planeDiagPerm a b σ) (k ∙ v) = k ∙ planeDiagFun a b σ v :=
  (ptMap_planeFlagPerm (planeDiagSemilin a b σ) (planeDiagSemilin_bijective a b σ)
    (finrank_span_singleton hv)).trans (map_span_singleton _ v)

theorem ProjPlane.bijective_mulVecLin (A : GL (Fin 3) k) :
    Function.Bijective (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) k)) := by
  constructor
  · intro v w h
    have := congrArg (Matrix.mulVec ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) h
    simpa [Matrix.mulVec_mulVec] using this
  · intro w
    exact ⟨Matrix.mulVec ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) w,
      by simp [Matrix.mulVec_mulVec]⟩

@[expose] noncomputable def planeGLPerm (A : GL (Fin 3) k) : Equiv.Perm (PlaneFlag k) :=
  planeFlagPerm (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) k)) (bijective_mulVecLin A)

@[simp] theorem planeGLPerm_pt (A : GL (Fin 3) k) (x : PlaneFlag k) :
    (planeGLPerm A x).pt = x.pt.map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) k)) := rfl

@[simp] theorem planeGLPerm_line (A : GL (Fin 3) k) (x : PlaneFlag k) :
    (planeGLPerm A x).line = x.line.map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) k)) := rfl

theorem planeGLPerm_mem_planeTypeAut (A : GL (Fin 3) k) : planeGLPerm A ∈ planeTypeAut k :=
  planeFlagPerm_mem_planeTypeAut _ _

end CFSG.Monster.B.Geometry
