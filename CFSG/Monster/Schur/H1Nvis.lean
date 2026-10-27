module

public import CFSG.Monster.Schur.FoxCert
public import CFSG.Monster.VisCert.FrameRows
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
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
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
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.VisCert

theorem dec_one_shiftLeft (i : Fin 24) : dec (1 <<< (i : ℕ)) = ellCls i := by
  unfold dec
  rw [Finset.sum_eq_single i]
  · simp [bvec_apply, Nat.one_shiftLeft]
  · intro j _ hj
    have : (i : ℕ) ≠ j := fun h => hj (Fin.ext h.symm)
    simp [bvec_apply, Nat.one_shiftLeft, this]
  · simp

theorem eq_of_smul_ellCls {g h : GLV} (H : ∀ i : Fin 24, g • ellCls i = h • ellCls i) : g = h := by
  refine Units.ext (Module.Basis.ext ellBasis fun i => ?_)
  rw [ellBasis_apply]
  exact H i

theorem wordGL_eq_one_of_actWord {r : List ℕ} (hr : ∀ g ∈ r, g < 15)
    (h : ∀ i < 24, actWord frameMatrices r (1 <<< i) = 1 <<< i) : wordGL r = 1 := by
  refine eq_of_smul_ellCls fun i => ?_
  rw [← dec_one_shiftLeft, wordGL_smul_dec r hr, h i i.2, one_smul]

theorem wordGL_foxRelators {r : List ℕ} (hr : r ∈ foxRelators) : wordGL r = 1 :=
  wordGL_eq_one_of_actWord (fun g hg => by have := foxRelators_letters hr hg; omega)
    fun i hi => foxRelators_actWord hr hi

theorem frameRows_lt :
    ∀ g : Fin 15, ∀ i : Fin 24, (frameMatrices[(g : ℕ)]!)[(i : ℕ)]! < 2 ^ 24 := by
  decide +kernel

theorem actGo_lt (rows : Array ℕ) (v : ℕ) (hrows : ∀ i < 24, rows[i]! < 2 ^ 24) :
    ∀ n acc, n ≤ 24 → acc < 2 ^ 24 → actGo rows v n acc < 2 ^ 24
  | 0, acc, _, h => by simpa [actGo] using h
  | n + 1, acc, hn, h => by
    rw [actGo]
    refine actGo_lt rows v hrows n _ (by omega) ?_
    split_ifs
    · exact Nat.xor_lt_two_pow h (hrows n (by omega))
    · exact h

theorem actRows_frame_lt {g : ℕ} (hg : g < 15) (v : ℕ) : actRows frameMatrices[g]! v < 2 ^ 24 :=
  actGo_lt _ v (fun i hi => frameRows_lt ⟨g, hg⟩ ⟨i, hi⟩) 24 0 le_rfl (by norm_num)

theorem maskDot_shift (A : ℕ → ZMod 2) {g v : ℕ} (hg1 : 1 ≤ g) (hg : g ≤ 14) (hv : v < 2 ^ 24) :
    maskDot 336 A (v <<< (24 * (g - 1))) =
      ∑ i ∈ Finset.range 24, A (24 * (g - 1) + i) * bitZ v i := by
  obtain ⟨k, hk⟩ : ∃ k, k = 24 * (g - 1) := ⟨_, rfl⟩
  rw [← hk]
  have h336 : (336 : ℕ) = k + (24 + (312 - k)) := by omega
  unfold maskDot
  rw [h336, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range k, A x * bitZ (v <<< k) x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have : x < k := Finset.mem_range.1 hx
    simp [bitZ, Nat.testBit_shiftLeft, not_le.2 this]
  have h3 : ∑ x ∈ Finset.range (312 - k),
      A (k + (24 + x)) * bitZ (v <<< k) (k + (24 + x)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have : v.testBit (24 + x) = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [bitZ, Nat.testBit_shiftLeft, this]
  rw [h1, h3, zero_add, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [bitZ, Nat.testBit_shiftLeft]

noncomputable def genElt (g : ℕ) (h1 : 1 ≤ g) (h2 : g ≤ 14) : Nvis :=
  ⟨kGenN g, kGenN_mem_Nvis h1 (by omega)⟩

noncomputable def wordElt (w : List ℕ) (hw : ∀ g ∈ w, 1 ≤ g ∧ g ≤ 14) : Nvis :=
  ⟨wordGL w, wordGL_mem_Nvis w fun g hg => ⟨(hw g hg).1, by have := (hw g hg).2; omega⟩⟩

noncomputable def coAval (f : Nvis → Module.Dual (ZMod 2) L2) (s : ℕ) : ZMod 2 :=
  if hs : s < 336 then
    f (genElt (s / 24 + 1) (by omega) (by omega))
      (ellCls ⟨s % 24, Nat.mod_lt _ (by norm_num)⟩)
  else 0

theorem coAval_gen {f : Nvis → Module.Dual (ZMod 2) L2} {g i : ℕ} (hg1 : 1 ≤ g) (hg : g ≤ 14)
    (hi : i < 24) : coAval f (24 * (g - 1) + i) = f (genElt g hg1 hg) (ellCls ⟨i, hi⟩) := by
  have hs : 24 * (g - 1) + i < 336 := by omega
  have e1 : (24 * (g - 1) + i) / 24 + 1 = g := by omega
  have e2 : (24 * (g - 1) + i) % 24 = i := by omega
  simp only [coAval, hs, ↓reduceDIte]
  congr 2
  · exact Subtype.ext (by simp only [genElt, e1])
  · exact Fin.ext e2

theorem cocycle_gen_dec {f : Nvis → Module.Dual (ZMod 2) L2} {g : ℕ} (hg1 : 1 ≤ g)
    (hg : g ≤ 14) (v : ℕ) :
    f (genElt g hg1 hg) (dec v) =
      ∑ i ∈ Finset.range 24, coAval f (24 * (g - 1) + i) * bitZ v i := by
  rw [dec, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun i => coAval f (24 * (g - 1) + i) * bitZ v i) 24]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coAval_gen hg1 hg i.2, mul_comm]
  rfl

theorem kGenN_eq {j : ℕ} (hj : j < 15) : kGenN j = kGen ⟨j, hj⟩ := by
  simp [kGenN, hj]

noncomputable def foxPhi (f : Nvis → Module.Dual (ZMod 2) L2) : Module.Dual (ZMod 2) L2 :=
  ellBasis.constr (ZMod 2) fun c : Fin 24 => maskDot 336 (coAval f) (foxB.getD c 0)

theorem foxPhi_dec (f : Nvis → Module.Dual (ZMod 2) L2) (x : ℕ) :
    foxPhi f (dec x) =
      ∑ c ∈ Finset.range 24, bitZ x c * maskDot 336 (coAval f) (foxB.getD c 0) := by
  rw [dec, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range
    (fun c => bitZ x c * maskDot 336 (coAval f) (foxB.getD c 0)) 24]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : foxPhi f (ellCls c) = maskDot 336 (coAval f) (foxB.getD c 0) := by
    rw [← ellBasis_apply, foxPhi, Module.Basis.constr_basis]
  rw [this]
  rfl

section Cocycle

variable {f : Nvis → Module.Dual (ZMod 2) L2}
  (hf : ∀ g h v, f (g * h) v = f g ((h : GLV) • v) + f h v)

include hf

theorem cocycle_one (v : L2) : f 1 v = 0 := by
  have h := hf 1 1 v
  rw [mul_one] at h
  have h2 : f 1 v + f 1 v = f 1 v + 0 := by
    rw [add_zero]
    convert h.symm using 3
  exact add_left_cancel h2

theorem fox_word : ∀ (w : List ℕ) (hw : ∀ g ∈ w, 1 ≤ g ∧ g ≤ 14) (v : ℕ), v < 2 ^ 24 →
    f (wordElt w hw) (dec v) = maskDot 336 (coAval f) (foxMask w v)
  | [], hw, v, hv => by
    rw [foxMask, maskDot_zero]
    exact cocycle_one hf _
  | g :: w, hw, v, hv => by
    have hg := hw g List.mem_cons_self
    have hw' : ∀ g' ∈ w, 1 ≤ g' ∧ g' ≤ 14 := fun g' h => hw g' (List.mem_cons_of_mem _ h)
    have hmul : wordElt (g :: w) hw = wordElt w hw' * genElt g hg.1 hg.2 := rfl
    rw [hmul, hf]
    have h1 : ((genElt g hg.1 hg.2 : Nvis) : GLV) • dec v = dec (actRows frameMatrices[g]! v) :=
      kGenN_smul_dec' (by omega) v
    rw [h1, fox_word w hw' _ (actRows_frame_lt (by omega) v), foxMask, maskDot_xor,
      maskDot_shift _ hg.1 hg.2 hv, cocycle_gen_dec hg.1 hg.2, add_comm]

theorem coAval_foxEqs : ∀ t ∈ foxEqs, maskDot 336 (coAval f) t = 0 := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨hp1, hp2⟩ := foxSel_valid hp
  have hrmem : foxRelators.getD p.1 [] ∈ foxRelators := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp1]
    exact List.getElem_mem _
  have h1 : 1 <<< p.2 < 2 ^ 24 := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [← fox_word hf _ (fun g hg => foxRelators_letters hrmem hg) _ h1]
  have : wordElt (foxRelators.getD p.1 []) (fun g hg => foxRelators_letters hrmem hg) = 1 :=
    Subtype.ext (wordGL_foxRelators hrmem)
  rw [this]
  exact cocycle_one hf _

theorem foxPhi_gen {g : ℕ} (hg1 : 1 ≤ g) (hg : g ≤ 14) (v : L2) :
    f (genElt g hg1 hg) v = foxPhi f ((kGenN g) • v) - foxPhi f v := by
  have hext : f (genElt g hg1 hg) =
      (foxPhi f).comp (((kGenN g : GLV) : L2 →ₗ[ZMod 2] L2)) - foxPhi f := by
    refine Module.Basis.ext ellBasis fun i => ?_
    rw [ellBasis_apply, LinearMap.sub_apply, LinearMap.comp_apply]
    have e1 := coAval_gen (f := f) hg1 hg i.2
    have e2 := fox_principal (coAval f) (coAval_foxEqs hf) hg1 hg i.2
    have e3 : ((kGenN g : GLV) : L2 →ₗ[ZMod 2] L2) (ellCls i) =
        dec ((frameMatrices[g]!)[(i : ℕ)]!) := by
      rw [kGenN_eq (by omega)]
      exact kGen_smul_ellCls ⟨g, by omega⟩ i
    have e4 : foxPhi f (ellCls i) =
        ∑ c ∈ Finset.range 24, bitZ (1 <<< (i : ℕ)) c * maskDot 336 (coAval f) (foxB.getD c 0) := by
      rw [← foxPhi_dec, dec_one_shiftLeft]
    rw [e3, foxPhi_dec, e4, ← e1, e2]
    simp only [lamRow, bitZ_xor, add_mul, Finset.sum_add_distrib]
    rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  rw [hext]
  rfl

theorem h1_Nvis_dual_aux :
    ∀ (x : GLV) (hx : x ∈ Nvis) (v : L2), f ⟨x, hx⟩ v = foxPhi f (x • v) - foxPhi f v := by
  intro x hx
  refine Subgroup.closure_induction (p := fun x hx => ∀ v : L2,
    f ⟨x, hx⟩ v = foxPhi f (x • v) - foxPhi f v) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, hj, rfl⟩ v
    have hj1 : 1 ≤ (j : ℕ) := hj
    have h := foxPhi_gen hf hj1 (by omega) v
    rw [kGenN_eq j.2, Fin.eta] at h
    refine Eq.trans ?_ h
    exact congrArg (fun y => f y v)
      (Subtype.ext (by simp only [genElt, kGenN_eq j.2, Fin.eta])).symm
  · intro v
    have : (⟨1, Nvis.one_mem⟩ : Nvis) = 1 := rfl
    rw [this, cocycle_one hf, one_smul, sub_self]
  · intro x y hx hy ihx ihy v
    have := hf ⟨x, hx⟩ ⟨y, hy⟩ v
    change f ⟨x * y, _⟩ v = _ at this
    rw [this, ihx, ihy, mul_smul]
    abel
  · intro x hx ihx v
    have h := hf ⟨x, hx⟩ ⟨x⁻¹, Nvis.inv_mem hx⟩ v
    have h1 : (⟨x, hx⟩ * ⟨x⁻¹, Nvis.inv_mem hx⟩ : Nvis) = 1 := Subtype.ext (mul_inv_cancel x)
    rw [h1, cocycle_one hf] at h
    change 0 = f ⟨x, hx⟩ (x⁻¹ • v) + f ⟨x⁻¹, Nvis.inv_mem hx⟩ v at h
    rw [ihx, smul_inv_smul] at h
    have h2 : f ⟨x⁻¹, Nvis.inv_mem hx⟩ v = -(foxPhi f v - foxPhi f (x⁻¹ • v)) :=
      eq_neg_of_add_eq_zero_right h.symm
    rw [h2, neg_sub]

end Cocycle

theorem h1_Nvis_dual (f : Nvis → Module.Dual (ZMod 2) L2)
    (hf : ∀ g h v, f (g * h) v = f g ((h : GLV) • v) + f h v) :
    ∃ φ : Module.Dual (ZMod 2) L2, ∀ (g : Nvis) v, f g v = φ ((g : GLV) • v) - φ v :=
  ⟨foxPhi f, fun g v => h1_Nvis_dual_aux hf g g.2 v⟩

end CFSG.Monster.Schur
