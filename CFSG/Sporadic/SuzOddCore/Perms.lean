module

public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.SchreierChainOrderGenerators
public import Batteries.Data.Vector.Lemmas
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose, irreducible] def permC (n : ℕ) (t : Array ℕ) : Equiv.Perm (Fin n) :=
  @dite _ ((∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j)
    (Classical.propDecidable _)
    (fun h => Equiv.ofBijective (fun i : Fin n => (⟨t[(i : ℕ)]!, h.1 i i.2⟩ : Fin n))
      (Finite.injective_iff_bijective.1 fun i j hij =>
        Fin.ext (h.2 i i.2 j j.2 (congrArg Fin.val hij))))
    (fun _ => 1)

theorem rep_permC {n : ℕ} {t r : Array ℕ} (h : isInvA n t r = true) :
    Rep n t (permC n t) ∧ Rep n r (permC n t)⁻¹ := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => (isInvA_spec h hi).1, fun i hi j hj hij => by
      rw [← (isInvA_spec h hi).2, ← (isInvA_spec h hj).2, hij]⟩
  have ht : Rep n t (permC n t) := fun x => by
    rw [permC]
    rw [@dite_eq_left_of_eq_true _ _ (Classical.propDecidable _) _ _ (eq_true hc)]
    rfl
  refine ⟨ht, fun x => ?_⟩
  set y := (permC n t)⁻¹ x
  have hy : permC n t y = x := by simp [y]
  have h1 := ht y
  rw [hy] at h1
  rw [← h1, (isInvA_spec h y.2).2]

@[expose] def rawOfArrays (n : ℕ) (hn : 1 ≤ n) (O S : Array (Array ℕ)) (hk : O.size ≤ S.size)
    (base : List (Fin n)) (hb : base.Nodup) (W : Array (List ℤ)) : RawSchreierDatum n where
  degree_pos := hn
  originalCount := O.size
  strongCount := S.size
  baseCount := base.length
  originalCount_le := hk
  original := Vector.ofFn fun i : Fin O.size => permC n O[(i : ℕ)]!
  strong := Vector.ofFn fun j : Fin S.size => permC n S[(j : ℕ)]!
  base := ⟨base.toArray, by simp⟩
  base_distinct := by simpa using hb
  derivation j _ := toLetters j.val W[(j : ℕ)]!

section RawOfArrays

variable {n : ℕ} {hn : 1 ≤ n} {O S : Array (Array ℕ)} {hk : O.size ≤ S.size}
  {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)}

theorem rawOfArrays_original_get (i : Fin (rawOfArrays n hn O S hk base hb W).originalCount) :
    (rawOfArrays n hn O S hk base hb W).original.get i = permC n O[(i : ℕ)]! := by
  have hi : (i : ℕ) < O.size := i.2
  simp [rawOfArrays, Vector.get]
  rw [getElem!_pos O (i : ℕ) hi]
  rfl

theorem rawOfArrays_strong_get (j : Fin (rawOfArrays n hn O S hk base hb W).strongCount) :
    (rawOfArrays n hn O S hk base hb W).strong.get j = permC n S[(j : ℕ)]! := by
  have hj : (j : ℕ) < S.size := j.2
  simp [rawOfArrays, Vector.get]
  rw [getElem!_pos S (j : ℕ) hj]
  rfl

theorem rawOfArrays_base_toList : (rawOfArrays n hn O S hk base hb W).base.toList = base := by
  change (⟨base.toArray, _⟩ : Vector (Fin n) base.length).toList = base
  simp

theorem rawOfArrays_derivation (j : Fin (rawOfArrays n hn O S hk base hb W).strongCount)
    (hj : (rawOfArrays n hn O S hk base hb W).originalCount ≤ j.val) :
    (rawOfArrays n hn O S hk base hb W).derivation j hj = toLetters j.val W[(j : ℕ)]! := rfl

theorem rawOfArrays_original_toList :
    (rawOfArrays n hn O S hk base hb W).original.toList =
      (List.finRange O.size).map fun i : Fin O.size => permC n O[(i : ℕ)]! := by
  change (Vector.ofFn fun i : Fin O.size => permC n O[(i : ℕ)]!).toList = _
  rw [Vector.toList_ofFn, List.ofFn_eq_map]

end RawOfArrays

@[expose] def pt (n : ℕ) [NeZero n] (x : ℕ) : Fin n :=
  ⟨x % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

theorem pt_val {n : ℕ} [NeZero n] {x : ℕ} (hx : x < n) : (pt n x : ℕ) = x := Nat.mod_eq_of_lt hx

@[expose] def certBase : List (Fin 22880) := certBaseNat.map (pt 22880)

theorem certBase_eq : certBase = [0, 1, 2, 3, 4, 5] := by decide

theorem certBase_nodup : certBase.Nodup := by rw [certBase_eq]; decide

theorem certGenArrs_size : certGenArrs.size = 2 := rfl

theorem certStrongArrs_size : certStrongArrs.size = 10 := rfl

theorem certGen_le_strong : certGenArrs.size ≤ certStrongArrs.size := by
  rw [certGenArrs_size, certStrongArrs_size]; norm_num

@[expose] def certChain : RawSchreierDatum 22880 :=
  rawOfArrays 22880 (by norm_num) certGenArrs certStrongArrs certGen_le_strong certBase
    certBase_nodup certDerivs

theorem certChain_originalCount : certChain.originalCount = 2 := rfl

theorem certChain_strongCount : certChain.strongCount = 10 := rfl

theorem certChain_baseCount : certChain.baseCount = 6 := by
  change certBase.length = 6
  rw [certBase_eq]
  rfl

@[expose] def suzA0 : Equiv.Perm (Fin 22880) := permC 22880 (certArr 0)

@[expose] def suzA1 : Equiv.Perm (Fin 22880) := permC 22880 (certArr 1)

@[expose] def suzS (j : ℕ) : Equiv.Perm (Fin 22880) := permC 22880 (certArr (j + 2))

@[expose] def suzP : Subgroup (Equiv.Perm (Fin 22880)) := Subgroup.closure {suzA0, suzA1}

theorem rep_certArr
    {k : ℕ} (hk : k < 12) : Rep 22880 (certArr k) (permC 22880 (certArr k)) :=
  (rep_permC (Bool.and_eq_true_iff.1 (arrays_check.1 k hk)).2).1

theorem rep_suzA0 :
    Rep 22880 (certArr 0) suzA0 := rep_certArr (by norm_num)

theorem rep_suzA1 :
    Rep 22880 (certArr 1) suzA1 := rep_certArr (by norm_num)

theorem rep_suzS
    {j : ℕ} (hj : j < 10) : Rep 22880 (certArr (j + 2)) (suzS j) :=
  rep_certArr (by omega)

theorem certGenArrs_get_zero : certGenArrs[0]! = certArr 0 := by simp [certGenArrs]

theorem certGenArrs_get_one : certGenArrs[1]! = certArr 1 := by simp [certGenArrs]

theorem certStrongArrs_get {j : ℕ} (hj : j < 10) : certStrongArrs[j]! = certArr (j + 2) := by
  interval_cases j <;> simp [certStrongArrs]

theorem certChain_original_get (i : Fin certChain.originalCount) :
    certChain.original.get i = permC 22880 certGenArrs[(i : ℕ)]! :=
  rawOfArrays_original_get i

theorem certChain_original_eq (i : Fin certChain.originalCount) :
    certChain.original.get i = ![suzA0, suzA1] (Fin.cast certChain_originalCount i) := by
  rw [certChain_original_get]
  have hi : (i : ℕ) < 2 := i.2
  interval_cases h : (i : ℕ)
  · rw [show Fin.cast certChain_originalCount i = 0 from Fin.ext h, certGenArrs_get_zero,
      Matrix.cons_val_zero]
    rfl
  · rw [show Fin.cast certChain_originalCount i = 1 from Fin.ext h, certGenArrs_get_one,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rfl

theorem certChain_strong_get (j : Fin certChain.strongCount) :
    certChain.strong.get j = suzS j := by
  have hj : (j : ℕ) < 10 := j.2
  rw [show certChain.strong.get j = permC 22880 certStrongArrs[(j : ℕ)]! from
    rawOfArrays_strong_get j, certStrongArrs_get hj]
  rfl

theorem certChain_base_toList : certChain.base.toList = [0, 1, 2, 3, 4, 5] :=
  (rawOfArrays_base_toList (n := 22880)).trans certBase_eq

theorem mem_certChain_original {g : Equiv.Perm (Fin 22880)} :
    g ∈ certChain.original.toList ↔ g = suzA0 ∨ g = suzA1 := by
  rw [schreier_vector_mem_toList_iff_get]
  constructor
  · rintro ⟨i, rfl⟩
    rw [certChain_original_eq]
    have hi : (i : ℕ) < 2 := i.2
    interval_cases h : (i : ℕ)
    · left
      rw [show Fin.cast certChain_originalCount i = 0 from Fin.ext h, Matrix.cons_val_zero]
    · right
      rw [show Fin.cast certChain_originalCount i = 1 from Fin.ext h, Matrix.cons_val_one,
        Matrix.cons_val_zero]
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by rw [certChain_originalCount]; norm_num⟩, by
        rw [certChain_original_eq]; exact Matrix.cons_val_zero _ _⟩
    · exact ⟨⟨1, by rw [certChain_originalCount]; norm_num⟩, by
        rw [certChain_original_eq]
        exact (Matrix.cons_val_one _ _).trans (Matrix.cons_val_zero _ _)⟩

theorem certChain_originalSubgroup : certChain.originalSubgroup = suzP := by
  rw [RawSchreierDatum.originalSubgroup, suzP]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact mem_certChain_original

@[expose] def suzB0 : Equiv.Perm (Fin 1782) := permC 1782 b0Arr

@[expose] def suzB1 : Equiv.Perm (Fin 1782) := permC 1782 b1Arr

@[expose] def suzV : Equiv.Perm (Fin 1782) := permC 1782 vArr

@[expose] def suzM : Subgroup (Equiv.Perm (Fin 1782)) := Subgroup.closure {suzB0, suzB1}

@[expose] def suzT : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (insert suzV (suzM : Set (Equiv.Perm (Fin 1782))))

theorem rep_b0 : Rep 1782 b0Arr suzB0 :=
  (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.1).2).1

theorem rep_b1 : Rep 1782 b1Arr suzB1 :=
  (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.2.1).2).1

theorem rep_v : Rep 1782 vArr suzV :=
  (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.2.2.1).2).1

theorem rep_smallArr
    {k : ℕ} (hk : k < 14) : Rep 1782 (smallArr k) (permC 1782 (smallArr k)) :=
  (rep_permC (Bool.and_eq_true_iff.1 (arrays_check.2.1 k hk)).2).1

@[expose] def smallBase : List (Fin 1782) := smallBaseNat.map (pt 1782)

theorem smallBase_eq : smallBase = [0, 1, 2, 3, 4, 8] := by decide

theorem smallBase_nodup : smallBase.Nodup := by rw [smallBase_eq]; decide

theorem smallGenArrs_size : smallGenArrs.size = 2 := rfl

theorem smallStrongArrs_size : smallStrongArrs.size = 12 := rfl

theorem smallGen_le_strong : smallGenArrs.size ≤ smallStrongArrs.size := by
  rw [smallGenArrs_size, smallStrongArrs_size]; norm_num

@[expose] def smallChain : RawSchreierDatum 1782 :=
  rawOfArrays 1782 (by norm_num) smallGenArrs smallStrongArrs smallGen_le_strong smallBase
    smallBase_nodup smallDerivs

theorem smallChain_originalCount : smallChain.originalCount = 2 := rfl

theorem smallChain_strongCount : smallChain.strongCount = 12 := rfl

theorem smallChain_baseCount : smallChain.baseCount = 6 := by
  change smallBase.length = 6
  rw [smallBase_eq]
  rfl

theorem smallChain_base_toList : smallChain.base.toList = [0, 1, 2, 3, 4, 8] := by
  rw [smallChain, rawOfArrays_base_toList, smallBase_eq]

theorem smallGenArrs_get_zero : smallGenArrs[0]! = smallArr 0 := by simp [smallGenArrs]

theorem smallGenArrs_get_one : smallGenArrs[1]! = smallArr 1 := by simp [smallGenArrs]

theorem smallStrongArrs_get {j : ℕ} (hj : j < 12) : smallStrongArrs[j]! = smallArr (j + 2) := by
  interval_cases j <;> simp [smallStrongArrs]

theorem smallChain_original_get (i : Fin smallChain.originalCount) :
    smallChain.original.get i = permC 1782 smallGenArrs[(i : ℕ)]! :=
  rawOfArrays_original_get i

theorem smallChain_strong_get (j : Fin smallChain.strongCount) :
    smallChain.strong.get j = permC 1782 (smallArr (j + 2)) := by
  have hj : (j : ℕ) < 12 := j.2
  rw [show smallChain.strong.get j = permC 1782 smallStrongArrs[(j : ℕ)]! from
    rawOfArrays_strong_get j, smallStrongArrs_get hj]

theorem smallChain_original_eq (i : Fin smallChain.originalCount) :
    smallChain.original.get i = ![suzB0, suzB1] (Fin.cast smallChain_originalCount i) := by
  rw [smallChain_original_get]
  have hi : (i : ℕ) < 2 := i.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h0, h1⟩ := arrays_check
  interval_cases h : (i : ℕ)
  · rw [show Fin.cast smallChain_originalCount i = 0 from Fin.ext h, smallGenArrs_get_zero, h0,
      Matrix.cons_val_zero]
    rfl
  · rw [show Fin.cast smallChain_originalCount i = 1 from Fin.ext h, smallGenArrs_get_one, h1,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rfl

theorem mem_smallChain_original {g : Equiv.Perm (Fin 1782)} :
    g ∈ smallChain.original.toList ↔ g = suzB0 ∨ g = suzB1 := by
  rw [schreier_vector_mem_toList_iff_get]
  constructor
  · rintro ⟨i, rfl⟩
    rw [smallChain_original_eq]
    have hi : (i : ℕ) < 2 := i.2
    interval_cases h : (i : ℕ)
    · left
      rw [show Fin.cast smallChain_originalCount i = 0 from Fin.ext h, Matrix.cons_val_zero]
    · right
      rw [show Fin.cast smallChain_originalCount i = 1 from Fin.ext h, Matrix.cons_val_one,
        Matrix.cons_val_zero]
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by rw [smallChain_originalCount]; norm_num⟩, by
        rw [smallChain_original_eq]; exact Matrix.cons_val_zero _ _⟩
    · exact ⟨⟨1, by rw [smallChain_originalCount]; norm_num⟩, by
        rw [smallChain_original_eq]
        exact (Matrix.cons_val_one _ _).trans (Matrix.cons_val_zero _ _)⟩

theorem smallChain_originalSubgroup :
    smallChain.originalSubgroup = suzM := by
  rw [RawSchreierDatum.originalSubgroup, suzM]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact mem_smallChain_original

abbrev SuzK : Type := Equiv.Perm (Fin 22880) × Equiv.Perm (Fin 1782)

@[expose] def suzPhi : SuzK →* Equiv.Perm (Fin 22880) :=
  MonoidHom.fst (Equiv.Perm (Fin 22880)) (Equiv.Perm (Fin 1782))

@[expose] def suzBGen (i : Fin certChain.originalCount) : Equiv.Perm (Fin 1782) :=
  ![suzB0, suzB1] (Fin.cast certChain_originalCount i)

@[expose] def suzU : Vector SuzK certChain.originalCount :=
  Vector.ofFn fun i => (certChain.original.get i, suzBGen i)

theorem suzU_get (i : Fin certChain.originalCount) :
    suzU.get i = (certChain.original.get i, suzBGen i) := by
  rw [suzU, Vector.get_ofFn]

end CFSG.Sporadic.SuzOddCore
