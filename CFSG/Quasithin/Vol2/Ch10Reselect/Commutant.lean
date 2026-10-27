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

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

private def E12 {K : Type*} [Field K] (a : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two]⟩

private def E21 {K : Type*} [Field K] (a : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; a, 1], by simp [Matrix.det_fin_two]⟩

private lemma E12_mulVec {K : Type*} [Field K] (a : K) (v : Fin 2 → K) :
    (E12 a : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0 + a * v 1, v 1] := by
  ext i; fin_cases i <;> simp [E12, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma E21_mulVec {K : Type*} [Field K] (a : K) (v : Fin 2 → K) :
    (E21 a : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0, a * v 0 + v 1] := by
  ext i; fin_cases i <;> simp [E21, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem addMonoidHom_eq_smul_of_commute_sl2 {K : Type*} [Field K]
    (f : (Fin 2 → K) →+ (Fin 2 → K))
    (hf : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      f ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ f v) :
    ∃ c : K, ∀ v, f v = c • v := by
  have hfix0 : f ![1, 0] = ![f ![1, 0] 0, 0] := by
    have h := hf (E12 (1 : K)) ![1, 0]
    have e : (E12 (1 : K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0] := by
      rw [E12_mulVec]; simp
    rw [e, E12_mulVec] at h
    have h1 : f ![1, 0] 1 = 0 := by simpa using congrFun h 0
    ext i
    fin_cases i <;> simp [h1]
  have hfix1 : f ![0, 1] = ![0, f ![0, 1] 1] := by
    have h := hf (E21 (1 : K)) ![0, 1]
    have e : (E21 (1 : K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![0, 1] = ![0, 1] := by
      rw [E21_mulVec]; simp
    rw [e, E21_mulVec] at h
    have h0 : f ![0, 1] 0 = 0 := by simpa using congrFun h 1
    ext i
    fin_cases i <;> simp [h0]
  obtain ⟨x, hx⟩ : ∃ x : K, f ![1, 0] = ![x, 0] := ⟨_, hfix0⟩
  obtain ⟨y, hy⟩ : ∃ y : K, f ![0, 1] = ![0, y] := ⟨_, hfix1⟩
  have hA : ∀ a : K, f ![a, 0] = ![a * y, 0] := by
    intro a
    have h := hf (E12 a) ![0, 1]
    simp only [E12_mulVec, hy, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      zero_add, mul_one] at h
    have h2 : f ![a, 1] = f ![a, 0] + ![0, y] := by
      rw [← hy, ← map_add]
      congr 1
      ext i
      fin_cases i <;> simp
    rw [h2] at h
    ext i
    fin_cases i
    · simpa using congrFun h 0
    · simpa using congrFun h 1
  have hB : ∀ b : K, f ![0, b] = ![0, b * x] := by
    intro b
    have h := hf (E21 b) ![1, 0]
    simp only [E21_mulVec, hx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      mul_one, add_zero, mul_zero, zero_add] at h
    have h2 : f ![1, b] = f ![1, 0] + f ![0, b] := by
      rw [← map_add]
      congr 1
      ext i
      fin_cases i <;> simp
    rw [h2, hx] at h
    ext i
    fin_cases i
    · simpa using congrFun h 0
    · simpa using congrFun h 1
  have hxy : x = y := by
    have h := hA 1
    rw [hx] at h
    simpa using congrFun h 0
  refine ⟨x, fun v => ?_⟩
  have hv : f v = f ![v 0, 0] + f ![0, v 1] := by
    rw [← map_add]
    congr 1
    ext i
    fin_cases i <;> simp
  rw [hv, hA, hB, ← hxy]
  ext i
  fin_cases i <;> simp <;> ring

theorem addMonoidHom_pair_of_commute_sl2 {K : Type*} [Field K]
    (f : ((Fin 2 → K) × (Fin 2 → K)) →+ ((Fin 2 → K) × (Fin 2 → K)))
    (hf : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : (Fin 2 → K) × (Fin 2 → K)),
      f ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v.1, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v.2) =
        ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ (f v).1, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (f v).2)) :
    ∃ a b c d : K, ∀ v, f v = (a • v.1 + b • v.2, c • v.1 + d • v.2) := by
  have hzero : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (0 : Fin 2 → K) = 0 :=
    fun g => Matrix.mulVec_zero _
  have hc1 : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      f ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v, 0) =
        ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ (f (v, 0)).1,
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (f (v, 0)).2) := by
    intro g v
    have h := hf g (v, 0)
    simpa only [hzero] using h
  have hc2 : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      f (0, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
        ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ (f (0, v)).1,
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (f (0, v)).2) := by
    intro g v
    have h := hf g (0, v)
    simpa only [hzero] using h
  obtain ⟨a, ha⟩ := addMonoidHom_eq_smul_of_commute_sl2
    ((AddMonoidHom.fst (Fin 2 → K) (Fin 2 → K)).comp
      (f.comp (AddMonoidHom.inl (Fin 2 → K) (Fin 2 → K))))
    (fun g v => congrArg Prod.fst (hc1 g v))
  obtain ⟨c, hc⟩ := addMonoidHom_eq_smul_of_commute_sl2
    ((AddMonoidHom.snd (Fin 2 → K) (Fin 2 → K)).comp
      (f.comp (AddMonoidHom.inl (Fin 2 → K) (Fin 2 → K))))
    (fun g v => congrArg Prod.snd (hc1 g v))
  obtain ⟨b, hb⟩ := addMonoidHom_eq_smul_of_commute_sl2
    ((AddMonoidHom.fst (Fin 2 → K) (Fin 2 → K)).comp
      (f.comp (AddMonoidHom.inr (Fin 2 → K) (Fin 2 → K))))
    (fun g v => congrArg Prod.fst (hc2 g v))
  obtain ⟨d, hd⟩ := addMonoidHom_eq_smul_of_commute_sl2
    ((AddMonoidHom.snd (Fin 2 → K) (Fin 2 → K)).comp
      (f.comp (AddMonoidHom.inr (Fin 2 → K) (Fin 2 → K))))
    (fun g v => congrArg Prod.snd (hc2 g v))
  have ha' : ∀ v, (f (v, 0)).1 = a • v := fun v => ha v
  have hc' : ∀ v, (f (v, 0)).2 = c • v := fun v => hc v
  have hb' : ∀ v, (f (0, v)).1 = b • v := fun v => hb v
  have hd' : ∀ v, (f (0, v)).2 = d • v := fun v => hd v
  refine ⟨a, b, c, d, fun v => ?_⟩
  have hsplit : f v = f (v.1, 0) + f (0, v.2) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  rw [hsplit]
  ext
  · simp only [Prod.fst_add, ha', hb']
  · simp only [Prod.snd_add, hc', hd']

@[expose] def centralizerSL2 (K : Type*) [Field K] :
    Subgroup (Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))) where
  carrier := {f | (∀ v w, f (v + w) = f v + f w) ∧
    ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : (Fin 2 → K) × (Fin 2 → K)),
      f ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v.1, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v.2) =
        ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ (f v).1, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (f v).2)}
  mul_mem' := by
    rintro f₁ f₂ ⟨hadd₁, hcomm₁⟩ ⟨hadd₂, hcomm₂⟩
    refine ⟨fun v w => ?_, fun g v => ?_⟩
    · simp only [Equiv.Perm.mul_apply]
      rw [hadd₂ v w]
      exact hadd₁ _ _
    · simp only [Equiv.Perm.mul_apply]
      rw [hcomm₂ g v, hcomm₁ g (f₂ v)]
  one_mem' := by
    refine ⟨fun v w => rfl, fun g v => rfl⟩
  inv_mem' := by
    rintro f ⟨hadd, hcomm⟩
    have hR : ∀ y, f (f⁻¹ y) = y := fun y => by
      rw [Equiv.Perm.inv_def]; exact Equiv.apply_symm_apply f y
    have hL : ∀ y, f⁻¹ (f y) = y := fun y => by
      rw [Equiv.Perm.inv_def]; exact Equiv.symm_apply_apply f y
    refine ⟨fun v w => ?_, fun g v => ?_⟩
    · calc f⁻¹ (v + w) = f⁻¹ (f (f⁻¹ v + f⁻¹ w)) := by rw [hadd, hR, hR]
        _ = f⁻¹ v + f⁻¹ w := hL _
    · have key : f (g *ᵥ (f⁻¹ v).1, g *ᵥ (f⁻¹ v).2) = (g *ᵥ v.1, g *ᵥ v.2) := by
        rw [hcomm g (f⁻¹ v), hR]
      rw [← key, hL]

private def cmRep {K : Type*} [Field K] (P : Matrix (Fin 2) (Fin 2) K)
    (v : (Fin 2 → K) × (Fin 2 → K)) : (Fin 2 → K) × (Fin 2 → K) :=
  (P 0 0 • v.1 + P 0 1 • v.2, P 1 0 • v.1 + P 1 1 • v.2)

private def cmMat {K : Type*} [Field K] (f : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))) :
    Matrix (Fin 2) (Fin 2) K :=
  !![(f (![1, 0], 0)).1 0, (f (0, ![1, 0])).1 0; (f (![1, 0], 0)).2 0, (f (0, ![1, 0])).2 0]

private lemma cmRep_mul {K : Type*} [Field K] (P Q : Matrix (Fin 2) (Fin 2) K)
    (v : (Fin 2 → K) × (Fin 2 → K)) :
    cmRep (P * Q) v = cmRep P (cmRep Q v) := by
  refine Prod.ext ?_ ?_ <;> simp only [cmRep, Matrix.mul_apply, Fin.sum_univ_two] <;> module

private lemma cmRep_one {K : Type*} [Field K] (v : (Fin 2 → K) × (Fin 2 → K)) :
    cmRep (1 : Matrix (Fin 2) (Fin 2) K) v = v := by
  simp [cmRep]

private lemma cmRep_inj {K : Type*} [Field K] {P Q : Matrix (Fin 2) (Fin 2) K}
    (h : ∀ v, cmRep P v = cmRep Q v) : P = Q := by
  have h1 := congrArg (fun w : (Fin 2 → K) × (Fin 2 → K) => w.1 0) (h (![1, 0], 0))
  have h2 := congrArg (fun w : (Fin 2 → K) × (Fin 2 → K) => w.2 0) (h (![1, 0], 0))
  have h3 := congrArg (fun w : (Fin 2 → K) × (Fin 2 → K) => w.1 0) (h (0, ![1, 0]))
  have h4 := congrArg (fun w : (Fin 2 → K) × (Fin 2 → K) => w.2 0) (h (0, ![1, 0]))
  simp [cmRep] at h1 h2 h3 h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

private lemma cmRep_cmMat {K : Type*} [Field K]
    (f : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))) (hf : f ∈ centralizerSL2 K)
    (v : (Fin 2 → K) × (Fin 2 → K)) : cmRep (cmMat f) v = f v := by
  obtain ⟨hadd, hcomm⟩ := hf
  obtain ⟨a, b, c, d, h⟩ := addMonoidHom_pair_of_commute_sl2 (AddMonoidHom.mk' f hadd) hcomm
  have h' : ∀ w, f w = (a • w.1 + b • w.2, c • w.1 + d • w.2) := h
  have m00 : cmMat f 0 0 = a := by simp [cmMat, h']
  have m01 : cmMat f 0 1 = b := by simp [cmMat, h']
  have m10 : cmMat f 1 0 = c := by simp [cmMat, h']
  have m11 : cmMat f 1 1 = d := by simp [cmMat, h']
  rw [h' v]
  simp only [cmRep, m00, m01, m10, m11]

private lemma cmMat_mul {K : Type*} [Field K]
    (f g : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))) (hf : f ∈ centralizerSL2 K)
    (hg : g ∈ centralizerSL2 K) :
    cmMat (f * g) = cmMat f * cmMat g := by
  apply cmRep_inj
  intro v
  have hfg : f * g ∈ centralizerSL2 K := (centralizerSL2 K).mul_mem hf hg
  rw [cmRep_cmMat _ hfg v, cmRep_mul, cmRep_cmMat _ hg v, cmRep_cmMat _ hf]
  rfl

private def cmHom (K : Type*) [Field K] : centralizerSL2 K →* Matrix (Fin 2) (Fin 2) K where
  toFun f := cmMat (f : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K)))
  map_one' := by
    apply cmRep_inj
    intro v
    show cmRep (cmMat 1) v = cmRep 1 v
    rw [cmRep_cmMat _ (centralizerSL2 K).one_mem v, cmRep_one]
    rfl
  map_mul' f g := by
    show cmMat ((f : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))) * (g : Equiv.Perm _)) =
      cmMat (f : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))) * cmMat (g : Equiv.Perm _)
    exact cmMat_mul _ _ f.2 g.2

private lemma cmHomUnits_injective (K : Type*) [Field K] :
    Function.Injective (cmHom K).toHomUnits := by
  intro f g h
  have hc : cmMat (f : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))) =
      cmMat (g : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))) := by
    have h' := congrArg Units.val h
    rw [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits] at h'
    exact h'
  apply Subtype.ext
  apply Equiv.ext
  intro v
  rw [← cmRep_cmMat _ f.2 v, ← cmRep_cmMat _ g.2 v, hc]

theorem orderOf_dvd_card_GL_two_of_mem_centralizerSL2 {K : Type*} [Field K] [Finite K]
    {f : Equiv.Perm ((Fin 2 → K) × (Fin 2 → K))} (hf : f ∈ centralizerSL2 K) :
    orderOf f ∣ Nat.card (GL (Fin 2) K) := by
  have hord : orderOf f = orderOf (⟨f, hf⟩ : centralizerSL2 K) :=
    Subgroup.orderOf_coe ⟨f, hf⟩
  rw [hord, ← orderOf_injective _ (cmHomUnits_injective K) ⟨f, hf⟩]
  exact orderOf_dvd_natCard _

end CFSG.Quasithin.Vol2.Ch10Reselect
