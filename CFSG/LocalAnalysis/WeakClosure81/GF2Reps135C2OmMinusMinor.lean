module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinorTri
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinorNode
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinorShort

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private theorem o8mMI_dScalar_eq_one {k : Type} [Field k] [CharP k 2]
    (hK : Nat.card K = 2) {χ : spinGroup (quadMinus 4 K b c) → k}
    (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1) :
    ∀ t : Fin 3, (o8mDatum hirrQ).dScalar χ t = 1 := by
  intro t
  by_cases ht2 : t.val < 2
  · exact o8mDatum_dScalar_long (hirrQ := hirrQ) hK (hχ 1 (one_mem _)) ht2
  · have ht3 : t = 2 := Fin.ext (by have := t.isLt; omega)
    rw [ht3]
    exact (o8mDatum_dScalar_short_of_trivial (hirrQ := hirrQ) hK hχ).1

open CFSG.LieType.RootSystem in
private theorem o8mMI_minor_X_mul_nW {i : Fin (4 - 1)}
    {w : (coxeterMatrix (isFiniteType_cartanB (4 - 1))).Group}
    (hlen : (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.length
        ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.simple i * w) =
      (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.length w + 1)
    {x : spinGroup (quadMinus 4 K b c)} (hx : x ∈ (o8mDatum hirrQ).X i) :
    o8mMinor i (mat 4 x * mat 4 ((o8mDatum hirrQ).nW w)) =
      o8mMinor i (mat 4 ((o8mDatum hirrQ).nW w)) := by
  have hxu : ((o8mDatum hirrQ).nW w)⁻¹ * x * (o8mDatum hirrQ).nW w ∈ (o8mDatum hirrQ).U :=
    (o8mDatum hirrQ).nW_conj w i hlen x hx
  have hmul : mat 4 x * mat 4 ((o8mDatum hirrQ).nW w) =
      mat 4 ((o8mDatum hirrQ).nW w) *
        mat 4 (((o8mDatum hirrQ).nW w)⁻¹ * x * (o8mDatum hirrQ).nW w) := by
    rw [← mat_mul, ← mat_mul]
    congr 1
    group
  rw [hmul]
  exact o8mMinor_mul_mat_of_mem_U (hirrQ := hirrQ) hxu i _

private theorem o8mMI_prod_map_ite {α : Type*} [DecidableEq α] {R : Type*} [CommRing R]
    (J : Finset α) (ω : List α) :
    (ω.map (fun s => if s ∈ J then (0 : R) else 1)).prod =
      ∏ i ∈ J, (if i ∈ ω then (0 : R) else 1) := by
  induction ω with
  | nil => simp
  | cons s ω ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hs : s ∈ J
    · rw [if_pos hs, zero_mul]
      exact (Finset.prod_eq_zero hs (by simp)).symm
    · rw [if_neg hs, one_mul, ih]
      refine Finset.prod_congr rfl fun i hi => ?_
      have his : i ≠ s := fun h => hs (h ▸ hi)
      simp [List.mem_cons, his]

open CFSG.LieType.RootSystem in
theorem o8mMinor_mat_nW_wordProd {ω : List (Fin (4 - 1))}
    (hω : (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.IsReduced ω)
    (i : Fin 3) :
    o8mMinor i (mat 4 ((o8mDatum hirrQ).nW
      ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.wordProd ω))) =
      if i ∈ ω then 0 else 1 := by
  induction ω with
  | nil =>
    rw [CoxeterSystem.wordProd_nil, (o8mDatum hirrQ).nW_one, mat_one, o8mMinor_one]
    simp
  | cons s ω ih =>
    obtain ⟨hred, hlen⟩ := CurtisDatum.reduced_cons hω
    rw [CoxeterSystem.wordProd_cons,
      (o8mDatum hirrQ).nW_simple_mul _ _ hlen, mat_mul]
    by_cases hsi : s = i
    · subst hsi
      rw [if_pos (by simp)]
      by_cases hi : s.val < 2
      · exact o8mMinor_mat_n_mul_eq_zero_of_long (hirrQ := hirrQ) (i := s) hi _
          (fun x hx => o8mMI_minor_X_mul_nW (hirrQ := hirrQ) hlen hx)
      · have hi2 : s = 2 := by
          have h1 : s.val < 3 := by simp
          have hv : s.val = 2 := by omega
          exact Fin.ext (by simpa using hv)
        subst hi2
        exact o8mMinor_mat_n_two_mul_eq_zero (hirrQ := hirrQ) _
          (fun x hx => o8mMI_minor_X_mul_nW (hirrQ := hirrQ) hlen hx)
    · rw [o8mMinor_mat_n_mul_of_ne (hirrQ := hirrQ) hsi, ih hred]
      have hmem : i ∈ s :: ω ↔ i ∈ ω := by
        simp [List.mem_cons, Ne.symm hsi]
      by_cases hmemω : i ∈ ω
      · have hmemcons : i ∈ s :: ω := hmem.mpr hmemω
        simp [hmemω, hmemcons]
      · have hmemcons : ¬ i ∈ s :: ω := fun h => hmemω (hmem.mp h)
        simp [hmemω, hmemcons]

open CFSG.LieType.RootSystem in
private theorem o8mMI_minor_mat_eq (hK : Nat.card K = 2)
    {w : (coxeterMatrix (isFiniteType_cartanB (4 - 1))).Group}
    {ω : List (Fin (4 - 1))}
    (hω : (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.IsReduced ω)
    (hw : w = (coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.wordProd ω)
    {l h u : spinGroup (quadMinus 4 K b c)} (hl : l ∈ (o8mDatum hirrQ).L)
    (hh : h ∈ (o8mDatum hirrQ).H) (hu : u ∈ (o8mDatum hirrQ).U) (i : Fin 3) :
    o8mMinor i (mat 4 (l * (o8mDatum hirrQ).nW w * (h * u))) =
      if i ∈ ω then 0 else 1 := by
  rw [hw]
  have hmat : mat 4 (l * (o8mDatum hirrQ).nW
      ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.wordProd ω) * (h * u)) =
      mat 4 l * (mat 4 ((o8mDatum hirrQ).nW
        ((coxeterMatrix (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.wordProd ω)) *
        (mat 4 h * mat 4 u)) := by
    rw [mat_mul, mat_mul, mat_mul, mul_assoc]
  rw [hmat]
  rw [o8mMinor_mat_mul_of_mem_L (hirrQ := hirrQ) hl i]
  rw [← mul_assoc, o8mMinor_mul_mat_of_mem_U (hirrQ := hirrQ) hu i]
  rw [o8mMinor_mul_mat_of_mem_H (hirrQ := hirrQ) hK hh i]
  exact o8mMinor_mat_nW_wordProd (hirrQ := hirrQ) hω i

theorem o8mDatum_sph_eq_minorProd (hK : Nat.card K = 2) {k : Type} [Field k] (φ : K →+* k)
    {χ : spinGroup (quadMinus 4 K b c) → k} (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1)
    {μ : Fin 3 → k} {J : Finset (Fin 3)} (hμ : ∀ i, μ i = if i ∈ J then 1 else 0)
    (g : spinGroup (quadMinus 4 K b c)) :
    (o8mDatum hirrQ).sph χ μ g = φ (o8mMinorProd J (mat 4 g)) := by
  classical
  have : CharP k 2 := charP_of_injective_ringHom φ.injective 2
  simp only [CurtisDatum.sph]
  set q := ((o8mDatum hirrQ).cover' g).choose
  obtain ⟨hl, hh, hu, hg⟩ := ((o8mDatum hirrQ).cover' g).choose_spec
  set ω := ((CFSG.LieType.RootSystem.coxeterMatrix
    (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.exists_isReduced q.2.1).choose
  obtain ⟨hred, hw⟩ := ((CFSG.LieType.RootSystem.coxeterMatrix
    (isFiniteType_cartanB (4 - 1))).toCoxeterSystem.exists_isReduced q.2.1).choose_spec
  have hχq : χ q.2.2.1 = 1 := hχ _ hh
  have hd := o8mMI_dScalar_eq_one (hirrQ := hirrQ) hK hχ
  have hcoinv : (o8mDatum hirrQ).coinvScalar χ μ ω =
      ∏ i ∈ J, (if i ∈ ω then (0 : k) else 1) := by
    simp only [CurtisDatum.coinvScalar]
    have hfac : ∀ s : Fin 3, μ s - (o8mDatum hirrQ).dScalar χ s =
        if s ∈ J then (0 : k) else 1 := by
      intro s
      rw [hd s, hμ s]
      by_cases hs : s ∈ J <;> simp [hs, CharTwo.neg_eq]
    simp only [hfac]
    exact o8mMI_prod_map_ite J ω
  have hminor : o8mMinorProd J (mat 4 g) =
      ∏ i ∈ J, (if i ∈ ω then (0 : K) else 1) := by
    simp only [o8mMinorProd]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hg]
    exact o8mMI_minor_mat_eq (hirrQ := hirrQ) hK hred hw hl hh hu i
  rw [hχq, one_mul, hcoinv, hminor, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [apply_ite φ, map_zero, map_one]

theorem o8mDatum_form_eq_minorProd (hK : Nat.card K = 2) {k : Type} [Field k] (φ : K →+* k)
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (spinGroup (quadMinus 4 K b c)) V} {y : V}
    {χ : spinGroup (quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (o8mDatum hirrQ).IsCurtisType ρ y χ μ) (hχ : ∀ h ∈ (o8mDatum hirrQ).H, χ h = 1)
    {J : Finset (Fin 3)} (hμ : ∀ i, μ i = if i ∈ J then 1 else 0) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (o8mDatum hirrQ).L, f z = 0) (hfy : f y = 1)
    (g : spinGroup (quadMinus 4 K b c)) :
    f (ρ g y) = φ (o8mMinorProd J (mat 4 g)) := by
  rw [(o8mDatum hirrQ).form_act ρ hf ht hfy g]
  exact o8mDatum_sph_eq_minorProd (hirrQ := hirrQ) hK φ hχ hμ g

end CFSG.LocalAnalysis.WeakClosure81
