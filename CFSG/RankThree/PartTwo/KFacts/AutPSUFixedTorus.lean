module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUSylowPoint
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
import CFSG.RankThree.PartOne.S11d.OddHerm
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofLinRat
import CFSG.LinearAlgebra.LinearGroups.Elations

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin Matrix
open scoped Pointwise

variable {n : ℕ} {K : Type} [Field K]

private theorem exists_odd_pow_eq_one (hu : UnitaryFieldData 2 n K) (hn : 1 ≤ n)
    (A : unitaryIsom3 hu) (hodd : Odd (orderOf (psuConj hu A))) :
    ∃ N : ℕ, Odd N ∧ (A : GL (Fin 3) K) ^ N = 1 := by
  set m := orderOf (psuConj hu A) with hm
  have hm1 : psuConj hu (A ^ m) = 1 := by
    rw [map_pow, hm, pow_orderOf_eq_one]
  obtain ⟨-, c, hc, hA⟩ :=
    eq_one_of_psuConj_mul_psuField_eq_one (h := hu) (A ^ m) 1 (by simpa using hm1)
  have hAGL : (A : GL (Fin 3) K) ^ m = GeneralLinearGroup.scalar (Fin 3) c := by
    simpa using hA
  have hc1 : (c : K) ^ (2 ^ n + 1) = 1 := by
    rw [← hu.norm_eq_pow, hc]
  have hc1u : c ^ (2 ^ n + 1) = 1 := by
    ext
    simpa using hc1
  have hscalar : (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) ^ (2 ^ n + 1) = 1 := by
    rw [← map_pow, show c ^ (2 ^ n + 1) = 1 from hc1u, map_one]
  refine ⟨m * (2 ^ n + 1), hodd.mul ?_, ?_⟩
  · have h2n : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact h2n.add_one
  · rw [pow_mul, hAGL, hscalar]

private theorem pow_smul_of_eq_smul_add (A : GL (Fin 3) K) {a w : Fin 3 → K} {α γ : K}
    (ha : A • a = α • a) (hw : A • w = α • w + γ • a) (k : ℕ) :
    (A ^ (k + 1)) • w = α ^ (k + 1) • w +
      (((k + 1 : ℕ) : K) * α ^ k * γ) • a := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, smul_add, smul_comm A (α ^ (k + 1)) w,
      smul_comm A (((k + 1 : ℕ) : K) * α ^ k * γ) a, ha, hw, smul_add,
      smul_smul (α ^ (k + 1)) α w, smul_smul (α ^ (k + 1)) γ a,
      smul_smul (((k + 1 : ℕ) : K) * α ^ k * γ) α a, add_assoc, ← add_smul]
    congr 1
    · congr 1
      ring
    · congr 1
      push_cast
      ring

private theorem self_form_ne_zero_of_orthogonal (hu : UnitaryFieldData 2 n K)
    {w : Fin 3 → K} {W : Submodule K (Fin 3 → K)}
    (hW : W = Submodule.span K {w})
    (hWsep : ∀ v : W,
      (∀ y : W, stdHermForm hu 3 (v : Fin 3 → K) (y : Fin 3 → K) = 0) → v = 0)
    (hw0 : w ≠ 0) : stdHermForm hu 3 w w ≠ 0 := by
  intro h0
  apply hw0
  have hwW : w ∈ W := by
    rw [hW]
    exact Submodule.mem_span_singleton_self w
  have h : (⟨w, hwW⟩ : W) = 0 := by
    apply hWsep
    intro y
    have hyW : (y : Fin 3 → K) ∈ Submodule.span K {w} := by
      rw [← hW]
      exact y.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hyW
    change stdHermForm hu 3 w (y : Fin 3 → K) = 0
    rw [← hc, map_smul, smul_eq_mul, h0, mul_zero]
  exact congrArg Subtype.val h

private theorem exists_fixed_isotropic_eigenvector (hu : UnitaryFieldData 2 n K)
    (A : unitaryIsom3 hu) {L : Submodule K (Fin 3 → K)}
    (hL : L ∈ isotropicLines hu 3) (hfix : (A : GL (Fin 3) K) • L = L) :
    ∃ a : Fin 3 → K, ∃ al : K, a ≠ 0 ∧ stdHermForm hu 3 a a = 0 ∧
      (A : GL (Fin 3) K) • a = al • a ∧ al ≠ 0 := by
  classical
  obtain ⟨a, ha0, ha_iso, hLspan⟩ := exists_eq_span_of_mem_isotropicLines hL
  have haL : a ∈ L := hLspan.symm ▸ Submodule.mem_span_singleton_self a
  have hAa_mem : (A : GL (Fin 3) K) • a ∈ (A : GL (Fin 3) K) • L :=
    Submodule.smul_mem_pointwise_smul a (A : GL (Fin 3) K) L haL
  rw [hfix] at hAa_mem
  obtain ⟨al, hal⟩ := Submodule.mem_span_singleton.mp (hLspan ▸ hAa_mem)
  refine ⟨a, al, ha0, ha_iso, hal.symm, ?_⟩
  intro h0
  have h0' : (A : GL (Fin 3) K) • a = 0 := by rw [hal.symm, h0, zero_smul]
  have := congrArg (fun v => (A : GL (Fin 3) K)⁻¹ • v) h0'
  exact ha0 (by simpa using this)

private theorem exists_hyperbolic_anisotropic_data (hu : UnitaryFieldData 2 n K)
    {a : Fin 3 → K} (ha0 : a ≠ 0) (ha_iso : stdHermForm hu 3 a a = 0) :
    ∃ (b w : Fin 3 → K) (H W : Submodule K (Fin 3 → K)),
      H = Submodule.span K {a, b} ∧ W = H.orthogonalBilin (stdHermForm hu 3) ∧
        IsCompl H W ∧ stdHermForm hu 3 a b = 1 ∧ stdHermForm hu 3 b b = 0 ∧
        w ≠ 0 ∧ W = Submodule.span K {w} ∧ stdHermForm hu 3 a w = 0 ∧
        stdHermForm hu 3 w a = 0 ∧ stdHermForm hu 3 w w ≠ 0 := by
  classical
  obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ := hermitian_hyperbolic_splitting hu
    (stdHermForm_isSymm hu 3) (stdHermForm_separatingLeft hu 3) ha0 ha_iso
  obtain ⟨-, -, hcompl, hWsep, hWdim⟩ := hsplit b hab hbb
  set H : Submodule K (Fin 3 → K) := Submodule.span K {a, b} with hH
  set W : Submodule K (Fin 3 → K) := H.orthogonalBilin (stdHermForm hu 3) with hW
  have hWdim1 : Module.finrank K W = 1 := by rw [hW, hWdim]; norm_num
  obtain ⟨w, hw0, hWspan⟩ := exists_eq_span_of_finrank_eq_one hWdim1
  have hwW : w ∈ W := hWspan ▸ Submodule.mem_span_singleton_self w
  have haw : stdHermForm hu 3 a w = 0 :=
    (Submodule.mem_orthogonalBilin.mp hwW) a (Submodule.subset_span (by simp))
  have hwa : stdHermForm hu 3 w a = 0 :=
    ((stdHermForm_isSymm hu 3).eq_iff).mpr haw
  have hww : stdHermForm hu 3 w w ≠ 0 :=
    self_form_ne_zero_of_orthogonal hu hWspan hWsep hw0
  exact ⟨b, w, H, W, rfl, rfl, hcompl, hab, hbb, hw0, hWspan, haw, hwa, hww⟩

private theorem exists_action_decomposition (hu : UnitaryFieldData 2 n K)
    (A : unitaryIsom3 hu) {a w : Fin 3 → K} {H W : Submodule K (Fin 3 → K)}
    {al : K} (b : Fin 3 → K) (hH : H = Submodule.span K {a, b})
    (hcompl : IsCompl H W) (hspan : W = Submodule.span K {w})
    (hα : (A : GL (Fin 3) K) • a = al • a) (hα0 : al ≠ 0)
    (ha_iso : stdHermForm hu 3 a a = 0) (hab : stdHermForm hu 3 a b = 1)
    (haw : stdHermForm hu 3 a w = 0) :
    ∃ p r : K, (A : GL (Fin 3) K) • w = p • a + r • w := by
  have hAw_perp : stdHermForm hu 3 a ((A : GL (Fin 3) K) • w) = 0 := by
    have hiso := isometry_of_mem_unitaryIsom3 hu A a w
    rw [hα, haw] at hiso
    have hbar : hu.bar al * stdHermForm hu 3 a ((A : GL (Fin 3) K) • w) = 0 := by
      simpa [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] using hiso
    exact (mul_eq_zero.mp hbar).resolve_left (by rwa [hu.bar_eq_zero_iff])
  have hAw_top : (A : GL (Fin 3) K) • w ∈ H ⊔ W := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, huH, z, hzW, huz⟩ := Submodule.mem_sup.mp hAw_top
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp (hH ▸ huH)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hzW)
  have hq0 : q = 0 := by
    have horth : stdHermForm hu 3 a ((A : GL (Fin 3) K) • w) = 0 := hAw_perp
    rw [← huz, ← hpq, ← hr] at horth
    exact (by simpa [map_add, map_smul, smul_eq_mul, ha_iso, hab, haw] using horth)
  refine ⟨p, r, ?_⟩
  rw [← huz, ← hpq, hq0, zero_smul, add_zero, hr]

private theorem pow_smul_of_eigenvector (A : GL (Fin 3) K) {a : Fin 3 → K} {al : K}
    (hα : A • a = al • a) (k : ℕ) : A ^ k • a = al ^ k • a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih, smul_comm A (al ^ k) a, hα, smul_smul, pow_succ]

private theorem exists_eigenvector_of_alpha_eq (hu : UnitaryFieldData 2 n K) (hn : 1 ≤ n)
    (A : unitaryIsom3 hu) {a w : Fin 3 → K} {al p r : K}
    (ha0 : a ≠ 0) (hα0 : al ≠ 0) (hα : (A : GL (Fin 3) K) • a = al • a)
    (hAw : (A : GL (Fin 3) K) • w = p • a + r • w) (hαr : al = r)
    (hw0 : w ≠ 0) (hww : stdHermForm hu 3 w w ≠ 0)
    (hwa : stdHermForm hu 3 w a = 0)
    (hodd : Odd (orderOf (psuConj hu A))) :
    ∃ u : Fin 3 → K, u ≠ 0 ∧ stdHermForm hu 3 u u ≠ 0 ∧
      stdHermForm hu 3 u a = 0 ∧ ∃ β : K, (A : GL (Fin 3) K) • u = β • u := by
  haveI : CharP K 2 := hu.charP
  obtain ⟨N, hNodd, hAN⟩ := exists_odd_pow_eq_one hu hn A hodd
  have hNpos : 0 < N := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hNodd
    exact Nat.not_odd_zero hNodd
  have hNa : (A : GL (Fin 3) K) ^ N • a = a := by rw [hAN, one_smul]
  have hαN : al ^ N = 1 := by
    rw [pow_smul_of_eigenvector (A : GL (Fin 3) K) hα N] at hNa
    exact smul_left_injective (R := K) (m := a) ha0 (by simpa using hNa)
  have hNw : (A : GL (Fin 3) K) ^ N • w = w := by rw [hAN, one_smul]
  have hcoeff : (N : K) = 1 := CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one hNodd
  have hw_eq : (A : GL (Fin 3) K) • w = al • w + p • a := by
    rw [hAw, hαr]
    abel
  have hformula := pow_smul_of_eq_smul_add (A : GL (Fin 3) K) hα hw_eq (N - 1)
  rw [Nat.sub_add_cancel hNpos, hNw, hαN, one_smul] at hformula
  rw [hcoeff, one_mul] at hformula
  have hp : p = 0 := by
    have h' : w + (0 : Fin 3 → K) = w + (al ^ (N - 1) * p) • a := by
      rw [add_zero]
      exact hformula
    have hc0 : (al ^ (N - 1) * p) • a = 0 := (add_left_cancel h').symm
    rcases smul_eq_zero.mp hc0 with h | h
    · exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hα0)
    · exact absurd h ha0
  refine ⟨w, hw0, hww, hwa, al, ?_⟩
  rw [hAw, hαr, hp, zero_smul, zero_add]

private theorem exists_translation_coeff (hu : UnitaryFieldData 2 n K) {al r p : K}
    (hαr : al ≠ r) :
    ∃ t : K, (al + r) * t = p ∧ p + t * al = r * t := by
  haveI : CharP K 2 := hu.charP
  have hden : al + r ≠ 0 := by
    intro h0
    have h1 : al = -r := by
      rw [eq_neg_iff_add_eq_zero]
      exact h0
    rw [CharTwo.neg_eq] at h1
    exact hαr h1
  refine ⟨p / (al + r), ?_, ?_⟩
  · rw [mul_comm, div_mul_cancel₀ _ hden]
  · rw [div_eq_mul_inv]
    field_simp [hden]
    have harr : al + r + al = r := by
      rw [add_assoc, add_comm r al, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [harr]

private theorem translate_ne_zero (hu : UnitaryFieldData 2 n K) {a w : Fin 3 → K}
    {H W : Submodule K (Fin 3 → K)} {t : K} {b : Fin 3 → K}
    (hH : H = Submodule.span K {a, b}) (hcompl : IsCompl H W)
    (hwW : w ∈ W) (hw0 : w ≠ 0) : w + t • a ≠ 0 := by
  haveI : CharP K 2 := hu.charP
  intro h0
  have hw_eq : w = t • a := by
    have h := eq_neg_of_add_eq_zero_left h0
    rwa [CharTwo.neg_eq] at h
  have h3 : w ∈ H := by
    rw [hw_eq, hH]
    exact Submodule.smul_mem _ t (Submodule.subset_span (by simp))
  exact hw0 (Submodule.disjoint_def.mp hcompl.disjoint w h3 hwW)

private theorem translate_anisotropic (hu : UnitaryFieldData 2 n K) {a w : Fin 3 → K}
    (t : K) (ha_iso : stdHermForm hu 3 a a = 0)
    (haw : stdHermForm hu 3 a w = 0) (hwa : stdHermForm hu 3 w a = 0)
    (hww : stdHermForm hu 3 w w ≠ 0) :
    stdHermForm hu 3 (w + t • a) (w + t • a) ≠ 0 ∧
      stdHermForm hu 3 (w + t • a) a = 0 := by
  constructor
  · have hcross : stdHermForm hu 3 w (t • a) = 0 := by
      rw [map_smul, smul_eq_mul, hwa, mul_zero]
    have hcross' : stdHermForm hu 3 (t • a) w = 0 := by
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, haw, mul_zero]
    have hself : stdHermForm hu 3 (t • a) (t • a) = 0 := by
      simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, RingHom.id_apply,
        smul_eq_mul, ha_iso, mul_zero, mul_zero]
    have hsum : stdHermForm hu 3 (w + t • a) (w + t • a) =
        stdHermForm hu 3 w w := by
      simp [map_add, LinearMap.add_apply, hcross, hcross', hself, haw, hwa, ha_iso]
    rw [hsum]
    exact hww
  · simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
      map_smul, smul_eq_mul, hwa, ha_iso, mul_zero, add_zero, RingHom.id_apply]

private theorem exists_eigenvector_of_alpha_ne (hu : UnitaryFieldData 2 n K)
    (A : unitaryIsom3 hu) {a w : Fin 3 → K} {H W : Submodule K (Fin 3 → K)}
    {al p r : K} (b : Fin 3 → K) (ha0 : a ≠ 0)
    (hα : (A : GL (Fin 3) K) • a = al • a) (hH : H = Submodule.span K {a, b})
    (hcompl : IsCompl H W) (hwW : w ∈ W) (hw0 : w ≠ 0)
    (ha_iso : stdHermForm hu 3 a a = 0) (haw : stdHermForm hu 3 a w = 0)
    (hwa : stdHermForm hu 3 w a = 0) (hww : stdHermForm hu 3 w w ≠ 0)
    (hAw : (A : GL (Fin 3) K) • w = p • a + r • w) (hαr : al ≠ r) :
    ∃ u : Fin 3 → K, u ≠ 0 ∧ stdHermForm hu 3 u u ≠ 0 ∧
      stdHermForm hu 3 u a = 0 ∧ ∃ β : K, (A : GL (Fin 3) K) • u = β • u := by
  obtain ⟨t, ht, hcoef⟩ := exists_translation_coeff hu hαr
  have htrans := translate_anisotropic hu t ha_iso haw hwa hww
  refine ⟨w + t • a, translate_ne_zero hu hH hcompl hwW hw0, htrans.1, htrans.2,
    r, ?_⟩
  rw [smul_add, smul_comm (A : GL (Fin 3) K) t a, hα, smul_smul, hAw,
    smul_add, smul_smul]
  have hgroup : (p • a + r • w) + (t * al) • a = r • w + (p + t * al) • a := by
    have h1 : (p • a + r • w) + (t * al) • a =
        (p • a + (t * al) • a) + r • w := by abel
    rw [h1, ← add_smul]
    abel
  rw [hgroup, hcoef]

private theorem eigenvalue_norm_one (hu : UnitaryFieldData 2 n K) (A : unitaryIsom3 hu)
    {u : Fin 3 → K} {β : K} (hun : stdHermForm hu 3 u u ≠ 0)
    (hβ : (A : GL (Fin 3) K) • u = β • u) : hu.norm β = 1 := by
  have hiso := isometry_of_mem_unitaryIsom3 hu A u u
  rw [hβ] at hiso
  have h' : (β * hu.bar β) * stdHermForm hu 3 u u = stdHermForm hu 3 u u := by
    simpa [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, mul_assoc] using hiso
  have hnorm : β * hu.bar β = 1 :=
    mul_right_cancel₀ hun (by rw [one_mul]; exact h')
  simpa [UnitaryFieldData.norm] using hnorm

private theorem exists_anisotropic_eigenvector (hu : UnitaryFieldData 2 n K) (hn : 1 ≤ n)
    (A : unitaryIsom3 hu) (L : Submodule K (Fin 3 → K)) (hL : L ∈ isotropicLines hu 3)
    (hfix : (A : GL (Fin 3) K) • L = L)
    (hodd : Odd (orderOf (psuConj hu A))) :
    ∃ a u : Fin 3 → K, a ≠ 0 ∧ u ≠ 0 ∧ stdHermForm hu 3 a a = 0 ∧
      stdHermForm hu 3 u u ≠ 0 ∧ stdHermForm hu 3 u a = 0 ∧
        ∃ β : K, (A : GL (Fin 3) K) • u = β • u ∧ hu.norm β = 1 := by
  obtain ⟨a, al, ha0, ha_iso, hα, hα0⟩ :=
    exists_fixed_isotropic_eigenvector hu A hL hfix
  obtain ⟨b, w, H, W, hH, hW, hcompl, hab, hbb, hw0, hspan, haw, hwa, hww⟩ :=
    exists_hyperbolic_anisotropic_data hu ha0 ha_iso
  have hwW : w ∈ W := hspan ▸ Submodule.mem_span_singleton_self w
  obtain ⟨p, r, hAw⟩ := exists_action_decomposition hu A b hH hcompl hspan hα hα0
    ha_iso hab haw
  have hex : ∃ u : Fin 3 → K, u ≠ 0 ∧ stdHermForm hu 3 u u ≠ 0 ∧
      stdHermForm hu 3 u a = 0 ∧ ∃ β : K, (A : GL (Fin 3) K) • u = β • u := by
    by_cases hαr : al = r
    · exact exists_eigenvector_of_alpha_eq hu hn A ha0 hα0 hα hAw hαr hw0 hww hwa hodd
    · exact exists_eigenvector_of_alpha_ne hu A b ha0 hα hH hcompl hwW hw0 ha_iso haw hwa
        hww hAw hαr
  obtain ⟨u, hu0, hun, hau, β, hβ⟩ := hex
  exact ⟨a, u, ha0, hu0, ha_iso, hun, hau, β, hβ,
    eigenvalue_norm_one hu A hun hβ⟩

private noncomputable def zLin (hu : UnitaryFieldData 2 n K) (u : Fin 3 → K) (lam : K) :
    (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
  lam • LinearMap.id + ((lam⁻¹ ^ 2 - lam) / stdHermForm hu 3 u u) •
    (stdHermForm hu 3 u).smulRight u

private theorem zLin_apply (hu : UnitaryFieldData 2 n K) (u v : Fin 3 → K) (lam : K) :
    zLin hu u lam v = lam • v +
      (((lam⁻¹ ^ 2 - lam) * stdHermForm hu 3 u v / stdHermForm hu 3 u u) • u) := by
  simp only [zLin, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, smul_eq_mul]
  rw [smul_smul]
  congr 1
  ring

private theorem zLin_self (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) (lam : K) :
    zLin hu u lam u = (lam⁻¹ ^ 2) • u := by
  rw [zLin_apply]
  have h1 : (lam⁻¹ ^ 2 - lam) * stdHermForm hu 3 u u / stdHermForm hu 3 u u =
      lam⁻¹ ^ 2 - lam := by field_simp
  rw [h1, sub_smul, sub_eq_add_neg]
  abel

private theorem zLin_perp (hu : UnitaryFieldData 2 n K) {u w : Fin 3 → K} (lam : K)
    (hw : stdHermForm hu 3 u w = 0) : zLin hu u lam w = lam • w := by
  rw [zLin_apply, hw, mul_zero, zero_div, zero_smul, add_zero]

private theorem zLin_isometry (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) {lam : K} (hlam : hu.norm lam = 1) (x y : Fin 3 → K) :
    stdHermForm hu 3 (zLin hu u lam x) (zLin hu u lam y) = stdHermForm hu 3 x y := by
  have hnorm : lam * hu.bar lam = 1 := by simpa [UnitaryFieldData.norm] using hlam
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hnorm
    exact zero_ne_one hnorm
  have hbar : hu.bar lam = lam⁻¹ := by
    exact mul_left_cancel₀ hlam0 (by rw [hnorm, mul_inv_cancel₀ hlam0])
  have hbar2 : hu.bar (lam⁻¹ ^ 2) = lam ^ 2 := by
    rw [map_pow, map_inv₀, hbar, inv_inv]
  set d := stdHermForm hu 3 u u with hddef
  set cx := stdHermForm hu 3 u x / d with hcxdef
  set cy := stdHermForm hu 3 u y / d with hcydef
  set x0 := x - cx • u with hx0def
  set y0 := y - cy • u with hy0def
  have hx0 : stdHermForm hu 3 u x0 = 0 := by
    rw [hx0def, map_sub, map_smul, smul_eq_mul, hcxdef, div_mul_cancel₀ _ hd]
    abel
  have hy0 : stdHermForm hu 3 u y0 = 0 := by
    rw [hy0def, map_sub, map_smul, smul_eq_mul, hcydef, div_mul_cancel₀ _ hd]
    abel
  have hxdecomp : x = x0 + cx • u := by rw [hx0def]; abel
  have hydecomp : y = y0 + cy • u := by rw [hy0def]; abel
  have hzx : zLin hu u lam x = lam • x0 + (cx * lam⁻¹ ^ 2) • u := by
    rw [hxdecomp, map_add, map_smul, zLin_perp hu lam hx0, zLin_self hu hd lam,
      smul_smul, mul_comm cx (lam⁻¹ ^ 2)]
  have hzy : zLin hu u lam y = lam • y0 + (cy * lam⁻¹ ^ 2) • u := by
    rw [hydecomp, map_add, map_smul, zLin_perp hu lam hy0, zLin_self hu hd lam,
      smul_smul, mul_comm cy (lam⁻¹ ^ 2)]
  rw [hzx, hzy, hxdecomp, hydecomp]
  have hx0u : stdHermForm hu 3 x0 u = 0 := ((stdHermForm_isSymm hu 3).eq_iff).mpr hx0
  have hy0u : stdHermForm hu 3 y0 u = 0 := ((stdHermForm_isSymm hu 3).eq_iff).mpr hy0
  simp only [map_add, map_mul, map_pow, map_inv₀, map_smulₛₗ, LinearMap.add_apply,
    LinearMap.smul_apply, map_smul, smul_eq_mul, hx0, hy0, hx0u, hy0u, hbar, hbar2,
    RingHom.id_apply]
  field_simp [hd, hlam0]
  ring

private theorem toMatrix'_zLin (hu : UnitaryFieldData 2 n K) (u : Fin 3 → K) (lam : K) :
    LinearMap.toMatrix' (zLin hu u lam) =
      lam • (1 : Matrix (Fin 3) (Fin 3) K) +
        (((lam⁻¹ ^ 2 - lam) / stdHermForm hu 3 u u) •
          Matrix.vecMulVec u (fun j => hu.bar (u j))) := by
  ext i j
  rw [LinearMap.toMatrix'_apply, zLin_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.vecMulVec_apply, stdHermForm_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  field_simp
  try ring

private theorem det_zLin (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) {lam : K} (hlam : hu.norm lam = 1) :
    LinearMap.det (zLin hu u lam) = 1 := by
  have hbar : hu.bar lam = lam⁻¹ := by
    have hnorm : lam * hu.bar lam = 1 := by simpa [UnitaryFieldData.norm] using hlam
    have hlam0 : lam ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hnorm
      exact zero_ne_one hnorm
    exact mul_left_cancel₀ hlam0 (by rw [hnorm, mul_inv_cancel₀ hlam0])
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hnorm : lam * hu.bar lam = 1 := by simpa [UnitaryFieldData.norm] using hlam
    rw [h0, zero_mul] at hnorm
    exact zero_ne_one hnorm
  rw [← LinearMap.det_toMatrix', toMatrix'_zLin]
  set d := stdHermForm hu 3 u u with hddef
  set c := (lam⁻¹ ^ 2 - lam) / d with hcdef
  have hfac : lam • (1 : Matrix (Fin 3) (Fin 3) K) +
      c • Matrix.vecMulVec u (fun j => hu.bar (u j)) =
      lam • (1 + (c / lam) • Matrix.vecMulVec u (fun j => hu.bar (u j))) := by
    rw [smul_add, smul_smul]
    congr 1
    field_simp
  rw [hfac, Matrix.det_smul]
  have hdet : (1 + (c / lam) • Matrix.vecMulVec u (fun j => hu.bar (u j))).det =
      1 + (c / lam) * d := by
    rw [CFSG.RankThree.PartTwo.Sec14.Item148Res8.det_one_add_smul_vecMulVec, hddef,
      stdHermForm_apply]
    simp [dotProduct]
  rw [hdet]
  simp only [Fintype.card_fin]
  rw [hcdef]
  field_simp [hd, hlam0]
  ring_nf

private theorem zLin_one (hu : UnitaryFieldData 2 n K) (u : Fin 3 → K) :
    zLin hu u 1 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [zLin_apply]
  simp

private theorem zLin_mul (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) {lam mu : K} (hlam : hu.norm lam = 1)
    (hmu : hu.norm mu = 1) :
    zLin hu u (lam * mu) = zLin hu u lam * zLin hu u mu := by
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0] at hlam
    simpa [UnitaryFieldData.norm] using hlam
  have hmu0 : mu ≠ 0 := by
    intro h0
    rw [h0] at hmu
    simpa [UnitaryFieldData.norm] using hmu
  have hMn : ∀ m ∈ Submodule.span K {u},
      (∀ n ∈ Submodule.span K {u}, stdHermForm hu 3 n m = 0) → m = 0 := by
    intro m hm h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
    have h' := h u (Submodule.mem_span_singleton_self u)
    rw [map_smul, smul_eq_mul] at h'
    rw [(mul_eq_zero.mp h').resolve_right hd, zero_smul]
  have hcompl := CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep
    (B := stdHermForm hu 3) hMn
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ (Submodule.span K {u}) ⊔
      ((Submodule.span K {u}).orthogonalBilin (stdHermForm hu 3)) := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hv
  rw [← hxy]
  change zLin hu u (lam * mu) (x + y) = zLin hu u lam (zLin hu u mu (x + y))
  rw [map_add, map_add, map_add]
  congr 1
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [map_smul, zLin_self hu hd, smul_smul]
    field_simp
  · have hy0 : stdHermForm hu 3 u y = 0 :=
      (Submodule.mem_orthogonalBilin.mp hy) u (Submodule.mem_span_singleton_self u)
    rw [zLin_perp hu mu hy0, map_smul, zLin_perp hu lam hy0,
      zLin_perp hu (lam * mu) hy0, smul_smul, mul_comm]

private noncomputable def zSU (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) {lam : K} (hlam : hu.norm lam = 1) :
    unitarySU 2 n K 3 :=
  have hdet : (LinearMap.toMatrix' (zLin hu u lam)).det = 1 := by
    rw [LinearMap.det_toMatrix', det_zLin hu hd hlam]
  ⟨GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix' (zLin hu u lam))
      (by rw [hdet]; exact one_ne_zero), by
    refine (mem_unitarySU_iff_isometry hu).mpr ⟨hdet, fun x y => ?_⟩
    have hx : ((GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix' (zLin hu u lam))
        (by rw [hdet]; exact one_ne_zero) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ x = zLin hu u lam x := by
      rw [← LinearMap.toMatrix'_mulVec]
      rfl
    have hy : ((GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix' (zLin hu u lam))
        (by rw [hdet]; exact one_ne_zero) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ y = zLin hu u lam y := by
      rw [← LinearMap.toMatrix'_mulVec]
      rfl
    rw [hx, hy]
    exact zLin_isometry hu hd hlam x y⟩

private theorem zSU_mulVec (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) {lam : K} (hlam : hu.norm lam = 1) (v : Fin 3 → K) :
    (((zSU hu hd hlam : unitarySU 2 n K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = zLin hu u lam v := by
  rw [← LinearMap.toMatrix'_mulVec]
  rfl

private theorem zSU_one (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) (h1 : hu.norm (1 : K) = 1) :
    zSU hu hd h1 = 1 := by
  apply unitarySU_ext_mulVecLin
  refine LinearMap.ext fun v => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, zSU_mulVec, zLin_one]
  simp

private theorem zSU_mul (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) {lam mu : K} (hlam : hu.norm lam = 1)
    (hmu : hu.norm mu = 1) (hmu' : hu.norm (lam * mu) = 1) :
    zSU hu hd hmu' = zSU hu hd hlam * zSU hu hd hmu := by
  apply unitarySU_ext_mulVecLin
  refine LinearMap.ext fun v => ?_
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul, LinearMap.comp_apply,
    Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  rw [zSU_mulVec (hu := hu) (hd := hd) (hlam := hmu),
    zSU_mulVec (hu := hu) (hd := hd) (hlam := hlam),
    zSU_mulVec (hu := hu) (hd := hd) (hlam := hmu')]
  change zLin hu u (lam * mu) v = (zLin hu u lam * zLin hu u mu) v
  rw [zLin_mul hu hd hlam hmu]

private theorem zSU_cube_of_mem_scalars (hu : UnitaryFieldData 2 n K) {u a : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) (ha0 : a ≠ 0) (hau : stdHermForm hu 3 u a = 0)
    {lam : K} (hlam : hu.norm lam = 1)
    (hsc : zSU hu hd hlam ∈ unitaryScalars hu 3) : lam ^ 3 = 1 := by
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0] at hlam
    simpa [UnitaryFieldData.norm] using hlam
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp at hd
  obtain ⟨c, _, _, hcoe⟩ := mem_unitaryScalars.mp hsc
  have h1 : c • u = lam⁻¹ ^ 2 • u := by
    have h := zSU_mulVec hu hd hlam u
    rw [hcoe, GeneralLinearGroup.coe_scalar] at h
    change (Matrix.diagonal (fun _ : Fin 3 => (c : K))) *ᵥ u = zLin hu u lam u at h
    rw [Matrix.diagonal_const_mulVec, zLin_self hu hd] at h
    exact h
  have hc1 : c = lam⁻¹ ^ 2 := smul_left_injective (R := K) (m := u) hu0 h1
  have h2 : c • a = lam • a := by
    have h := zSU_mulVec hu hd hlam a
    rw [hcoe, GeneralLinearGroup.coe_scalar] at h
    change (Matrix.diagonal (fun _ : Fin 3 => (c : K))) *ᵥ a =
      zLin hu u lam a at h
    rw [Matrix.diagonal_const_mulVec, zLin_perp hu lam hau] at h
    exact h
  have hc2 : c = lam := smul_left_injective (R := K) (m := a) ha0 h2
  have h : lam⁻¹ ^ 2 = lam := hc1.symm.trans hc2
  field_simp [hlam0] at h
  simpa [eq_comm] using h

private theorem zLin_conj_apply (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) (A : unitaryIsom3 hu) {β : K}
    (huβ : (A : GL (Fin 3) K) • u = β • u) (hβ : hu.norm β = 1) (lam : K)
    (v : Fin 3 → K) :
    (A : GL (Fin 3) K) • zLin hu u lam ((A : GL (Fin 3) K)⁻¹ • v) =
      zLin hu u lam v := by
  have hβbar : hu.bar β * β = 1 := by
    have h : β * hu.bar β = 1 := by simpa [UnitaryFieldData.norm] using hβ
    simpa [mul_comm] using h
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0] at hβbar
    simp at hβbar
  have hbarβ : hu.bar β = β⁻¹ := by
    exact mul_right_cancel₀ hβ0 (by rw [hβbar, inv_mul_cancel₀ hβ0])
  have hiso := isometry_of_mem_unitaryIsom3 hu A u ((A : GL (Fin 3) K)⁻¹ • v)
  rw [huβ, smul_inv_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at hiso
  rw [zLin_apply, zLin_apply, smul_add]
  rw [smul_comm (A : GL (Fin 3) K) lam ((A : GL (Fin 3) K)⁻¹ • v),
    smul_inv_smul]
  rw [smul_comm (A : GL (Fin 3) K)
    (((lam⁻¹ ^ 2 - lam) * stdHermForm hu 3 u ((A : GL (Fin 3) K)⁻¹ • v) /
      stdHermForm hu 3 u u)) u, huβ, smul_smul, ← hiso]
  congr 1
  rw [hbarβ]
  field_simp [hd, hβ0]

private theorem zSU_conj (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) (A : unitaryIsom3 hu) {β : K}
    (huβ : (A : GL (Fin 3) K) • u = β • u) (hβ : hu.norm β = 1) {lam : K}
    (hlam : hu.norm lam = 1) :
    suConj hu A (zSU hu hd hlam) = zSU hu hd hlam := by
  apply unitarySU_ext_mulVecLin
  refine LinearMap.ext fun v => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
  change (((suConj hu A (zSU hu hd hlam) : unitarySU 2 n K 3) : GL (Fin 3) K) • v) =
    ((zSU hu hd hlam : unitarySU 2 n K 3) : GL (Fin 3) K) • v
  rw [coe_suConj, mul_smul, mul_smul]
  change (A : GL (Fin 3) K) • (((zSU hu hd hlam : unitarySU 2 n K 3) : GL (Fin 3) K) •
    ((A : GL (Fin 3) K)⁻¹ • v)) =
      ((zSU hu hd hlam : unitarySU 2 n K 3) : GL (Fin 3) K) • v
  rw [show ((zSU hu hd hlam : unitarySU 2 n K 3) : GL (Fin 3) K) •
      ((A : GL (Fin 3) K)⁻¹ • v) = zLin hu u lam ((A : GL (Fin 3) K)⁻¹ • v) from
    zSU_mulVec hu hd hlam _, zLin_conj_apply hu hd A huβ hβ lam v]
  change zLin hu u lam v = (((zSU hu hd hlam : unitarySU 2 n K 3) : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ v
  rw [zSU_mulVec hu hd hlam v]

private theorem zSU_pow (hu : UnitaryFieldData 2 n K) {u : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) {lam : K} (hlam : hu.norm lam = 1) :
    ∀ k (hk : hu.norm (lam ^ k) = 1),
      zSU hu hd hk = (zSU hu hd hlam) ^ k := by
  intro k
  induction k with
  | zero =>
    intro hk
    simpa using zSU_one hu hd (by simpa using hk)
  | succ k ih =>
    intro hk
    have hp : lam ^ (k + 1) = lam ^ k * lam := by rw [← pow_succ]
    have hk' : hu.norm (lam ^ k) = 1 := by
      have h := hk
      rw [hp, norm_mul_eq hu, hlam, mul_one] at h
      exact h
    have hstep : hu.norm (lam ^ k * lam) = 1 := hp ▸ hk
    have hpow : (zSU hu hd hlam) ^ (k + 1) =
        (zSU hu hd hlam) ^ k * zSU hu hd hlam := by rw [pow_succ]
    rw [hpow, ← ih hk']
    convert zSU_mul hu hd hk' hlam hstep using 2

private theorem exists_lambda_order_norm (hu : UnitaryFieldData 2 n K) {r : ℕ}
    (hr : r.Prime) (hrd : r ∣ 2 ^ n + 1) :
    ∃ lam : Kˣ, orderOf lam = r ∧ hu.norm (lam : K) = 1 := by
  classical
  haveI : Finite K := hu.finite
  haveI : Fact r.Prime := ⟨hr⟩
  have hcard : Nat.card Kˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_units, hu.card_eq_sq]
    simpa using Nat.sq_sub_sq (2 ^ n) 1
  have hdiv : r ∣ Nat.card Kˣ := by
    rw [hcard]
    exact dvd_mul_of_dvd_left hrd _
  obtain ⟨lam, hlam_ord⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r hdiv
  have hlam_pow : (lam : K) ^ (2 ^ n + 1) = 1 := by
    have h : lam ^ (2 ^ n + 1) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp (by rw [hlam_ord]; exact hrd)
    exact congrArg (fun x : Kˣ => (x : K)) h
  refine ⟨lam, hlam_ord, ?_⟩
  rw [hu.norm_eq_pow]
  exact hlam_pow

private theorem orderOf_proj_zSU (hu : UnitaryFieldData 2 n K) {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) {u a : Fin 3 → K}
    (hd : stdHermForm hu 3 u u ≠ 0) (ha0 : a ≠ 0)
    (hau : stdHermForm hu 3 u a = 0) {lam : Kˣ}
    (hlam_ord : orderOf lam = r) (hnorm : hu.norm (lam : K) = 1) :
    orderOf (unitaryProj hu 3 (zSU hu hd hnorm)) = r := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hlamr : (lam : K) ^ r = 1 := by
    have h : lam ^ r = 1 := by rw [← hlam_ord]; exact pow_orderOf_eq_one lam
    exact congrArg (fun x : Kˣ => (x : K)) h
  have h1norm : hu.norm (1 : K) = 1 := by simp [UnitaryFieldData.norm]
  have hnormr : hu.norm ((lam : K) ^ r) = 1 := by
    rw [hlamr]
    exact h1norm
  have hzeta : zSU hu hd hnormr = 1 := by
    convert zSU_one hu hd h1norm using 2
  have hzr : (unitaryProj hu 3 (zSU hu hd hnorm)) ^ r = 1 := by
    have hpow : (zSU hu hd hnorm) ^ r = 1 := by
      have h := zSU_pow hu hd hnorm r hnormr
      rw [hzeta] at h
      exact h.symm
    rw [← map_pow, hpow, map_one]
  have hlam3 : (lam : K) ^ 3 ≠ 1 := by
    intro h3
    have h3u : lam ^ 3 = 1 := by ext; simpa using h3
    have hdvd3 : orderOf lam ∣ 3 := (orderOf_dvd_iff_pow_eq_one).mpr h3u
    rw [hlam_ord] at hdvd3
    have hle : r ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd3
    omega
  have hz1 : unitaryProj hu 3 (zSU hu hd hnorm) ≠ 1 := by
    intro hz
    have hker : zSU hu hd hnorm ∈ (unitaryProj hu 3).ker := by
      rw [MonoidHom.mem_ker]
      exact hz
    rw [ker_unitaryProj] at hker
    exact hlam3 (zSU_cube_of_mem_scalars hu hd ha0 hau hnorm hker)
  exact orderOf_eq_prime hzr hz1

theorem exists_orderOf_eq_fixed_of_psuConj {n : ℕ} {K : Type} [Field K]
    (hu : UnitaryFieldData 2 n K) (hn : 2 ≤ n) (A : unitaryIsom3 hu)
    (hodd : Odd (orderOf (psuConj hu A)))
    (S : Sylow 2 (unitaryPSU hu 3))
    (hS : ∀ x ∈ (S : Subgroup (unitaryPSU hu 3)),
      psuConj hu A x ∈ (S : Subgroup (unitaryPSU hu 3)))
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hrd : r ∣ 2 ^ n + 1) :
    ∃ z : unitaryPSU hu 3, orderOf z = r ∧ psuConj hu A z = z := by
  obtain ⟨L, hL, hfix⟩ := smul_eq_of_normalizes_sylow hu hn A S hS
  obtain ⟨a, u, ha0, hu0, ha_iso, hun, hau, β, huβ, hβ⟩ :=
    exists_anisotropic_eigenvector hu (by omega) A L hL hfix hodd
  obtain ⟨lam, hlam_ord, hnorm⟩ := exists_lambda_order_norm hu hr hrd
  let z : unitaryPSU hu 3 := unitaryProj hu 3 (zSU hu hun hnorm)
  have horder : orderOf z = r :=
    orderOf_proj_zSU hu hr hr3 hun ha0 hau hlam_ord hnorm
  have hfixz : psuConj hu A z = z := by
    change psuConj hu A (zSU hu hun hnorm : unitaryPSU hu 3) =
      (zSU hu hun hnorm : unitaryPSU hu 3)
    rw [psuConj_mk, zSU_conj hu hun A huβ hβ hnorm]
  exact ⟨z, horder, hfixz⟩

end CFSG.RankThree.PartTwo.KFacts
