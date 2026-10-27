module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAdjoint

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary

section Pairing

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

omit [FiniteDimensional K V] in
theorem injective_unit (u : LinearMap.GeneralLinearGroup K V) :
    Function.Injective (u : Module.End K V) := ((Module.End.isUnit_iff _).mp u.isUnit).1

theorem coeff_zero_ne_zero_of_mem_primaryFactors
    (hsq : Squarefree (minpoly K (x : Module.End K V))) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) : a.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := X_dvd_iff.mpr h0
  have hirr := irreducible_of_mem_primaryFactors ha
  have hq' : IsUnit q := by
    rcases hirr.isUnit_or_isUnit (show a = X * q from hq) with h | h
    · exact absurd h not_isUnit_X
    · exact h
  obtain ⟨r, hr, hrq⟩ := Polynomial.isUnit_iff.mp hq'
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq ha)
  apply hv0
  have h1 : aeval (x : Module.End K V) a v = 0 := mem_primaryComponent.mp hv
  rw [hq, ← hrq, map_mul, aeval_X, aeval_C, Module.End.mul_apply] at h1
  have h2 : (x : Module.End K V) (r • v) = 0 := by
    have : (algebraMap K (Module.End K V) r) v = r • v := rfl
    rw [← this]; exact h1
  have h3 : r • v = 0 := injective_unit x (h2.trans (map_zero _).symm)
  exact (smul_eq_zero.mp h3).resolve_left (isUnit_iff_ne_zero.mp hr)


structure UnitaryPrimaryData (σ : K →+* K) (B : V →ₛₗ[σ] V →ₗ[K] K)
    (x : LinearMap.GeneralLinearGroup K V) : Prop where
  invol : Function.Involutive σ
  symm : B.IsSymm
  sep : B.SeparatingLeft
  isom : x ∈ sesqUnitaryGroup B
  squarefree : Squarefree (minpoly K (x : Module.End K V))

variable (H : UnitaryPrimaryData σ B x)
include H

theorem orthogonal_of_ne_dualPoly {a b : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hb : b ∈ primaryFactors (x : Module.End K V)) (hab : b ≠ dualPoly σ a) {v w : V}
    (hv : v ∈ primaryComponent (x : Module.End K V) a)
    (hw : w ∈ primaryComponent (x : Module.End K V) b) : B v w = 0 := by
  classical
  have hσ := H.invol
  have hB := H.symm
  have hBl := H.sep
  have hx := H.isom
  have hsq := H.squarefree
  set X : Module.End K V := (x : Module.End K V) with hXdef
  set Y : Module.End K V := ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) with hYdef
  have hXY : X * Y = 1 := by rw [hXdef, hYdef, ← Units.val_mul, mul_inv_cancel]; rfl
  have hYX : Y * X = 1 := by rw [hXdef, hYdef, ← Units.val_mul, inv_mul_cancel]; rfl
  have hcomm : Commute Y X := by
    rw [Commute, SemiconjBy, hYX, hXY]
  set N := a.natDegree with hN
  have hYNXN : Y ^ N * X ^ N = 1 := by rw [← hcomm.mul_pow, hYX, one_pow]
  have ha0 := coeff_zero_ne_zero_of_mem_primaryFactors hsq ha
  have hdirr : Irreducible (dualPoly σ a) :=
    irreducible_dualPoly hσ (irreducible_of_mem_primaryFactors ha) ha0
  have hdmonic : (dualPoly σ a).Monic := monic_dualPoly ha0
  have hnd : ¬ b ∣ dualPoly σ a := fun hd => hab (eq_of_monic_of_associated
    (monic_of_mem_primaryFactors hb) hdmonic
    ((irreducible_of_mem_primaryFactors hb).associated_of_dvd hdirr hd))
  obtain ⟨u, s, hus⟩ := (irreducible_of_mem_primaryFactors hb).coprime_iff_not_dvd.mpr hnd
  set c : K := (σ (a.coeff 0))⁻¹ with hcdef
  have hc : c ≠ 0 := inv_ne_zero ((map_ne_zero σ).mpr ha0)
  set T := hermAdjoint hB hBl (aeval X a) with hT
  have hD : aeval X (dualPoly σ a) = c • (X ^ N * T) := aeval_dualPoly hB hBl hx a
  have hT' : T = c⁻¹ • (Y ^ N * aeval X (dualPoly σ a)) := by
    rw [hD, mul_smul_comm, ← mul_assoc, hYNXN, one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  set w₀ : V := aeval X s (c • (X ^ N) w) with hw₀
  have hbw : aeval X b w = 0 := mem_primaryComponent.mp hw
  have hbX : aeval X b ((X ^ N) w) = 0 := by
    have := (commute_aeval ((Commute.refl X).pow_left N) b).eq
    have h2 := congrArg (fun T : Module.End K V => T w) this
    simp only [Module.End.mul_apply, hbw, map_zero] at h2
    exact h2.symm
  have hDw₀ : aeval X (dualPoly σ a) w₀ = c • (X ^ N) w := by
    have h1 : aeval X (dualPoly σ a * s) = 1 - aeval X u * aeval X b := by
      rw [← map_mul, show dualPoly σ a * s = 1 - u * b by linear_combination hus, map_sub, map_mul,
        map_one]
    have h2 : aeval X (dualPoly σ a) w₀ = aeval X (dualPoly σ a * s) (c • (X ^ N) w) := by
      rw [map_mul, Module.End.mul_apply]
    rw [h2, h1, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, map_smul, hbX,
      smul_zero, map_zero, sub_zero]
  have hTw₀ : T w₀ = w := by
    rw [hT', LinearMap.smul_apply, Module.End.mul_apply, hDw₀, map_smul]
    have : (Y ^ N) ((X ^ N) w) = w := by
      rw [← Module.End.mul_apply, hYNXN]; rfl
    rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h3 := hermAdjoint_spec hB hBl (aeval X a) v w₀
  rw [mem_primaryComponent.mp hv, map_zero, ← hT, hTw₀] at h3
  exact h3.symm



omit H in
theorem eq_sum_primaryProjection (hsq : Squarefree (minpoly K (x : Module.End K V))) (w : V) :
    w = ∑ b ∈ primaryFactors (x : Module.End K V), primaryProjection (x : Module.End K V) b w := by
  have := LinearMap.congr_fun (sum_primaryProjection hsq) w
  rw [LinearMap.sum_apply] at this
  simpa using this.symm

theorem dualPoly_mem_primaryFactors {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    dualPoly σ a ∈ primaryFactors (x : Module.End K V) := by
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot H.squarefree ha)
  obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
    by_contra! h
    exact hv0 (H.sep v h)
  by_contra hnot
  apply hw
  rw [eq_sum_primaryProjection H.squarefree w, map_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  refine orthogonal_of_ne_dualPoly H ha hb (fun h => hnot (h ▸ hb)) hv ?_
  exact primaryProjection_mem H.squarefree hb w

theorem dualPoly_dualPoly_of_mem {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    dualPoly σ (dualPoly σ a) = a :=
  dualPoly_dualPoly H.invol (monic_of_mem_primaryFactors ha)
    (coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha)

theorem dualPoly_injOn :
    Set.InjOn (dualPoly σ) (primaryFactors (x : Module.End K V) : Set K[X]) := fun a ha b hb h => by
  rw [← dualPoly_dualPoly_of_mem H ha, h, dualPoly_dualPoly_of_mem H hb]


@[expose] noncomputable def UnitaryPrimaryData.adj (r : Module.End K V) : Module.End K V :=
  hermAdjoint H.symm H.sep r

theorem UnitaryPrimaryData.adj_spec (r : Module.End K V) (v w : V) :
    B (r v) w = B v (H.adj r w) := hermAdjoint_spec H.symm H.sep r v w

theorem B_eq_sum (v w : V) :
    B v w = ∑ b ∈ primaryFactors (x : Module.End K V),
      B (primaryProjection (x : Module.End K V) b v)
        (primaryProjection (x : Module.End K V) (dualPoly σ b) w) := by
  classical
  have hsq := H.squarefree
  have h1 : B v w = ∑ b ∈ primaryFactors (x : Module.End K V),
      B (primaryProjection (x : Module.End K V) b v) w := by
    conv_lhs => rw [eq_sum_primaryProjection hsq v]
    rw [map_sum, LinearMap.sum_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun b hb => ?_
  conv_lhs => rw [eq_sum_primaryProjection hsq w]
  rw [map_sum, Finset.sum_eq_single (dualPoly σ b)]
  · intro c hc hcb
    exact orthogonal_of_ne_dualPoly H hb hc hcb (primaryProjection_mem hsq hb v)
      (primaryProjection_mem hsq hc w)
  · intro h
    exact absurd (dualPoly_mem_primaryFactors H hb) h


theorem eq_zero_of_perfect_right {a b : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hb : b ∈ primaryFactors (x : Module.End K V)) (hba : b = dualPoly σ a) {w : V}
    (hw : w ∈ primaryComponent (x : Module.End K V) b)
    (h : ∀ v ∈ primaryComponent (x : Module.End K V) a, B v w = 0) : w = 0 := by
  classical
  have hsq := H.squarefree
  refine eq_zero_of_forall_left H.symm H.sep fun v => ?_
  rw [B_eq_sum H v w, Finset.sum_eq_single a]
  · rw [← hba, primaryProjection_of_mem hsq hb hw]
    exact h _ (primaryProjection_mem hsq ha v)
  · intro c hc hca
    have hne : b ≠ dualPoly σ c := fun hbc => hca (dualPoly_injOn H hc ha
      (by rw [← hbc, hba]))
    rw [primaryProjection_of_mem_ne hsq (dualPoly_mem_primaryFactors H hc) hb hne hw, map_zero]
  · intro h'
    exact absurd ha h'

theorem eq_zero_of_perfect_left {a b : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hb : b ∈ primaryFactors (x : Module.End K V)) (hba : b = dualPoly σ a) {v : V}
    (hv : v ∈ primaryComponent (x : Module.End K V) a)
    (h : ∀ w ∈ primaryComponent (x : Module.End K V) b, B v w = 0) : v = 0 := by
  refine eq_zero_of_perfect_right H hb ha ?_ hv fun u hu => (H.symm.eq_iff).mp (h u hu)
  rw [hba, dualPoly_dualPoly_of_mem H ha]

omit H in
theorem finrank_le_of_forall_eq_zero {P Q : Submodule K V}
    (hperf : ∀ w ∈ Q, (∀ v ∈ P, B v w = 0) → w = 0) :
    Module.finrank K Q ≤ Module.finrank K P := by
  classical
  let e := Module.finBasis K P
  let Φ : Q →ₗ[K] (Fin (Module.finrank K P) → K) :=
    LinearMap.pi fun i => (B (e i : V)).comp Q.subtype
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hi : ∀ i, B (e i : V) (w : V) = 0 := fun i => congrFun hw i
    refine Subtype.ext (hperf w w.2 fun v hv => ?_)
    have hv' : v = ∑ i, e.repr ⟨v, hv⟩ i • (e i : V) := by
      have h2 := congrArg (fun p : P => (p : V)) (e.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact h2.symm
    rw [hv', map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, hi i, smul_zero]
  have := LinearMap.finrank_le_finrank_of_injective hΦ
  simpa using this

theorem finrank_primaryComponent_dualPoly {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) :
    Module.finrank K (primaryComponent (x : Module.End K V) (dualPoly σ a)) =
      Module.finrank K (primaryComponent (x : Module.End K V) a) := by
  have hb := dualPoly_mem_primaryFactors H ha
  refine le_antisymm (finrank_le_of_forall_eq_zero (B := B) fun w hw h =>
    eq_zero_of_perfect_right H ha hb rfl hw h)
    (finrank_le_of_forall_eq_zero (B := B) fun w hw h => ?_)
  refine eq_zero_of_perfect_right H hb ha ?_ hw h
  rw [dualPoly_dualPoly_of_mem H ha]

theorem isotropic_primaryComponent {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hne : a ≠ dualPoly σ a) {v w : V} (hv : v ∈ primaryComponent (x : Module.End K V) a)
    (hw : w ∈ primaryComponent (x : Module.End K V) a) : B v w = 0 :=
  orthogonal_of_ne_dualPoly H ha ha hne hv hw


theorem separatingLeft_primaryComponent_sup {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne : a ≠ dualPoly σ a) :
    (B.domRestrict₁₂ (primaryComponent (x : Module.End K V) a ⊔
        primaryComponent (x : Module.End K V) (dualPoly σ a))
      (primaryComponent (x : Module.End K V) a ⊔
        primaryComponent (x : Module.End K V) (dualPoly σ a))).SeparatingLeft := by
  have hb := dualPoly_mem_primaryFactors H ha
  have hne' : dualPoly σ a ≠ dualPoly σ (dualPoly σ a) := by
    rw [dualPoly_dualPoly_of_mem H ha]; exact hne.symm
  intro w hw
  obtain ⟨w₁, hw₁, w₂, hw₂, hsum⟩ := Submodule.mem_sup.mp w.2
  have hzero : ∀ w' ∈ primaryComponent (x : Module.End K V) a ⊔
      primaryComponent (x : Module.End K V) (dualPoly σ a), B (w : V) w' = 0 := fun w' hw' =>
    hw ⟨w', hw'⟩
  have h1 : w₁ = 0 := by
    refine eq_zero_of_perfect_left H ha hb rfl hw₁ fun u hu => ?_
    have := hzero u (Submodule.mem_sup_right hu)
    rw [← hsum, map_add, LinearMap.add_apply,
      isotropic_primaryComponent H hb hne' hw₂ hu, add_zero] at this
    exact this
  have h2 : w₂ = 0 := by
    refine eq_zero_of_perfect_right H ha hb rfl hw₂ fun u hu => ?_
    have := hzero u (Submodule.mem_sup_left hu)
    rw [← hsum, map_add, LinearMap.add_apply, h1, map_zero, LinearMap.zero_apply, zero_add] at this
    exact (H.symm.eq_iff).mp this
  exact Subtype.ext (by rw [← hsum, h1, h2, add_zero]; rfl)

theorem separatingLeft_primaryComponent_selfDual {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (heq : dualPoly σ a = a) :
    (B.domRestrict₁₂ (primaryComponent (x : Module.End K V) a)
      (primaryComponent (x : Module.End K V) a)).SeparatingLeft := by
  intro w hw
  refine Subtype.ext (eq_zero_of_perfect_left H ha ha heq.symm w.2 fun u hu => ?_)
  exact hw ⟨u, hu⟩

theorem adj_primaryProjection {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V)) :
    H.adj (primaryProjection (x : Module.End K V) a) =
      primaryProjection (x : Module.End K V) (dualPoly σ a) := by
  classical
  have hsq := H.squarefree
  have hb := dualPoly_mem_primaryFactors H ha
  symm
  refine hermAdjoint_unique H.symm H.sep fun v w => ?_
  rw [B_eq_sum H (primaryProjection (x : Module.End K V) a v) w, B_eq_sum H v
    (primaryProjection (x : Module.End K V) (dualPoly σ a) w)]
  rw [Finset.sum_eq_single a, Finset.sum_eq_single a]
  · rw [primaryProjection_of_mem hsq ha (primaryProjection_mem hsq ha v),
      primaryProjection_of_mem hsq hb (primaryProjection_mem hsq hb w)]
  · intro c hc hca
    have hne : dualPoly σ a ≠ dualPoly σ c := fun h => hca (dualPoly_injOn H hc ha h.symm)
    rw [primaryProjection_of_mem_ne hsq (dualPoly_mem_primaryFactors H hc) hb hne
      (primaryProjection_mem hsq hb w), map_zero]
  · intro h
    exact absurd ha h
  · intro c hc hca
    rw [primaryProjection_of_mem_ne hsq hc ha hca.symm (primaryProjection_mem hsq ha v),
      map_zero, LinearMap.zero_apply]
  · intro h
    exact absurd ha h

end Pairing

end CFSG.RankThree.PartOne.KCUnitary
