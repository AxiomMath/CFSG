module

public import CFSG.RankThree.PartOne.KFOUT3.CycUnits
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Polynomial Matrix

variable {K : Type} [Field K]

@[expose] noncomputable def qHom (m : Matrix (Fin 3) (Fin 3) K) (hm : m ^ 3 = 1) :
    Qring K →ₐ[K] Matrix (Fin 3) (Fin 3) K :=
  Ideal.Quotient.liftₐ (Ideal.span {(X ^ 3 - 1 : K[X])}) (Polynomial.aeval m) (by
    intro f hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.1 hf
    simp [hm])

theorem qHom_mk (m : Matrix (Fin 3) (Fin 3) K) (hm : m ^ 3 = 1) (f : K[X]) :
    qHom m hm (AdjoinRoot.mk _ f) = Polynomial.aeval m f := rfl

theorem qHom_injective {m : Matrix (Fin 3) (Fin 3) K} (hm : m ^ 3 = 1) {e : Fin 3 → K}
    (he : IsUnit (krylov m e).det) : Function.Injective (qHom m hm) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective q
  rw [qHom_mk] at hq
  have hdeg3 : (X ^ 3 - 1 : K[X]).natDegree = 3 := by compute_degree!
  have hmonic : (X ^ 3 - 1 : K[X]).Monic := by monicity!
  have hne1 : (X ^ 3 - 1 : K[X]) ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [hdeg3, natDegree_one] at this
    omega
  have hmd := modByMonic_add_div f (X ^ 3 - 1 : K[X])
  have hdeg : (f %ₘ (X ^ 3 - 1 : K[X])).natDegree < 3 := by
    have h1 := natDegree_modByMonic_lt f hmonic hne1
    rwa [hdeg3] at h1
  set r := f %ₘ (X ^ 3 - 1 : K[X]) with hr
  set d := f /ₘ (X ^ 3 - 1 : K[X]) with hd
  have hfr : AdjoinRoot.mk (X ^ 3 - 1 : K[X]) f = AdjoinRoot.mk (X ^ 3 - 1 : K[X]) r := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨d, by linear_combination (-1 : K[X]) * hmd⟩
  have hrm : Polynomial.aeval m r = 0 := by
    have h1 : Polynomial.aeval m f = Polynomial.aeval m r +
        Polynomial.aeval m ((X ^ 3 - 1 : K[X]) * d) := by
      rw [← map_add, hmd]
    rw [hq] at h1
    have h2 : Polynomial.aeval m ((X ^ 3 - 1 : K[X]) * d) = 0 := by
      rw [map_mul]
      simp [hm]
    rw [h2, add_zero] at h1
    exact h1.symm
  have hrpol : Polynomial.aeval m r = pol m (fun i => r.coeff i) := by
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)]
    simp [pol, Finset.sum_range_succ, pow_succ]
  rw [hrpol] at hrm
  have hcoef : (fun i : Fin 3 => r.coeff i) = 0 := by
    apply pol_injective he
    rw [hrm]
    simp [pol]
  have hr0 : r = 0 := by
    apply Polynomial.ext
    intro n
    by_cases hn : n < 3
    · have := congrFun hcoef ⟨n, hn⟩
      simpa using this
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  rw [hfr, hr0, map_zero]

theorem exists_qHom_eq {m : Matrix (Fin 3) (Fin 3) K} (hm : m ^ 3 = 1) {e : Fin 3 → K}
    (he : IsUnit (krylov m e).det) {c : Matrix (Fin 3) (Fin 3) K} (hc : c * m = m * c) :
    ∃ q, qHom m hm q = c := by
  obtain ⟨a, rfl⟩ := eq_pol_of_commute he hc
  refine ⟨AdjoinRoot.mk _ (C (a 0) + C (a 1) * X + C (a 2) * X ^ 2), ?_⟩
  rw [qHom_mk]
  simp [pol, Algebra.smul_def, pow_two]

theorem qHom_commute {m : Matrix (Fin 3) (Fin 3) K} (hm : m ^ 3 = 1) (q : Qring K) :
    qHom m hm q * m = m * qHom m hm q := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective q
  rw [qHom_mk]
  have h := (Commute.all (X : K[X]) f).map
    (Polynomial.aeval m : K[X] →ₐ[K] Matrix (Fin 3) (Fin 3) K)
  rw [Polynomial.aeval_X] at h
  exact h.symm.eq

section Centralizer

variable [CharP K 2] [Finite K]

theorem exists_cyc_threeElts (h3 : ¬ 3 ∣ Nat.card K - 1) {M : GL (Fin 3) K} (hM : M ^ 3 = 1)
    {e : Fin 3 → K} (he : IsUnit (krylov (M : Matrix (Fin 3) (Fin 3) K) e).det) :
    (∀ c d : GL (Fin 3) K, c * M = M * c → d * M = M * d → c * d = d * c) ∧
    ∃ U : Subgroup (GL (Fin 3) K),
      (∀ c : GL (Fin 3) K, c ∈ U ↔ c * M = M * c ∧ ∃ n : ℕ, c ^ (3 ^ n) = 1) ∧ IsCyclic U ∧
        Nat.card U = 3 ^ (Nat.card K ^ 2 - 1).factorization 3 := by
  have hm : (M : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hM, Units.val_one]
  have hmat : ∀ c : GL (Fin 3) K, c * M = M * c →
      (c : Matrix (Fin 3) (Fin 3) K) * M = M * c := by
    intro c hc
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hc
    simpa using this
  refine ⟨fun c d hc hd => ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact commute_of_commute he (hmat c hc) (hmat d hd)
  · obtain ⟨P, hP, hcyc, hcard⟩ := exists_threeElts_cyclic (K := K) h3
    let Θ : (Qring K)ˣ →* GL (Fin 3) K :=
      Units.map (qHom (M : Matrix (Fin 3) (Fin 3) K) hm).toRingHom.toMonoidHom
    have hΘ : Function.Injective Θ := Units.map_injective (qHom_injective hm he)
    have hΘcomm : ∀ u : (Qring K)ˣ, Θ u * M = M * Θ u := fun u => Units.ext (qHom_commute hm u)
    have hΘval : ∀ u : (Qring K)ˣ, ((Θ u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        qHom (M : Matrix (Fin 3) (Fin 3) K) hm u := fun u => rfl
    have hequiv := Subgroup.equivMapOfInjective P Θ hΘ
    refine ⟨P.map Θ, fun c => ⟨?_, ?_⟩, ?_, ?_⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨n, hn⟩ := (hP u).1 hu
      exact ⟨hΘcomm u, n, by rw [← map_pow, hn, map_one]⟩
    · rintro ⟨hc, n, hn⟩
      have hc' : c⁻¹ * M = M * c⁻¹ := by
        calc c⁻¹ * M = c⁻¹ * (M * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * M) * c⁻¹ := by rw [hc]
          _ = M * c⁻¹ := by group
      obtain ⟨q₁, hq₁⟩ := exists_qHom_eq hm he (hmat c hc)
      obtain ⟨q₂, hq₂⟩ := exists_qHom_eq hm he (hmat c⁻¹ hc')
      have h12 : q₁ * q₂ = 1 := by
        apply qHom_injective hm he
        rw [map_mul, hq₁, hq₂, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have h21 : q₂ * q₁ = 1 := by
        apply qHom_injective hm he
        rw [map_mul, hq₁, hq₂, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      let u : (Qring K)ˣ := ⟨q₁, q₂, h12, h21⟩
      have hu : Θ u = c := Units.ext hq₁
      have hun : u ^ (3 ^ n) = 1 := by
        apply hΘ
        rw [map_pow, hu, hn, map_one]
      exact ⟨u, (hP u).2 ⟨n, hun⟩, hu⟩
    · exact isCyclic_of_surjective hequiv hequiv.surjective
    · rw [← Nat.card_congr hequiv.toEquiv, hcard]

end Centralizer

end CFSG.RankThree.PartOne.KFOUT3
