module

public import CFSG.LocalAnalysis.SteinbergCDQuadraticGraphModel

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Matrix

variable {K : Type*} [Field K] [CharP K 2] [Finite K]

theorem exists_semilinear_of_fix {α : QGAut K} (hα : α ∈ qgStab K)
    (ht : Multiplicative.toAdd α (qgT K) = qgT K) :
    ∃ (M : GL (Fin 2) K) (σ : K ≃+* K),
      ∀ v, qgInduced α v = (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set f := Multiplicative.toAdd α with hf
  set L := qgInduced α with hLdef
  have hω : ∀ v, f (qgPoint v) = qgPoint (L v) := fun v => (qgPoint_qgInduced hα v).symm
  set ν : K → K := fun z => (f (0, 0, 0, z)).2.2.2 with hνdef
  have hν : ∀ z, f (0, 0, 0, z) = (0, 0, 0, ν z) := by
    intro z
    obtain ⟨h1, h2', h3⟩ := toAdd_mem_qgZ hα (e := ((0, 0, 0, z) : QGSpace K)) ⟨rfl, rfl, rfl⟩
    exact Prod.ext h1 (Prod.ext h2' (Prod.ext h3 rfl))
  have hνadd : ∀ z z', ν (z + z') = ν z + ν z' := by
    intro z z'
    have e : ((0, 0, 0, z + z') : QGSpace K) = (0, 0, 0, z) + (0, 0, 0, z') := by simp
    have h := map_add f ((0, 0, 0, z) : QGSpace K) (0, 0, 0, z')
    rw [← e, hν, hν, hν] at h
    simpa using congrArg (fun e : QGSpace K => e.2.2.2) h
  have hνinj : ∀ z, ν z = 0 → z = 0 := by
    intro z hz
    have h0 : f (0, 0, 0, z) = 0 := by
      rw [hν, hz]
      rfl
    have h1 := f.injective (h0.trans (map_zero f).symm)
    exact congrArg (fun e : QGSpace K => e.2.2.2) h1
  have hν0 : ν 0 = 0 := by
    have := hνadd 0 0
    rw [add_zero] at this
    linear_combination -this
  have hI : ∀ v w : Fin 2 → K,
      qgPoint v + qgPoint w = qgPoint (v + w) + qgT K + (0, 0, 0, qgPolar v w) := by
    intro v w
    simp only [qgPoint, qgT, qgPolar]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp
    · simp
    · simp
    · simp only [Prod.snd_add, Pi.add_apply]
      linear_combination (-(v 0 * w 1 + w 0 * v 1)) * h2
  have hL : ∀ v w, L (v + w) = L v + L w ∧ qgPolar (L v) (L w) = ν (qgPolar v w) := by
    intro v w
    have e1 := congrArg f (hI v w)
    rw [map_add, map_add, map_add, hω, hω, hω, ht, hν, hI (L v) (L w)] at e1
    have c1 := congrArg (fun e : QGSpace K => e.2.1) e1
    have c2 := congrArg (fun e : QGSpace K => e.2.2.1) e1
    have c3 := congrArg (fun e : QGSpace K => e.2.2.2) e1
    simp only [qgPoint, qgT, Prod.snd_add, Prod.fst_add, add_zero, Pi.add_apply] at c1 c2 c3
    have hadd : L (v + w) = L v + L w := by
      ext i
      fin_cases i
      · show L (v + w) 0 = L v 0 + L w 0
        exact c1.symm
      · show L (v + w) 1 = L v 1 + L w 1
        exact c2.symm
    refine ⟨hadd, ?_⟩
    rw [hadd] at c3
    simp only [Pi.add_apply] at c3
    linear_combination c3
  have hLadd : ∀ v w, L (v + w) = L v + L w := fun v w => (hL v w).1
  have hLpol : ∀ v w, qgPolar (L v) (L w) = ν (qgPolar v w) := fun v w => (hL v w).2
  set p := L ![1, 0] with hp
  set r := L ![0, 1] with hr
  set δ := qgPolar p r with hδdef
  have hδ : δ = ν 1 := by
    rw [hδdef, hp, hr, hLpol]
    simp [qgPolar]
  have hδ0 : δ ≠ 0 := fun h => one_ne_zero (hνinj 1 (by rw [← hδ]; exact h))
  have hcramer : ∀ w : Fin 2 → K, δ • w = qgPolar w r • p + qgPolar p w • r := by
    intro w
    ext i
    fin_cases i
    · show δ * w 0 = qgPolar w r * p 0 + qgPolar p w * r 0
      simp only [hδdef, qgPolar]
      linear_combination (-(p 0 * r 0 * w 1)) * h2
    · show δ * w 1 = qgPolar w r * p 1 + qgPolar p w * r 1
      simp only [hδdef, qgPolar]
      linear_combination (-(w 0 * p 1 * r 1)) * h2
  have hLa : ∀ a, L ![a, 0] = (ν a / δ) • p := by
    intro a
    have e1 : qgPolar p (L ![a, 0]) = 0 := by
      rw [hp, hLpol]
      simp [qgPolar, hν0]
    have e2 : qgPolar (L ![a, 0]) r = ν a := by
      rw [hr, hLpol]
      simp [qgPolar]
    have := hcramer (L ![a, 0])
    rw [e1, e2, zero_smul, add_zero] at this
    rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
  have hLb : ∀ b, L ![0, b] = (ν b / δ) • r := by
    intro b
    have e1 : qgPolar (L ![0, b]) r = 0 := by
      rw [hr, hLpol]
      simp [qgPolar, hν0]
    have e2 : qgPolar p (L ![0, b]) = ν b := by
      rw [hp, hLpol]
      simp [qgPolar]
    have := hcramer (L ![0, b])
    rw [e1, e2, zero_smul, zero_add] at this
    rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
  have hmul : ∀ a b, ν (a * b) / δ = ν a / δ * (ν b / δ) := by
    intro a b
    have e := hLpol ![a, 0] ![0, b]
    rw [hLa, hLb] at e
    have e' : qgPolar ((ν a / δ) • p) ((ν b / δ) • r) = ν a / δ * (ν b / δ) * δ := by
      simp only [qgPolar, hδdef, Pi.smul_apply, smul_eq_mul]
      ring
    have e3 : qgPolar ![a, 0] ![0, b] = a * b := by simp [qgPolar]
    rw [e', e3] at e
    rw [← e, mul_div_cancel_right₀ _ hδ0]
  let σf : K →+* K :=
    { toFun := fun a => ν a / δ
      map_one' := show ν 1 / δ = 1 by rw [← hδ, div_self hδ0]
      map_mul' := hmul
      map_zero' := show ν 0 / δ = 0 by rw [hν0, zero_div]
      map_add' := fun a b => show ν (a + b) / δ = ν a / δ + ν b / δ by rw [hνadd, add_div] }
  let σ : K ≃+* K := RingEquiv.ofBijective σf (Finite.injective_iff_bijective.1 σf.injective)
  have hσ : ∀ a, σ a = ν a / δ := fun a => rfl
  let Mm : Matrix (Fin 2) (Fin 2) K := !![p 0, r 0; p 1, r 1]
  have hdet : Mm.det = δ := by
    rw [det_fin_two_of, hδdef]
    simp only [qgPolar]
    linear_combination (-(r 0 * p 1)) * h2
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Mm (by rw [hdet]; exact hδ0), σ, fun v => ?_⟩
  have hv : v = ![v 0, 0] + ![0, v 1] := by
    ext i
    fin_cases i <;> simp
  have hMm : ((GeneralLinearGroup.mkOfDetNeZero Mm (by rw [hdet]; exact hδ0) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = Mm := rfl
  conv_lhs => rw [hv]
  rw [hLadd, hLa, hLb, hMm]
  ext i
  fin_cases i <;> simp [Mm, mulVec, dotProduct, Fin.sum_univ_two, hσ] <;> ring

theorem exists_affine_of_mem {α : QGAut K} (hα : α ∈ qgStab K) :
    ∃ (v₀ : Fin 2 → K) (M : GL (Fin 2) K) (σ : K ≃+* K),
      ∀ v, qgInduced α v = v₀ + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i) := by
  set v₀ := qgInduced α 0 with hv₀
  have hτ := qgTransl_mem (K := K) (v₀ 0) (v₀ 1)
  have hv0 : (![v₀ 0, v₀ 1] : Fin 2 → K) = v₀ := by
    ext i
    fin_cases i <;> rfl
  have hfix : Multiplicative.toAdd (qgTransl (v₀ 0) (v₀ 1) * α) (qgT K) = qgT K := by
    rw [← qgPoint_zero, ← qgPoint_qgInduced (mul_mem hτ hα), qgInduced_mul hτ hα,
      qgInduced_qgTransl, hv0, ← hv₀]
    congr 1
    ext i
    simp [CharTwo.add_self_eq_zero]
  obtain ⟨M, σ, hM⟩ := exists_semilinear_of_fix (mul_mem hτ hα) hfix
  refine ⟨v₀, M, σ, fun v => ?_⟩
  have h := hM v
  rw [qgInduced_mul hτ hα, qgInduced_qgTransl, hv0] at h
  rw [← h]
  ext i
  simp only [Pi.add_apply]
  rw [add_comm (qgInduced α v i), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem qgInduced_qgTransl_mul_qgSemi (v₀ : Fin 2 → K) (M : GL (Fin 2) K) (σ : K ≃+* K)
    (v : Fin 2 → K) :
    qgInduced (qgTransl (v₀ 0) (v₀ 1) * qgSemi M σ) v =
      v₀ + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i) := by
  rw [qgInduced_mul (qgTransl_mem _ _) (qgSemi_mem M σ), qgInduced_qgTransl, qgInduced_qgSemi,
    add_comm]
  congr 1
  ext i
  fin_cases i <;> rfl

omit [CharP K 2] [Finite K] in
theorem affine_params_unique {v₀ v₀' : Fin 2 → K} {M M' : GL (Fin 2) K} {σ σ' : K ≃+* K}
    (h : ∀ v : Fin 2 → K, v₀ + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ (v i)) =
      v₀' + (M' : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ' (v i))) :
    v₀ = v₀' ∧ M = M' ∧ σ = σ' := by
  have h0 := h 0
  simp only [Pi.zero_apply, map_zero] at h0
  have hz : (fun _ : Fin 2 => (0 : K)) = 0 := rfl
  rw [hz, mulVec_zero, mulVec_zero, add_zero, add_zero] at h0
  subst h0
  have h' : ∀ v : Fin 2 → K, (M : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ (v i)) =
      (M' : Matrix (Fin 2) (Fin 2) K) *ᵥ (fun i => σ' (v i)) := fun v => add_left_cancel (h v)
  have hent : ∀ a b : K, ∀ i : Fin 2,
      (M : Matrix (Fin 2) (Fin 2) K) i 0 * σ a + (M : Matrix (Fin 2) (Fin 2) K) i 1 * σ b =
        (M' : Matrix (Fin 2) (Fin 2) K) i 0 * σ' a +
          (M' : Matrix (Fin 2) (Fin 2) K) i 1 * σ' b := by
    intro a b i
    have := congrFun (h' ![a, b]) i
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using this
  have hM : M = M' := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases j
    · simpa using hent 1 0 i
    · simpa using hent 0 1 i
  subst hM
  refine ⟨rfl, rfl, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, (M : Matrix (Fin 2) (Fin 2) K) i 0 ≠ 0 := by
    by_contra hall
    push Not at hall
    have hdet : (M : Matrix (Fin 2) (Fin 2) K).det = 0 := by
      rw [det_fin_two, hall 0, hall 1]
      ring
    exact ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero hdet
  ext a
  have := hent a 0 i
  simp only [map_zero, mul_zero, add_zero] at this
  exact mul_left_cancel₀ hi this

theorem induced_iff_affine (g : (Fin 2 → K) → Fin 2 → K) :
    (∃ α ∈ qgStab K, ∀ v, Multiplicative.toAdd α (qgPoint v) = qgPoint (g v)) ↔
      ∃ (v₀ : Fin 2 → K) (M : GL (Fin 2) K) (σ : K ≃+* K),
        ∀ v, g v = v₀ + (M : Matrix (Fin 2) (Fin 2) K) *ᵥ fun i => σ (v i) := by
  constructor
  · rintro ⟨α, hα, hg⟩
    obtain ⟨v₀, M, σ, hM⟩ := exists_affine_of_mem hα
    refine ⟨v₀, M, σ, fun v => ?_⟩
    rw [← hM]
    apply qgPoint_injective
    rw [qgPoint_qgInduced hα, hg]
  · rintro ⟨v₀, M, σ, hg⟩
    refine ⟨_, mul_mem (qgTransl_mem (v₀ 0) (v₀ 1)) (qgSemi_mem M σ), fun v => ?_⟩
    rw [← qgPoint_qgInduced (mul_mem (qgTransl_mem (v₀ 0) (v₀ 1)) (qgSemi_mem M σ)),
      qgInduced_qgTransl_mul_qgSemi, hg]

end CFSG.LocalAnalysis.SteinbergCD
