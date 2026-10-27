module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.SzG11TwoOm4Witt

public section

namespace CFSG.Quasithin.G11.SzG11S.Two.Om4

open CFSG.Assembly.LowTwoRank Matrix
open LinearMap (BilinForm)

theorem isometry_of_mem_omega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : (ι → K) → K) {g : GL ι K} (hg : g ∈ StatedOmega Q) (v : ι → K) :
    Q ((g : Matrix ι ι K) *ᵥ v) = Q v := by
  let Iso : Subgroup (GL ι K) :=
    { carrier := {A | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}
      one_mem' := fun v => by simp
      mul_mem' := fun {A B} hA hB v => by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
      inv_mem' := fun {A} hA v => by
        have h := hA (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec] at h
        exact h.symm }
  have hS : Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ≤ Iso :=
    (Subgroup.closure_le Iso).2 (fun A hA => hA)
  have hΩ : StatedOmega Q ≤ Iso := by
    unfold StatedOmega
    refine (Subgroup.commutator_mono hS hS).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Iso.mul_mem (Iso.mul_mem (Iso.mul_mem ha hb) (Iso.inv_mem ha)) (Iso.inv_mem hb)
  exact hΩ hg v

abbrev Idx : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

theorem idx_ext {K : Type} {u u' : Idx → K} (h0 : u (.inl 0) = u' (.inl 0))
    (h1 : u (.inr (.inl 0)) = u' (.inr (.inl 0))) (h2 : u (.inr (.inr 0)) = u' (.inr (.inr 0)))
    (h3 : u (.inr (.inr 1)) = u' (.inr (.inr 1))) : u = u' := by
  funext i
  rcases i with i | i | i
  · have : i = 0 := Fin.ext (by omega)
    subst this
    exact h0
  · have : i = 0 := Fin.ext (by omega)
    subst this
    exact h1
  · fin_cases i
    · exact h2
    · exact h3

theorem quad_apply {K : Type} [Field K] (b c : K) (v : Idx → K) :
    StatedQuadMinus 2 K b c v = v (.inl 0) * v (.inr (.inl 0)) + v (.inr (.inr 0)) ^ 2 +
      b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2 := by
  simp [StatedQuadMinus]

@[expose] def coordEquiv (K : Type) : (Idx → K) ≃ K × K × K × K where
  toFun v := (v (.inl 0), v (.inr (.inl 0)), v (.inr (.inr 0)), v (.inr (.inr 1)))
  invFun z := Sum.elim (fun _ => z.1) (Sum.elim (fun _ => z.2.1)
    (fun j => if j = 0 then z.2.2.1 else z.2.2.2))
  left_inv v := by
    apply idx_ext <;> simp
  right_inv z := by
    simp

variable {K : Type} [Field K]

theorem quad_polar (h2 : (2 : K) = 0) (b c : K) (hb : b ≠ 0) :
    ∃ β : BilinForm K (Idx → K),
      (∀ u v, StatedQuadMinus 2 K b c (u + v) =
        StatedQuadMinus 2 K b c u + StatedQuadMinus 2 K b c v + β u v) ∧ β.Nondegenerate := by
  let f : (Idx → K) → (Idx → K) → K := fun u v =>
    u (.inl 0) * v (.inr (.inl 0)) + v (.inl 0) * u (.inr (.inl 0)) +
      b * (u (.inr (.inr 0)) * v (.inr (.inr 1)) + v (.inr (.inr 0)) * u (.inr (.inr 1)))
  have hsymm : ∀ u v, f u v = f v u := fun u v => by simp only [f]; ring
  let β : BilinForm K (Idx → K) := LinearMap.mk₂ K f
    (fun u u' v => by simp only [f, Pi.add_apply]; ring)
    (fun κ u v => by simp only [f, Pi.smul_apply, smul_eq_mul]; ring)
    (fun u v v' => by simp only [f, Pi.add_apply]; ring)
    (fun κ u v => by simp only [f, Pi.smul_apply, smul_eq_mul]; ring)
  have hβ : ∀ u v, β u v = f u v := fun u v => rfl
  have hsep : ∀ u : Idx → K, (∀ v, β u v = 0) → u = 0 := by
    intro u hu
    have e0 := hu (Pi.single (.inl 0) 1)
    have e1 := hu (Pi.single (.inr (.inl 0)) 1)
    have e2 := hu (Pi.single (.inr (.inr 0)) 1)
    have e3 := hu (Pi.single (.inr (.inr 1)) 1)
    simp [hβ, f] at e0 e1 e2 e3
    refine idx_ext ?_ ?_ ?_ ?_
    · simpa using e1
    · simpa using e0
    · simpa [hb] using e3
    · simpa [hb] using e2
  refine ⟨β, fun u v => ?_, hsep, fun v hv => hsep v (fun u => by rw [hβ, hsymm]; exact hv u)⟩
  rw [hβ]
  simp only [f, quad_apply, Pi.add_apply]
  linear_combination (u (.inr (.inr 0)) * v (.inr (.inr 0)) +
    c * u (.inr (.inr 1)) * v (.inr (.inr 1))) * h2

theorem not_span_one (w : Idx → K) : ∃ v : Idx → K, ∀ κ : K, v ≠ κ • w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨κ₁, h₁⟩ := hcon (Pi.single (.inl 0) 1)
  obtain ⟨κ₂, h₂⟩ := hcon (Pi.single (.inr (.inl 0)) 1)
  have a1 := congrFun h₁ (.inl 0)
  have a2 := congrFun h₂ (.inl 0)
  have a3 := congrFun h₂ (.inr (.inl 0))
  simp at a1 a2 a3
  have ha : w (.inl 0) ≠ 0 := fun h => by rw [h, mul_zero] at a1; exact one_ne_zero a1
  have hκ : κ₂ = 0 := by
    rcases a2 with h | h
    · exact h
    · exact absurd h ha
  rw [hκ, zero_mul] at a3
  exact one_ne_zero a3

variable [Fintype K]

theorem sq_bijective (h2 : (2 : K) = 0) : Function.Bijective (fun t : K => t ^ 2) := by
  have hinj : Function.Injective (fun t : K => t ^ 2) := by
    intro a b hab
    have h : (a + b) ^ 2 = 0 := by
      rw [sq_add_of_two_eq_zero h2]
      simp only at hab
      linear_combination hab + (b ^ 2) * h2
    have h' := (pow_eq_zero_iff two_ne_zero).1 h
    linear_combination h' - b * h2
  exact hinj.bijective_of_finite

theorem sum_chi_sq_mul (h2 : (2 : K) = 0) (h4 : ∀ κ : K, κ ^ 4 = κ)
    (hK : Fintype.card K = 4) {p : K} (hp : p ≠ 0) : ∑ t : K, chi (t ^ 2 * p) = 0 := by
  have e1 : ∑ t : K, chi (t ^ 2 * p) = ∑ y : K, chi (y * p) :=
    Fintype.sum_equiv (Equiv.ofBijective _ (sq_bijective h2)) _ _ (fun t => rfl)
  have e2 : ∑ y : K, chi (y * p) = ∑ y : K, chi y :=
    Fintype.sum_equiv (Equiv.mulRight₀ p hp) _ _ (fun y => rfl)
  rw [e1, e2, sum_chi_eq_zero h2 h4 hK]

theorem sum_chi_mul_mul (h2 : (2 : K) = 0) (h4 : ∀ κ : K, κ ^ 4 = κ) (hK : Fintype.card K = 4) :
    ∑ p : K, ∑ q : K, chi (p * q) = 4 := by
  classical
  have h : ∀ p : K, ∑ q : K, chi (p * q) = if p = 0 then 4 else 0 := by
    intro p
    split_ifs with hp
    · simp [hp, chi_zero, hK]
    · rw [Fintype.sum_equiv (Equiv.mulLeft₀ p hp) (fun q => chi (p * q)) chi (fun q => rfl),
        sum_chi_eq_zero h2 h4 hK]
  simp [h]

theorem sum_chi_norm (h2 : (2 : K) = 0) (h4 : ∀ κ : K, κ ^ 4 = κ) (hK : Fintype.card K = 4)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∑ s : K, ∑ t : K, chi (s ^ 2 + b * s * t + c * t ^ 2) = -4 := by
  classical
  rw [Finset.sum_comm]
  have hg : ∀ t : K, ∑ s : K, chi (s ^ 2 + b * s * t + c * t ^ 2) =
      (∑ s' : K, chi (t ^ 2 * (s' ^ 2 + b * s' + c))) - (if t = 0 then 4 else 0) := by
    intro t
    split_ifs with ht
    · subst ht
      have h1 : ∑ s : K, chi (s ^ 2 + b * s * 0 + c * 0 ^ 2) = ∑ y : K, chi y := by
        refine Fintype.sum_equiv (Equiv.ofBijective _ (sq_bijective h2)) _ _ (fun s => ?_)
        simp
      have h3 : ∑ s' : K, chi ((0 : K) ^ 2 * (s' ^ 2 + b * s' + c)) = 4 := by
        simp [chi_zero, hK]
      rw [h1, h3, sum_chi_eq_zero h2 h4 hK]
      norm_num
    · rw [sub_zero]
      refine (Fintype.sum_equiv (Equiv.mulLeft₀ t ht)
        (fun s' => chi (t ^ 2 * (s' ^ 2 + b * s' + c)))
        (fun s => chi (s ^ 2 + b * s * t + c * t ^ 2)) (fun s' => ?_)).symm
      show chi (t ^ 2 * (s' ^ 2 + b * s' + c)) = chi ((t * s') ^ 2 + b * (t * s') * t + c * t ^ 2)
      congr 1
      ring
  have hh : ∑ t : K, ∑ s' : K, chi (t ^ 2 * (s' ^ 2 + b * s' + c)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun s' _ => ?_)
    exact sum_chi_sq_mul h2 h4 hK (hbc s')
  simp only [hg, Finset.sum_sub_distrib, hh]
  simp

theorem sum_chi_quad (h2 : (2 : K) = 0) (hK : Fintype.card K = 4) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∑ v : Idx → K, chi (StatedQuadMinus 2 K b c v) = -16 := by
  classical
  have h4 : ∀ κ : K, κ ^ 4 = κ := fun κ => by
    simpa [hK] using FiniteField.pow_card κ
  have hsum : ∑ v : Idx → K, chi (StatedQuadMinus 2 K b c v) =
      ∑ z : K × K × K × K, chi (z.1 * z.2.1) *
        chi (z.2.2.1 ^ 2 + b * z.2.2.1 * z.2.2.2 + c * z.2.2.2 ^ 2) := by
    refine Fintype.sum_equiv (coordEquiv K) _ _ (fun v => ?_)
    rw [quad_apply, ← chi_add h2 h4]
    simp only [coordEquiv, Equiv.coe_fn_mk]
    congr 1
    ring
  rw [hsum]
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_chi_mul_mul h2 h4 hK, sum_chi_norm h2 h4 hK hbc]
  norm_num

end CFSG.Quasithin.G11.SzG11S.Two.Om4
