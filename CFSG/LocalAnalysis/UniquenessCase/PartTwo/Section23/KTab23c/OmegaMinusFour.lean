module

public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.CoprimeActionSupport.SemiregularFiniteSetCardDivisibility
import CFSG.Quasithin.Background.Harris.L2.OmegaMinusCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

open CFSG.Open Matrix
open CFSG.Quasithin.G11.Harris.L2 (statedQuadMinus_two)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def e1M (K : Type) [Field K] : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl 0) 1

private def polarM (b c : K) (w w' : ιM → K) : K :=
  StatedQuadMinus 2 K b c (w + w') - StatedQuadMinus 2 K b c w -
    StatedQuadMinus 2 K b c w'

private theorem polarM_apply [CharP K 2] {b c : K} (w w' : ιM → K) :
    polarM b c w w' =
      w (Sum.inl 0) * w' (Sum.inr (Sum.inl 0)) +
        w' (Sum.inl 0) * w (Sum.inr (Sum.inl 0)) +
          b * (w (Sum.inr (Sum.inr 0)) * w' (Sum.inr (Sum.inr 1)) +
            w' (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1))) := by
  simp only [polarM, statedQuadMinus_two, Pi.add_apply]
  ring_nf
  simp [CharTwo.two_eq_zero]

private theorem polarM_e1M [CharP K 2] {b c : K} (w : ιM → K) :
    polarM b c w (e1M K) = w (Sum.inr (Sum.inl 0)) := by
  rw [polarM_apply]
  simp [e1M]

private theorem polarM_add_left [CharP K 2] {b c : K} (w₁ w₂ w' : ιM → K) :
    polarM b c (w₁ + w₂) w' = polarM b c w₁ w' + polarM b c w₂ w' := by
  simp only [polarM_apply, Pi.add_apply]
  ring

private theorem polarM_mulVec [CharP K 2] {b c : K} {g : GL ιM K}
    (hg : ∀ v, StatedQuadMinus 2 K b c ((g : Matrix ιM ιM K) *ᵥ v) =
      StatedQuadMinus 2 K b c v) (v v' : ιM → K) :
    polarM b c ((g : Matrix ιM ιM K) *ᵥ v) ((g : Matrix ιM ιM K) *ᵥ v') = polarM b c v v' := by
  simp only [polarM, ← Matrix.mulVec_add, hg]

private def vecM (x u v : K) : ιM → K :=
  fun i => match i with
    | Sum.inl _ => x
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr k) => if k = 0 then u else v

@[simp] private theorem vecM_x (x u v : K) : vecM x u v (Sum.inl 0) = x := rfl

@[simp] private theorem vecM_y (x u v : K) : vecM x u v (Sum.inr (Sum.inl 0)) = 0 := rfl

@[simp] private theorem vecM_u (x u v : K) : vecM x u v (Sum.inr (Sum.inr 0)) = u := by
  simp [vecM]

@[simp] private theorem vecM_v (x u v : K) : vecM x u v (Sum.inr (Sum.inr 1)) = v := by
  simp [vecM]

private theorem quadMinus_vecM (b c : K) (x u v : K) :
    StatedQuadMinus 2 K b c (vecM x u v) = u ^ 2 + b * u * v + c * v ^ 2 := by
  rw [statedQuadMinus_two]
  simp [vecM]

private def perpEquiv (b c : K) :
    {w : ιM → K // w (Sum.inr (Sum.inl 0)) = 0 ∧ StatedQuadMinus 2 K b c w = 1} ≃
      K × {p : K × K // p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1} where
  toFun w := ⟨w.1 (Sum.inl 0), (w.1 (Sum.inr (Sum.inr 0)), w.1 (Sum.inr (Sum.inr 1))), by
    have h := w.2.2
    rw [statedQuadMinus_two, w.2.1] at h
    simpa using h⟩
  invFun p := ⟨vecM p.1 p.2.1.1 p.2.1.2, by
    refine ⟨vecM_y .., ?_⟩
    rw [quadMinus_vecM]
    exact p.2.2⟩
  left_inv w := by
    refine Subtype.ext (funext fun i => ?_)
    rcases i with i | i
    · fin_cases i
      rfl
    · rcases i with i | i
      · fin_cases i
        exact w.2.1.symm
      · fin_cases i <;> simp [vecM]
  right_inv p := by
    refine Prod.ext ?_ (Subtype.ext (Prod.ext ?_ ?_)) <;> simp [vecM]

private def conicN (b c : K) (p : K × K) : K := p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2

private noncomputable def conicToK (b c : K) (p : K × K) : Option K := by
  classical
  exact if h : p.2 = 0 then none else some ((p.1 - 1) / p.2)

private def conicInvK [CharP K 2] (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : Option K → K × K
  | none => (1, 0)
  | some t => (1 + t * (b / (t ^ 2 + b * t + c)), b / (t ^ 2 + b * t + c))

private theorem conicN_invK [CharP K 2] (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (o : Option K) :
    conicN b c (conicInvK b c hb hirr o) = 1 := by
  cases o with
  | none => simp [conicN, conicInvK]
  | some t =>
    have hD : t ^ 2 + b * t + c ≠ 0 := hirr t
    have hgen : ∀ v : K, (1 + t * v) ^ 2 + b * (1 + t * v) * v + c * v ^ 2 =
        1 + v * (v * (t ^ 2 + b * t + c) + b) := by
      intro v
      ring_nf
      simp [CharTwo.two_eq_zero]
    simp only [conicN, conicInvK]
    rw [hgen, div_mul_cancel₀ b hD, CharTwo.add_self_eq_zero, mul_zero, add_zero]

private theorem conicToK_none (b c : K) (p : K × K) (h : p.2 = 0) : conicToK b c p = none := by
  classical
  simp only [conicToK]
  exact dif_pos h

private theorem conicToK_some (b c : K) (p : K × K) (h : p.2 ≠ 0) :
    conicToK b c p = some ((p.1 - 1) / p.2) := by
  classical
  simp only [conicToK]
  exact dif_neg h

private theorem conicToK_invK [CharP K 2] (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (o : Option K) :
    conicToK b c (conicInvK b c hb hirr o) = o := by
  cases o with
  | none =>
    rw [show conicInvK b c hb hirr none = (1, 0) from rfl, conicToK_none b c (1, 0) rfl]
  | some t =>
    have hD : t ^ 2 + b * t + c ≠ 0 := hirr t
    have hv : b / (t ^ 2 + b * t + c) ≠ 0 := div_ne_zero hb hD
    simp only [conicInvK]
    rw [conicToK_some b c _ hv, add_sub_cancel_left, mul_div_cancel_right₀ t hv]

private theorem conicInvK_toK [CharP K 2] (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : K × K} (hp : conicN b c p = 1) :
    conicInvK b c hb hirr (conicToK b c p) = p := by
  classical
  by_cases hv : p.2 = 0
  · have hu2 : p.1 ^ 2 = 1 := by
      have h := hp
      rw [conicN, hv] at h
      simpa using h
    have hu1 : p.1 = 1 := by
      have h : (p.1 + 1) ^ 2 = 0 := by
        rw [show (p.1 + 1) ^ 2 = p.1 ^ 2 + 1 by
          ring_nf
          simp [CharTwo.two_eq_zero], hu2, CharTwo.add_self_eq_zero]
      exact CharTwo.add_eq_zero.mp (sq_eq_zero_iff.mp h)
    rw [conicToK_none b c p hv]
    simp only [conicInvK]
    exact Prod.ext hu1.symm hv.symm
  · set t : K := (p.1 - 1) / p.2 with ht
    set D : K := t ^ 2 + b * t + c with hDdef
    have hD : D ≠ 0 := by
      rw [hDdef]
      exact hirr t
    have h1 : 1 + t * p.2 = p.1 := by
      rw [ht]
      rw [div_mul_cancel₀ (p.1 - 1) hv, add_comm, sub_add_cancel]
    have hgen : ∀ v : K, (1 + t * v) ^ 2 + b * (1 + t * v) * v + c * v ^ 2 =
        1 + v * (v * D + b) := by
      intro v
      rw [hDdef]
      ring_nf
      simp [CharTwo.two_eq_zero]
    have h2 := hgen p.2
    rw [h1] at h2
    have hp' : p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 = 1 := hp
    rw [hp'] at h2
    have h5 : p.2 * (p.2 * D + b) = 0 := add_eq_left.mp h2.symm
    have h4 : p.2 * D = b :=
      CharTwo.add_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left hv)
    have hbD : b / D = p.2 := by
      rw [← h4]
      exact mul_div_cancel_right₀ p.2 hD
    have htval : (p.1 - 1) / p.2 = t := ht.symm
    simp only [conicToK_some b c p hv, htval]
    rw [show conicInvK b c hb hirr (some t) = (1 + t * (b / D), b / D) from rfl, hbD]
    exact Prod.ext h1 rfl

private noncomputable def conicEquiv [CharP K 2] (b c : K) (hb : b ≠ 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    {p : K × K // conicN b c p = 1} ≃ Option K :=
  Equiv.mk (fun p => conicToK b c p.1)
    (fun o => ⟨conicInvK b c hb hirr o, conicN_invK b c hb hirr o⟩)
    (fun p => Subtype.ext (conicInvK_toK b c hb hirr p.2))
    (fun o => conicToK_invK b c hb hirr o)

theorem ne_zero_of_irreducible_quadratic [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  subst hb
  have hsurj : Function.Surjective fun s : K => s ^ 2 := by
    rw [← Finite.injective_iff_surjective]
    intro a b hab
    change a ^ 2 = b ^ 2 at hab
    have h : (a + b) ^ 2 = 0 := by
      rw [add_sq, hab]
      ring_nf
      simp [CharTwo.two_eq_zero]
    exact CharTwo.add_eq_zero.mp (sq_eq_zero_iff.mp h)
  obtain ⟨s, hs⟩ := hsurj c
  change s ^ 2 = c at hs
  exact hirr s (by rw [zero_mul, add_zero, hs, CharTwo.add_self_eq_zero])

theorem card_perp_quad_eq_one [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card {w : ιM → K // w (Sum.inr (Sum.inl 0)) = 0 ∧ StatedQuadMinus 2 K b c w = 1} =
      Nat.card K * (Nat.card K + 1) := by
  have hb : b ≠ 0 := ne_zero_of_irreducible_quadratic hirr
  have hconic : Nat.card {p : K × K // conicN b c p = 1} = Nat.card (Option K) :=
    Nat.card_congr (conicEquiv b c hb hirr)
  have hperp : Nat.card {w : ιM → K // w (Sum.inr (Sum.inl 0)) = 0 ∧
      StatedQuadMinus 2 K b c w = 1} =
      Nat.card (K × {p : K × K // conicN b c p = 1}) :=
    Nat.card_congr (perpEquiv b c)
  rw [hperp, Nat.card_prod, hconic, Finite.card_option]

theorem sq_eq_one_of_fix_perp [CharP K 2] {b c : K} (hb : b ≠ 0) {g : GL ιM K}
    (hg : ∀ v, StatedQuadMinus 2 K b c ((g : Matrix ιM ιM K) *ᵥ v) = StatedQuadMinus 2 K b c v)
    (he : (g : Matrix ιM ιM K) *ᵥ e1M K = e1M K) {w : ιM → K}
    (hw : w (Sum.inr (Sum.inl 0)) = 0) (hQw : StatedQuadMinus 2 K b c w ≠ 0)
    (hgw : (g : Matrix ιM ιM K) *ᵥ w = w) : g ^ 2 = 1 := by
  classical
  have hP : ∀ v v', polarM b c ((g : Matrix ιM ιM K) *ᵥ v) ((g : Matrix ιM ιM K) *ᵥ v') =
      polarM b c v v' := polarM_mulVec hg
  have hy : ∀ v : ιM → K, ((g : Matrix ιM ιM K) *ᵥ v) (Sum.inr (Sum.inl 0)) =
      v (Sum.inr (Sum.inl 0)) := by
    intro v
    have h := hP v (e1M K)
    rw [he, polarM_e1M, polarM_e1M] at h
    exact h
  have key : ∀ z : ιM → K, (g : Matrix ιM ιM K) *ᵥ ((g : Matrix ιM ιM K) *ᵥ z) = z := by
    intro z
    set d : ιM → K := (g : Matrix ιM ιM K) *ᵥ z - z with hd
    have hzd : z + d = (g : Matrix ιM ιM K) *ᵥ z := by rw [hd]; abel
    have hzw : polarM b c d w = 0 := by
      have h := hP z w
      rw [hgw] at h
      have h2 : polarM b c (z + d) w = polarM b c z w := by rw [hzd]; exact h
      rwa [polarM_add_left, add_eq_left] at h2
    have hze : polarM b c d (e1M K) = 0 := by
      have h := hP z (e1M K)
      rw [he] at h
      have h2 : polarM b c (z + d) (e1M K) = polarM b c z (e1M K) := by rw [hzd]; exact h
      rwa [polarM_add_left, add_eq_left] at h2
    have hdy : d (Sum.inr (Sum.inl 0)) = 0 := by
      rw [← polarM_e1M (b := b) (c := c) (w := d)]
      exact hze
    have hcross : d (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) =
        w (Sum.inr (Sum.inr 0)) * d (Sum.inr (Sum.inr 1)) := by
      have h := hzw
      rw [polarM_apply, hdy, hw] at h
      simp only [mul_zero, zero_mul, add_zero, zero_add] at h
      rcases mul_eq_zero.mp h with h0 | h0
      · exact absurd h0 hb
      · exact CharTwo.add_eq_zero.mp h0
    have hwne : ¬ (w (Sum.inr (Sum.inr 0)) = 0 ∧ w (Sum.inr (Sum.inr 1)) = 0) := by
      rintro ⟨h1, h2⟩
      refine hQw ?_
      rw [statedQuadMinus_two]
      simp [hw, h1, h2]
    have hdecomp : ∀ t : K, d (Sum.inr (Sum.inr 0)) = t * w (Sum.inr (Sum.inr 0)) →
        d (Sum.inr (Sum.inr 1)) = t * w (Sum.inr (Sum.inr 1)) →
        ∃ α : K, d = α • e1M K + t • w := by
      intro t hu hv
      refine ⟨d (Sum.inl 0) - t * w (Sum.inl 0), ?_⟩
      funext i
      rcases i with i | i
      · fin_cases i
        simp [e1M]
      · rcases i with i | i
        · fin_cases i
          simp [e1M, hw, hdy]
        · fin_cases i
          · simp [e1M]
            exact hu
          · simp [e1M]
            exact hv
    obtain ⟨t, α, hα⟩ : ∃ (t α : K), d = α • e1M K + t • w := by
      by_cases hu : w (Sum.inr (Sum.inr 0)) = 0
      · have hv : w (Sum.inr (Sum.inr 1)) ≠ 0 := fun h0 => hwne ⟨hu, h0⟩
        have hdu : d (Sum.inr (Sum.inr 0)) = 0 := by
          rw [hu, zero_mul] at hcross
          exact (mul_eq_zero.mp hcross).resolve_right hv
        obtain ⟨α, hα⟩ := hdecomp (d (Sum.inr (Sum.inr 1)) / w (Sum.inr (Sum.inr 1)))
          (by rw [hdu, hu, mul_zero]) (div_mul_cancel₀ _ hv).symm
        exact ⟨_, α, hα⟩
      · have hdv : d (Sum.inr (Sum.inr 1)) =
            d (Sum.inr (Sum.inr 0)) / w (Sum.inr (Sum.inr 0)) * w (Sum.inr (Sum.inr 1)) := by
          have h := hcross
          rw [(div_mul_cancel₀ (d (Sum.inr (Sum.inr 0))) hu).symm] at h
          have h2 : w (Sum.inr (Sum.inr 0)) *
              (d (Sum.inr (Sum.inr 0)) / w (Sum.inr (Sum.inr 0)) *
                w (Sum.inr (Sum.inr 1))) = w (Sum.inr (Sum.inr 0)) *
                  d (Sum.inr (Sum.inr 1)) := by
            rw [← h]; ring
          exact (mul_left_cancel₀ hu h2).symm
        obtain ⟨α, hα⟩ := hdecomp (d (Sum.inr (Sum.inr 0)) / w (Sum.inr (Sum.inr 0)))
          (div_mul_cancel₀ _ hu).symm hdv
        exact ⟨_, α, hα⟩
    have hGd : (g : Matrix ιM ιM K) *ᵥ d = d := by
      rw [hα, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, he, hgw]
    calc (g : Matrix ιM ιM K) *ᵥ ((g : Matrix ιM ιM K) *ᵥ z)
        = (g : Matrix ιM ιM K) *ᵥ (z + d) := by rw [hzd]
      _ = (g : Matrix ιM ιM K) *ᵥ z + (g : Matrix ιM ιM K) *ᵥ d := Matrix.mulVec_add ..
      _ = (z + d) + d := by rw [hzd, hGd]
      _ = z := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hmat : ((g ^ 2 : GL ιM K) : Matrix ιM ιM K) = 1 := by
    rw [Units.val_pow_eq_pow_val, pow_two]
    refine Matrix.ext_iff_mulVec.mpr (fun z => ?_)
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    exact key z
  exact Units.ext hmat

theorem card_dvd_of_odd_of_fix [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {E : Subgroup (GL ιM K)}
    (hE : ∀ g ∈ E, ∀ v, StatedQuadMinus 2 K b c ((g : Matrix ιM ιM K) *ᵥ v) =
      StatedQuadMinus 2 K b c v)
    (hodd : Odd (Nat.card ↥E)) (hfix : ∀ g ∈ E, (g : Matrix ιM ιM K) *ᵥ e1M K = e1M K) :
    Nat.card ↥E ∣ Nat.card K + 1 := by
  classical
  have hb : b ≠ 0 := ne_zero_of_irreducible_quadratic hirr
  let X := {w : ιM → K // w (Sum.inr (Sum.inl 0)) = 0 ∧ StatedQuadMinus 2 K b c w = 1}
  have hcardX : Nat.card X = Nat.card K * (Nat.card K + 1) := card_perp_quad_eq_one hirr
  have hy0 : ∀ (g : ↥E) (w : X),
      (((g : GL ιM K) : Matrix ιM ιM K) *ᵥ w.1) (Sum.inr (Sum.inl 0)) = 0 := by
    intro g w
    have hP := polarM_mulVec (b := b) (c := c) (g := (g : GL ιM K)) (hE g g.2) w.1 (e1M K)
    rw [hfix g g.2, polarM_e1M, polarM_e1M, w.2.1] at hP
    exact hP
  haveI : Finite X := Subtype.finite
  letI actX : MulAction ↥E X :=
    { smul := fun g w => ⟨((g : GL ιM K) : Matrix ιM ιM K) *ᵥ w.1, hy0 g w, by
        show StatedQuadMinus 2 K b c (((g : GL ιM K) : Matrix ιM ιM K) *ᵥ w.1) = 1
        rw [hE g g.2]
        exact w.2.2⟩
      one_smul := fun w => Subtype.ext (by
        show (((1 : ↥E) : GL ιM K) : Matrix ιM ιM K) *ᵥ w.1 = w.1
        rw [show (((1 : ↥E) : GL ιM K) : Matrix ιM ιM K) = 1 from rfl, Matrix.one_mulVec])
      mul_smul := fun a b w => Subtype.ext (by
        show ((↑(a * b : ↥E) : GL ιM K) : Matrix ιM ιM K) *ᵥ w.1 =
          ((a : GL ιM K) : Matrix ιM ιM K) *ᵥ (((b : GL ιM K) : Matrix ιM ιM K) *ᵥ w.1)
        rw [show ((↑(a * b : ↥E) : GL ιM K) : Matrix ιM ιM K) =
          ((a : GL ιM K) : Matrix ιM ιM K) * ((b : GL ιM K) : Matrix ιM ιM K) from rfl,
          ← Matrix.mulVec_mulVec]) }
  have hXone : ∀ w : X, (1 : ↥E) • w = w := fun w => one_smul ↥E w
  have hXmul : ∀ (a b : ↥E) (w : X), (a * b) • w = a • b • w := fun a b w => mul_smul a b w
  have hstab : ∀ (g : ↥E) (w : X), g • w = w → g = 1 := by
    intro g w hgw
    have hmat : ((g : GL ιM K) : Matrix ιM ιM K) *ᵥ w.1 = w.1 := congrArg Subtype.val hgw
    have hsq : (g : GL ιM K) ^ 2 = 1 :=
      sq_eq_one_of_fix_perp hb (hE g g.2) (hfix g g.2) w.2.1 (by rw [w.2.2]; exact one_ne_zero)
        hmat
    have hdvd2 : orderOf (g : GL ιM K) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    have hdvdE : orderOf (g : GL ιM K) ∣ Nat.card ↥E := Subgroup.orderOf_dvd_natCard E g.2
    have hoddg : Odd (orderOf (g : GL ιM K)) := Odd.of_dvd_nat hodd hdvdE
    have hone : orderOf (g : GL ιM K) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
      · exact h1
      · rw [h2] at hoddg
        exact absurd hoddg (by simp [Nat.odd_iff])
    have hg1 : (g : GL ιM K) = 1 := orderOf_eq_one_iff.mp hone
    exact Subtype.ext hg1
  have hdvd : Nat.card ↥E ∣ Nat.card X := by
    let Y := X ⊕ Unit
    let x0 : Y := Sum.inr ()
    letI smulY : SMul ↥E Y := ⟨fun g y => Sum.map (fun w : X => g • w) id y⟩
    letI actY : MulAction ↥E Y :=
      { smulY with
        one_smul := by
          rintro (_ | u)
          · exact congrArg Sum.inl (hXone _)
          · rfl
        mul_smul := by
          rintro a b (_ | u)
          · exact congrArg Sum.inl (hXmul a b _)
          · rfl }
    have hfixY : ∀ g : ↥E, g • x0 = x0 := fun g => rfl
    have hfreeY : ∀ g : ↥E, g ≠ 1 → ∀ y : Y, y ≠ x0 → g • y ≠ y := by
      rintro g hg1 (w | u) hy hEq
      · exact hg1 (hstab g w (Sum.inl.inj hEq))
      · exact hy (by rw [Subsingleton.elim u ()])
    have h :=
      CFSG.GroupTheory.CoprimeActionSupport.SemiregularFiniteSetCardDivisibility.card_dvd_pred
        (B := ↥E) x0 hfixY hfreeY
    have hYX : Nat.card Y = Nat.card X + 1 := by
      have h1 : Y = (X ⊕ Unit) := rfl
      rw [h1, Nat.card_sum]
      simp
    rwa [hYX, Nat.add_sub_cancel] at h
  have hdvd' : Nat.card ↥E ∣ Nat.card K * (Nat.card K + 1) := by
    rwa [hcardX] at hdvd
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card (K := K) 2
  have hcop2 : Nat.Coprime (Nat.card ↥E) 2 := Nat.coprime_two_right.mpr hodd
  have h2n : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  have hcop : Nat.Coprime (Nat.card ↥E) (Nat.card K) := by
    rw [h2n]
    exact hcop2.pow_right (n : ℕ)
  exact hcop.dvd_of_dvd_mul_left hdvd'

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

end
