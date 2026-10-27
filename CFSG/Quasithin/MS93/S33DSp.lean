module

public import CFSG.Quasithin.MS93.S33XOm

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open scoped Matrix

variable {F : Type} [Field F]

section Omega5

variable [CharP F 2]

@[expose] def omD (p₀ : MSP.V4 F) : Subgroup (Multiplicative ((Fin 2 ⊕ Fin 2 → F) × F)) where
  carrier := {w | ∃ c : F, w = Multiplicative.ofAdd (c • p₀, c ^ 2 * sp4Quad F p₀)}
  one_mem' := ⟨0, by rw [zero_smul, zero_pow two_ne_zero, zero_mul, Prod.mk_zero_zero, ofAdd_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
    refine ⟨c + d, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
    refine Prod.ext (by simp [add_smul]) ?_
    simp only [Prod.snd_add]
    rw [add_pow_char c d]
    ring
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_inv, toAdd_ofAdd]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_neg]
      funext i
      exact CharTwo.neg_eq _
    · simp only [Prod.snd_neg]
      exact CharTwo.neg_eq _

theorem form_eq_bil (x y : MSP.V4 F) : MSP.form F x y = bil x y := by
  rw [MSP.form_apply, bil, sub_eq_add_neg, CharTwo.neg_eq]
  ring

theorem omega5Act_mul_inv_mem_omD {p₀ : MSP.V4 F} {g : MSP.Sp4 F}
    (hg : g ∈ MSP.qPoint (F ∙ p₀)) {x : MSP.V4 F} (hx : MSP.form F p₀ x = 0) (s : F) :
    omega5Act F g (Multiplicative.ofAdd (x, s)) * (Multiplicative.ofAdd (x, s))⁻¹ ∈ omD p₀ := by
  have hxp : x ∈ MSP.perp (F ∙ p₀) := MSP.mem_perp_span.2 hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 ((MSP.mem_qPoint.1 hg).2 x hxp)
  have hgx : MSP.mat g *ᵥ x = x + c • p₀ := by rw [hc]; abel
  refine ⟨c, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, omega5Act_toAdd, toAdd_ofAdd, toAdd_ofAdd]
  have hm : spMat g *ᵥ x = x + c • p₀ := hgx
  rw [hm, sp4Quad_add]
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_add, Prod.snd_neg]
    have h1 : sp4Quad F (c • p₀) = c ^ 2 * sp4Quad F p₀ := by
      simp only [sp4Quad, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : bil x (c • p₀) = 0 := by
      rw [← form_eq_bil, map_smul, smul_eq_mul, MSP.form_swap, hx, neg_zero, mul_zero]
    rw [h1, h2, CharTwo.neg_eq]
    have h3 : sp4Quad F x + sp4Quad F x = 0 := CharTwo.add_self_eq_zero _
    have h4 : s + s = 0 := CharTwo.add_self_eq_zero _
    linear_combination h3 + h4

theorem card_omD_le [Finite F] (p₀ : MSP.V4 F) : Nat.card (omD p₀) ≤ Nat.card F := by
  have hsurj : Function.Surjective (fun c : F => (⟨Multiplicative.ofAdd (c • p₀, c ^ 2 *
      sp4Quad F p₀), c, rfl⟩ : ↥(omD p₀))) := by
    rintro ⟨_, c, rfl⟩
    exact ⟨c, rfl⟩
  exact Nat.card_le_card_of_surjective _ hsurj

theorem prod_mem_omComm_xPoint [Fintype F] (hF : 2 < Fintype.card F) {p₀ : MSP.V4 F}
    (hp₀ : p₀ ≠ 0) (c s : F) :
    Multiplicative.ofAdd (c • p₀, s) ∈ omComm (MSP.xPoint (F ∙ p₀)) := by
  have hp : MSP.IsPoint (F ∙ p₀) := MSP.isPoint_span hp₀
  obtain ⟨x, hx⟩ := MSP.exists_form_eq_one hp₀
  have hcomm : omega5Act F (MSP.transv p₀ c) (Multiplicative.ofAdd (x, 0)) *
      (Multiplicative.ofAdd (x, 0))⁻¹ ∈ omComm (MSP.xPoint (F ∙ p₀)) :=
    Subgroup.subset_closure ⟨_, MSP.transv_mem_xPoint p₀ c, _, rfl⟩
  have hval : omega5Act F (MSP.transv p₀ c) (Multiplicative.ofAdd (x, 0)) *
      (Multiplicative.ofAdd (x, 0))⁻¹ =
        Multiplicative.ofAdd (c • p₀, c ^ 2 * sp4Quad F p₀ + c) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, omega5Act_toAdd, toAdd_ofAdd, toAdd_ofAdd]
    have hm : spMat (MSP.transv p₀ c) *ᵥ x = x + c • p₀ := by
      change MSP.mat (MSP.transv p₀ c) *ᵥ x = _
      rw [MSP.transv_mulVec, hx, mul_one]
    rw [hm, sp4Quad_add]
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_add, Prod.snd_neg, neg_zero, add_zero, zero_add]
    have h1 : sp4Quad F (c • p₀) = c ^ 2 * sp4Quad F p₀ := by
      simp only [sp4Quad, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : bil x (c • p₀) = c := by
      rw [← form_eq_bil, map_smul, smul_eq_mul, MSP.form_swap, hx, CharTwo.neg_eq, mul_one]
    rw [h1, h2]
    have h3 : sp4Quad F x + sp4Quad F x = 0 := CharTwo.add_self_eq_zero _
    linear_combination h3
  have hrad : Multiplicative.ofAdd ((0 : MSP.V4 F), s - (c ^ 2 * sp4Quad F p₀ + c)) ∈
      omComm (MSP.xPoint (F ∙ p₀)) :=
    rad_le_omComm_xPoint hF hp (show ((0 : MSP.V4 F), _).1 = 0 from rfl)
  have e : Multiplicative.ofAdd (c • p₀, s) =
      Multiplicative.ofAdd (c • p₀, c ^ 2 * sp4Quad F p₀ + c) *
        Multiplicative.ofAdd ((0 : MSP.V4 F), s - (c ^ 2 * sp4Quad F p₀ + c)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_add]
    ring
  rw [e, ← hval]
  exact mul_mem hcomm hrad

end Omega5

theorem sub_mem_span_of_fix {p₀ c : MSP.V4 F} (hp₀ : p₀ ≠ 0) (hpc : MSP.form F p₀ c = 0)
    (hc : c ∉ F ∙ p₀) {y : MSP.Sp4 F} (hyp : MSP.mat y *ᵥ p₀ = p₀) (hyc : MSP.mat y *ᵥ c = c)
    (v : MSP.V4 F) : MSP.mat y *ᵥ v - v ∈ Submodule.span F {p₀, c} := by
  have hl : MSP.IsLine (Submodule.span F {p₀, c}) := by
    refine ⟨MSP.finrank_span_pair hp₀ hc, MSP.form_span_pair hpc⟩
  rw [← hl.perp_eq, MSP.mem_perp]
  intro w hw
  have hw' : MSP.mat y *ᵥ w = w := by
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hw
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hyp, hyc]
  rw [map_sub, ← MSP.form_mat y w v, hw', sub_self]

end CFSG.Quasithin.MS93.S33
