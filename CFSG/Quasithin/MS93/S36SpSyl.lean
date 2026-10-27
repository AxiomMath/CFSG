module

public import CFSG.Quasithin.MS93.MSPLevi
public import CFSG.Quasithin.MS93.MSPOpp

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin.MS93.MSP Matrix
open scoped commutatorElement

section ClassTwo

variable {K : Type*} [Group K]

theorem commutator_sup_le_left {A B : Subgroup K} (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hA : A ⊔ B ≤ Subgroup.normalizer (A : Set K)) : ⁅A ⊔ B, A ⊔ B⁆ ≤ A := by
  have hc : ∀ g ∈ A ⊔ B, ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun g hg a ha => (Subgroup.mem_normalizer_iff.1 (hA hg) a).1 ha
  have hxB : ∀ x ∈ B, ∀ y ∈ A ⊔ B, ⁅x, y⁆ ∈ A := by
    intro x hx
    let Kx : Subgroup K :=
      { carrier := {y | y ∈ A ⊔ B ∧ ⁅x, y⁆ ∈ A}
        one_mem' := ⟨Subgroup.one_mem _, by simp⟩
        mul_mem' := by
          rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
          refine ⟨Subgroup.mul_mem _ hy₁ hy₂, ?_⟩
          have e : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact Subgroup.mul_mem _ h₁ (hc _ hy₁ _ h₂)
        inv_mem' := by
          rintro y ⟨hy, h₁⟩
          refine ⟨Subgroup.inv_mem _ hy, ?_⟩
          have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact hc _ (Subgroup.inv_mem _ hy) _ (Subgroup.inv_mem _ h₁) }
    have hAK : A ≤ Kx := fun a ha => ⟨Subgroup.mem_sup_left ha, by
      have e : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact Subgroup.mul_mem _ (hc _ (Subgroup.mem_sup_right hx) _ ha) (Subgroup.inv_mem _ ha)⟩
    have hBK : B ≤ Kx := fun b hb => ⟨Subgroup.mem_sup_right hb, by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (hB x hx b hb)]
      exact Subgroup.one_mem _⟩
    exact fun y hy => (sup_le hAK hBK hy).2
  let K' : Subgroup K :=
    { carrier := {x | x ∈ A ⊔ B ∧ ∀ y ∈ A ⊔ B, ⁅x, y⁆ ∈ A}
      one_mem' := ⟨Subgroup.one_mem _, fun y _ => by simp⟩
      mul_mem' := by
        rintro x₁ x₂ ⟨hx₁, h₁⟩ ⟨hx₂, h₂⟩
        refine ⟨Subgroup.mul_mem _ hx₁ hx₂, fun y hy => ?_⟩
        have e : ⁅x₁ * x₂, y⁆ = (x₁ * ⁅x₂, y⁆ * x₁⁻¹) * ⁅x₁, y⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (hc _ hx₁ _ (h₂ y hy)) (h₁ y hy)
      inv_mem' := by
        rintro x ⟨hx, h₁⟩
        refine ⟨Subgroup.inv_mem _ hx, fun y hy => ?_⟩
        have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hc _ (Subgroup.inv_mem _ hx) _ (Subgroup.inv_mem _ (h₁ y hy)) }
  have hAK : A ≤ K' := fun a ha => ⟨Subgroup.mem_sup_left ha, fun y hy => by
    have e : ⁅a, y⁆ = a * (y * a⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ ha (hc _ hy _ (Subgroup.inv_mem _ ha))⟩
  have hBK : B ≤ K' := fun b hb => ⟨Subgroup.mem_sup_right hb, hxB b hb⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact (sup_le hAK hBK hx).2 y hy

theorem commutator_commutator_eq_bot_of_sup {A B : Subgroup K}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hAn : A ⊔ B ≤ Subgroup.normalizer (A : Set K))
    (hBn : A ⊔ B ≤ Subgroup.normalizer (B : Set K)) :
    ⁅⁅A ⊔ B, A ⊔ B⁆, A ⊔ B⁆ = ⊥ := by
  have h1 : ⁅A ⊔ B, A ⊔ B⁆ ≤ A := commutator_sup_le_left hB hAn
  have h2 : ⁅A ⊔ B, A ⊔ B⁆ ≤ B := by
    rw [sup_comm] at hAn hBn ⊢
    exact commutator_sup_le_left hA hBn
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro c hc z hz
  have hcent : A ⊔ B ≤ Subgroup.centralizer ({c} : Set K) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_) <;> rw [Subgroup.mem_centralizer_singleton_iff]
    · exact hA a ha c (h1 hc)
    · exact hB b hb c (h2 hc)
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hcent hz)).symm

end ClassTwo

variable {F : Type} [Field F]

section Standard

theorem sub_mem_ln₀_of_mem_sylS {s : Sp4 F} (hs : s ∈ sylS F) {v : V4 F}
    (hv : v ∈ perp (pt₀ F)) : mat s *ᵥ v - v ∈ ln₀ F := by
  let K : Subgroup (Sp4 F) :=
    { carrier := {g | g ∈ P₁ F ∧ g ∈ P₂ F ∧ ∀ w ∈ perp (pt₀ F), mat g *ᵥ w - w ∈ ln₀ F}
      one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun w _ => by
        rw [mat_one, Matrix.one_mulVec, sub_self]
        exact Submodule.zero_mem _⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁, hg₁', h₁⟩ ⟨hg₂, hg₂', h₂⟩
        refine ⟨Subgroup.mul_mem _ hg₁ hg₂, Subgroup.mul_mem _ hg₁' hg₂', fun w hw => ?_⟩
        have e : mat (g₁ * g₂) *ᵥ w - w =
            mat g₁ *ᵥ (mat g₂ *ᵥ w - w) + (mat g₁ *ᵥ w - w) := by
          rw [mat_mul_mulVec, mulVec_sub]
          abel
        rw [e]
        exact Submodule.add_mem _ (mulVec_mem_of_mem_stab hg₁ (h₂ w hw)) (h₁ w hw)
      inv_mem' := by
        rintro g ⟨hg, hg', h₁⟩
        refine ⟨Subgroup.inv_mem _ hg, Subgroup.inv_mem _ hg', fun w hw => ?_⟩
        have hw' : mat g⁻¹ *ᵥ w ∈ perp (pt₀ F) :=
          mulVec_mem_of_mem_stab (stab_le_stab_perp _ (Subgroup.inv_mem _ hg')) hw
        have e : mat g⁻¹ *ᵥ w - w = -(mat g *ᵥ (mat g⁻¹ *ᵥ w) - mat g⁻¹ *ᵥ w) := by
          rw [mat_mulVec_inv]
          abel
        rw [e]
        exact Submodule.neg_mem _ (h₁ _ hw') }
  have hQ₁ : Q₁ F ≤ K := fun g hg => ⟨fixer_le_stab _ hg,
    fixer_le_stab _ (fixer_antitone pt₀_le_ln₀ hg), fun w _ => by
      have := sub_mem_perp_of_mem_fixer hg w
      rwa [isLine_ln₀.perp_eq] at this⟩
  have hQ₂ : Q₂ F ≤ K := fun g hg => ⟨sylS_le_P₁ (Q₂_le_sylS hg), Q₂_le_P₂ hg,
    fun w hw => pt₀_le_ln₀ ((mem_qPoint.1 hg).2 w hw)⟩
  rw [← Q₁_sup_Q₂] at hs
  exact (sup_le hQ₁ hQ₂ hs).2.2 v hv

variable [CharP F 2]

theorem commutator_commutator_sylS : ⁅⁅sylS F, sylS F⁆, sylS F⁆ = ⊥ := by
  rw [← Q₁_sup_Q₂]
  refine commutator_commutator_eq_bot_of_sup (fun a ha a' ha' => Q₁_comm ha ha')
    (fun b hb b' hb' => Q₂_comm hb hb') ?_ ?_
  · rw [Q₁_sup_Q₂]
    exact sylS_le_P₁.trans P₁_le_normalizer_Q₁
  · rw [Q₁_sup_Q₂]
    exact sylS_le_P₂.trans P₂_le_normalizer_Q₂

end Standard

theorem qPoint_comm [CharP F 2] {p : Submodule F (V4 F)} (hp : IsPoint p) {x y : Sp4 F}
    (hx : x ∈ qPoint p) (hy : y ∈ qPoint p) : x * y = y * x := by
  obtain ⟨g, rfl⟩ := exists_map_pt₀_eq hp
  rw [qPoint_map_eq] at hx hy
  have h := Q₂_comm (mem_map_conj.1 hx) (mem_map_conj.1 hy)
  calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    _ = y * x := by group

section Flag

variable [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem mulVec_conj (g s : Sp4 F) (w : V4 F) :
    mat (g * s * g⁻¹) *ᵥ (mat g *ᵥ w) = mat g *ᵥ (mat s *ᵥ w) := by
  rw [mat_mul_mulVec, mat_mul_mulVec, mat_inv_mulVec]

theorem exists_flag_of_isPGroup {H : Subgroup (Sp4 F)} (hH : IsPGroup 2 H) :
    ∃ p l : Submodule F (V4 F), IsPoint p ∧ IsLine l ∧ p ≤ l ∧
      (∀ s ∈ H, ∀ w ∈ p, mat s *ᵥ w = w) ∧ (∀ s ∈ H, ∀ w ∈ perp p, mat s *ᵥ w - w ∈ l) ∧
      (∀ s ∈ H, ∀ w ∈ l, mat s *ᵥ w - w ∈ p) ∧ ⁅⁅H, H⁆, H⁆ = ⊥ := by
  obtain ⟨S, hS⟩ := hH.exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := exists_sylow_sylS (F := F)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Sp4 F) S₀ S
  have hgS : (sylS F).map (MulAut.conj g).toMonoidHom = S := by
    rw [← hg, ← hS₀]
    rfl
  have hHS : H ≤ (sylS F).map (MulAut.conj g).toMonoidHom := hgS ▸ hS
  have hs : ∀ s ∈ H, ∃ s₀ ∈ sylS F, s = g * s₀ * g⁻¹ := fun s hs' =>
    ⟨g⁻¹ * s * g, mem_map_conj.1 (hHS hs'), by group⟩
  have hw : ∀ (W : Submodule F (V4 F)) (w : V4 F), w ∈ W.map (mulVecLin (mat g)) →
      ∃ w₀ ∈ W, w = mat g *ᵥ w₀ := fun W w hw' =>
    ⟨mat g⁻¹ *ᵥ w, mem_map_mulVecLin.1 hw', (mat_mulVec_inv g w).symm⟩
  refine ⟨(pt₀ F).map (mulVecLin (mat g)), (ln₀ F).map (mulVecLin (mat g)), ?_,
    isLine_map isLine_ln₀ g, Submodule.map_mono pt₀_le_ln₀, ?_, ?_, ?_, ?_⟩
  · show Module.finrank F _ = 1
    rw [← (Submodule.equivMapOfInjective _ (mulVec_mat_injective g) (pt₀ F)).finrank_eq]
    exact isPoint_pt₀
  · intro s hs' w hw'
    obtain ⟨s₀, hs₀, rfl⟩ := hs s hs'
    obtain ⟨w₀, hw₀, rfl⟩ := hw _ w hw'
    rw [mulVec_conj]
    have : w₀ ∈ fixSp (sylS F) := by rw [fixSp_sylS]; exact hw₀
    rw [mem_fixSp.1 this s₀ hs₀]
  · intro s hs' w hw'
    rw [perp_map] at hw'
    obtain ⟨s₀, hs₀, rfl⟩ := hs s hs'
    obtain ⟨w₀, hw₀, rfl⟩ := hw _ w hw'
    rw [mulVec_conj, ← mulVec_sub]
    exact Submodule.mem_map_of_mem (sub_mem_ln₀_of_mem_sylS hs₀ hw₀)
  · intro s hs' w hw'
    obtain ⟨s₀, hs₀, rfl⟩ := hs s hs'
    obtain ⟨w₀, hw₀, rfl⟩ := hw _ w hw'
    rw [mulVec_conj, ← mulVec_sub]
    exact Submodule.mem_map_of_mem (sub_mem_pt₀_of_mem_sylS hs₀ hw₀)
  · refine eq_bot_iff.2 ((Subgroup.commutator_mono (Subgroup.commutator_mono hHS hHS) hHS).trans ?_)
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, commutator_commutator_sylS,
      Subgroup.map_bot]

end Flag

section Siegel

variable [CharP F 2]

@[expose] noncomputable def siegel (v w : V4 F) : Sp4 F :=
  transv (v + w) 1 * transv v 1 * transv w 1

theorem siegel_mulVec {v w : V4 F} (hvw : form F v w = 0) (x : V4 F) :
    mat (siegel v w) *ᵥ x = x + form F v x • w + form F w x • v := by
  have hwv : form F w v = 0 := by rw [form_swap, hvw, neg_zero]
  rw [siegel, mat_mul_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, transv_mulVec]
  simp only [one_mul, map_add, map_smul, LinearMap.add_apply, smul_eq_mul, form_self, hvw, hwv,
    mul_zero, add_zero]
  have h2 : ∀ (a : F) (u : V4 F), a • u + a • u = 0 := fun a u => by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  rw [add_smul, smul_add, smul_add]
  calc x + form F w x • w + form F v x • v +
        (form F v x • v + form F v x • w + (form F w x • v + form F w x • w)) =
      x + form F v x • w + form F w x • v + (form F v x • v + form F v x • v) +
        (form F w x • w + form F w x • w) := by abel
    _ = x + form F v x • w + form F w x • v := by rw [h2, h2, add_zero, add_zero]

theorem siegel_mem_qPoint {v w : V4 F} (hvw : form F v w = 0) : siegel v w ∈ qPoint (F ∙ v) := by
  have hwv : form F w v = 0 := by rw [form_swap, hvw, neg_zero]
  refine mem_qPoint.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [siegel_mulVec hvw, map_smul, map_smul, smul_eq_mul, smul_eq_mul, form_self, hwv,
      mul_zero, zero_smul, zero_smul, add_zero, add_zero]
  · rw [siegel_mulVec hvw, mem_perp_span.1 hy, zero_smul, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

omit [CharP F 2] in
theorem siegel_conj (g : Sp4 F) (v w : V4 F) :
    g * siegel v w * g⁻¹ = siegel (mat g *ᵥ v) (mat g *ᵥ w) := by
  have e : g * siegel v w * g⁻¹ = (g * transv (v + w) 1 * g⁻¹) * (g * transv v 1 * g⁻¹) *
      (g * transv w 1 * g⁻¹) := by
    rw [siegel]
    group
  rw [e, transv_conj, transv_conj, transv_conj, mulVec_add, siegel]

theorem mem_qPoint_of_commutator_mem {v : V4 F} (hv : v ≠ 0) {g : Sp4 F}
    (hgv : mat g *ᵥ v = v)
    (hc : ∀ w ∈ perp (F ∙ v), g * siegel v w * g⁻¹ * (siegel v w)⁻¹ ∈ xPoint (F ∙ v)) :
    g ∈ qPoint (F ∙ v) := by
  refine mem_qPoint.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [mulVec_smul, hgv]
  have hvy : form F v y = 0 := mem_perp_span.1 hy
  have hvgy : form F v (mat g *ᵥ y) = 0 := by
    rw [← hgv, form_mat]
    exact hvy
  rw [← perp_perp (F ∙ v), mem_perp]
  intro x hx
  have hvx : form F v x = 0 := mem_perp_span.1 hx
  have h1 := hc y hy
  rw [siegel_conj, hgv] at h1
  have hx' : mat (siegel v y) *ᵥ x ∈ perp (F ∙ v) := by
    rw [mem_perp_span, siegel_mulVec hvy, map_add, map_add, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul, hvx, hvy, form_self, mul_zero, mul_zero, add_zero, add_zero]
  have h2 := mem_fixer.1 h1 _ hx'
  rw [mat_mul_mulVec, mat_inv_mulVec, siegel_mulVec hvgy, siegel_mulVec hvy, hvx] at h2
  simp only [zero_smul, add_zero, add_right_inj] at h2
  have h3 : form F (mat g *ᵥ y) x = form F y x := smul_left_injective F hv h2
  rw [form_swap, map_sub, LinearMap.sub_apply, h3, sub_self, neg_zero]

end Siegel


end CFSG.Quasithin.MS93.S36SP
