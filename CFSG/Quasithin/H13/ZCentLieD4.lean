module

public import CFSG.Quasithin.H13.ZCentLieCore
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Bruhat
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.SylowCenters
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native

public section

namespace CFSG.Quasithin.H13.ZCentLie

open CFSG.LocalAnalysis.EvenBN.TrialityD4 Subgroup
open scoped Pointwise

theorem wordAct_five_eq :
    ∀ k : Fin 12, wordAct (weylList k) (false, 5) = (false, 5) → k = 0 ∨ k = 1 := by
  decide

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem rootGroup_inf_eq_bot {i j : Fin 6} (hij : i ≠ j) :
    d.rootGroup i ⊓ d.rootGroup j = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hi, hj⟩
  have h3 : g ∈ d.boxProd (fun l => decide (l = i) && decide (l = j)) := by
    rw [← d.boxProd_inter]
    exact ⟨d.coe_rootGroup_subset_boxProd i hi, d.coe_rootGroup_subset_boxProd j hj⟩
  have hfalse : (fun l : Fin 6 => decide (l = i) && decide (l = j)) = fun _ => false := by
    funext l
    by_cases h : l = i
    · subst h
      simp [hij]
    · simp [h]
  rw [hfalse, d.boxProd_false] at h3
  rw [Set.mem_singleton_iff.1 h3]
  exact one_mem _

theorem conj_w₀_rootGroup_inf_S (j : Fin 6) : (MulAut.conj d.w₀ • d.rootGroup j) ⊓ d.S = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  have h1 : g ∈ d.conjB d.w₀ ⊓ d.S := by
    refine ⟨?_, (Subgroup.mem_inf.1 hg).2⟩
    change g ∈ MulAut.conj d.w₀⁻¹ • d.B
    rw [TrialityD4Data.mem_conj_inv_smul]
    have h2 : g ∈ MulAut.conj d.w₀ • d.rootGroup j := (Subgroup.mem_inf.1 hg).1
    rw [mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
      inv_inv] at h2
    have hw : d.w₀⁻¹ = d.w₀ := inv_eq_of_mul_eq_one_right d.w₀_mul_self
    rw [hw] at h2
    rw [hw]
    exact (le_sup_left : d.S ≤ d.B) (d.rootGroup_le_S j h2)
  rwa [d.conjB_w₀_inf_S_eq_bot] at h1

theorem commute_x₆ {g : X} {c₀ : d.Γ₀} (hc₀ : c₀ ≠ 0) (hg : g * d.x₆ c₀ = d.x₆ c₀ * g)
    (c : d.Γ₀) : g * d.x₆ c = d.x₆ c * g := by
  obtain ⟨x, hx, h, hh, w, hw, y, hy, rfl⟩ := d.exists_bruhat_normal_form g
  have hyS : y ∈ d.S := d.Uminus_le_S w hy
  have hcent : ∀ s ∈ d.S, ∀ a, s * d.x₆ a = d.x₆ a * s := fun s hs a =>
    (mem_centralizer_iff.1 (d.S_le_centralizer_V hs) _ ⟨a, rfl⟩).symm
  obtain ⟨t, rfl⟩ := hh
  have hTw : d.torus t * w * d.x₆ c₀ = d.x₆ c₀ * (d.torus t * w) := by
    have e1 : x * d.torus t * w * y * d.x₆ c₀ = x * (d.torus t * w * d.x₆ c₀) * y := by
      rw [mul_assoc (x * d.torus t * w), hcent y hyS]
      group
    have e2 : d.x₆ c₀ * (x * d.torus t * w * y) = x * (d.x₆ c₀ * (d.torus t * w)) * y := by
      calc d.x₆ c₀ * (x * d.torus t * w * y) = (d.x₆ c₀ * x) * (d.torus t * w) * y := by group
        _ = (x * d.x₆ c₀) * (d.torus t * w) * y := by rw [hcent x hx c₀]
        _ = x * (d.x₆ c₀ * (d.torus t * w)) * y := by group
    rw [e1, e2] at hg
    exact mul_left_cancel (mul_right_cancel hg)
  obtain ⟨k, rfl⟩ := d.exists_weylWord_eq hw
  have hmem6 : d.weylWord k * d.x₆ c₀ * (d.weylWord k)⁻¹ ∈ d.rootGroup 5 := by
    have e : d.weylWord k * d.x₆ c₀ * (d.weylWord k)⁻¹ =
        d.torus t⁻¹ * d.x₆ c₀ * (d.torus t⁻¹)⁻¹ := by
      rw [map_inv, inv_inv]
      calc d.weylWord k * d.x₆ c₀ * (d.weylWord k)⁻¹ =
          (d.torus t)⁻¹ * ((d.torus t * d.weylWord k) * d.x₆ c₀) * (d.weylWord k)⁻¹ := by
            group
        _ = (d.torus t)⁻¹ * (d.x₆ c₀ * (d.torus t * d.weylWord k)) * (d.weylWord k)⁻¹ := by
            rw [hTw]
        _ = (d.torus t)⁻¹ * d.x₆ c₀ * d.torus t := by group
    rw [e, d.torus_x₆]
    show _ ∈ d.U₆
    exact ⟨_, rfl⟩
  have hne1 : d.weylWord k * d.x₆ c₀ * (d.weylWord k)⁻¹ ≠ 1 := by
    intro h1
    apply hc₀
    apply d.x₆_injective
    rw [d.x₆_zero]
    calc d.x₆ c₀ = (d.weylWord k)⁻¹ * (d.weylWord k * d.x₆ c₀ * (d.weylWord k)⁻¹) *
        d.weylWord k := by group
      _ = 1 := by rw [h1]; group
  have hconj : d.weylWord k * d.x₆ c₀ * (d.weylWord k)⁻¹ ∈
      d.signedRootGroup (wordAct (weylList k) (false, 5)) := by
    rw [← d.smul_rootGroup_weylWord]
    exact ⟨d.x₆ c₀, (show d.x₆ c₀ ∈ d.U₆ from ⟨c₀, rfl⟩), rfl⟩
  have hk : k = 0 ∨ k = 1 := by
    rcases hr : wordAct (weylList k) (false, 5) with ⟨b, j⟩
    rw [hr] at hconj
    cases b with
    | false =>
      by_cases hj : j = 5
      · subst hj
        exact wordAct_five_eq k hr
      · exfalso
        have h1 : d.weylWord k * d.x₆ c₀ * (d.weylWord k)⁻¹ ∈ d.rootGroup j ⊓ d.rootGroup 5 :=
          ⟨hconj, hmem6⟩
        rw [rootGroup_inf_eq_bot d hj, mem_bot] at h1
        exact hne1 h1
    | true =>
      exfalso
      have h1 : d.weylWord k * d.x₆ c₀ * (d.weylWord k)⁻¹ ∈
          (MulAut.conj d.w₀ • d.rootGroup j) ⊓ d.S := ⟨hconj, d.rootGroup_le_S 5 hmem6⟩
      rw [conj_w₀_rootGroup_inf_S d, mem_bot] at h1
      exact hne1 h1
  have hwx : ∀ a, d.weylWord k * d.x₆ a = d.x₆ a * d.weylWord k := by
    intro a
    rcases hk with rfl | rfl
    · have h0 : d.weylWord 0 = 1 := by
        simp [TrialityD4Data.weylWord, TrialityD4Data.word, weylList]
      rw [h0, one_mul, mul_one]
    · have h1 : d.weylWord 1 = d.u := by
        simp [TrialityD4Data.weylWord, TrialityD4Data.word, weylList, TrialityD4Data.gen]
      rw [h1]
      calc d.u * d.x₆ a = d.u * d.x₆ a * d.u * d.u := by
            rw [mul_assoc (d.u * d.x₆ a), d.u_mul_self, mul_one]
        _ = d.x₆ a * d.u := by rw [d.u_x₆]
  have hT : d.torus t * d.x₆ c₀ = d.x₆ c₀ * d.torus t := by
    have h1 := hTw
    rw [mul_assoc, hwx c₀, ← mul_assoc, ← mul_assoc] at h1
    exact mul_right_cancel h1
  have hTa : ∀ a, d.torus t * d.x₆ a = d.x₆ a * d.torus t := by
    have h1 := d.torus_x₆ t c₀
    rw [hT, mul_inv_cancel_right] at h1
    have h2 := d.x₆_injective h1
    have hχ1 : ((t.1 : d.Γ₀) * t.1 * fixedNorm d.σ_cube (t.2 : d.Γ)) = 1 :=
      mul_right_cancel₀ hc₀ (h2.symm.trans (one_mul c₀).symm)
    intro a
    have h3 := d.torus_x₆ t a
    rw [hχ1, one_mul] at h3
    exact mul_inv_eq_iff_eq_mul.1 h3
  calc x * d.torus t * d.weylWord k * y * d.x₆ c =
      x * d.torus t * d.weylWord k * (y * d.x₆ c) := by group
    _ = x * d.torus t * d.weylWord k * (d.x₆ c * y) := by rw [hcent y hyS]
    _ = x * d.torus t * (d.weylWord k * d.x₆ c) * y := by group
    _ = x * d.torus t * (d.x₆ c * d.weylWord k) * y := by rw [hwx]
    _ = x * (d.torus t * d.x₆ c) * d.weylWord k * y := by group
    _ = x * (d.x₆ c * d.torus t) * d.weylWord k * y := by rw [hTa]
    _ = x * d.x₆ c * d.torus t * d.weylWord k * y := by group
    _ = d.x₆ c * x * d.torus t * d.weylWord k * y := by rw [hcent x hx]
    _ = d.x₆ c * (x * d.torus t * d.weylWord k * y) := by group

theorem zCentAt_trialityD4 : ZCentAt d.S := by
  intro u w k hu hcu hu1 hw hcw hk
  have hV : ∀ z ∈ d.S, (∀ t ∈ d.S, z * t = t * z) → z ∈ d.V := fun z hz hzc => by
    rw [← d.S_inf_centralizer_S]
    exact ⟨hz, mem_centralizer_iff.2 fun t ht => (hzc t ht).symm⟩
  obtain ⟨c₀, rfl⟩ := hV u hu hcu
  obtain ⟨c, rfl⟩ := hV w hw hcw
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    exact hu1 d.x₆_zero
  exact commute_x₆ d hc₀ hk c

theorem zCentAt_sylow_of_trialityD4
    {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hf : 1 ≤ f)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel Y .trialityD4 2 f) (P : Sylow 2 Y) :
    ZCentAt (P : Subgroup Y) := by
  obtain ⟨d'⟩ := nonempty_trialityD4Data_of_lieModel hf (Or.inr (Or.inl ⟨rfl, by decide, h⟩))
  obtain ⟨⟨P₀, hP₀⟩, -⟩ := d'.yamada_3_1
  refine zCentAt_sylow (P₀ := P₀) ?_ P
  rw [hP₀]
  exact zCentAt_trialityD4 d'

end CFSG.Quasithin.H13.ZCentLie
