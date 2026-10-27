module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Tr
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL5Vertex

public section

namespace CFSG.Quasithin.F6.GoldAmL5

open CFSG.Quasithin.F6.GoldAmL4

variable {D E : Type*} [Group D] [Group E]

structure MConj (a b s ρ y : E) : Prop where
  hy : y ^ 3 = 1
  hyc : y⁻¹ * (a * b) * y = a * a * s * ρ
  hyp : y⁻¹ * (a * a) * y = a * b⁻¹ * ρ
  hyq : y⁻¹ * s * y = ρ
  hyr : y⁻¹ * ρ * y = s * ρ

structure MRelB (a b s ρ y : E) : Prop extends MConj a b s ρ y where
  hyt : y * (a * ρ) * y = a * ρ

section Rel

variable {a b s x y ρ : E}

theorem embR_cR (hT : TRel a b s) (hR : RhoRel a b s ρ) : embR hT hR cR = a * b := by
  rw [embR_apply]
  have h : toTc cR = tC := rfl
  have hf : cR.f = 0 := rfl
  rw [h, hT.emb_tC, hf]
  simp

theorem embR_pR (hT : TRel a b s) (hR : RhoRel a b s ρ) : embR hT hR pR = a * a := by
  rw [embR_apply]
  have h : toTc pR = tP := rfl
  have hf : pR.f = 0 := rfl
  rw [h, hT.emb_tP, hf]
  simp

theorem embR_alpha1 (hT : TRel a b s) (hR : RhoRel a b s ρ) :
    embR hT hR alpha5.1 = a * a * s * ρ := by
  rw [embR_apply]
  have h : toTc alpha5.1 = tA * tA * tS := rfl
  have hf : alpha5.1.f = 1 := rfl
  rw [h, hf, map_mul, map_mul, hT.emb_tA, hT.emb_tS]
  simp

theorem embR_alpha2 (hT : TRel a b s) (hR : RhoRel a b s ρ) :
    embR hT hR alpha5.2.1 = a * b⁻¹ * ρ := by
  rw [embR_apply]
  have h : toTc alpha5.2.1 = tA * tB⁻¹ := rfl
  have hf : alpha5.2.1.f = 1 := rfl
  rw [h, hf, map_mul, map_inv, hT.emb_tA, hT.emb_tB]
  simp

theorem embR_alpha3 (hT : TRel a b s) (hR : RhoRel a b s ρ) :
    embR hT hR alpha5.2.2.1 = ρ := by
  rw [embR_apply]
  have h : toTc alpha5.2.2.1 = 1 := rfl
  have hf : alpha5.2.2.1.f = 1 := rfl
  rw [h, hf, map_one]
  simp

theorem embR_alpha4 (hT : TRel a b s) (hR : RhoRel a b s ρ) :
    embR hT hR alpha5.2.2.2 = s * ρ := by
  rw [embR_apply]
  have h : toTc alpha5.2.2.2 = tS := rfl
  have hf : alpha5.2.2.2.f = 1 := rfl
  rw [h, hf, hT.emb_tS]
  simp

theorem embR_rT0 (hT : TRel a b s) (hR : RhoRel a b s ρ) : embR hT hR rT0 = a * ρ := by
  rw [embR_apply]
  have h : toTc rT0 = tA := rfl
  have hf : rT0.f = 1 := rfl
  rw [h, hf, hT.emb_tA]
  simp

theorem not_mem_range_of_cube (hT : TRel a b s) (hR : RhoRel a b s ρ) {z : E} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : z ∉ (embR hT hR).range := by
  rintro ⟨w, rfl⟩
  apply hz1
  have h8 : (embR hT hR w) ^ 8 = 1 := by rw [← map_pow, tr_pow8, map_one]
  calc embR hT hR w = (embR hT hR w) ^ 9 * ((embR hT hR w) ^ 8)⁻¹ := by group
    _ = 1 := by
      rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hz3, one_pow, h8]
      simp

theorem MConj.conj_embR (hT : TRel a b s) (hR : RhoRel a b s ρ) (h : MConj a b s ρ y) (w : Tr)
    (hw : inQ2 w) : y⁻¹ * embR hT hR w * y = embR hT hR (Fq alpha5 w) := by
  let κ : E →* E := (MulAut.conj y⁻¹).toMonoidHom
  have hκ : ∀ g, κ g = y⁻¹ * g * y := fun g => by
    show y⁻¹ * g * y⁻¹⁻¹ = _
    rw [inv_inv]
  have key := conj_Fq (embR hT hR) κ alpha5
    (by rw [hκ, embR_cR, embR_alpha1]; exact h.hyc)
    (by rw [hκ, embR_pR, embR_alpha2]; exact h.hyp)
    (by rw [hκ, embR_rS, embR_alpha3]; exact h.hyq)
    (by rw [hκ, embR_rR, embR_alpha4]; exact h.hyr) w hw
  rw [hκ] at key
  exact key

theorem MConj.ne_one (hT : TRel a b s) (hR : RhoRel a b s ρ) (h : MConj a b s ρ y)
    (hinj : Function.Injective (embR hT hR)) : y ≠ 1 := by
  intro hy
  have h1 := h.hyq
  rw [hy] at h1
  simp only [inv_one, one_mul, mul_one] at h1
  apply rS_ne_rR
  apply hinj
  rw [embR_rS, embR_rR]
  exact h1

theorem MRelB.vertexSpec (hT : TRel a b s) (hR : RhoRel a b s ρ) (h : MRelB a b s ρ y)
    (hinj : Function.Injective (embR hT hR)) :
    VertexSpecG (embR hT hR) Q2r rT0 y (Fq alpha5) rT0 rT0 where
  y_cube := h.hy
  y_not_mem := not_mem_range_of_cube hT hR h.hy (h.toMConj.ne_one hT hR hinj)
  act_mem := fun w hw => alpha5_mem w hw
  conj := fun w hw => h.toMConj.conj_embR hT hR w hw
  t₁ := by rw [embR_rT0]; exact h.hyt
  t₂ := by
    rw [embR_rT0]
    calc y⁻¹ * (a * ρ) * y⁻¹ = y⁻¹ * (y * (a * ρ) * y) * y⁻¹ := by rw [h.hyt]
      _ = a * ρ := by group

theorem aRho_comm (hAρ : ARho a b s x ρ) : ρ * x = x * ρ := by
  calc ρ * x = ρ * x * (ρ * ρ) := by rw [hAρ.hρ, mul_one]
    _ = (ρ * x * ρ) * ρ := by group
    _ = x * ρ := by rw [hAρ.hρx]

theorem aRho_conj_embR (hA : ARel a b s x) (hAρ : ARho a b s x ρ) (w : Tr) (hw : inQ1 w) :
    x⁻¹ * embR hA.toTRel hAρ.toRhoRel w * x = embR hA.toTRel hAρ.toRhoRel (actA w) := by
  have hbase : toTc w ∈ baseSub := mem_baseSub.mpr hw
  have h1 := hA.conj_emb (toTc w) hbase
  have hρx : x⁻¹ * ρ ^ w.f.val * x = ρ ^ w.f.val := by
    have hc : Commute x (ρ ^ w.f.val) := ((show Commute ρ x from aRho_comm hAρ).symm).pow_right _
    calc x⁻¹ * ρ ^ w.f.val * x = x⁻¹ * (ρ ^ w.f.val * x) := by group
      _ = x⁻¹ * (x * ρ ^ w.f.val) := by rw [← hc.eq]
      _ = ρ ^ w.f.val := by group
  have e : toTc (actA w) = xAct (toTc w) := rfl
  have hf : (actA w).f = w.f := rfl
  rw [embR_apply, embR_apply, e, hf, ← h1]
  calc x⁻¹ * (hA.toTRel.emb (toTc w) * ρ ^ w.f.val) * x
      = (x⁻¹ * hA.toTRel.emb (toTc w) * x) * (x⁻¹ * ρ ^ w.f.val * x) := by group
    _ = (x⁻¹ * hA.toTRel.emb (toTc w) * x) * ρ ^ w.f.val := by rw [hρx]

theorem aRho_vertexSpec (hA : ARel a b s x) (hAρ : ARho a b s x ρ)
    (hinj : Function.Injective (embR hA.toTRel hAρ.toRhoRel)) :
    VertexSpecG (embR hA.toTRel hAρ.toRhoRel) Q1r rS x actA rS rS where
  y_cube := hA.hx
  y_not_mem := by
    refine not_mem_range_of_cube hA.toTRel hAρ.toRhoRel hA.hx ?_
    intro hx1
    have h1 := hA.hxa
    rw [hx1] at h1
    simp only [inv_one, one_mul, mul_one] at h1
    apply rA_ne_rB
    apply hinj
    rw [embR_rA, embR_rB]
    exact h1
  act_mem := fun w _ => actA_Q1 w
  conj := fun w hw => aRho_conj_embR hA hAρ w hw
  t₁ := by rw [embR_rS]; exact hA.hxs
  t₂ := by
    rw [embR_rS]
    calc x⁻¹ * s * x⁻¹ = x⁻¹ * (x * s * x) * x⁻¹ := by rw [hA.hxs]
      _ = s := by group

end Rel

theorem Q1_or' : ∀ w : Tr, w ∈ Q1r ∨ w * rS⁻¹ ∈ Q1r := Q1_or

theorem Q2_or' : ∀ w : Tr, w ∈ Q2r ∨ w * rT0⁻¹ ∈ Q2r := Q2_or

theorem closure_range_union_R {a b s ρ : D} (hT : TRel a b s) (hR : RhoRel a b s ρ) (y : D) :
    Subgroup.closure (((embR hT hR).range : Set D) ∪ {y}) =
      Subgroup.closure ({a, b, s, ρ, y} : Set D) := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, embR_range hT hR, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem isAmalgamIso_of_tuples5 {a b s x y ρ : D} {a' b' s' x' y' ρ' : E}
    (hA : ARel a b s x) (hAρ : ARho a b s x ρ) (hB : MRelB a b s ρ y)
    (hA' : ARel a' b' s' x') (hAρ' : ARho a' b' s' x' ρ') (hB' : MRelB a' b' s' ρ' y')
    (hcard : Nat.card (Subgroup.closure ({a, b, s, ρ} : Set D)) = 64)
    (hcard' : Nat.card (Subgroup.closure ({a', b', s', ρ'} : Set E)) = 64)
    (hinf : Subgroup.closure ({a, b, s, ρ, y} : Set D) ⊓
      Subgroup.closure ({a, b, s, ρ, x} : Set D) = Subgroup.closure ({a, b, s, ρ} : Set D))
    (hinf' : Subgroup.closure ({a', b', s', ρ', y'} : Set E) ⊓
      Subgroup.closure ({a', b', s', ρ', x'} : Set E) =
        Subgroup.closure ({a', b', s', ρ'} : Set E)) :
    CFSG.Quasithin.F6.IsAmalgamIso (Subgroup.closure ({a, b, s, ρ, y} : Set D))
      (Subgroup.closure ({a, b, s, ρ, x} : Set D)) (Subgroup.closure ({a', b', s', ρ', y'} : Set E))
      (Subgroup.closure ({a', b', s', ρ', x'} : Set E)) := by
  have hT := hA.toTRel
  have hT' := hA'.toTRel
  have hR := hAρ.toRhoRel
  have hR' := hAρ'.toRhoRel
  have hinj := embR_injective hT hR hcard
  have hinj' := embR_injective hT' hR' hcard'
  have eB := closure_range_union_R hT hR y
  have eA := closure_range_union_R hT hR x
  have eB' := closure_range_union_R hT' hR' y'
  have eA' := closure_range_union_R hT' hR' x'
  have hT1 : Subgroup.closure ({a, b, s, ρ} : Set D) = (embR hT hR).range :=
    (embR_range hT hR).symm
  have hT1' : Subgroup.closure ({a', b', s', ρ'} : Set E) = (embR hT' hR').range :=
    (embR_range hT' hR').symm
  rw [← eB, ← eA, ← eB', ← eA']
  rw [← eB, ← eA, hT1] at hinf
  rw [← eB', ← eA', hT1'] at hinf'
  exact isAmalgamIso_of_specs hinj hinj' Q2_or' Q1_or' (hB.vertexSpec hT hR hinj)
    (hB'.vertexSpec hT' hR' hinj') (aRho_vertexSpec hA hAρ hinj) (aRho_vertexSpec hA' hAρ' hinj')
    hinf hinf'

end CFSG.Quasithin.F6.GoldAmL5
