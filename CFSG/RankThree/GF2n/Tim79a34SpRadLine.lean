module

public import CFSG.RankThree.GF2n.Tim79a34SpRad

import CFSG.LinearAlgebra.SpanUnionExtraction
import CFSG.Timmesfeld.LocalTwoSubgroups.CoprimeActionBounds
public import CFSG.Timmesfeld.Transvection.AssembleRel

public section

namespace CFSG.RankThree.GF2n.Tim79a

open scoped Matrix Pointwise
open Matrix Module
open CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic

section Field

variable {n : ℕ} {F : Type} [Field F]

theorem spFormL_injective : Function.Injective (spFormL (n := n) (K := F)) := by
  intro u v h
  by_contra hne
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero (sub_ne_zero.mpr hne)
  apply hy
  have huy : spForm u y = spForm v y := congrFun (congrArg DFunLike.coe h) y
  rw [spForm_sub_left, huy, sub_self]

theorem exists_eq_smul_add_smul_of_forall_spForm {a u₀ u : Fin n ⊕ Fin n → F}
    (h : ∀ x, spForm a x = 0 → spForm u₀ x = 0 → spForm u x = 0) :
    ∃ μ ν : F, u = μ • u₀ + ν • a := by
  let L : Fin 2 → (Fin n ⊕ Fin n → F) →ₗ[F] F := fun i => if i = 0 then spFormL a else spFormL u₀
  have hker : ⨅ i, LinearMap.ker (L i) ≤ LinearMap.ker (spFormL u) := by
    intro x hx
    rw [Submodule.mem_iInf] at hx
    have h0 : spForm a x = 0 := by
      have := hx 0
      rwa [show L 0 = spFormL a by simp [L]] at this
    have h1 : spForm u₀ x = 0 := by
      have := hx 1
      rwa [show L 1 = spFormL u₀ by simp [L]] at this
    exact h x h0 h1
  have hmem : spFormL u ∈ Submodule.span F (Set.range L) :=
    mem_span_of_iInf_ker_le_ker hker
  have hrange : (Set.range L) = ({spFormL a, spFormL u₀} : Set ((Fin n ⊕ Fin n → F) →ₗ[F] F)) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · simp [L]
      · simp [L]
    · intro hf
      rcases hf with hf | hf
      · exact ⟨0, by rw [show L 0 = spFormL a by simp [L]]; exact hf.symm⟩
      · exact ⟨1, by rw [show L 1 = spFormL u₀ by simp [L]]; exact hf.symm⟩
  obtain ⟨α, β, hαβ⟩ := (Submodule.mem_span_pair (R := F)).1 (by rwa [hrange] at hmem)
  refine ⟨β, α, spFormL_injective ?_⟩
  refine LinearMap.ext fun x => ?_
  have hx : α * spForm a x + β * spForm u₀ x = spForm u x := by
    simpa [spFormL] using LinearMap.congr_fun hαβ x
  change spForm u x = spForm (β • u₀ + α • a) x
  rw [spForm_add_left, spForm_smul_left', spForm_smul_left']
  rw [← hx]
  abel

end Field

section CharTwo

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem spForm_eq_zero_of_param {a u : Fin n ⊕ Fin n → F} {g : StatedSp n F}
    (hg : g ∈ spRad a) {c : F}
    (h : ∀ x, SpExtras.mat n F g *ᵥ x = x + spForm a x • u +
      spForm u x • a + (c * spForm a x) • a) : spForm a u = 0 := by
  by_cases ha : a = 0
  · rw [ha, spForm_zero_left]
  · obtain ⟨b, hb⟩ := exists_spForm_eq_one ha
    have hga : SpExtras.mat n F g *ᵥ a = a := hg.1
    have h1 : spForm a (SpExtras.mat n F g *ᵥ b) = spForm a b := by
      have := spForm_mat_mulVec g a b
      rwa [hga] at this
    have h2 : spForm a (SpExtras.mat n F g *ᵥ b) =
        spForm a b + spForm a b * spForm a u := by
      rw [h b]
      simp [spForm_add_right, spForm_smul_right', spForm_self]
    have hzero : spForm a b * spForm a u = 0 := by
      have h := h2.symm.trans h1
      have h' : spForm a b + spForm a b * spForm a u = spForm a b + 0 := by
        rw [add_zero]
        exact h
      exact add_left_cancel h'
    simpa [hb] using hzero

@[expose] def spRadLine (a w : Fin n ⊕ Fin n → F) : Subgroup (StatedSp n F) where
  carrier := {g | g ∈ spRad a ∧ ∃ μ c : F, ∀ x : Fin n ⊕ Fin n → F,
    SpExtras.mat n F g *ᵥ x = x + spForm a x • (μ • w) + spForm (μ • w) x • a +
      (c * spForm a x) • a}
  mul_mem' := by
    rintro g h ⟨hg, μ, c, hgx⟩ ⟨hh, μ', c', hhx⟩
    obtain ⟨hu, hu'⟩ := spForm_eq_zero_of_param hg hgx, spForm_eq_zero_of_param hh hhx
    refine ⟨(spRad a).mul_mem hg hh, μ + μ', c + c' + spForm (μ • w) (μ' • w), fun x => ?_⟩
    rw [mat_mul_mulVec_of_param hu hu' hgx hhx, add_smul]
  one_mem' := by
    refine ⟨(spRad a).one_mem, 0, 0, fun x => ?_⟩
    rw [map_one, Matrix.one_mulVec]
    simp
  inv_mem' := by
    rintro g ⟨hg, μ, c, hgx⟩
    have hu : spForm a (μ • w) = 0 := spForm_eq_zero_of_param hg hgx
    have hgg : g * g = 1 := by
      refine eq_of_mat_mulVec_eq fun x => ?_
      rw [mat_mul_mulVec_of_param hu hu hgx hgx, map_one, Matrix.one_mulVec,
        vec_add_self, spForm_self, CharTwo.add_self_eq_zero]
      simp
    have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
    exact ⟨(spRad a).inv_mem hg, μ, c, by rw [hinv]; exact hgx⟩

theorem mem_spRadLine {a w : Fin n ⊕ Fin n → F} {g : StatedSp n F} :
    g ∈ spRadLine a w ↔ g ∈ spRad a ∧ ∃ μ c : F, ∀ x : Fin n ⊕ Fin n → F,
      SpExtras.mat n F g *ᵥ x = x + spForm a x • (μ • w) + spForm (μ • w) x • a +
        (c * spForm a x) • a :=
  Iff.rfl

theorem le_spRadLine_of_isTransGroup {a w : Fin n ⊕ Fin n → F}
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) : T ≤ spRadLine a w := by
  intro t ht
  obtain ⟨c, hc⟩ := (hT.1 t).1 ht
  refine ⟨le_spRad_of_isTransGroup hT ht, 0, c, fun x => ?_⟩
  rw [hc, spTrans_mulVec]
  simp

end CharTwo

section Cardinal

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem spRadLine_card [Finite F] {a w : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    (hw : spForm a w = 0) (hwa : ∀ μ : F, w ≠ μ • a) :
    Nat.card ↥(spRadLine a w) = Nat.card F ^ 2 := by
  let hu : ∀ μ : F, spForm a (μ • w) = 0 := fun μ => by
    rw [spForm_smul_right', hw, mul_zero]
  let f : F × F → ↥(spRadLine a w) := fun p =>
    ⟨spTau a (p.1 • w) p.2 (hu p.1), mem_spRadLine.2
      ⟨spTau_mem a (p.1 • w) p.2 (hu p.1), p.1, p.2,
        fun x => spTau_mulVec a (p.1 • w) p.2 (hu p.1) x⟩⟩
  have hinj : Function.Injective f := by
    rintro ⟨μ, c⟩ ⟨μ', c'⟩ h
    have hsp : spTau a (μ • w) c (hu μ) = spTau a (μ' • w) c' (hu μ') :=
      Subtype.ext_iff.mp h
    obtain ⟨hc, lam, hlam⟩ := (spTau_eq_iff ha (hu μ) (hu μ')).1 hsp
    have hμ : μ = μ' := by
      by_contra hne
      have hdiff : μ' - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hw' : w = ((μ' - μ)⁻¹ * lam) • a := by
        have h : (μ' - μ) • w = lam • a := by
          rw [sub_smul, hlam]
          abel
        calc w = ((μ' - μ)⁻¹ * (μ' - μ)) • w := by
              rw [inv_mul_cancel₀ hdiff, one_smul]
          _ = (μ' - μ)⁻¹ • ((μ' - μ) • w) := by rw [smul_smul]
          _ = (μ' - μ)⁻¹ • (lam • a) := by rw [h]
          _ = ((μ' - μ)⁻¹ * lam) • a := by rw [smul_smul]
      exact hwa _ hw'
    exact Prod.ext hμ hc
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hgm⟩
    obtain ⟨hg, μ, c, hgx⟩ := mem_spRadLine.1 hgm
    refine ⟨(μ, c), Subtype.ext ?_⟩
    refine eq_of_mat_mulVec_eq fun x => ?_
    rw [spTau_mulVec, hgx]
  have hcard : Nat.card (F × F) = Nat.card ↥(spRadLine a w) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [← hcard, Nat.card_prod, pow_two]

end Cardinal

section Conjugation

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem mat_conj_mulVec_of_param_smul {a w : Fin n ⊕ Fin n → F} {l ν : F}
    {x g : StatedSp n F}
    (hx : ∀ v, SpExtras.mat n F x *ᵥ v = v + spForm a v • w + spForm w v • a +
      (l * spForm a v) • a)
    (hga : SpExtras.mat n F g *ᵥ a = ν • a) (v : Fin n ⊕ Fin n → F) :
    SpExtras.mat n F (g * x * g⁻¹) *ᵥ v = v + spForm a v • (ν • (SpExtras.mat n F g *ᵥ w)) +
      spForm (ν • (SpExtras.mat n F g *ᵥ w)) v • a + ((ν * ν * l) * spForm a v) • a := by
  have h1 : spForm a (SpExtras.mat n F g⁻¹ *ᵥ v) = ν * spForm a v := by
    have h := spForm_mat_mulVec g a (SpExtras.mat n F g⁻¹ *ᵥ v)
    rw [hga, mat_mulVec_mat_inv_mulVec, spForm_smul_left'] at h
    exact h.symm
  have h2 : spForm w (SpExtras.mat n F g⁻¹ *ᵥ v) = spForm (SpExtras.mat n F g *ᵥ w) v := by
    have h := spForm_mat_mulVec g w (SpExtras.mat n F g⁻¹ *ᵥ v)
    rw [mat_mulVec_mat_inv_mulVec] at h
    exact h.symm
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hx, h1, h2, mulVec_add, mulVec_add,
    mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mat_mulVec_mat_inv_mulVec, hga,
    spForm_smul_left', smul_smul, smul_smul]
  rw [mul_comm (spForm (SpExtras.mat n F g *ᵥ w) v) ν]
  ring_nf
  rw [smul_smul, mul_comm (spForm a v) ν]
  abel

theorem mat_conj_mulVec_of_line_param {a w : Fin n ⊕ Fin n → F} {μ c ν : F}
    {x g : StatedSp n F}
    (hx : ∀ v, SpExtras.mat n F x *ᵥ v = v + spForm a v • (μ • w) + spForm (μ • w) v • a +
      (c * spForm a v) • a)
    (hga : SpExtras.mat n F g *ᵥ a = ν • a) (v : Fin n ⊕ Fin n → F) :
    SpExtras.mat n F (g * x * g⁻¹) *ᵥ v =
      v + spForm a v • ((ν * μ) • (SpExtras.mat n F g *ᵥ w)) +
        spForm ((ν * μ) • (SpExtras.mat n F g *ᵥ w)) v • a +
          ((ν * ν * c) * spForm a v) • a := by
  rw [mat_conj_mulVec_of_param_smul hx hga v]
  simp only [mulVec_smul, smul_smul, mul_assoc]

theorem map_conj_spRadLine {a w : Fin n ⊕ Fin n → F} {g : StatedSp n F} (hg : g ∈ spLine a) :
    (spRadLine a w).map (MulAut.conj g).toMonoidHom = spRadLine a (SpExtras.mat n F g *ᵥ w) := by
  obtain ⟨ν, hν, hga⟩ := hg
  have hgline : g ∈ spLine a := ⟨ν, hν, hga⟩
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨hxrad, μ, c, hxparam⟩ := mem_spRadLine.1 hx
    refine mem_spRadLine.2 ⟨conj_mem_spRad hgline hxrad, ν * μ, ν * ν * c, fun v => ?_⟩
    exact mat_conj_mulVec_of_line_param hxparam hga v
  · rintro y ⟨hyrad, μ', c', hyparam⟩
    have hνa : SpExtras.mat n F g⁻¹ *ᵥ a = ν⁻¹ • a := by
      have h1 : ν • (SpExtras.mat n F g⁻¹ *ᵥ a) = a := by
        rw [← mulVec_smul, ← hga, mat_inv_mulVec_mat_mulVec]
      exact (eq_inv_smul_iff₀ hν).2 h1
    have hginv : g⁻¹ ∈ spLine a := by
      exact (spLine a).inv_mem hgline
    refine ⟨g⁻¹ * y * g, mem_spRadLine.2 ⟨conj_mem_spRad hginv hyrad, ν⁻¹ * μ', ν⁻¹ * ν⁻¹ * c',
      fun v => ?_⟩, ?_⟩
    · have h := mat_conj_mulVec_of_line_param hyparam hνa v
      rw [show g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g by rw [inv_inv]] at h
      have hw : (SpExtras.mat n F g⁻¹) *ᵥ ((SpExtras.mat n F g) *ᵥ w) = w := by
        rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]
      rw [hw] at h
      exact h
    · change g * (g⁻¹ * y * g) * g⁻¹ = y
      group

end Conjugation

section FixedVectors

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem spRad_mulVec_eq_self_iff {a u x : Fin n ⊕ Fin n → F} {g : StatedSp n F} {c : F}
    (ha : a ≠ 0) (hparam : ∀ y, SpExtras.mat n F g *ᵥ y = y + spForm a y • u +
      spForm u y • a + (c * spForm a y) • a) (hx : spForm a x = 0) :
    SpExtras.mat n F g *ᵥ x = x ↔ spForm u x = 0 := by
  constructor
  · intro h
    rw [hparam x, hx] at h
    simp only [zero_smul, mul_zero, add_zero] at h
    have h1 : x + spForm u x • a = x + 0 := by
      rw [add_zero]
      exact h
    exact (smul_eq_zero.mp (add_left_cancel h1)).resolve_right ha
  · intro h
    rw [hparam x, hx, h]
    simp

theorem param_add_smul_a {a u : Fin n ⊕ Fin n → F} (ν c : F) (y : Fin n ⊕ Fin n → F) :
    y + spForm a y • (u + ν • a) + spForm (u + ν • a) y • a + (c * spForm a y) • a =
      y + spForm a y • u + spForm u y • a + (c * spForm a y) • a := by
  rw [smul_add, spForm_add_left, spForm_smul_left', smul_smul, add_smul]
  have h2 : (spForm a y * ν) • a + (ν * spForm a y) • a = 0 := by
    rw [mul_comm (spForm a y) ν, ← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  linear_combination (norm := module) h2

end FixedVectors

section LineLemma

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem exists_sup_eq_spRadLine [Finite F] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T D : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hD : D ≤ spRad a)
    (hDT : D ⊓ T = ⊥) (hcard : Nat.card ↥D = Nat.card F)
    (hfix : ∀ d₀ ∈ D, d₀ ≠ 1 → ∀ x, spForm a x = 0 →
      SpExtras.mat n F d₀ *ᵥ x = x → ∀ d ∈ D, SpExtras.mat n F d *ᵥ x = x) :
    ∃ w, spForm a w = 0 ∧ (∀ μ : F, w ≠ μ • a) ∧ D ⊔ T = spRadLine a w := by
  have hF2 : 1 < Nat.card F := by
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  haveI : Finite ↥D := Nat.finite_of_card_ne_zero
    (by rw [hcard]; exact Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
  have hDne : D ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]
    exact hF2
  haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).2 hDne
  obtain ⟨d₀, hd₀D, hd₀1⟩ := Subgroup.exists_ne_one_of_nontrivial D
  obtain ⟨u₀, hu₀, c₀, hu₀param⟩ := exists_spRad_param ha (hD hd₀D)
  have hwa : ∀ μ : F, u₀ ≠ μ • a := by
    intro μ hμ
    have hmat : SpExtras.mat n F d₀ = spTrans a c₀ := mat_eq_spTrans_of_param hu₀param hμ
    have hdT : d₀ ∈ T := (hT.1 d₀).2 ⟨c₀, hmat⟩
    have hbot : d₀ ∈ D ⊓ T := Subgroup.mem_inf.2 ⟨hd₀D, hdT⟩
    rw [hDT] at hbot
    exact hd₀1 (Subgroup.mem_bot.1 hbot)
  have hDle : D ≤ spRadLine a u₀ := by
    intro d hd
    obtain ⟨ud, hud, cd, hudparam⟩ := exists_spRad_param ha (hD hd)
    have hforall : ∀ x, spForm a x = 0 → spForm u₀ x = 0 → spForm ud x = 0 := by
      intro x hx hx₀
      have hd₀x : SpExtras.mat n F d₀ *ᵥ x = x :=
        (spRad_mulVec_eq_self_iff ha hu₀param hx).2 hx₀
      have hdx : SpExtras.mat n F d *ᵥ x = x :=
        hfix d₀ hd₀D hd₀1 x hx hd₀x d hd
      exact (spRad_mulVec_eq_self_iff ha hudparam hx).1 hdx
    obtain ⟨μ, ν, hμν⟩ := exists_eq_smul_add_smul_of_forall_spForm hforall
    refine mem_spRadLine.2 ⟨hD hd, μ, cd, fun y => ?_⟩
    rw [hudparam y, hμν, param_add_smul_a]
  have hTle : T ≤ spRadLine a u₀ := le_spRadLine_of_isTransGroup hT
  have hle : D ⊔ T ≤ spRadLine a u₀ := sup_le hDle hTle
  have hcomm : ∀ b ∈ D, ∀ t ∈ T, b * t * b⁻¹ ∈ T := by
    intro b hb t ht
    rw [spRadCommStmt_holds ha b (hD hb) t (le_spRad_of_isTransGroup hT ht)]
    convert ht using 1
    group
  have hsupcard : Nat.card ↥(D ⊔ T) = Nat.card F ^ 2 := by
    have h := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
      D T hcomm
    rw [hDT, Subgroup.card_bot, Nat.mul_one, hcard, IsTransGroup.natCard_eq ha hT] at h
    exact h.trans (pow_two (Nat.card F)).symm
  have hlinecard : Nat.card ↥(spRadLine a u₀) = Nat.card F ^ 2 :=
    spRadLine_card ha hu₀ hwa
  haveI : Finite ↥(spRadLine a u₀) := Nat.finite_of_card_ne_zero
    (by rw [hlinecard]; exact pow_ne_zero 2 (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩))
  exact ⟨u₀, hu₀, hwa,
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hlinecard.trans hsupcard.symm))⟩

end LineLemma

section Subgroup

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

@[expose] def spRadSub (a : Fin n ⊕ Fin n → F) (U : Submodule F (Fin n ⊕ Fin n → F)) :
    Subgroup (StatedSp n F) where
  carrier := {g | g ∈ spRad a ∧ ∃ u ∈ U, ∃ c : F, ∀ x : Fin n ⊕ Fin n → F,
    SpExtras.mat n F g *ᵥ x = x + spForm a x • u + spForm u x • a + (c * spForm a x) • a}
  mul_mem' := by
    rintro g h ⟨hg, u, huU, c, hgx⟩ ⟨hh, u', hu'U, c', hhx⟩
    have hu := spForm_eq_zero_of_param hg hgx
    have hu' := spForm_eq_zero_of_param hh hhx
    refine ⟨(spRad a).mul_mem hg hh, u + u', U.add_mem huU hu'U, c + c' + spForm u u',
      fun x => ?_⟩
    rw [mat_mul_mulVec_of_param hu hu' hgx hhx]
  one_mem' := by
    refine ⟨(spRad a).one_mem, 0, U.zero_mem, 0, fun x => ?_⟩
    rw [map_one, Matrix.one_mulVec]
    simp
  inv_mem' := by
    rintro g ⟨hg, u, huU, c, hgx⟩
    have hu := spForm_eq_zero_of_param hg hgx
    have hgg : g * g = 1 := by
      refine eq_of_mat_mulVec_eq fun x => ?_
      rw [mat_mul_mulVec_of_param hu hu hgx hgx, map_one, Matrix.one_mulVec,
        vec_add_self, spForm_self, CharTwo.add_self_eq_zero]
      simp
    have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
    exact ⟨(spRad a).inv_mem hg, u, huU, c, by rw [hinv]; exact hgx⟩

theorem mem_spRadSub {a : Fin n ⊕ Fin n → F} {U : Submodule F (Fin n ⊕ Fin n → F)}
    {g : StatedSp n F} :
    g ∈ spRadSub a U ↔ g ∈ spRad a ∧ ∃ u ∈ U, ∃ c : F, ∀ x : Fin n ⊕ Fin n → F,
      SpExtras.mat n F g *ᵥ x = x + spForm a x • u + spForm u x • a + (c * spForm a x) • a :=
  Iff.rfl

theorem spRadSub_le_spRad (a : Fin n ⊕ Fin n → F) (U : Submodule F (Fin n ⊕ Fin n → F)) :
    spRadSub a U ≤ spRad a := fun _ hg => hg.1

theorem spRadSub_eq_spRad_of_le {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {U : Submodule F (Fin n ⊕ Fin n → F)} (hU : LinearMap.ker (spFormL a) ≤ U) :
    spRadSub a U = spRad a := by
  refine le_antisymm (spRadSub_le_spRad a U) ?_
  intro g hg
  obtain ⟨u, hu, c, hx⟩ := exists_spRad_param ha hg
  refine mem_spRadSub.2 ⟨hg, u, hU ?_, c, hx⟩
  rw [LinearMap.mem_ker]
  exact hu

theorem spRadSub_eq_spRad_iff {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {U : Submodule F (Fin n ⊕ Fin n → F)} (haU : a ∈ U) :
    spRadSub a U = spRad a ↔ LinearMap.ker (spFormL a) ≤ U := by
  constructor
  · intro h u hu
    have hu0 : spForm a u = 0 := LinearMap.mem_ker.1 hu
    have htau : spTau a u 0 hu0 ∈ spRad a := spTau_mem a u 0 hu0
    rw [← h] at htau
    obtain ⟨-, u', hu'U, c, hτ'⟩ := mem_spRadSub.1 htau
    obtain ⟨lam, hlam⟩ := exists_eq_add_smul_of_param ha hτ' (spTau_mulVec a u 0 hu0)
    have hueq : u = u' + (-lam) • a := by
      rw [hlam, neg_smul]
      abel
    rw [hueq]
    exact U.add_mem hu'U (U.smul_mem (-lam) haU)
  · intro hU
    exact spRadSub_eq_spRad_of_le ha hU

theorem conj_mem_spRadSub {a : Fin n ⊕ Fin n → F} {U : Submodule F (Fin n ⊕ Fin n → F)}
    {g : StatedSp n F} (hg : g ∈ spLine a) (hU : ∀ u ∈ U, SpExtras.mat n F g *ᵥ u ∈ U)
    {x : StatedSp n F} (hx : x ∈ spRadSub a U) : g * x * g⁻¹ ∈ spRadSub a U := by
  obtain ⟨ν, hν, hga⟩ := hg
  obtain ⟨hxrad, u, huU, c, hxparam⟩ := mem_spRadSub.1 hx
  refine mem_spRadSub.2 ⟨conj_mem_spRad ⟨ν, hν, hga⟩ hxrad, ν • (SpExtras.mat n F g *ᵥ u),
    U.smul_mem ν (hU u huU), ν * ν * c, fun v => ?_⟩
  rw [mat_conj_mulVec_of_param_smul hxparam hga v, smul_smul]

end Subgroup

section Span

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

@[expose] def spRadSpan (a w : Fin n ⊕ Fin n → F) (N : Subgroup (StatedSp n F)) :
    Submodule F (Fin n ⊕ Fin n → F) :=
  Submodule.span F ({a} ∪ Set.range (fun g : N => SpExtras.mat n F (g : StatedSp n F) *ᵥ w))

theorem spForm_mat_mulVec_eq_zero_of_mem_spLine {a w : Fin n ⊕ Fin n → F}
    (hw : spForm a w = 0) {g : StatedSp n F} (hg : g ∈ spLine a) :
    spForm a (SpExtras.mat n F g *ᵥ w) = 0 := by
  obtain ⟨ν, hν, hga⟩ := hg
  have h := spForm_mat_mulVec g a w
  rw [hga, spForm_smul_left', hw] at h
  exact (mul_eq_zero.mp h).resolve_left hν

theorem spTau_smul_a_mem {a : Fin n ⊕ Fin n → F} {T : Subgroup (StatedSp n F)}
    (hT : IsTransGroup a T) (r c : F) (h : spForm a (r • a) = 0) :
    spTau a (r • a) c h ∈ T :=
  (hT.1 _).2 ⟨c, mat_eq_spTrans_of_param (spTau_mulVec a (r • a) c h) rfl⟩

theorem spTau_mem_spRadLine {a w : Fin n ⊕ Fin n → F} (hw : spForm a w = 0) {μ c : F}
    (h : spForm a (μ • w) = 0) : spTau a (μ • w) c h ∈ spRadLine a w :=
  mem_spRadLine.2 ⟨spTau_mem a (μ • w) c h, μ, c,
    fun x => spTau_mulVec a (μ • w) c h x⟩

theorem spRadSpan_le_ker {a w : Fin n ⊕ Fin n → F} (hw : spForm a w = 0)
    {N : Subgroup (StatedSp n F)} (hN : N ≤ spLine a) :
    spRadSpan a w N ≤ LinearMap.ker (spFormL a) := by
  refine Submodule.span_le.mpr ?_
  intro v hv
  rcases hv with hv | ⟨g, rfl⟩
  · rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact LinearMap.mem_ker.2 (spForm_self a)
  · exact LinearMap.mem_ker.2 (spForm_mat_mulVec_eq_zero_of_mem_spLine hw (hN g.2))

theorem a_mem_spRadSpan (a w : Fin n ⊕ Fin n → F) (N : Subgroup (StatedSp n F)) :
    a ∈ spRadSpan a w N :=
  Submodule.subset_span (Set.mem_union_left _ (Set.mem_singleton a))

theorem mat_mulVec_mem_spRadSpan (a w : Fin n ⊕ Fin n → F) (N : Subgroup (StatedSp n F))
    (g : N) : SpExtras.mat n F (g : StatedSp n F) *ᵥ w ∈ spRadSpan a w N :=
  Submodule.subset_span (Set.mem_union_right _ (Set.mem_range_self g))

theorem map_mulVec_mem_spRadSpan {a w : Fin n ⊕ Fin n → F} {N : Subgroup (StatedSp n F)}
    {b : StatedSp n F} (hb : b ∈ N)
    (hba : SpExtras.mat n F b *ᵥ a ∈ spRadSpan a w N) :
    ∀ u ∈ spRadSpan a w N, SpExtras.mat n F b *ᵥ u ∈ spRadSpan a w N := by
  intro u hu
  refine Submodule.span_induction (p := fun u _ =>
    SpExtras.mat n F b *ᵥ u ∈ spRadSpan a w N) ?_ ?_ ?_ ?_ hu
  · rintro v (rfl | ⟨g, rfl⟩)
    · exact hba
    · rw [mulVec_mulVec, ← map_mul]
      exact mat_mulVec_mem_spRadSpan a w N (⟨b * g, N.mul_mem hb g.2⟩)
  · rw [mulVec_zero]; exact (spRadSpan a w N).zero_mem
  · intro x y _ _ hx hy
    rw [mulVec_add]; exact (spRadSpan a w N).add_mem hx hy
  · intro r x _ hx
    rw [mulVec_smul]; exact (spRadSpan a w N).smul_mem r hx

theorem spTau_add_mem {a x y : Fin n ⊕ Fin n → F} {R : Subgroup (StatedSp n F)}
    (hx0 : spForm a x = 0) (hy0 : spForm a y = 0)
    (hxR : ∀ c, ∀ h : spForm a x = 0, spTau a x c h ∈ R)
    (hyR : ∀ c, ∀ h : spForm a y = 0, spTau a y c h ∈ R) {c : F}
    (hxy : spForm a (x + y) = 0) : spTau a (x + y) c hxy ∈ R := by
  have hprod := spTau_mul a x y (c + spForm x y) 0 hx0 hy0
  have hmem : spTau a x (c + spForm x y) hx0 * spTau a y 0 hy0 ∈ R :=
    R.mul_mem (hxR _ hx0) (hyR _ hy0)
  have hc : c + spForm x y + 0 + spForm x y = c := by
    rw [add_zero]
    calc c + spForm x y + spForm x y = c + (spForm x y + spForm x y) := by abel
      _ = c + 0 := by rw [CharTwo.add_self_eq_zero]
      _ = c := add_zero c
  rw [hprod] at hmem
  rwa [show spTau a (x + y) (c + spForm x y + 0 + spForm x y) _ =
    spTau a (x + y) c hxy by rw [hc]] at hmem

theorem spTau_mem_of_mem_addClosure {a : Fin n ⊕ Fin n → F} {t : Set (Fin n ⊕ Fin n → F)}
    {T R : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hTR : T ≤ R)
    (hs : ∀ v ∈ t, spForm a v = 0)
    (hmem : ∀ v ∈ t, ∀ c, ∀ hv : spForm a v = 0, spTau a v c hv ∈ R)
    {u : Fin n ⊕ Fin n → F} (hu : u ∈ AddSubmonoid.closure t) :
    ∀ c, ∀ hu' : spForm a u = 0, spTau a u c hu' ∈ R := by
  let P : (Fin n ⊕ Fin n → F) → Prop := fun v =>
    spForm a v = 0 ∧ ∀ c, ∀ hv : spForm a v = 0, spTau a v c hv ∈ R
  have hP : P u := by
    refine AddSubmonoid.closure_induction (motive := fun v _ => P v) ?_ ?_ ?_ hu
    · intro v hv
      exact ⟨hs v hv, hmem v hv⟩
    · refine ⟨spForm_zero_right a, fun c h0 => hTR ?_⟩
      exact (hT.1 _).2 ⟨c, mat_spTau_zero a c h0⟩
    · intro x y _ _ hx hy
      refine ⟨?_, ?_⟩
      · rw [spForm_add_right, hx.1, hy.1, add_zero]
      · intro c hxy
        exact spTau_add_mem hx.1 hy.1 hx.2 hy.2 hxy
  exact hP.2

end Span

section Cover

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem spRadSub_span_le_of_lines {ι : Type} {a w : Fin n ⊕ Fin n → F}
    {T R : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hTR : T ≤ R)
    (g : ι → StatedSp n F)
    (hline : ∀ i, spRadLine a (SpExtras.mat n F (g i) *ᵥ w) ≤ R)
    (hgen : ∀ i, spForm a (SpExtras.mat n F (g i) *ᵥ w) = 0) :
    spRadSub a (Submodule.span F ({a} ∪
      Set.range (fun i => SpExtras.mat n F (g i) *ᵥ w))) ≤ R := by
  intro x hx
  obtain ⟨hxrad, u, huU, c, hxparam⟩ := mem_spRadSub.1 hx
  have hu : spForm a u = 0 := spForm_eq_zero_of_param hxrad hxparam
  have hxeq : x = spTau a u c hu := by
    refine eq_of_mat_mulVec_eq fun v => ?_
    rw [hxparam v, spTau_mulVec]
  rw [hxeq]
  let s : Set (Fin n ⊕ Fin n → F) := {a} ∪
    Set.range (fun i => SpExtras.mat n F (g i) *ᵥ w)
  let t : Set (Fin n ⊕ Fin n → F) := (Set.univ : Set F) • s
  have huCl : u ∈ AddSubmonoid.closure t := by
    rw [show t = (Set.univ : Set F) • s from rfl, ← Submodule.span_eq_closure]
    exact huU
  refine spTau_mem_of_mem_addClosure hT hTR ?_ ?_ huCl c hu
  · intro v hv
    change v ∈ (Set.univ : Set F) • s at hv
    obtain ⟨r, -, y, hy, rfl⟩ := Set.mem_smul.mp hv
    rcases hy with rfl | ⟨i, rfl⟩
    · rw [spForm_smul_right', spForm_self, mul_zero]
    · rw [spForm_smul_right', hgen i, mul_zero]
  · intro v hv c' hv'
    change v ∈ (Set.univ : Set F) • s at hv
    obtain ⟨r, -, y, hy, rfl⟩ := Set.mem_smul.mp hv
    rcases hy with rfl | ⟨i, rfl⟩
    · exact hTR (spTau_smul_a_mem hT r c' hv')
    · exact hline i (spTau_mem_spRadLine (hgen i) hv')

end Cover

section NormalizerSpan

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem spRadSub_spRadSpan_ne_transGroup {a w : Fin n ⊕ Fin n → F}
    {T N : Subgroup (StatedSp n F)} (ha : a ≠ 0) (hT : IsTransGroup a T)
    (hw : spForm a w = 0) (hwa : ∀ μ : F, w ≠ μ • a) :
    spRadSub a (spRadSpan a w N) ≠ T := by
  intro hEq
  have hwU : w ∈ spRadSpan a w N := by
    have := mat_mulVec_mem_spRadSpan a w N (1 : N)
    simpa using this
  have htau_mem : spTau a w 0 hw ∈ spRadSub a (spRadSpan a w N) :=
    mem_spRadSub.2 ⟨spTau_mem a w 0 hw, w, hwU, 0,
      fun x => spTau_mulVec a w 0 hw x⟩
  have htau_T : spTau a w 0 hw ∈ T := by
    rw [hEq] at htau_mem
    exact htau_mem
  obtain ⟨c, hc⟩ := (hT.1 _).1 htau_T
  have htpar : ∀ x, SpExtras.mat n F (spTau a w 0 hw) *ᵥ x =
      x + spForm a x • (0 : Fin n ⊕ Fin n → F) + spForm (0 : Fin n ⊕ Fin n → F) x • a +
        (c * spForm a x) • a := by
    intro x
    rw [hc, spTrans_mulVec]
    simp
  obtain ⟨lam, hlam⟩ := exists_eq_add_smul_of_param ha (spTau_mulVec a w 0 hw) htpar
  exact hwa lam (by simpa using hlam)

theorem spRadSub_spRadSpan_normalizer_eq_spRad [Finite F] {a w : Fin n ⊕ Fin n → F}
    {T : Subgroup (StatedSp n F)} (ha : a ≠ 0) (hT : IsTransGroup a T) (hw : spForm a w = 0)
    (hwa : ∀ μ : F, w ≠ μ • a) :
    spRadSub a (spRadSpan a w (Subgroup.normalizer (T : Set (StatedSp n F)))) = spRad a := by
  let N : Subgroup (StatedSp n F) := Subgroup.normalizer (T : Set (StatedSp n F))
  have hNle : N ≤ spLine a := fun g hg => by
    simpa [N, normalizer_eq_spLine ha hT] using hg
  have haU : a ∈ spRadSpan a w N := a_mem_spRadSpan a w N
  have hS_le : spRadSub a (spRadSpan a w N) ≤ spRad a := spRadSub_le_spRad a _
  have hS_le_core : spRadSub a (spRadSpan a w N) ≤
      pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n F))) :=
    hS_le.trans (spRad_le_pCoreOf ha hT)
  have hT_le_S : T ≤ spRadSub a (spRadSpan a w N) := by
    intro t ht
    obtain ⟨c, hc⟩ := (hT.1 t).1 ht
    refine mem_spRadSub.2 ⟨le_spRad_of_isTransGroup hT ht, 0,
      (spRadSpan a w N).zero_mem, c, fun x => ?_⟩
    rw [hc, spTrans_mulVec]
    simp
  have hS_norm : ∀ b ∈ N, ∀ r ∈ spRadSub a (spRadSpan a w N), b * r * b⁻¹ ∈
      spRadSub a (spRadSpan a w N) := by
    intro b hb r hr
    have hbline : b ∈ spLine a := hNle hb
    obtain ⟨ν, hν, hba⟩ := hbline
    have hbain : SpExtras.mat n F b *ᵥ a ∈ spRadSpan a w N := by
      rw [hba]
      exact (spRadSpan a w N).smul_mem ν haU
    exact conj_mem_spRadSub ⟨ν, hν, hba⟩ (map_mulVec_mem_spRadSpan hb hbain) hr
  have hS_ne_T : spRadSub a (spRadSpan a w N) ≠ T :=
    spRadSub_spRadSpan_ne_transGroup ha hT hw hwa
  have hIrr := spModelIrr_holds n F a T ha hT
  have hcore := spCoreStmt_holds n F ha hT
  rcases hIrr (spRadSub a (spRadSpan a w N)) hT_le_S hS_le_core hS_norm with h | h
  · exact absurd h hS_ne_T
  · exact h.trans hcore

theorem spRadSpan_normalizer_eq_ker [Finite F] {a w : Fin n ⊕ Fin n → F}
    {T : Subgroup (StatedSp n F)} (ha : a ≠ 0) (hT : IsTransGroup a T) (hw : spForm a w = 0)
    (hwa : ∀ μ : F, w ≠ μ • a) :
    spRadSpan a w (Subgroup.normalizer (T : Set (StatedSp n F))) =
      LinearMap.ker (spFormL a) := by
  let N : Subgroup (StatedSp n F) := Subgroup.normalizer (T : Set (StatedSp n F))
  have hNle : N ≤ spLine a := fun g hg => by
    simpa [N, normalizer_eq_spLine ha hT] using hg
  have hS_eq : spRadSub a (spRadSpan a w N) = spRad a :=
    spRadSub_spRadSpan_normalizer_eq_spRad ha hT hw hwa
  have hKle : LinearMap.ker (spFormL a) ≤ spRadSpan a w N :=
    (spRadSub_eq_spRad_iff ha (a_mem_spRadSpan a w N)).1 hS_eq
  exact le_antisymm (spRadSpan_le_ker hw hNle) hKle

end NormalizerSpan

section Finrank

variable {n : ℕ} {F : Type} [Field F]

theorem one_le_of_ne_zero {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exfalso
    subst h
    apply ha
    funext i
    rcases i with i | i <;> exact i.elim0
  · omega

theorem finrank_ker_spFormL {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) :
    Module.finrank F (LinearMap.ker (spFormL a)) = 2 * n - 1 := by
  have hn1 : 1 ≤ n := one_le_of_ne_zero ha
  have hf : spFormL a ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_spForm_ne_zero ha
    intro h
    apply hy
    simpa [spFormL] using LinearMap.congr_fun h y
  have h := LinearMap.finrank_range_add_finrank_ker (spFormL a)
  rw [Module.Dual.range_eq_top_of_ne_zero hf, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h
  have h2 : Module.finrank F (LinearMap.ker (spFormL a)) + 1 = n + n := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have h3 : (2 * n - 1) + 1 = n + n := by
    rw [two_mul]
    exact Nat.sub_add_cancel (by omega)
  exact Nat.add_right_cancel (h2.trans h3.symm)

end Finrank

section Basis

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem exists_span_eq_ker [Finite F] {a w : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hw : spForm a w = 0)
    (hwa : ∀ μ : F, w ≠ μ • a) :
    ∃ g : Fin (2 * n - 2) → ↥(StatedSp n F),
      (∀ i, g i ∈ Subgroup.normalizer (T : Set (StatedSp n F))) ∧
      Submodule.span F ({a} ∪ Set.range (fun i => SpExtras.mat n F (g i) *ᵥ w)) =
        LinearMap.ker (spFormL a) := by
  let N : Subgroup (StatedSp n F) := Subgroup.normalizer (T : Set (StatedSp n F))
  let v : N → Fin n ⊕ Fin n → F := fun g => SpExtras.mat n F (g : StatedSp n F) *ᵥ w
  have hU : spRadSpan a w N = LinearMap.ker (spFormL a) :=
    spRadSpan_normalizer_eq_ker ha hT hw hwa
  have hn1 : 1 ≤ n := one_le_of_ne_zero ha
  have hm : Module.finrank F (Submodule.span F ({a} ∪ Set.range v)) = (2 * n - 2) + 1 := by
    change Module.finrank F (spRadSpan a w N) = (2 * n - 2) + 1
    rw [hU, finrank_ker_spFormL ha]
    omega
  haveI : FiniteDimensional F (Submodule.span F ({a} ∪ Set.range v)) := inferInstance
  obtain ⟨s, hs⟩ := CFSG.LinearAlgebra.exists_fin_span_union_eq
    (K := F) (V := Fin n ⊕ Fin n → F) (ι := N) ha v hm
  refine ⟨fun i => (s i : StatedSp n F), fun i => (s i).2, ?_⟩
  change Submodule.span F ({a} ∪ Set.range (v ∘ s)) = LinearMap.ker (spFormL a)
  rw [hs]
  change spRadSpan a w N = LinearMap.ker (spFormL a)
  exact hU

end Basis

section CoverTheorem

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem exists_cover_spRad [Finite F] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) {w : Fin n ⊕ Fin n → F}
    (hw : spForm a w = 0) (hwa : ∀ μ : F, w ≠ μ • a) :
    ∃ g : Fin (2 * n - 2) → ↥(StatedSp n F),
      (∀ i, g i ∈ Subgroup.normalizer (T : Set (StatedSp n F))) ∧
      spRad a ≤ T ⊔ ⨆ i, (spRadLine a w).map (MulAut.conj (g i)).toMonoidHom := by
  obtain ⟨g, hgN, hspan⟩ := exists_span_eq_ker ha hT hw hwa
  let U := Submodule.span F ({a} ∪ Set.range (fun i => SpExtras.mat n F (g i) *ᵥ w))
  have hU : U = LinearMap.ker (spFormL a) := hspan
  have hgline : ∀ i, g i ∈ spLine a := by
    intro i
    have := hgN i
    rwa [normalizer_eq_spLine ha hT] at this
  let R : Subgroup (StatedSp n F) := T ⊔ ⨆ i, (spRadLine a w).map
    (MulAut.conj (g i)).toMonoidHom
  have hTleR : T ≤ R := le_sup_left
  have hline : ∀ i, spRadLine a (SpExtras.mat n F (g i) *ᵥ w) ≤ R := by
    intro i
    rw [← map_conj_spRadLine (hgline i)]
    exact (le_iSup (fun i => (spRadLine a w).map (MulAut.conj (g i)).toMonoidHom) i).trans
      le_sup_right
  have hgen : ∀ i, spForm a (SpExtras.mat n F (g i) *ᵥ w) = 0 :=
    fun i => spForm_mat_mulVec_eq_zero_of_mem_spLine hw (hgline i)
  have hsub_le : spRadSub a U ≤ R :=
    spRadSub_span_le_of_lines hT hTleR g hline hgen
  have hsub_eq : spRadSub a U = spRad a := by
    exact spRadSub_eq_spRad_of_le ha (by rw [hU])
  have hspRad_le : spRad a ≤ R := by
    rw [← hsub_eq]
    exact hsub_le
  exact ⟨g, hgN, hspRad_le⟩

end CoverTheorem
