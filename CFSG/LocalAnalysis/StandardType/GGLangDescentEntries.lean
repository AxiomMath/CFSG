module

import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6OuterDescent
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldLiftTwist
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section


open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.GLTheoremA.T158 (exists_baseChangeGL_eq_of_entries)
open CFSG.StandardType.TwE6FieldCore (ringHom_pow_apply_eq_pow)

attribute [local instance] ZMod.algebra algebraicClosure.isAlgClosure IsAlgClosure.isAlgClosed

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem langDescent_baseChangeGL_iterate
    {τ : Tag} {L : Type} [Field L] (Fr : L →+* L) (k : ℕ)
    (g : ModGL τ L) :
    (baseChangeGL Fr)^[k] g = baseChangeGL (Fr ^ k) g := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero]
    exact (baseChangeGL_id L g).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, baseChangeGL_baseChangeGL]
    congr 1
    rw [← RingHom.mul_def, ← pow_succ']

private theorem langDescent_iterate_mul_mul {τ : Tag} {L : Type} [Field L] {Fr : L →+* L}
    {a b z : ModGL τ L}
    (ha : Units.map (entrywiseHom Fr) a = a) (hb : Units.map (entrywiseHom Fr) b = b)
    (hz : Units.map (entrywiseHom Fr) z = a * z * b) :
    ∀ k, (Units.map (entrywiseHom Fr))^[k] z = a ^ k * z * b ^ k := by
  intro k
  induction k with
  | zero => rw [Function.iterate_zero_apply, pow_zero, pow_zero, one_mul, mul_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_mul, map_pow, map_pow, ha, hb, hz]
    group

private theorem langDescent_units_map_diagramAt {τ : Tag} {L : Type} [Field L] (Fr : L →+* L)
    {t : TwistTag} (h : t.tag = τ) :
    Units.map (entrywiseHom Fr) (diagramAt τ L t h) = diagramAt τ L t h := by
  cases h
  exact units_map_entrywiseHom_diagramMap Fr

private theorem langDescent_baseChangeGL_diagramAt
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    {t : TwistTag} (h : t.tag = τ) :
    baseChangeGL (algebraMap (ZMod 2) L) (diagramAt τ (ZMod 2) t h) = diagramAt τ L t h := by
  cases h
  exact baseChangeGL_diagramMap (algebraMap (ZMod 2) L) t

theorem LangSetup.model_g0_mem_range_algebraicClosure
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) :
    S.D.model ≤ (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L) :
        ModGL τ (algebraicClosure (ZMod 2) L) →* ModGL τ L).range ∧
      S.D.g0 ∈ (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L) :
        ModGL τ (algebraicClosure (ZMod 2) L) →* ModGL τ L).range := by
  classical
  let K := algebraicClosure (ZMod 2) L
  have halg : ∀ {c : L} {N : ℕ}, 1 < N → c ^ N = c → c ∈ K := by
    intro c N hN hc
    exact mem_algebraicClosure_iff.2 ⟨Polynomial.X ^ N - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod 2) hN, by simp [hc]⟩
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  obtain ⟨w, hw⟩ := S.D.n_weyl
  have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
  haveI : Finite (ModGL τ (ZMod 2)) := finite_modGL
  let d : ℕ := Nat.card (ModGL τ (ZMod 2))
  have hdpos : 0 < d := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  have hdne : d ≠ 0 := hdpos.ne'
  have hFP : Units.map (entrywiseHom Fr) P = P := by
    rcases hP with rfl | ⟨t, htag, rfl⟩
    · rw [map_one]
    · exact langDescent_units_map_diagramAt Fr htag
  have hPbc : ∃ P₀ : ModGL τ (ZMod 2), baseChangeGL (algebraMap (ZMod 2) L) P₀ = P := by
    rcases hP with rfl | ⟨t, htag, rfl⟩
    · exact ⟨1, map_one _⟩
    · exact ⟨_, langDescent_baseChangeGL_diagramAt htag⟩
  have hnbc : baseChangeGL (algebraMap (ZMod 2) L)
      (canonicalRep (coxeterSystem τ) (ZMod 2) w) = S.D.n := by
    rw [hw]
    exact baseChangeGL_canonicalRep (algebraMap (ZMod 2) L) w
  obtain ⟨P₀, hP₀⟩ := hPbc
  have hcbc : baseChangeGL (algebraMap (ZMod 2) L)
      (canonicalRep (coxeterSystem τ) (ZMod 2) w * P₀) = S.D.n * P := by
    rw [map_mul, hnbc, hP₀]
  have hcd : (S.D.n * P) ^ d = 1 := by
    rw [← hcbc, ← map_pow, pow_card_eq_one', map_one]
  have hPd : P ^ d = 1 := by
    rw [← hP₀, ← map_pow, pow_card_eq_one', map_one]
  have hcinvd : ((S.D.n * P)⁻¹) ^ d = 1 := by rw [inv_pow, hcd, inv_one]
  have hPinvd : (P⁻¹) ^ d = 1 := by rw [inv_pow, hPd, inv_one]
  have hFc : Units.map (entrywiseHom Fr) (S.D.n * P) = S.D.n * P := by
    rw [map_mul, hFP, hw, CFSG.RankThree.PartOne.KE.frobenius_canonicalRep Fr w]
  have hF_eq : Units.map (entrywiseHom Fr) = (baseChangeGL Fr : ModGL τ L →* ModGL τ L) :=
    MonoidHom.ext (fun (g : ModGL τ L) => units_map_entrywiseHom_eq_baseChangeGL (τ := τ) Fr g)
  have hentry_of_ab : ∀ {z a b : ModGL τ L}, Units.map (entrywiseHom Fr) a = a →
      Units.map (entrywiseHom Fr) b = b → Units.map (entrywiseHom Fr) z = a * z * b →
      a ^ d = 1 → b ^ d = 1 →
      ∀ x y, (z : Module.End L (RootModule τ L)) (Finsupp.single y 1) x ∈ K := by
    intro z a b ha hb hz had hbd x y
    have hFix : (Units.map (entrywiseHom Fr))^[d] z = z := by
      rw [langDescent_iterate_mul_mul ha hb hz d, had, hbd, one_mul, mul_one]
    rw [hF_eq] at hFix
    rw [langDescent_baseChangeGL_iterate Fr d z] at hFix
    have hcoe := congrArg (fun g : ModGL τ L =>
      (g : Module.End L (RootModule τ L)) (Finsupp.single y 1) x) hFix
    rw [baseChangeGL_apply_single, Finsupp.mapRange_apply,
      ringHom_pow_apply_eq_pow hFr d] at hcoe
    exact halg (Nat.one_lt_pow hdne hq1) hcoe
  have hFy : ∀ y ∈ S.D.model, Units.map (entrywiseHom Fr) y = (S.D.n * P)⁻¹ * y * (S.D.n * P) := by
    intro y hy
    have h2 := ((S.D.mem_model).1 hy).2
    have h3 : S.D.n * (P * Units.map (entrywiseHom Fr) y * P⁻¹) * S.D.n⁻¹ = y := by
      rw [← hΦ y]; exact h2
    conv_rhs => rw [← h3]
    group
  have hentry : ∀ y ∈ S.D.model, ∀ a b,
      (y : Module.End L (RootModule τ L)) (Finsupp.single b 1) a ∈ K := by
    intro y hy
    exact hentry_of_ab (by rw [map_inv, hFc]) hFc (hFy y hy) hcinvd hcd
  have hFyinv : ∀ y ∈ S.D.model,
      Units.map (entrywiseHom Fr) y⁻¹ = (S.D.n * P)⁻¹ * y⁻¹ * (S.D.n * P) := by
    intro y hy
    have h := hFy y hy
    rw [map_inv, h]; group
  have hentryinv : ∀ y ∈ S.D.model, ∀ a b,
      ((y⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b 1) a ∈ K := by
    intro y hy
    exact hentry_of_ab (by rw [map_inv, hFc]) hFc (hFyinv y hy) hcinvd hcd
  have hFg0 : Units.map (entrywiseHom Fr) S.D.g0 = P⁻¹ * S.D.g0 * (S.D.n * P) := by
    have h := S.D.lang
    rw [hΦ] at h
    have h' : Units.map (entrywiseHom Fr) S.D.g0 = P⁻¹ * (S.D.g0 * S.D.n) * P := by
      rw [← h]; group
    calc Units.map (entrywiseHom Fr) S.D.g0
        = P⁻¹ * (S.D.g0 * S.D.n) * P := h'
      _ = P⁻¹ * S.D.g0 * (S.D.n * P) := by group
  have hg0entry : ∀ a b,
      (S.D.g0 : Module.End L (RootModule τ L)) (Finsupp.single b 1) a ∈ K :=
    hentry_of_ab (by rw [map_inv, hFP]) hFc hFg0 hPinvd hcd
  have hFg0inv : Units.map (entrywiseHom Fr) S.D.g0⁻¹ = (S.D.n * P)⁻¹ * S.D.g0⁻¹ * P := by
    rw [map_inv, hFg0]; group
  have hg0entryinv : ∀ a b,
      ((S.D.g0⁻¹ : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b 1) a ∈ K :=
    hentry_of_ab (by rw [map_inv, hFc]) hFP hFg0inv hcinvd hPd
  refine ⟨?_, ?_⟩
  · intro y hy
    exact ⟨_, (exists_baseChangeGL_eq_of_entries (algebraMap K L) y
      (fun a b => ⟨⟨_, hentry y hy a b⟩, rfl⟩)
      (fun a b => ⟨⟨_, hentryinv y hy a b⟩, rfl⟩)).choose_spec⟩
  · exact ⟨_, (exists_baseChangeGL_eq_of_entries (algebraMap K L) S.D.g0
      (fun a b => ⟨⟨_, hg0entry a b⟩, rfl⟩)
      (fun a b => ⟨⟨_, hg0entryinv a b⟩, rfl⟩)).choose_spec⟩

end CFSG.HardMathSupport.Timmesfeld.LangTorus
