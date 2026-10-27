module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.Flag

open Submodule

universe u

@[expose] def tri (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, i

theorem tri_succ (m : ℕ) : tri (m + 1) = tri m + m := Finset.sum_range_succ _ _

theorem zmod_two_eq_one {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  revert c hc
  decide

section
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_fixed_mem [Finite W] (S : Subgroup (W ≃ₗ[ZMod 2] W)) (hS : IsPGroup 2 S)
    (U : Submodule (ZMod 2) W) (hU : ∀ s ∈ S, ∀ u ∈ U, (s : W ≃ₗ[ZMod 2] W) u ∈ U)
    (hU0 : U ≠ ⊥) : ∃ u ∈ U, u ≠ 0 ∧ ∀ s ∈ S, (s : W ≃ₗ[ZMod 2] W) u = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S U :=
    { smul := fun s u => ⟨(s : W ≃ₗ[ZMod 2] W) u, hU _ s.2 _ u.2⟩
      one_smul := fun u => rfl
      mul_smul := fun s t u => rfl }
  have h := hS.card_modEq_card_fixedPoints U
  have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU0
  have hU1 : 0 < Module.finrank (ZMod 2) U := Module.finrank_pos
  have hcard : Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hdvd : 2 ∣ Nat.card U := hcard ▸ dvd_pow_self 2 hU1.ne'
  have h2 : 2 ∣ Nat.card (MulAction.fixedPoints S U) :=
    Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd))
  have h0 : (0 : U) ∈ MulAction.fixedPoints S U := fun s => Subtype.ext (map_zero _)
  have hlt : 1 < Nat.card (MulAction.fixedPoints S U) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints S U) :=
      Nat.card_pos_iff.2 ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
    omega
  have hnt := Finite.one_lt_card_iff_nontrivial.1 hlt
  obtain ⟨x, hx⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints S U)
  refine ⟨x.1.1, x.1.2, fun h => hx (Subtype.ext (Subtype.ext h)), fun s hs => ?_⟩
  have := congrArg Subtype.val (x.2 ⟨s, hs⟩)
  exact this

noncomputable def quotAct (S : Subgroup (W ≃ₗ[ZMod 2] W)) (N : Submodule (ZMod 2) W)
    (hN : ∀ s ∈ S, N.map ((s : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = N) :
    S →* ((W ⧸ N) ≃ₗ[ZMod 2] (W ⧸ N)) where
  toFun s := Submodule.Quotient.equiv N N (s : W ≃ₗ[ZMod 2] W) (hN s s.2)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp
  map_mul' s t := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp

theorem quotAct_mk (S : Subgroup (W ≃ₗ[ZMod 2] W)) (N : Submodule (ZMod 2) W)
    (hN : ∀ s ∈ S, N.map ((s : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = N) (s : S) (x : W) :
    quotAct S N hN s (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((s : W ≃ₗ[ZMod 2] W) x) := by
  simp [quotAct]

noncomputable def transvPart (N : Submodule (ZMod 2) W) (s : W ≃ₗ[ZMod 2] W)
    (h1 : ∀ x, s x - x ∈ N) (h2 : ∀ x ∈ N, s x = x) : (W ⧸ N) →ₗ[ZMod 2] N :=
  N.liftQ (LinearMap.codRestrict N ((s : W →ₗ[ZMod 2] W) - LinearMap.id) h1) (by
    intro x hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp [h2 x hx])

theorem transvPart_mk (N : Submodule (ZMod 2) W) (s : W ≃ₗ[ZMod 2] W)
    (h1 : ∀ x, s x - x ∈ N) (h2 : ∀ x ∈ N, s x = x) (x : W) :
    (transvPart N s h1 h2 (Submodule.Quotient.mk x) : W) = s x - x := by
  simp [transvPart]

end


theorem flag_main (m : ℕ) : ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] [Finite W],
    Module.finrank (ZMod 2) W = m → ∀ (S : Subgroup (W ≃ₗ[ZMod 2] W)), IsPGroup 2 S →
    Nat.card S ≤ 2 ^ tri m ∧ (Nat.card S = 2 ^ tri m → ∀ U U' : Submodule (ZMod 2) W,
      (∀ s ∈ S, ∀ u ∈ U, (s : W ≃ₗ[ZMod 2] W) u ∈ U) →
      (∀ s ∈ S, ∀ u ∈ U', (s : W ≃ₗ[ZMod 2] W) u ∈ U') → U ≤ U' ∨ U' ≤ U) := by
  induction m with
  | zero =>
    intro W _ _ _ hm S hS
    have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    have hsub : Subsingleton W := Module.finrank_zero_iff.1 hm
    refine ⟨?_, fun _ U U' _ _ => Or.inl ?_⟩
    · have : Subsingleton (W ≃ₗ[ZMod 2] W) :=
        ⟨fun a b => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
      rw [tri, Finset.range_zero, Finset.sum_empty, pow_zero]
      exact (Nat.card_of_subsingleton (1 : S)).le
    · intro x _
      rw [Subsingleton.elim x 0]
      exact U'.zero_mem
  | succ m ih =>
    intro W _ _ _ hm S hS
    classical
    have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    have : Nontrivial W := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨v, -, hv0, hvS⟩ := exists_fixed_mem S hS ⊤ (fun _ _ _ _ => trivial) top_ne_bot
    set N : Submodule (ZMod 2) W := (ZMod 2) ∙ v with hNdef
    have hNS : ∀ s ∈ S, N.map ((s : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = N := by
      intro s hs
      rw [hNdef, Submodule.map_span, Set.image_singleton]
      congr 2
      exact hvS s hs
    have hN1 : Module.finrank (ZMod 2) N = 1 := finrank_span_singleton hv0
    have hrank : Module.finrank (ZMod 2) (W ⧸ N) = m := by
      have := Submodule.finrank_quotient_add_finrank N
      omega
    set ρ := quotAct S N hNS with hρ
    have : Finite (W ⧸ N) := Finite.of_surjective N.mkQ (Submodule.mkQ_surjective N)
    obtain ⟨hb, hc⟩ := ih hrank ρ.range
      (hS.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective)
    have hfixN : ∀ s : S, ∀ x ∈ N, (s : W ≃ₗ[ZMod 2] W) x = x := by
      intro s x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [map_smul, hvS s s.2]
    have hker1 : ∀ s : ρ.ker, ∀ x, ((s : S) : W ≃ₗ[ZMod 2] W) x - x ∈ N := by
      intro s x
      have h := congrArg (fun f => f (Submodule.Quotient.mk x : W ⧸ N)) (MonoidHom.mem_ker.1 s.2)
      simp only [hρ, quotAct_mk] at h
      exact (Submodule.Quotient.eq N).1 h
    let ι : ρ.ker → ((W ⧸ N) →ₗ[ZMod 2] N) := fun s =>
      transvPart N ((s : S) : W ≃ₗ[ZMod 2] W) (hker1 s) (hfixN s)
    have hι : Function.Injective ι := by
      intro s t hst
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      have h := congrArg (fun f => ((f (Submodule.Quotient.mk x : W ⧸ N) : N) : W)) hst
      simp only [ι, transvPart_mk] at h
      exact sub_left_injective h
    have : Finite ((W ⧸ N) →ₗ[ZMod 2] N) := Module.finite_of_finite (ZMod 2)
    have hX : Nat.card ((W ⧸ N) →ₗ[ZMod 2] N) = 2 ^ m := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        Module.finrank_linearMap, hrank, hN1, mul_one]
    have hkle : Nat.card ρ.ker ≤ 2 ^ m := hX ▸ Nat.card_le_card_of_injective ι hι
    have hSeq : Nat.card S = Nat.card ρ.range * Nat.card ρ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    refine ⟨?_, fun hSc U U' hU hU' => ?_⟩
    · rw [hSeq, tri_succ, pow_add]
      exact Nat.mul_le_mul hb hkle
    · have hpow1 : 0 < 2 ^ tri m := pow_pos (by norm_num) _
      have hpow2 : 0 < 2 ^ m := pow_pos (by norm_num) _
      have hprod : Nat.card ρ.range * Nat.card ρ.ker = 2 ^ tri m * 2 ^ m := by
        rw [← hSeq, hSc, tri_succ, pow_add]
      have hreq : Nat.card ρ.range = 2 ^ tri m := by
        refine le_antisymm hb (Nat.le_of_not_lt fun hlt => ?_)
        have : Nat.card ρ.range * Nat.card ρ.ker < 2 ^ tri m * 2 ^ m :=
          lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt (Nat.pos_of_ne_zero (by
            intro h0
            rw [h0, mul_zero] at hprod
            exact absurd hprod.symm (Nat.mul_ne_zero hpow1.ne' hpow2.ne'))))
            (Nat.mul_le_mul_left _ hkle)
        omega
      have hkeq : Nat.card ρ.ker = 2 ^ m := by
        rw [hreq] at hprod
        exact Nat.eq_of_mul_eq_mul_left hpow1 hprod
      have hbij : Function.Bijective ι := hι.bijective_of_nat_card_le (by rw [hX, hkeq])
      have hfix : ∀ w : W, (∀ s ∈ S, (s : W ≃ₗ[ZMod 2] W) w = w) → w ∈ N := by
        intro w hw
        by_contra hwN
        obtain ⟨f, hfw, hNf⟩ := Submodule.exists_le_ker_of_notMem hwN
        let ψ : (W ⧸ N) →ₗ[ZMod 2] N :=
          N.liftQ (f.smulRight (⟨v, Submodule.mem_span_singleton_self v⟩ : N)) (by
            intro x hx
            rw [LinearMap.mem_ker, LinearMap.smulRight_apply, LinearMap.mem_ker.1 (hNf hx),
              zero_smul])
        obtain ⟨s, hs⟩ := hbij.2 ψ
        have h := congrArg (fun g => ((g (Submodule.Quotient.mk w : W ⧸ N) : N) : W)) hs
        simp only [ι, transvPart_mk, ψ, Submodule.liftQ_apply, LinearMap.smulRight_apply,
          zmod_two_eq_one hfw, one_smul] at h
        rw [hw _ (s : S).2, sub_self] at h
        exact hv0 h.symm
      have hNle : ∀ U : Submodule (ZMod 2) W, (∀ s ∈ S, ∀ u ∈ U, (s : W ≃ₗ[ZMod 2] W) u ∈ U) →
          U ≠ ⊥ → N ≤ U := by
        intro U hU hU0
        obtain ⟨u, huU, hu0, huS⟩ := exists_fixed_mem S hS U hU hU0
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hfix u huS)
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hc
          exact hu0 hc.symm
        rw [zmod_two_eq_one hc0, one_smul] at hc
        rw [hNdef, Submodule.span_singleton_le_iff_mem, hc]
        exact huU
      have hinv : ∀ U : Submodule (ZMod 2) W, (∀ s ∈ S, ∀ u ∈ U, (s : W ≃ₗ[ZMod 2] W) u ∈ U) →
          ∀ r ∈ ρ.range, ∀ x ∈ U.map N.mkQ, (r : (W ⧸ N) ≃ₗ[ZMod 2] (W ⧸ N)) x ∈ U.map N.mkQ := by
        intro U hU r hr x hx
        obtain ⟨s, rfl⟩ := hr
        obtain ⟨u, huU, rfl⟩ := hx
        rw [Submodule.mkQ_apply, hρ, quotAct_mk]
        exact ⟨_, hU _ s.2 _ huU, rfl⟩
      by_cases hU0 : U = ⊥
      · exact Or.inl (hU0 ▸ bot_le)
      by_cases hU'0 : U' = ⊥
      · exact Or.inr (hU'0 ▸ bot_le)
      rcases hc hreq (U.map N.mkQ) (U'.map N.mkQ) (hinv U hU) (hinv U' hU') with h | h
      · left
        have := Submodule.comap_mono (f := N.mkQ) h
        rwa [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.2 (hNle U hU hU0),
          sup_eq_right.2 (hNle U' hU' hU'0)] at this
      · right
        have := Submodule.comap_mono (f := N.mkQ) h
        rwa [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ, sup_eq_right.2 (hNle U hU hU0),
          sup_eq_right.2 (hNle U' hU' hU'0)] at this

end CFSG.Quasithin.H13.Flag
