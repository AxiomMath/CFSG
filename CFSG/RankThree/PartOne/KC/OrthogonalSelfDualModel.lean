module

public import CFSG.RankThree.PartOne.KC.OrthogonalPairedModel

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section SelfDual

variable {K : Type*} [Field K] {h : K[X]} [Fact (Irreducible h)]

theorem aeval_root_inv_eq_zero_of_self (h0 : h.coeff 0 ≠ 0)
    (hself : h = reciprocalPolynomial h) (hlam0 : AdjoinRoot.root h ≠ 0) :
    aeval (AdjoinRoot.root h)⁻¹ h = 0 := by
  have h1 := aeval_reciprocalPolynomial_of_unit (A := AdjoinRoot h) (Units.mk0 _ hlam0) h
  rw [← hself] at h1
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val] at h1
  have h2 : aeval (AdjoinRoot.root h) h = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [h2] at h1
  have h3 := h1.symm
  rw [Algebra.smul_def, mul_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact absurd (by simpa using h3) h0
  · exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ hlam0)

theorem exists_involution_root_inv (h0 : h.coeff 0 ≠ 0) (hself : h = reciprocalPolynomial h)
    (hlam0 : AdjoinRoot.root h ≠ 0) :
    ∃ σ : AdjoinRoot h ≃ₐ[K] AdjoinRoot h, σ (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ ∧
      ∀ z, σ (σ z) = z := by
  have hroot : h.eval₂ (Algebra.ofId K (AdjoinRoot h)) (AdjoinRoot.root h)⁻¹ = 0 := by
    have := aeval_root_inv_eq_zero_of_self h0 hself hlam0
    rwa [aeval_def] at this
  let σ₀ : AdjoinRoot h →ₐ[K] AdjoinRoot h :=
    AdjoinRoot.liftAlgHom h (Algebra.ofId K (AdjoinRoot h)) (AdjoinRoot.root h)⁻¹ hroot
  have hσ₀ : σ₀ (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hcomp : σ₀.comp σ₀ = AlgHom.id K (AdjoinRoot h) := by
    apply AdjoinRoot.algHom_ext
    simp [hσ₀, map_inv₀]
  have hσσ : ∀ z, σ₀ (σ₀ z) = z := fun z => AlgHom.congr_fun hcomp z
  exact ⟨AlgEquiv.ofAlgHom σ₀ σ₀ hcomp hcomp, hσ₀, hσσ⟩

end SelfDual

section SelfDualModel

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.selfDualModel (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    SelfDualModel Q x h (irreducible_of_mem_primaryFactors hh) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := (mem_primaryFactors.mp hh).2.1
  have : Fact (Irreducible h) := ⟨hirr⟩
  have h0 := hx.coeff_zero_ne hh
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hp0 : p ≠ 0 := fun h0' => hx.cast_ne_zero (by rw [h0']; simp)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0' => by
    rw [h0', zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  have hlaminv : (AdjoinRoot.root h)⁻¹ ≠ AdjoinRoot.root h := by
    intro heq
    have hsq : AdjoinRoot.root h ^ 2 = 1 := by
      have h1 := mul_inv_cancel₀ hlam0
      rw [heq] at h1
      rw [sq]
      exact h1
    obtain ⟨k, hk⟩ := hp2
    apply hlam1
    calc AdjoinRoot.root h = AdjoinRoot.root h * (AdjoinRoot.root h ^ 2) ^ k := by
          rw [hsq, one_pow, mul_one]
      _ = AdjoinRoot.root h ^ p := by rw [← pow_mul, ← pow_succ', hk]
      _ = 1 := hlamp
  obtain ⟨σ, hσlam, hσσ⟩ := exists_involution_root_inv h0 hself hlam0
  have hσne : σ ≠ 1 := fun h1 => hlaminv (by rw [← hσlam, h1]; rfl)
  obtain ⟨d, hd, hσ⟩ := exists_involution_eq_frobPow σ hσσ hσne
  have hσapp : ∀ z, σ z = z ^ (Nat.card K ^ d) := fun z => by rw [hσ, frobPow_apply]
  have hdeg : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  refine ⟨d, by rw [← hdeg, hd], fun z => ?_, ⟨AdjoinRoot.root h, ?_⟩, ?_, fun c => ?_, ?_, ?_⟩
  · rw [← hσapp, ← hσapp, hσσ]
  · rw [← hσapp, hσlam]
    exact hlaminv
  · exact (Nat.card_congr (Equiv.subtypeEquivRight fun z =>
      mem_fixedSubfield K (AdjoinRoot h) d z)).symm.trans (card_fixedSubfield K (AdjoinRoot h) hd)
  · rw [← hσapp, AlgEquiv.commutes]
  · rw [← hσapp, hσlam]
  · set U := primaryComponent x.toLinearMap h with hU
    let β : U →ₗ[K] U →ₗ[K] K := (QuadraticMap.polarBilin Q).compl₁₂ U.subtype U.subtype
    have hsymm : ∀ u w, β u w = β w u := fun u w => QuadraticMap.polar_comm Q _ _
    have hxinv : ∀ w : U, (((AdjoinRoot.root h)⁻¹ • w : U) : V) = x.symm (w : V) := by
      intro w
      have h1 : ((AdjoinRoot.root h • ((AdjoinRoot.root h)⁻¹ • w) : U) : V) = (w : V) := by
        rw [smul_inv_smul₀ hlam0]
      rw [coe_root_smul_primaryComponent x.toLinearMap h] at h1
      exact x.eq_symm_apply.mpr h1
    have hbal : ∀ (a : AdjoinRoot h) (u w : U), β (a • u) w = β u (σ a • w) := by
      intro a
      have ha : a ∈ Algebra.adjoin K {AdjoinRoot.root h} := by
        rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
      induction ha using Algebra.adjoin_induction with
      | mem a ha =>
        rw [Set.mem_singleton_iff] at ha
        subst ha
        intro u w
        change QuadraticMap.polar Q ((AdjoinRoot.root h • u : U) : V) (w : V) =
          QuadraticMap.polar Q (u : V) ((σ (AdjoinRoot.root h) • w : U) : V)
        rw [coe_root_smul_primaryComponent x.toLinearMap h, hσlam, hxinv]
        exact hx.polar_apply _ _
      | algebraMap c =>
        intro u w
        change QuadraticMap.polar Q ((algebraMap K (AdjoinRoot h) c • u : U) : V) (w : V) =
          QuadraticMap.polar Q (u : V) ((σ (algebraMap K (AdjoinRoot h) c) • w : U) : V)
        rw [AlgEquiv.commutes, coe_algebraMap_smul_primaryComponent x.toLinearMap h,
          coe_algebraMap_smul_primaryComponent x.toLinearMap h, QuadraticMap.polar_smul_left,
          QuadraticMap.polar_smul_right]
      | add a b _ _ ha hb =>
        intro u w
        rw [add_smul, map_add, LinearMap.add_apply, ha u w, hb u w, map_add σ, add_smul, map_add]
      | mul a b _ _ ha hb =>
        intro u w
        rw [mul_smul, ha (b • u) w, hb u (σ a • w), map_mul, mul_comm (σ a) (σ b), mul_smul]
    have hnd : ∀ u : U, (∀ w, β u w = 0) → u = 0 := fun u hu =>
      Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => hu ⟨w, hw⟩)
    have hunit : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ.toRingEquiv := by
      rw [hσ]
      exact isUnitaryInvolution K (AdjoinRoot h) hd
    obtain ⟨ι, hι⟩ := exists_hermitian_trace_coordinates β σ hunit hsymm hbal hnd
    set m := primaryMultiplicity x.toLinearMap h with hm
    let ι' : (Fin m → AdjoinRoot h) →ₗ[K] V := U.subtype ∘ₗ (ι.toLinearMap.restrictScalars K)
    have hι'x : ∀ a, x (ι' a) = ι' (AdjoinRoot.root h • a) := fun a => by
      have := coe_root_smul_primaryComponent x.toLinearMap h (ι a)
      change x ((ι a : U) : V) = ((ι (AdjoinRoot.root h • a) : U) : V)
      rw [map_smul]
      exact this.symm
    have hxQ : ∀ v, Q (x v) = Q v := fun v =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem v
    have hpolarH : ∀ a b, QuadraticMap.polar (hermitianForm hd) a b =
        Algebra.trace K (AdjoinRoot h) (a * σ b) := fun a b => by
      rw [hermitianForm_polar, hσ]
    have hTr : ∀ a b : Fin m → AdjoinRoot h, ∑ i, Algebra.trace K (AdjoinRoot h) (a i * σ (b i)) =
        Algebra.trace K (AdjoinRoot h) (∑ i, σ (a i) * b i) := fun a b => by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.trace_eq_of_algEquiv σ (a i * σ (b i)), map_mul, hσσ, mul_comm]
    have hD : ∀ a, Q (ι' a) = ∑ i, hermitianForm hd (a i) := by
      refine fun a => sub_eq_zero.mp (eq_zero_of_additive_smul_invariant hx.cast_ne_zero hlam1
        hlamp (AddMonoidHom.mk' (fun a => Q (ι' a) - ∑ i, hermitianForm hd (a i)) fun a b => ?_)
        (fun a => ?_) a)
      · have h1 : Q (ι' (a + b)) = Q (ι' a) + Q (ι' b) +
            Algebra.trace K (AdjoinRoot h) (∑ i, σ (a i) * b i) := by
          rw [map_add, QuadraticMap.map_add (⇑Q) _ _]
          congr 1
          exact hι a b
        have h2 : ∑ i, hermitianForm hd ((a + b) i) = ∑ i, hermitianForm hd (a i) +
            ∑ i, hermitianForm hd (b i) + Algebra.trace K (AdjoinRoot h) (∑ i, σ (a i) * b i) := by
          rw [← hTr, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.add_apply, QuadraticMap.map_add (⇑(hermitianForm hd)) _ _, hpolarH]
        rw [h1, h2]
        ring
      · have hu : ((Units.mk0 _ hlam0 : (AdjoinRoot h)ˣ) : AdjoinRoot h) *
            σ (Units.mk0 _ hlam0 : (AdjoinRoot h)ˣ) = 1 := by
          simp [hσlam, hlam0]
        change Q (ι' (AdjoinRoot.root h • a)) - ∑ i, hermitianForm hd ((AdjoinRoot.root h • a) i) =
          Q (ι' a) - ∑ i, hermitianForm hd (a i)
        rw [← hι'x, hxQ]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hermitianForm_mulEquiv (K := K) hd (Units.mk0 _ hlam0) (by rw [← hσ]; exact hu)
          (a i)
        simpa using this
    refine ⟨ι', fun a b hab => ι.injective (Subtype.ext hab), ?_, fun a => ?_, hι'x⟩
    · ext u
      constructor
      · rintro ⟨a, rfl⟩
        exact (ι a).2
      · intro hu
        exact ⟨ι.symm ⟨u, hu⟩, by simp [ι']⟩
    · have hmem : ∑ i, a i * a i ^ (Nat.card K ^ d) ∈ fixedSubfield K (AdjoinRoot h) d :=
        sum_mem fun i _ => by simpa [frobPow_apply] using mul_frobPow_mem_fixedSubfield hd (a i)
      refine ⟨hmem, ?_⟩
      rw [hD]
      have : (⟨∑ i, a i * a i ^ (Nat.card K ^ d), hmem⟩ : fixedSubfield K (AdjoinRoot h) d) =
          ∑ i, unitaryNorm hd (a i) := by
        apply Subtype.ext
        simp [coe_unitaryNorm, frobPow_apply]
      rw [this, map_sum]
      rfl

end SelfDualModel

end CFSG.RankThree.PartOne.KCOrthogonal
