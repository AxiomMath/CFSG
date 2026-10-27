module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAbstract

public section

namespace CFSG.RankThree.PartOne.KCSymplectic

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

section Det

variable {r : ℕ} {K : Type} [Field K]

theorem mem_spPull_of_blockGLDet {x : StatedSp r K} {h : K[X]} {g : StatedSp r K}
    (hg : g ∈ spSupported x {h, reciprocalPolynomial h}) (γ : blockGL (spEnd x) h)
    (hγ : ∀ (v : Fin r ⊕ Fin r → K) (hv : v ∈ primaryComponent (spEnd x) h),
      blockApply γ v hv = spEnd g v) (hdet : blockGLDet (spEnd x) h γ = 1) : g ∈ spPull x h := by
  have hOrb : spLin r K g ∈ orbitFactor (spForm r K) (spLin r K x) h := by
    rw [orbitFactor_spForm]
    exact hg
  have hgl : spLin r K g ∈ gl_centralizer (spLin r K x) := orbitFactor_le_gl_centralizer hOrb
  have hrestr : blockRestrict (spLin r K x) h ⟨spLin r K g, hgl⟩ = γ :=
    blockGL_ext fun v hv => (blockApply_blockRestrict _ _ _ v hv).trans (hγ v hv).symm
  refine mem_specialBlock.mpr ⟨hOrb, hgl, ?_⟩
  change blockGLDet (spEnd x) h (blockRestrict (spLin r K x) h ⟨spLin r K g, hgl⟩) = 1
  rw [hrestr]
  exact hdet

end Det

section Model

variable {r : ℕ} {K : Type} [Field K] {x : StatedSp r K} {h : primaryFactors (spEnd x)}

theorem exists_local_of_model {p : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X]))
    {F : Subgroup (StatedSp r K)} (hF : F = spSupported x {(h : K[X]), reciprocalPolynomial h})
    (ψ : F →* (primaryComponent (spEnd x) (h : K[X]) ≃ₗ[AdjoinRoot (h : K[X])]
      primaryComponent (spEnd x) (h : K[X])))
    (hψ : Function.Injective ψ)
    (hact : ∀ (g : F) (w : primaryComponent (spEnd x) (h : K[X])),
      ((ψ g w : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) =
        spEnd (g : StatedSp r K) (w : Fin r ⊕ Fin r → K))
    (hscal : ∀ c : (AdjoinRoot (h : K[X]))ˣ, c ^ p = 1 →
      DistribMulAction.toModuleAut (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X])) c ∈ ψ.range)
    {t : StatedSp r K} (ht : t ∈ F) (htp : t ^ p = 1) :
    ∃ s k : StatedSp r K, s ∈ F ∧ k ∈ F ∧ k ∈ spPull x (h : K[X]) ∧ t = s * k ∧
      (∀ g ∈ F, s * g = g * s) ∧ s ^ p = 1 ∧ k ^ p = 1 := by
  obtain ⟨s, hsc, hsp, hsd⟩ := exists_scalar_factor ψ hψ hp hpm hscal (t := (⟨t, ht⟩ : F))
    (Subtype.ext (by simpa using htp))
  set t' : F := ⟨t, ht⟩ with ht'
  set k' : F := s⁻¹ * t' with hk'
  have hsk : Commute s⁻¹ t' := (show Commute s t' from hsc t').inv_left
  refine ⟨(s : StatedSp r K), (k' : StatedSp r K), s.2, k'.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    let gl := LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot (h : K[X]))
      (primaryComponent (spEnd x) (h : K[X]))
    have hdet : LinearEquiv.det (ψ k') = 1 := by
      rw [hk', map_mul, map_mul, map_inv, map_inv, hsd, inv_mul_cancel]
    refine mem_spPull_of_blockGLDet (hF ▸ k'.2) (gl.symm (ψ k')) (fun v hv => ?_) ?_
    · have h1 : (gl.symm (ψ k') : Module.End (AdjoinRoot (h : K[X]))
          (primaryComponent (spEnd x) (h : K[X]))) ⟨v, hv⟩ = ψ k' ⟨v, hv⟩ :=
        congrArg (fun f => f ⟨v, hv⟩) (gl.apply_symm_apply (ψ k'))
      change (((gl.symm (ψ k') : Module.End (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X]))) ⟨v, hv⟩ : primaryComponent (spEnd x)
          (h : K[X])) : Fin r ⊕ Fin r → K) = _
      rw [h1]
      exact hact k' ⟨v, hv⟩
    · refine Units.ext ?_
      have h2 := congrArg (fun u : (AdjoinRoot (h : K[X]))ˣ => (u : AdjoinRoot (h : K[X]))) hdet
      simp only [LinearEquiv.coe_det, Units.val_one] at h2
      have h3 : ((ψ k' : primaryComponent (spEnd x) (h : K[X]) ≃ₗ[AdjoinRoot (h : K[X])]
          primaryComponent (spEnd x) (h : K[X])) : Module.End (AdjoinRoot (h : K[X]))
            (primaryComponent (spEnd x) (h : K[X]))) =
          (gl.symm (ψ k') : Module.End (AdjoinRoot (h : K[X]))
            (primaryComponent (spEnd x) (h : K[X]))) := by
        conv_lhs => rw [← gl.apply_symm_apply (ψ k')]
        rfl
      change LinearMap.det (gl.symm (ψ k') : Module.End (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X]))) = 1
      rw [← h3]
      exact h2
  ·
    rw [hk']
    show t = ((s * (s⁻¹ * t') : F) : StatedSp r K)
    rw [mul_inv_cancel_left]
  · exact fun g hg => congrArg Subtype.val (hsc ⟨g, hg⟩)
  · rw [← Subgroup.coe_pow, hsp]
    rfl
  · rw [← Subgroup.coe_pow, hk', hsk.mul_pow, inv_pow, hsp, inv_one, one_mul]
    have : t' ^ p = 1 := Subtype.ext (by simpa using htp)
    rw [this]
    rfl

end Model


section Paired

variable {r : ℕ} {K : Type} [Field K] {x : StatedSp r K} {h : primaryFactors (spEnd x)}

theorem exists_local_paired {ℓ f p : ℕ} (hP : SpPairedBlock ℓ f p x h) (hp : p.Prime)
    (hpm : ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X])) {t : StatedSp r K}
    (ht : t ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) (htp : t ^ p = 1) :
    ∃ s k : StatedSp r K, s ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ∧
      k ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ∧
      k ∈ spPull x (h : K[X]) ∧ t = s * k ∧
      (∀ g ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}, s * g = g * s) ∧
      s ^ p = 1 ∧ k ^ p = 1 := by
  obtain ⟨φ, hφ, -⟩ := hP.factor
  let gl := LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot (h : K[X]))
    (primaryComponent (spEnd x) (h : K[X]))
  let ψ := gl.toMonoidHom.comp φ.toMonoidHom
  have hsurj : Function.Surjective ψ := gl.surjective.comp φ.surjective
  exact exists_local_of_model hp hpm rfl ψ (gl.injective.comp φ.injective)
    (fun g w => hφ g w w.2) (fun c _ => MonoidHom.mem_range.2 (hsurj _)) ht htp

end Paired

section SelfDual

variable {r : ℕ} {K : Type} [Field K] {x : StatedSp r K} {h : primaryFactors (spEnd x)}

theorem exists_local_selfDual {ℓ f p : ℕ} (hS : SpSelfDualBlock ℓ f p x h)
    (hself : reciprocalPolynomial (h : K[X]) = h) (hp : p.Prime)
    (hpm : ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X])) {t : StatedSp r K}
    (ht : t ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) (htp : t ^ p = 1) :
    ∃ s k : StatedSp r K, s ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ∧
      k ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ∧
      k ∈ spPull x (h : K[X]) ∧ t = s * k ∧
      (∀ g ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}, s * g = g * s) ∧
      s ^ p = 1 ∧ k ^ p = 1 := by
  obtain ⟨d, -, hpd, σ, hσq, -, -, -, -, hE, hbar, Hf, -, -, -, -, φ, hφ⟩ := hS.exists_half
  have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
    rw [hself, Set.pair_eq_singleton]
  let gl := LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot (h : K[X]))
    (primaryComponent (spEnd x) (h : K[X]))
  let ψ := gl.toMonoidHom.comp ((sesqUnitaryGroup Hf).subtype.comp φ.toMonoidHom)
  have hcoe : ∀ (δ : primaryComponent (spEnd x) (h : K[X]) ≃ₗ[AdjoinRoot (h : K[X])]
      primaryComponent (spEnd x) (h : K[X])) u,
      (((gl.symm δ : blockGL (spEnd x) (h : K[X])) :
        Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))) u) = δ u :=
    fun δ u => congrArg (fun f => f u) (gl.apply_symm_apply δ)
  have key : ∀ δ : primaryComponent (spEnd x) (h : K[X]) ≃ₗ[AdjoinRoot (h : K[X])]
      primaryComponent (spEnd x) (h : K[X]), (∀ u v, Hf (δ u) (δ v) = Hf u v) → δ ∈ ψ.range := by
    intro δ hδ
    have hmem : gl.symm δ ∈ sesqUnitaryGroup Hf :=
      mem_sesqUnitaryGroup.2 fun u v => by rw [hcoe, hcoe]; exact hδ u v
    refine MonoidHom.mem_range.2 ⟨φ.symm ⟨gl.symm δ, hmem⟩, ?_⟩
    change gl ((φ (φ.symm ⟨gl.symm δ, hmem⟩) : sesqUnitaryGroup Hf) :
      blockGL (spEnd x) (h : K[X])) = δ
    rw [MulEquiv.apply_symm_apply]
    exact gl.apply_symm_apply δ
  have hscal : ∀ c : (AdjoinRoot (h : K[X]))ˣ, c ^ p = 1 →
      DistribMulAction.toModuleAut (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X])) c ∈ ψ.range := by
    intro c hc
    refine key _ fun u v => ?_
    have hbc : hE.bar (c : AdjoinRoot (h : K[X])) * (c : AdjoinRoot (h : K[X])) = 1 := by
      rw [hbar, hσq, ← pow_succ]
      obtain ⟨k, hk⟩ := hpd
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hc, Units.val_one, one_pow]
    change Hf ((c : AdjoinRoot (h : K[X])) • u) ((c : AdjoinRoot (h : K[X])) • v) = Hf u v
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      mul_comm (c : AdjoinRoot (h : K[X])) (hE.bar (c : AdjoinRoot (h : K[X]))), hbc, one_mul]
  obtain ⟨s, k, hs, hk, hkP, hts, hsc, hsp, hkp⟩ := exists_local_of_model
    (F := spSupported x {(h : K[X])}) hp hpm (by rw [hO]) ψ
    (gl.injective.comp (Subtype.val_injective.comp φ.injective)) (fun g w => hφ g w w.2) hscal
    (by rw [← hO]; exact ht) htp
  refine ⟨s, k, ?_, ?_, hkP, hts, fun g hg => hsc g ?_, hsp, hkp⟩
  · rw [hO]
    exact hs
  · rw [hO]
    exact hk
  · rw [← hO]
    exact hg

end SelfDual

end CFSG.RankThree.PartOne.KCSymplectic
