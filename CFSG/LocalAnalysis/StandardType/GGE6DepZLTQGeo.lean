module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal


theorem exists_qGeo {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω]
    [Algebra K Ω] (τ : GaloisField 2 (2 * n) ≃+* K)
    (hτ : τ.toRingHom.comp (frobQ 2 n) = σ.toRingHom.comp τ.toRingHom) :
    ∃ q : twistedE6Group 2 n →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      Function.Surjective q ∧ q.ker ≤ Subgroup.center (twistedE6Group 2 n) ∧
      ∀ u : twistedE6Group 2 n,
        baseChangeGL (algebraMap K Ω) ((q u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
            ModGL TwistTag.E6.tag K) =
          baseChangeGL ((algebraMap K Ω).comp τ.toRingHom)
            ((e6Isogeny (GaloisField 2 (2 * n))
              (u : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * n)))) :
                ↥(adjointGroup Tag.E6 (GaloisField 2 (2 * n)))) :
              ModGL Tag.E6 (GaloisField 2 (2 * n))) := by
  have hτ' : τ.symm.toRingHom.comp σ.toRingHom = (frobQ 2 n).comp τ.symm.toRingHom :=
    RingHom.ext fun c => by
      change τ.symm.toRingHom (σ c) = frobQ 2 n (τ.symm.toRingHom c)
      rw [frobQ_apply, hσ, map_pow]
  have hΓ : ⁅twistedFixedGroup .E6 K σ.toRingHom, twistedFixedGroup .E6 K σ.toRingHom⁆ =
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ).2.2.1
  let q : twistedE6Group 2 n →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    (MulEquiv.subgroupCongr hΓ).toMonoidHom.comp
      ((MpStdTwE6.derivedEquiv τ hτ hτ' .E6).toMonoidHom.comp (twistedE6Isogeny 2 n hn))
  refine ⟨q, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := (MulEquiv.subgroupCongr hΓ).surjective y
    obtain ⟨w, hw⟩ := (MpStdTwE6.derivedEquiv τ hτ hτ' .E6).surjective x
    obtain ⟨u, hu⟩ := twistedE6Isogeny_surjective 2 n hn w
    refine ⟨u, ?_⟩
    show (MulEquiv.subgroupCongr hΓ)
      ((MpStdTwE6.derivedEquiv τ hτ hτ' .E6) (twistedE6Isogeny 2 n hn u)) = y
    rw [hu, hw, hx]
  · intro u hu
    have h1 : u ∈ (twistedE6Isogeny 2 n hn).ker := by
      rw [MonoidHom.mem_ker] at hu ⊢
      have h2 : MpStdTwE6.derivedEquiv τ hτ hτ' .E6 (twistedE6Isogeny 2 n hn u) = 1 := by
        apply (MulEquiv.subgroupCongr hΓ).injective
        show q u = (MulEquiv.subgroupCongr hΓ) 1
        rw [hu, map_one]
      apply (MpStdTwE6.derivedEquiv τ hτ hτ' .E6).injective
      rw [h2, map_one]
    exact RootDetectTwE6.ker_le_center n (twistedE6Isogeny 2 n hn)
      (coe_twistedE6Isogeny 2 n hn) h1
  · intro u
    show baseChangeGL (algebraMap K Ω)
        (((MulEquiv.subgroupCongr hΓ)
          ((MpStdTwE6.derivedEquiv τ hτ hτ' .E6) (twistedE6Isogeny 2 n hn u)) :
            ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) = _
    rw [MulEquiv.subgroupCongr_apply, MpStdTwE6.coe_derivedEquiv, baseChangeGL_baseChangeGL]
    rfl

end CFSG.StandardType.E6Dep.ZL

end
