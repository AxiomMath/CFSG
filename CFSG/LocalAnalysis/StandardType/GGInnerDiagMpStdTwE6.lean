module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdTwE6Core
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace MpStdTwE6

section Perfect

theorem commutator_twistedE6Group {f : ℕ} (hf : 1 ≤ f) : commutator (twistedE6Group 2 f) = ⊤ := by
  have h4 : 4 ≤ Nat.card (GaloisField 2 (2 * f)) := by
    rw [GaloisField.card 2 (2 * f) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (fixedGroup_isPerfect_of_four_le_card (frobQ 2 f) (frobQ_frobQ 2 f hf) h4).commutator_eq_top

end Perfect

section Std

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (τ : GaloisField 2 (2 * f) ≃+* K)
  {σ : K →+* K} (hτ : τ.toRingHom.comp (frobQ 2 f) = σ.comp τ.toRingHom)
  (hτ' : τ.symm.toRingHom.comp σ = (frobQ 2 f).comp τ.symm.toRingHom)
  (T : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ ≃*
    ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f))

@[expose] noncomputable def stdHom :
    twistedE6Group 2 f →* ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f) :=
  T.toMonoidHom.comp ((derivedEquiv τ hτ hτ' .E6).toMonoidHom.comp (twistedE6Isogeny 2 f hf))

theorem stdHom_apply (u : twistedE6Group 2 f) :
    stdHom hf τ hτ hτ' T u = T (derivedEquiv τ hτ hτ' .E6 (twistedE6Isogeny 2 f hf u)) :=
  rfl

theorem stdHom_surjective : Function.Surjective (stdHom hf τ hτ hτ' T) := by
  intro y
  obtain ⟨x, hx⟩ := T.surjective y
  obtain ⟨w, hw⟩ := (derivedEquiv τ hτ hτ' .E6).surjective x
  obtain ⟨u, hu⟩ := twistedE6Isogeny_surjective 2 f hf w
  refine ⟨u, ?_⟩
  rw [stdHom_apply, hu, hw, hx]

theorem ker_stdHom_le_center :
    (stdHom hf τ hτ hτ' T).ker ≤ Subgroup.center (twistedE6Group 2 f) := by
  intro u hu
  have h1 : u ∈ (twistedE6Isogeny 2 f hf).ker := by
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [stdHom_apply] at hu
    have h2 : derivedEquiv τ hτ hτ' .E6 (twistedE6Isogeny 2 f hf u) = 1 := by
      apply T.injective
      rw [hu, map_one]
    apply (derivedEquiv τ hτ hτ' .E6).injective
    rw [h2, map_one]
  exact RootDetectTwE6.ker_le_center f (twistedE6Isogeny 2 f hf)
    (coe_twistedE6Isogeny 2 f hf) h1

end Std


section Ends

variable {K : Type} [Field K] (e : Module.End K (RootModule TwistTag.E6.tag K) ≃*
    Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))
  (he : ∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
    e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan K b)

include he in
theorem e_conj_rootDiag (a : Fin TwistTag.E6.tag.rank → Kˣ) (g : ModGL TwistTag.E6.tag K) :
    e (((rootDiagUnit TwistTag.E6.tag a * g * (rootDiagUnit TwistTag.E6.tag a)⁻¹ :
        ModGL TwistTag.E6.tag K)) : Module.End K (RootModule TwistTag.E6.tag K)) =
      LargeEvenDiagMap TwistTag.E6.tag.cartan K a *
        e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) *
          LargeEvenDiagMap TwistTag.E6.tag.cartan K a⁻¹ := by
  have h1 : ((rootDiagUnit TwistTag.E6.tag a : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) = rootDiag a := rfl
  have h2 : (((rootDiagUnit TwistTag.E6.tag a)⁻¹ : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) = rootDiag a⁻¹ := rfl
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul, h1, h2, he, he]

theorem largeEvenDiagMap_mul_inv (a : Fin TwistTag.E6.tag.rank → Kˣ) :
    LargeEvenDiagMap TwistTag.E6.tag.cartan K a * LargeEvenDiagMap TwistTag.E6.tag.cartan K a⁻¹ =
      1 := by
  rw [← TableB.largeEvenDiagMap_mul, mul_inv_cancel, TableB.largeEvenDiagMap_one]

end Ends

section Xi

variable {f : ℕ} {K : Type} [Field K] (τ : GaloisField 2 (2 * f) ≃+* K)
  {σ : K →+* K} (hτ : τ.toRingHom.comp (frobQ 2 f) = σ.comp τ.toRingHom)
  (hτ' : τ.symm.toRingHom.comp σ = (frobQ 2 f).comp τ.symm.toRingHom)
  (T : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ ≃*
    ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f))
  (hZ : Subgroup.center ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f) = ⊥)

@[expose] noncomputable def xiEquiv :
    LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f) ≃*
      ↥⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
        twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆ :=
  (centerQuotEquivOfBot hZ).trans (T.symm.trans (derivedEquiv τ hτ hτ' .E6).symm)

theorem xiEquiv_mk (h : ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f)) :
    xiEquiv τ hτ hτ' T hZ (LargeEvenCenterMk _ h) = (derivedEquiv τ hτ hτ' .E6).symm (T.symm h) := by
  rw [xiEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, centerQuotEquivOfBot_mk]

theorem xiEquiv_symm_apply (x : ↥⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
    twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆) :
    (xiEquiv τ hτ hτ' T hZ).symm x = LargeEvenCenterMk _ (T (derivedEquiv τ hτ hτ' .E6 x)) := by
  rw [MulEquiv.symm_apply_eq, xiEquiv_mk, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end Xi

section Act

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (τ : GaloisField 2 (2 * f) ≃+* K)
  {σ : K →+* K} (hτ : τ.toRingHom.comp (frobQ 2 f) = σ.comp τ.toRingHom)
  (hτ' : τ.symm.toRingHom.comp σ = (frobQ 2 f).comp τ.symm.toRingHom)
  (T : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ ≃*
    ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f))
  (hZ : Subgroup.center ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f) = ⊥)

theorem xiEquiv_mk_stdHom (u : twistedE6Group 2 f) :
    xiEquiv τ hτ hτ' T hZ (LargeEvenCenterMk _ (stdHom hf τ hτ hτ' T u)) = twistedE6Isogeny 2 f hf u := by
  rw [xiEquiv_mk, stdHom_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

variable (e : Module.End K (RootModule TwistTag.E6.tag K) ≃*
    Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))
  (hT : ∀ g, ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
    Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
      e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)))
  (he : ∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
    e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan K b)

include hT he in
theorem ggInndiag_le
    (hΓ : ⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ =
      graphFixedRootGroup TwistTag.E6 K σ) :
    ggInndiag (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f))
        (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
          (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f)) ≤
      ((diagTw .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
        (⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
          twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆).normalizerMonoidHom).comap
        (MulAut.congr (xiEquiv τ hτ hτ' T hZ)).toMonoidHom := by
  have hInn : ∀ r, MulAut.conj r ∈
      ((diagTw .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
        (⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
          twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆).normalizerMonoidHom).comap
        (MulAut.congr (xiEquiv τ hτ hτ' T hZ)).toMonoidHom := by
    intro r
    refine ⟨⟨(xiEquiv τ hτ hτ' T hZ r : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))),
      Subgroup.le_normalizer (xiEquiv τ hτ hτ' T hZ r).2⟩,
      ⟨xiEquiv τ hτ hτ' T hZ r, (xiEquiv τ hτ hτ' T hZ r).2, 1, isCompat_one,
        by rw [MpStdE6.rootDiagUnit_one, mul_one]⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    show (xiEquiv τ hτ hτ' T hZ r : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) * x *
        (xiEquiv τ hτ hτ' T hZ r : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹ =
      ((xiEquiv τ hτ hτ' T hZ (r * (xiEquiv τ hτ hτ' T hZ).symm x * r⁻¹) :
        ↥⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
          twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  have hDiag : ∀ φ ∈ LargeEvenChevDiagImage TwistTag.E6.tag.cartan K
      (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f), φ ∈
      ((diagTw .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
        (⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
          twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆).normalizerMonoidHom).comap
        (MulAut.congr (xiEquiv τ hτ hτ' T hZ)).toMonoidHom := by
    rintro φ ⟨a, h1, -, hφ⟩
    have hnorm : ∀ x ∈ ⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆,
        rootDiagUnit TwistTag.E6.tag a * x * (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈
          ⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ := by
      intro x hx
      obtain ⟨h', hh'⟩ := h1 (T ⟨x, hx⟩)
      have hy : ((T.symm h' : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆) :
          ModGL TwistTag.E6.tag K) =
          rootDiagUnit TwistTag.E6.tag a * x * (rootDiagUnit TwistTag.E6.tag a)⁻¹ := by
        apply Units.ext
        apply e.injective
        rw [← hT (T.symm h'), MulEquiv.apply_symm_apply, e_conj_rootDiag e he a x]
        have hx' := hT ⟨x, hx⟩
        rw [← hx']
        calc ((h' : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
              Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
            ((h' : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
              Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) *
              (LargeEvenDiagMap TwistTag.E6.tag.cartan K a *
                LargeEvenDiagMap TwistTag.E6.tag.cartan K a⁻¹) := by
              rw [largeEvenDiagMap_mul_inv, mul_one]
          _ = _ := by rw [← mul_assoc, hh']
      rw [← hy]
      exact (T.symm h').2
    have hcK : IsCompat σ a := fun i =>
      TableB.TwE6.compat_of_forall_conj_mem (t := TwistTag.E6) (σ := σ) (b := a)
        (fun g hg => by
          rw [← hΓ] at hg ⊢
          exact hnorm g hg) i
    set a' : Fin TwistTag.E6.tag.rank → (GaloisField 2 (2 * f))ˣ :=
      fun i => Units.map τ.symm.toRingHom.toMonoidHom (a i) with ha'def
    have ha' : IsCompat (frobQ 2 f) a' := isCompat_symm τ hτ' hcK
    have haa : (fun i => Units.map τ.toRingHom.toMonoidHom (a' i)) = a := by
      funext i
      apply Units.ext
      simp [ha'def]
    refine ⟨⟨rootDiagUnit TwistTag.E6.tag a', rootDiagUnit_mem_normalizer_derived ha'⟩,
      ⟨1, one_mem _, a', ha', by rw [one_mul]⟩, MulEquiv.ext fun x => ?_⟩
    set y : ↥⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
        twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆ :=
      ⟨rootDiagUnit TwistTag.E6.tag a' * (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (rootDiagUnit TwistTag.E6.tag a')⁻¹, conj_rootDiag_mem_derived ha' x.2⟩ with hydef
    have hyx : (⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
        twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆).normalizerMonoidHom
        ⟨rootDiagUnit TwistTag.E6.tag a', rootDiagUnit_mem_normalizer_derived ha'⟩ x = y := rfl
    have hB : ((derivedEquiv τ hτ hτ' .E6 y : ↥⁅twistedFixedGroup .E6 K σ,
        twistedFixedGroup .E6 K σ⁆) : ModGL TwistTag.E6.tag K) =
        rootDiagUnit TwistTag.E6.tag a *
          ((derivedEquiv τ hτ hτ' .E6 x : ↥⁅twistedFixedGroup .E6 K σ,
            twistedFixedGroup .E6 K σ⁆) : ModGL TwistTag.E6.tag K) *
          (rootDiagUnit TwistTag.E6.tag a)⁻¹ := by
      rw [coe_derivedEquiv, coe_derivedEquiv, hydef]
      show baseChangeGL τ.toRingHom (rootDiagUnit TwistTag.E6.tag a' *
        (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          (rootDiagUnit TwistTag.E6.tag a')⁻¹) = _
      rw [MpStdE6.baseChangeGL_conj_rootDiag, haa]
    have hrel : ((T (derivedEquiv τ hτ hτ' .E6 y) : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
          Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) *
          LargeEvenDiagMap TwistTag.E6.tag.cartan K a =
        LargeEvenDiagMap TwistTag.E6.tag.cartan K a *
          ((T (derivedEquiv τ hτ hτ' .E6 x) : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) := by
      rw [hT, hT, hB, e_conj_rootDiag e he a, mul_assoc, mul_assoc,
        show LargeEvenDiagMap TwistTag.E6.tag.cartan K a⁻¹ *
          LargeEvenDiagMap TwistTag.E6.tag.cartan K a = 1 by
          rw [← TableB.largeEvenDiagMap_mul, inv_mul_cancel, TableB.largeEvenDiagMap_one],
        mul_one]
    have h1' := hφ (T (derivedEquiv τ hτ hτ' .E6 x)) (T (derivedEquiv τ hτ hτ' .E6 y)) hrel
    rw [hyx]
    show y = xiEquiv τ hτ hτ' T hZ (φ ((xiEquiv τ hτ hτ' T hZ).symm x))
    rw [xiEquiv_symm_apply, h1', xiEquiv_mk, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]
  refine sup_le ?_ ((Subgroup.closure_le _).mpr ?_)
  · rintro _ ⟨r, rfl⟩
    exact hInn r
  · intro φ hφ
    refine (Subgroup.closure_le _).mpr ?_ hφ
    rintro ψ' (⟨r, rfl⟩ | hψ')
    · exact hInn r
    · exact hDiag ψ' hψ'

end Act

section Rev

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (τ : GaloisField 2 (2 * f) ≃+* K)
  {σ : K →+* K} (hτ : τ.toRingHom.comp (frobQ 2 f) = σ.comp τ.toRingHom)
  (hτ' : τ.symm.toRingHom.comp σ = (frobQ 2 f).comp τ.symm.toRingHom)
  (T : ↥⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ ≃*
    ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f))
  (hZ : Subgroup.center ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f) = ⊥)
  (e : Module.End K (RootModule TwistTag.E6.tag K) ≃*
    Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K))
  (hT : ∀ g, ((T g : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
    Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
      e ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)))
  (he : ∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
    e (rootDiag b) = LargeEvenDiagMap TwistTag.E6.tag.cartan K b)
  (hΓ : ⁅twistedFixedGroup .E6 K σ, twistedFixedGroup .E6 K σ⁆ =
    graphFixedRootGroup TwistTag.E6 K σ)

include hf hτ hτ' hZ hT he hΓ in
theorem exists_stdEquiv_revProp {G : Type} [Group G] (ψ : twistedE6Group 2 f →* G)
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f)) :
    ∃ θ₀ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃*
        LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f),
      GGRevProp (twistedE6Datum 2 f) ψ ψ.range
        (ggInndiag (LargeEvenCenterQuot
            (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f))
          (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
            (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f))) θ₀ := by
  obtain ⟨θ, hθ⟩ := InnerDiagTwE6.exists_centerQuot_equiv (commutator_twistedE6Group hf) ψ hker
    (stdHom hf τ hτ hτ' T) (stdHom_surjective hf τ hτ hτ' T) (ker_stdHom_le_center hf τ hτ hτ' T)
    hZ
  refine ⟨θ, ?_⟩
  rintro c hc ⟨φ, hφ, hind⟩
  obtain ⟨y, ⟨g, hg, a, ha, hy⟩, hκ⟩ := ggInndiag_le τ hτ hτ' T hZ e hT he hΓ hφ
  obtain ⟨a₀, ha₀⟩ := twistedE6Isogeny_surjective 2 f hf ⟨g, hg⟩
  have ha₀' : ((twistedE6Isogeny 2 f hf a₀ : ↥⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f))
      (frobQ 2 f), twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) = g := by rw [ha₀]
  refine MpStdE6.ggPsiInnerDiag_of_conj_diag (twistedE6Datum 2 f)
    (RootDetectTwE6.ker_le_center f (twistedE6Isogeny 2 f hf) (coe_twistedE6Isogeny 2 f hf))
    (RootDetectTwE6.odd_card_ker f (twistedE6Isogeny 2 f hf) (coe_twistedE6Isogeny 2 f hf))
    (RootDetectTwE6.twistedRootGroup_mul_self f) a (fun β hβ => ?_) hc a₀ fun y₁ y₂ h12 => ?_
  · obtain ⟨h, hh, hz⟩ := RootDetectTwE6.hdiag_twisted (frobQ 2 f) (frobQ_frobQ 2 f hf) a ha β hβ
    exact ⟨h, hh, fun z hzm => hz z hzm⟩
  · have h1 := hind (ψ.rangeRestrict y₁) (ψ.rangeRestrict y₂) h12
    rw [hθ, hθ] at h1
    have h2 : (MulAut.congr (xiEquiv τ hτ hτ' T hZ)).toMonoidHom φ (twistedE6Isogeny 2 f hf y₁) =
        twistedE6Isogeny 2 f hf y₂ := by
      show xiEquiv τ hτ hτ' T hZ (φ ((xiEquiv τ hτ hτ' T hZ).symm (twistedE6Isogeny 2 f hf y₁))) =
        twistedE6Isogeny 2 f hf y₂
      rw [← xiEquiv_mk_stdHom hf τ hτ hτ' T hZ y₁, MulEquiv.symm_apply_apply, h1,
        xiEquiv_mk_stdHom]
    rw [← hκ] at h2
    have h3 := congrArg Subtype.val h2
    rw [← h3, ha₀']
    show (y : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        ((twistedE6Isogeny 2 f hf y₁ : ↥⁅twistedFixedGroup .E6 (GaloisField 2 (2 * f))
          (frobQ 2 f), twistedFixedGroup .E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (y : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹ = _
    rw [hy]
    group

end Rev

end MpStdTwE6

section Input

theorem ggInnerDiagStdTwE6_holds : GGInnerDiagStdTwE6 := by
  intro G _ _ f ψ hadm hker K _ _ hK
  have hf : 1 ≤ f := hadm.2.1
  have : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 f with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * f))
  have hcard : Fintype.card (GaloisField 2 (2 * f)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_galoisField_two_mul 2 f hf,
      hK]
  set τ := FiniteField.ringEquivOfCardEq hcard
  have hτ : τ.toRingHom.comp (frobQ 2 f) = σ.comp τ.toRingHom := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, frobQ_apply, hσ, map_pow]
  have hτ' : τ.symm.toRingHom.comp σ = (frobQ 2 f).comp τ.symm.toRingHom :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, frobQ_apply, hσ, map_pow]
  obtain ⟨e, T, hT, he⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) f σ hσ
  have hΓ := (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf K hK σ hσ).2.2.1
  have hZ : Subgroup.center ↥(LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f) =
      ⊥ := by
    obtain ⟨hZ0, -⟩ := (InndiagE6.twistedNFOn_isRoot_E6 hf K hK).of_eq
      (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
    rw [largeEvenTwistedH_eq]
    exact hZ0
  exact MpStdTwE6.exists_stdEquiv_revProp hf τ hτ hτ' T hZ e hT he hΓ ψ hker

end Input

end CFSG.StandardType
