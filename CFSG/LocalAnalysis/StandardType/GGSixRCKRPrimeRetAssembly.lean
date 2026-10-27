module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetLang
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import CFSG.RankThree.PartOne.KE.SigmaCentralizer
import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
import CFSG.LieType.Steinberg.Isogeny.TwistedE6
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld CFSG.LieType.Steinberg.Minuscule
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckRet_torus_fixed
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    (hρΨ : ∀ γ ∈ rootsOfFam β Set.univ, S.ρ γ ∈ rootsOfFam β Set.univ)
    {w' : WeylGroup Tag.E6} (hw' : ∀ γ ∈ rootsOfFam β Set.univ, w' • ι γ = ι (S.ρ γ))
    {σ : GGL ≃+* GGL} (hσ : ∀ c, σ c = c ^ S.D.q)
    {b : ModGL τ GGL} (hb : b ∈ S.D.torus) :
    rootDiagUnit Tag.E6 (fun k : Fin Tag.E6.rank => rckRootVal b (β k)) ∈
      CFSG.RankThree.PartOne.KE.twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) GGL w')
        (frobGL σ) := by
  classical
  have hbT : b ∈ torusGroup τ GGL := (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
  have hb' : rootDiagUnit τ (rckTorusCoord b) = b := rck_rootDiagUnit_coord hbT
  have hbS : rootDiagUnit τ (rckTorusCoord b) ∈ S.D.torus := by rw [hb']; exact hb
  rw [CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
  refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
  set c : Fin Tag.E6.rank → GGLˣ := fun k => rckRootVal b (β k) with hc
  have hΦ : frobGL σ (rootDiagUnit Tag.E6 c) =
      rootDiagUnit Tag.E6 (fun k => Units.map σ.toRingHom.toMonoidHom (c k)) :=
    units_map_entrywiseHom_rootDiagUnit_ringEquiv σ c
  rw [hΦ]
  have key : rootDiagUnit Tag.E6 c = canonicalRep (coxeterSystem Tag.E6) GGL w' *
      rootDiagUnit Tag.E6 (fun k => Units.map σ.toRingHom.toMonoidHom (c k)) *
        (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ := by
    rw [rootDiagUnit_eq_conj_canonicalRep_iff]
    refine rootChar_smul_eq_rootChar_of_forall_isRoot fun α hα => ?_
    obtain ⟨γ, hγ, rfl⟩ := hι.1.surjOn hα
    have hval : ∀ δ ∈ rootsOfFam β Set.univ,
        rootChar c (ι δ) = rootChar (rckTorusCoord b) δ := by
      intro δ hδ
      have h1 := rckRet_torus_val hι hbT δ hδ
      unfold rckRootVal at h1
      rw [rck_coord_rootDiagUnit] at h1
      exact h1
    have hroot : IsRoot τ γ := hγ.1
    have h2 := S.frob.rootChar_eq (rckTorusCoord b) hbS γ hroot
    have hnat : ∀ v, rootChar (fun k => Units.map σ.toRingHom.toMonoidHom (c k)) v =
        Units.map σ.toRingHom.toMonoidHom (rootChar c v) := by
      intro v
      simp [rootChar, map_prod, map_zpow]
    have hpow : ∀ u : GGLˣ, Units.map σ.toRingHom.toMonoidHom u = u ^ S.D.q := by
      intro u
      apply Units.ext
      simp [hσ]
    rw [hw' γ hγ, hval _ (hρΨ γ hγ), h2, hnat, hval _ hγ, hpow]
  exact key.symm

theorem rckRet_conj_mem_R
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {t : ModGL τ GGL} (ht : t ∈ torusGroup τ GGL) (hFt : S.D.step t = t)
    {r : ModGL τ GGL} (hr : r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    t * r * t⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  let φ : ModGL τ GGL →* ModGL τ GGL := (MulAut.conj t).toMonoidHom
  have hφ : ∀ g, φ g = t * g * t⁻¹ := fun g => rfl
  have htM : t ∈ S.D.model := ⟨CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup' ht, hFt⟩
  have hM : S.D.model.map φ ≤ S.D.model := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hφ]
    exact mul_mem (mul_mem htM hg) (inv_mem htM)
  have hΓ : S.Γ.map φ ≤ S.Γ := by
    have h1 : (⁅S.D.model, S.D.model⁆).map φ ≤ ⁅S.D.model, S.D.model⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hM hM
    exact h1
  have hS : (rootSpan τ GGL (rationalRoots S.ρ (rootCharHom a) i)).map φ ≤
      rootSpan τ GGL (rationalRoots S.ρ (rootCharHom a) i) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hφ]
    have hN := CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (L := GGL) (τ := τ)
      (S := rationalRoots S.ρ (rootCharHom a) i) (by
        rw [CFSG.StandardType.F4ExplicitPos.CommonFactor.rationalRoots_eq_componentRoots_of_orbitLength_one i hs1]
        exact fun γ hγ => isRoot_of_mem_componentRoots hγ)
    exact (Subgroup.mem_normalizer_iff.1 (hN ht) g).1 hg
  have hrs : (rationalSpan S.ρ S.Γ (rootCharHom a) i).map φ ≤
      rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf hS hΓ)
  have : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map φ ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    unfold rationalComponent
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hrs hrs
  exact this ⟨r, hr, rfl⟩

theorem rckRet_R_le_H
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) {a : Fin τ.rank → GGLˣ}
    (i : KernelComponent (rootCharHom a))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ GGL (componentRoots (rootCharHom a) i) := by
  calc rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
        Subgroup.commutator_le.2 fun x hx y hy => by
          rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
            (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    _ ≤ rootSpan τ GGL (rationalRoots S.ρ (rootCharHom a) i) := inf_le_left
    _ = rootSpan τ GGL (componentRoots (rootCharHom a) i) := by
        rw [CFSG.StandardType.F4ExplicitPos.CommonFactor.rationalRoots_eq_componentRoots_of_orbitLength_one i hs1]


@[expose] noncomputable def rckRetKappa
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ} (θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL)
    {R : Subgroup (ModGL τ GGL)} (hRH : R ≤ RetH τ β) : ↥R →* ModGL Tag.E6 GGL :=
  θ.comp (Subgroup.inclusion hRH)

theorem rckRetKappa_apply
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ} {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL}
    {R : Subgroup (ModGL τ GGL)} (hRH : R ≤ RetH τ β) (r : ↥R) :
    rckRetKappa θ hRH r = θ ⟨(r : ModGL τ GGL), hRH r.2⟩ := rfl

theorem rckRet_kappa_range
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ} {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ)
    {z : ModGL τ GGL} {zh : ModGL Tag.E6 GGL}
    (hcompat : ∀ x : ↥(RetH τ β), ∃ hx : z * (x : ModGL τ GGL) * z⁻¹ ∈ RetH τ β,
      θ ⟨z * (x : ModGL τ GGL) * z⁻¹, hx⟩ = zh * θ x * zh⁻¹)
    (K' : Subfield GGL) (hK' : Finite ↥K')
    {R : Subgroup (ModGL τ GGL)} (hRH : R ≤ RetH τ β)
    (hR : ∀ r, r ∈ R ↔ ∃ x ∈ rootSpan τ ↥K' (rootsOfFam β Set.univ),
      r = z * baseChangeGL K'.subtype x * z⁻¹) :
    (rckRetKappa θ hRH).range =
      ((adjointGroup Tag.E6 ↥K').map (baseChangeGL K'.subtype)).map
        (MulAut.conj zh).toMonoidHom := by
  classical
  have hK := hθ.2.2.2 K' hK'
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨x, hx, hrx⟩ := (hR r).1 r.2
    have hw : baseChangeGL K'.subtype x ∈ RetH τ β :=
      map_baseChangeGL_rootSpan_le K'.subtype _ ⟨x, hx, rfl⟩
    have hwmem : (⟨baseChangeGL K'.subtype x, hw⟩ : ↥(RetH τ β)) ∈
        (((rootSpan τ ↥K' (rootsOfFam β Set.univ)).map (baseChangeGL K'.subtype)).subgroupOf
          (RetH τ β)) := Subgroup.mem_subgroupOf.2 ⟨x, hx, rfl⟩
    have hθw := Subgroup.mem_map_of_mem θ hwmem
    rw [hK] at hθw
    obtain ⟨hx', heq⟩ := hcompat ⟨baseChangeGL K'.subtype x, hw⟩
    refine ⟨_, hθw, ?_⟩
    have e : (⟨(r : ModGL τ GGL), hRH r.2⟩ : ↥(RetH τ β)) =
        ⟨z * baseChangeGL K'.subtype x * z⁻¹, hx'⟩ := Subtype.ext hrx
    rw [rckRetKappa_apply, e, heq]
    rfl
  · rintro ⟨y₀, hy₀, rfl⟩
    rw [← hK] at hy₀
    obtain ⟨⟨w, hw⟩, hwmem, hθw⟩ := Subgroup.mem_map.1 hy₀
    obtain ⟨x, hx, hwx⟩ := Subgroup.mem_subgroupOf.1 hwmem
    obtain ⟨hx', heq⟩ := hcompat ⟨w, hw⟩
    have hrR : z * w * z⁻¹ ∈ R := (hR _).2 ⟨x, hx, by rw [hwx]⟩
    refine ⟨⟨z * w * z⁻¹, hrR⟩, ?_⟩
    rw [rckRetKappa_apply]
    change θ ⟨z * w * z⁻¹, hRH hrR⟩ = _
    have e : (⟨z * w * z⁻¹, hRH hrR⟩ : ↥(RetH τ β)) = ⟨z * (⟨w, hw⟩ : ↥(RetH τ β)) * z⁻¹, hx'⟩ :=
      rfl
    rw [e, heq, hθw]
    rfl

theorem rckRet_center_SKGamma
    (K' : Subfield GGL) {zh y : ModGL Tag.E6 GGL}
    (hy : y ∈ ((adjointGroup Tag.E6 ↥K').map (baseChangeGL K'.subtype)).map
      (MulAut.conj zh).toMonoidHom)
    (hc : ∀ u ∈ ((adjointGroup Tag.E6 ↥K').map (baseChangeGL K'.subtype)).map
      (MulAut.conj zh).toMonoidHom, y * u = u * y) : y = 1 := by
  classical
  obtain ⟨y₁, ⟨y₀, hy₀, rfl⟩, rfl⟩ := hy
  have hcen : (⟨y₀, hy₀⟩ : ↥(adjointGroup Tag.E6 ↥K')) ∈
      Subgroup.center ↥(adjointGroup Tag.E6 ↥K') := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 := hc (zh * baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K') * zh⁻¹)
      ⟨_, ⟨(g : ModGL Tag.E6 ↥K'), g.2, rfl⟩, rfl⟩
    have h1' : zh * baseChangeGL K'.subtype y₀ * zh⁻¹ *
        (zh * baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K') * zh⁻¹) =
        (zh * baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K') * zh⁻¹) *
          (zh * baseChangeGL K'.subtype y₀ * zh⁻¹) := h1
    have h2 : zh * (baseChangeGL K'.subtype y₀ * baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K')) *
        zh⁻¹ = zh * (baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K') *
          baseChangeGL K'.subtype y₀) * zh⁻¹ := by
      calc zh * (baseChangeGL K'.subtype y₀ *
              baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K')) * zh⁻¹
          = zh * baseChangeGL K'.subtype y₀ * zh⁻¹ *
            (zh * baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K') * zh⁻¹) := by group
        _ = (zh * baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K') * zh⁻¹) *
            (zh * baseChangeGL K'.subtype y₀ * zh⁻¹) := h1'
        _ = zh * (baseChangeGL K'.subtype (g : ModGL Tag.E6 ↥K') *
            baseChangeGL K'.subtype y₀) * zh⁻¹ := by group
    have h3 := mul_left_cancel (mul_right_cancel h2)
    rw [← map_mul, ← map_mul] at h3
    exact (baseChangeGL_injective _ h3).symm
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field Tag.E6 ↥K', Subgroup.mem_bot] at hcen
  have : y₀ = 1 := congrArg Subtype.val hcen
  change (MulAut.conj zh) (baseChangeGL K'.subtype y₀) = 1
  rw [this, map_one, map_one]

theorem rckRet_kappa_ker
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ} {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    {θ : ↥(RetH τ β) →* ModGL Tag.E6 GGL} (hθ : RetCompSpec β ι θ)
    {R : Subgroup (ModGL τ GGL)} (hRH : R ≤ RetH τ β) {Γ' : Subgroup (ModGL Tag.E6 GGL)}
    (hrange : (rckRetKappa θ hRH).range = Γ')
    (hΓ : ∀ y ∈ Γ', (∀ u ∈ Γ', y * u = u * y) → y = 1) :
    (rckRetKappa θ hRH).ker = Subgroup.center ↥R := by
  classical
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker, rckRetKappa_apply] at hx
    have hxc := hθ.2.2.1 _ hx
    rw [Subgroup.mem_center_iff] at hxc ⊢
    intro g
    apply Subtype.ext
    have := hxc ⟨(g : ModGL τ GGL), hRH g.2⟩
    have h2 : (g : ModGL τ GGL) * (x : ModGL τ GGL) = (x : ModGL τ GGL) * (g : ModGL τ GGL) :=
      congrArg Subtype.val this
    exact h2
  · intro hx
    rw [MonoidHom.mem_ker]
    refine hΓ _ (hrange ▸ ⟨x, rfl⟩) fun u hu => ?_
    rw [← hrange] at hu
    obtain ⟨r, rfl⟩ := hu
    have hcomm : r * x = x * r := Subgroup.mem_center_iff.1 hx r
    calc rckRetKappa θ hRH x * rckRetKappa θ hRH r = rckRetKappa θ hRH (x * r) :=
          (map_mul _ _ _).symm
      _ = rckRetKappa θ hRH (r * x) := by rw [hcomm]
      _ = rckRetKappa θ hRH r * rckRetKappa θ hRH x := map_mul _ _ _

theorem rckRet_SK_step_conj
    {σ : GGL ≃+* GGL} {w' : WeylGroup Tag.E6} {zh : ModGL Tag.E6 GGL}
    (hlang : frobGL σ zh⁻¹ = zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w')
    (γ : Fin Tag.E6.rank → ℤ) (c : GGL) :
    canonicalRep (coxeterSystem Tag.E6) GGL w' * frobGL σ (zh * pinnedX Tag.E6 GGL γ c * zh⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ =
      zh * pinnedX Tag.E6 GGL γ (σ c) * zh⁻¹ := by
  have h1 : frobGL σ zh = (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹ * zh := by
    have h := congrArg (fun m => m⁻¹) hlang
    simpa using h
  rw [map_mul, map_mul, map_inv, h1, frobGL_pinnedX]
  group


private theorem rckRet_eq_of_central_odd {H : Type*} [Group H] {y₁ y₂ : H} {k : ℕ}
    (hc : y₁ * y₂⁻¹ ∈ Subgroup.center H) (hodd : Odd (orderOf (y₁ * y₂⁻¹)))
    (h₁ : y₁ ^ 2 ^ k = 1) (h₂ : y₂ ^ 2 ^ k = 1) : y₁ = y₂ := by
  have hcent : Commute (y₁ * y₂⁻¹) y₂ := (Subgroup.mem_center_iff.mp hc y₂).symm
  have hceq : (y₁ * y₂⁻¹) * y₂ = y₁ := by group
  have hpow : (y₁ * y₂⁻¹) ^ 2 ^ k = 1 := by
    have h : ((y₁ * y₂⁻¹) * y₂) ^ 2 ^ k = 1 := by rw [hceq, h₁]
    rw [hcent.mul_pow (2 ^ k), h₂, mul_one] at h
    exact h
  have hdvd : orderOf (y₁ * y₂⁻¹) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hm0 : m = 0 := by
    by_contra hne
    have h2 : Even (2 ^ m) := Nat.even_pow.2 ⟨even_two, hne⟩
    rw [← hm] at h2
    exact (Nat.not_even_iff_odd.2 hodd) h2
  rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
  exact mul_inv_eq_one.1 hm

theorem rckRet_transfer_innerDiag
    {M : LieUniversal} (hrg : ∀ γ ∈ M.D.roots, IsPGroup 2 (M.D.rootGroup γ))
    {X : Type} [Group X] {R : Subgroup X} (φ : M.K →* ↥R)
    {Y : Type} [Group Y] (κ : ↥R →* Y) (hκ : κ.ker ≤ Subgroup.center ↥R)
    (hZodd : ∀ x ∈ Subgroup.center ↥R, Odd (orderOf x))
    {b : X} (hbR : ∀ r ∈ R, b * r * b⁻¹ ∈ R ∧ b⁻¹ * r * b ∈ R) {t : Y}
    (hconj : ∀ (x : ↥R) (hx : b * (x : X) * b⁻¹ ∈ R),
      κ ⟨b * (x : X) * b⁻¹, hx⟩ = t * κ x * t⁻¹)
    (hdiag : GGPsiInnerDiag M.D (κ.comp φ) t) :
    GGPsiInnerDiag M.D (R.subtype.comp φ) b := by
  classical
  obtain ⟨g', hg', hall⟩ := hdiag
  obtain ⟨u, rfl⟩ := hg'
  refine ⟨R.subtype (φ u), ⟨u, rfl⟩, fun γ hγ => ?_⟩
  obtain ⟨hh, hhT, hz⟩ := hall γ hγ
  refine ⟨hh, hhT, fun z hz' => ?_⟩
  have hzγ := hz z hz'
  set r : ↥R := φ u with hr
  set ρ : ↥R := φ z with hρ
  have hρ' : b⁻¹ * (ρ : X) * b ∈ R := (hbR _ ρ.2).2
  let ρ' : ↥R := ⟨b⁻¹ * (ρ : X) * b, hρ'⟩
  have hb2 : b * (ρ' : X) * b⁻¹ ∈ R := by
    have e : b * (ρ' : X) * b⁻¹ = (ρ : X) := by
      change b * (b⁻¹ * (ρ : X) * b) * b⁻¹ = _
      group
    rw [e]; exact ρ.2
  have hκρ' : κ ρ' = t⁻¹ * κ ρ * t := by
    have h := hconj ρ' hb2
    have e : (⟨b * (ρ' : X) * b⁻¹, hb2⟩ : ↥R) = ρ := by
      apply Subtype.ext
      change b * (b⁻¹ * (ρ : X) * b) * b⁻¹ = _
      group
    rw [e] at h
    rw [h]
    group
  let y₁ : ↥R := r⁻¹ * ρ' * r
  let y₂ : ↥R := φ (hh * z * hh⁻¹)
  have hκy : κ y₁ = κ y₂ := by
    have h1 : κ y₁ = (κ r)⁻¹ * (t⁻¹ * κ ρ * t) * κ r := by
      simp only [y₁, map_mul, map_inv, hκρ']
    have h2 : κ y₂ = (t * κ r)⁻¹ * κ ρ * (t * κ r) := by
      have := hzγ
      change (t * κ (φ u))⁻¹ * κ (φ z) * (t * κ (φ u)) = κ (φ (hh * z * hh⁻¹)) at this
      exact this.symm
    rw [h1, h2]
    group
  have hcZ : y₁ * y₂⁻¹ ∈ Subgroup.center ↥R :=
    hκ (MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hκy, mul_inv_cancel]))
  have hcodd : Odd (orderOf (y₁ * y₂⁻¹)) := hZodd _ hcZ
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (hrg γ hγ) ⟨z, hz'⟩
  have hzord : orderOf z = 2 ^ k := by
    rw [← hk]
    exact orderOf_injective (Subgroup.subtype (M.D.rootGroup γ)) Subtype.coe_injective ⟨z, hz'⟩
  have hz2k : z ^ 2 ^ k = 1 := by
    rw [← hzord]
    exact pow_orderOf_eq_one z
  have hρpow : ρ ^ 2 ^ k = 1 := by rw [hρ, ← map_pow, hz2k, map_one]
  have hρ'pow : ρ' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    change (b⁻¹ * (ρ : X) * b) ^ 2 ^ k = 1
    rw [show b⁻¹ * (ρ : X) * b = b⁻¹ * (ρ : X) * b⁻¹⁻¹ by rw [inv_inv], conj_pow]
    have : (ρ : X) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hρpow
      simpa using this
    rw [this]
    group
  have hy₁pow : y₁ ^ 2 ^ k = 1 := by
    simp only [y₁]
    rw [show r⁻¹ * ρ' * r = r⁻¹ * ρ' * r⁻¹⁻¹ by rw [inv_inv], conj_pow, hρ'pow]
    group
  have hy₂pow : y₂ ^ 2 ^ k = 1 := by
    simp only [y₂]
    rw [← map_pow, show hh * z * hh⁻¹ = hh * z * hh⁻¹ from rfl, conj_pow, hz2k]
    simp
  have hfinal : y₁ = y₂ := rckRet_eq_of_central_odd hcZ hcodd hy₁pow hy₂pow
  have e : (b * (R.subtype (φ u)))⁻¹ * (R.subtype.comp φ) z * (b * (R.subtype (φ u))) =
      (y₁ : X) := by
    change (b * (r : X))⁻¹ * (ρ : X) * (b * (r : X)) = ((r⁻¹ * ρ' * r : ↥R) : X)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ρ']
    group
  rw [e, hfinal]
  rfl


theorem rckRet_pair_root
    {σ : GGL ≃+* GGL} {zh : ModGL Tag.E6 GGL} {w' : WeylGroup Tag.E6}
    (hlang : frobGL σ zh⁻¹ = zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w')
    {step : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL}
    (hstep : ∀ y, step y = canonicalRep (coxeterSystem Tag.E6) GGL w' * frobGL σ y *
      (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹)
    (γ : Fin Tag.E6.rank → ℤ) :
    ((rootSubgroup Tag.E6 GGL γ).map (MulAut.conj zh).toMonoidHom).map step =
        (rootSubgroup Tag.E6 GGL γ).map (MulAut.conj zh).toMonoidHom ∧
      ∀ y, y ∈ ((rootSubgroup Tag.E6 GGL γ).map (MulAut.conj zh).toMonoidHom ⊓
          step.eqLocus (MonoidHom.id _)) ↔
        ∃ c, σ c = c ∧ y = zh * pinnedX Tag.E6 GGL γ c * zh⁻¹ := by
  classical
  have hst : ∀ c, step (zh * pinnedX Tag.E6 GGL γ c * zh⁻¹) =
      zh * pinnedX Tag.E6 GGL γ (σ c) * zh⁻¹ := fun c => by
    rw [hstep]
    exact rckRet_SK_step_conj hlang γ c
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, ⟨x', hx', rfl⟩, rfl⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx'
      refine ⟨pinnedX Tag.E6 GGL γ (σ c), mem_rootSubgroup.2 ⟨_, rfl⟩, ?_⟩
      change zh * pinnedX Tag.E6 GGL γ (σ c) * zh⁻¹ = step (zh * pinnedX Tag.E6 GGL γ c * zh⁻¹)
      rw [hst]
    · rintro ⟨x', hx', rfl⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx'
      refine ⟨zh * pinnedX Tag.E6 GGL γ (σ.symm c) * zh⁻¹,
        ⟨pinnedX Tag.E6 GGL γ (σ.symm c), mem_rootSubgroup.2 ⟨_, rfl⟩, rfl⟩, ?_⟩
      rw [hst, RingEquiv.apply_symm_apply]
      rfl
  · intro y
    constructor
    · rintro ⟨⟨x', hx', rfl⟩, hfix⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx'
      refine ⟨c, ?_, rfl⟩
      have h1 : step (zh * pinnedX Tag.E6 GGL γ c * zh⁻¹) = zh * pinnedX Tag.E6 GGL γ c * zh⁻¹ :=
        hfix
      rw [hst] at h1
      have h2 : pinnedX Tag.E6 GGL γ (σ c) = pinnedX Tag.E6 GGL γ c :=
        mul_left_cancel (mul_right_cancel h1)
      exact pinnedX_injective (τ := Tag.E6) (R := GGL) γ h2
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨pinnedX Tag.E6 GGL γ c, mem_rootSubgroup.2 ⟨_, rfl⟩, rfl⟩, ?_⟩
      change step (zh * pinnedX Tag.E6 GGL γ c * zh⁻¹) = zh * pinnedX Tag.E6 GGL γ c * zh⁻¹
      rw [hst, hc]

theorem rckRet_pair_image
    {f : ℕ} {σ : GGL ≃+* GGL} (e : GaloisField 2 f →+* GGL)
    (hefix : ∀ c, σ (e c) = e c) (hesurj : ∀ y : GGL, σ y = y → ∃ c, e c = y)
    {zh : ModGL Tag.E6 GGL} {w' : WeylGroup Tag.E6}
    (hlang : frobGL σ zh⁻¹ = zh⁻¹ * canonicalRep (coxeterSystem Tag.E6) GGL w')
    {step : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL}
    (hstep : ∀ y, step y = canonicalRep (coxeterSystem Tag.E6) GGL w' * frobGL σ y *
      (canonicalRep (coxeterSystem Tag.E6) GGL w')⁻¹)
    {ψ : (ggU .E6 0 f).K →* ModGL Tag.E6 GGL}
    (hψ : ∀ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ' → ∀ c : GaloisField 2 f,
      ψ (e6Data_valid.xm (GaloisField 2 f) γ' c) = zh * pinnedX Tag.E6 GGL γ' (e c) * zh⁻¹)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ((ggU .E6 0 f).D.rootGroup γ).map ψ =
      (rootSubgroup Tag.E6 GGL γ).map (MulAut.conj zh).toMonoidHom ⊓
        step.eqLocus (MonoidHom.id _) := by
  classical
  have h2 := (rckRet_pair_root hlang hstep γ).2
  ext y
  rw [h2 y]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_rootGroup (GaloisField 2 f)).mp hx
    exact ⟨e t, hefix t, hψ γ hγ t⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨t, rfl⟩ := hesurj c hc
    exact ⟨e6Data_valid.xm (GaloisField 2 f) γ t,
      (e6Data_valid.mem_rootGroup (GaloisField 2 f)).mpr ⟨t, rfl⟩, hψ γ hγ t⟩


end CFSG.StandardType.RCKRP

end
