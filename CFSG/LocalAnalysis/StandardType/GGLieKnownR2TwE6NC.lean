module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverLift
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6Iso
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LinkTwE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2FixedPointOdd
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ExcNCRoots
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiAdd
public import CFSG.LieType.Chevalley.E6PinnedAdjoint

public section

namespace CFSG.StandardType.LieKnownR2.TwE6

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.CurtisTits
open CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

private noncomputable def l10st6n_frobQEquiv (f : ℕ) :
    GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
  RingEquiv.ofBijective (frobQ 2 f)
    ⟨RingHom.injective (frobQ 2 f),
      Finite.surjective_of_injective (RingHom.injective (frobQ 2 f))⟩

private theorem l10st6n_orbitUnion_J0 :
    TwistTag.E6.orbitUnion J0 =
      (Jθ .E6 :
        Set (Fin TwistTag.E6.tag.rank)) := by
  ext i
  rw [TwE6LongRoot.Psi.mem_orbitUnion_J0]
  rfl

private theorem l10st6n_mem_roots_of_long {K : Type*} [Group K]
    {D : UniversalRootDatum K} {β : Fin D.rank → ℤ} (hl : GGLongRoot D β) :
    β ∈ D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hl
  exact weylAction_mem_roots hγ₀ w

private theorem l10st6n_adj_noCentral_highest
    {f : ℕ} :
    GGRootNoCentralAt (⊤ : Subgroup
        (twistedE6RootGroup (GaloisField 2 (2 * f)) (l10st6n_frobQEquiv f)))
      (twE6RootSubgroup (GaloisField 2 (2 * f)) (l10st6n_frobQEquiv f)
        e6HighestRoot) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  let σ : k ≃+* k := l10st6n_frobQEquiv f
  have hσθ : σ.toRingHom = θ := RingHom.ext fun _ => rfl
  have hroot : highRoot .E6 =
      e6HighestRoot := rfl
  have hroot' : highRoot TwistTag.E6.tag = e6HighestRoot := by
    show highRoot Tag.E6 = e6HighestRoot
    exact hroot
  obtain ⟨h, hhP, hodd, hfpf⟩ :=
    LinkTwE6.twE6_exists_odd_fpf k θ
  have hhP' : h ∈ Pθ .E6 k ⊓
      graphFixedRootGroup TwistTag.E6 k σ.toRingHom := by
    rw [hσθ]
    exact hhP
  have hhNamb : h ∈ Subgroup.normalizer
      (rootSubgroup .E6 k
        e6HighestRoot : Set (ModGL .E6 k)) := by
    have hC2 := CFSG.StandardType.LieKnownR2.even_highest_root_normalizer .E6 k
    have hN_eq : adjointGroup .E6 k ⊓ Subgroup.normalizer
        (rootSubgroup .E6 k
          e6HighestRoot : Set (ModGL .E6 k)) =
        parabolicSubgroup .E6 k
          (Jθ .E6) := by
      rw [inf_comm, ← hroot]
      exact hC2.1
    have hhInt : h ∈ adjointGroup .E6 k ⊓ Subgroup.normalizer
        (rootSubgroup .E6 k e6HighestRoot : Set (ModGL .E6 k)) := by
      rw [hN_eq]
      exact hhP'.1
    exact hhInt.2
  let hG : twistedE6RootGroup k σ := ⟨h, hhP'.2⟩
  have hhN : hG ∈ Subgroup.normalizer
      (((rootSubgroup TwistTag.E6.tag k
          e6HighestRoot).comap
        (twistedE6RootGroup k σ).subtype : Subgroup (twistedE6RootGroup k σ)) :
          Set (twistedE6RootGroup k σ)) :=
    TwE6LongRoot.mem_normalizer_comap_of_coe_mem_normalizer
      (twistedE6RootGroup k σ) hhNamb
  have hoddG : Odd (orderOf hG) := by
    rw [← Subgroup.orderOf_coe hG]
    exact hodd
  refine noCentral_of_fixedPoint_odd (K := ⊤)
    (R := (rootSubgroup TwistTag.E6.tag k
      e6HighestRoot).comap (twistedE6RootGroup k σ).subtype)
    hoddG ?_ ?_
  · simpa using hhN
  · intro y hy hyh
    simp only [top_inf_eq] at hy
    let yE : ModGL .E6 k :=
      show ModGL .E6 k from ((y : twistedE6RootGroup k σ) : ModGL TwistTag.E6.tag k)
    have hyRad : y ∈ twE6LongRootRadical
        (twE6RootSubgroup k σ e6HighestRoot) := by
      rw [twE6LongRootRadical]
      rw [ringChar.eq k 2]
      exact hy
    have hrad := CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.radical_std_eq
      (K := k) σ
    rw [hrad] at hyRad
    have hyQ : yE ∈
        parabolicRadical .E6 k
          (Jθ .E6) := by
      have h1 : yE ∈
          graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom
            J0 :=
        Subgroup.mem_subgroupOf.mp hyRad
      rw [hσθ] at h1
      rw [graphFixedParabolicRadical] at h1
      rw [l10st6n_orbitUnion_J0] at h1
      exact h1.1
    have hcomm : h * yE * h⁻¹ *
        yE⁻¹ ∈
        rootSubgroup .E6 k
          (highRoot .E6) := by
      have h' : h * yE = yE * h := by
        have h1 := congrArg (Subtype.val) hyh
        simp only [Subgroup.coe_mul] at h1
        exact h1
      have h1 : h * yE * h⁻¹ *
          yE⁻¹ = 1 := by
        rw [h']
        group
      rw [h1]
      exact (rootSubgroup .E6 k
        (highRoot .E6)).one_mem
    have hyU : yE ∈
        rootSubgroup .E6 k
          (highRoot .E6) :=
      hfpf yE hyQ hcomm
    change yE ∈ rootSubgroup .E6 k (highRoot .E6)
    exact hyU

private theorem l10st6n_univ_noCentral_highest
    {f : ℕ} (hf : 1 ≤ f) :
    GGRootNoCentralAt (⊤ : Subgroup (twistedE6Group 2 f))
      ((twistedE6Datum 2 f).rootGroup
        (highRoot .F4)) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  let σ : k ≃+* k := l10st6n_frobQEquiv f
  have hσθ : σ.toRingHom = θ := RingHom.ext fun _ => rfl
  have hK : Nat.card k = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, θ c = c ^ (2 ^ f) := fun c => frobQ_apply 2 f c
  have hγ : highRoot .F4 ∈
      (twistedDatum k θ).roots := by
    rw [twistedDatum_roots]
    exact isRoot_highRoot .F4
  have hodd : Odd (Nat.card (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ hσ).ker) :=
    CFSG.StandardType.RootDetectTwE6.odd_card_ker f
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ hσ) (fun _ => rfl)
  have hmap := CFSG.StandardType.LieKnownR2.Short.map_twistedIsogenyC_rootGroup_highRoot
    hf hK θ hσ
  have hadj := l10st6n_adj_noCentral_highest (f := f)
  refine Cover.ggRootNoCentralAt_top_of_map_surjective
    (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ hσ)
    (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf hK θ hσ)
    (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ hσ).le hodd
    (CFSG.StandardType.LieKnownR2.Short.isPGroup_two_twistedRootGroup θ hγ) ?_
  rw [hmap]
  have hσθ' : (l10st6n_frobQEquiv f : k →+* k) = θ := hσθ
  have hσθ'' : (l10st6n_frobQEquiv f).toRingHom = θ := hσθ
  change GGRootNoCentralAt
    (⊤ : Subgroup (graphFixedRootGroup TwistTag.E6 k (l10st6n_frobQEquiv f).toRingHom))
    ((rootSubgroup TwistTag.E6.tag k e6HighestRoot).comap
      (graphFixedRootGroup TwistTag.E6 k (l10st6n_frobQEquiv f).toRingHom).subtype) at hadj
  have hgroup : graphFixedRootGroup TwistTag.E6 k (l10st6n_frobQEquiv f).toRingHom =
      graphFixedRootGroup TwistTag.E6 k θ := by
    rw [hσθ'']
  rw [hgroup] at hadj
  exact hadj

private theorem l10st6n_noCentral_long
    {n f : ℕ} (hf : 1 ≤ f)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hl : GGLongRoot (ggU .twistedE6 n f).D β) :
    GGRootNoCentralAt (⊤ : Subgroup (ggU .twistedE6 n f).K)
      ((ggU .twistedE6 n f).D.rootGroup β) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 f hf
  have hct := twistedDatum_isCTGroupDatum θ hθ
    (iSup_twistedDatum_rootGroup θ hθ)
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβeq⟩ := hl
  have hγ₀ : γ₀ = highRoot .F4 :=
    CFSG.StandardType.LieKnownR2.Short.eq_highRoot_of_maxHeight_twistedE6 θ hγ₀mem hγ₀max
  have hNC : GGRootNoCentralAt (⊤ : Subgroup (ggU .twistedE6 n f).K)
      ((ggU .twistedE6 n f).D.rootGroup γ₀) := by
    change GGRootNoCentralAt (⊤ : Subgroup (twistedE6Group 2 f))
      ((twistedE6Datum 2 f).rootGroup γ₀)
    simpa only [hγ₀] using l10st6n_univ_noCentral_highest (f := f) hf
  have hact := CFSG.LieType.Steinberg.actsAs_nrep
    (D := (ggU .twistedE6 n f).D) hct w
  have hmap : ((ggU .twistedE6 n f).D.rootGroup γ₀).map
      (MulAut.conj (CFSG.LieType.Steinberg.nrep
        (D := (ggU .twistedE6 n f).D) hct w)).toMonoidHom =
        (ggU .twistedE6 n f).D.rootGroup β := by
    rw [hact γ₀ hγ₀mem, ← hβeq]
  have h := CFSG.StandardType.ggRootNoCentralAt_top_map_mulEquiv
    (MulAut.conj (CFSG.LieType.Steinberg.nrep
      (D := (ggU .twistedE6 n f).D) hct w)) hNC
  rwa [hmap] at h

theorem ggRootNoCentral_twistedE6_long
    {n f : ℕ} (hf : 1 ≤ f)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hl : GGLongRoot (ggU .twistedE6 n f).D β)
    (u : (ggU .twistedE6 n f).K) :
    GGRootNoCentralAt (⊤ : Subgroup (ggU .twistedE6 n f).K)
      (ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u) := by
  have hNC := l10st6n_noCentral_long hf hl
  have hmap : ((ggU .twistedE6 n f).D.rootGroup β).map
      (MulAut.conj u).toMonoidHom =
        ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u := by
    simp only [ggRootSub, Subgroup.map_id]
  have h := CFSG.StandardType.ggRootNoCentralAt_top_map_mulEquiv (MulAut.conj u) hNC
  rwa [hmap] at h

theorem ggRootNoCentralAt_ggU_twistedE6_long
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (φ : (ggU .twistedE6 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ} (hl : GGLongRoot (ggU .twistedE6 n f).D β)
    (u : (ggU .twistedE6 n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .twistedE6 n f).D φ β u) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hK : Nat.card k = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, θ c = c ^ (2 ^ f) := fun c => frobQ_apply 2 f c
  have hoddπ : Odd (Nat.card
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ hσ).ker) :=
    CFSG.StandardType.RootDetectTwE6.odd_card_ker f
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ hσ) (fun _ => rfl)
  have hker_le : φ.ker ≤ (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ hσ).ker := by
    rw [CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ hσ]
    exact hker
  have hodd : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat hoddπ (Subgroup.card_dvd_of_le hker_le)
  have hβmem : β ∈ (twistedDatum k θ).roots := l10st6n_mem_roots_of_long hl
  have hR : IsPGroup 2 (ggRootSub (ggU .twistedE6 n f).D
      (MonoidHom.id (ggU .twistedE6 n f).K) β u) := by
    rw [ggRootSub, Subgroup.map_id]
    exact IsPGroup.map
      (CFSG.StandardType.LieKnownR2.Short.isPGroup_two_twistedRootGroup θ hβmem)
      (MulAut.conj u).toMonoidHom
  have hbase := ggRootNoCentral_twistedE6_long hf hl u
  have h := SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker φ hker hodd hR hbase
  have hgoal : ggRootSub (ggU .twistedE6 n f).D φ β u =
      (ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u).map φ :=
    CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map (ggU .twistedE6 n f).D φ β u
  rw [hgoal]
  exact h

end CFSG.StandardType.LieKnownR2.TwE6
