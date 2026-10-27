module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6ShortNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6ShortInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Root

public section

namespace CFSG.StandardType.LieKnownR2.TwE6

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
open CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.CurtisTits CFSG.StandardType.LieKnownR2.Short
open scoped commutatorElement

private theorem l10sw3_noCentral_short
    {n f : ℕ} (hf : 2 ≤ f) {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hs : ∃ w : GGWeyl (ggU .twistedE6 n f).D,
      β = weylAction (ggU .twistedE6 n f).D.isFiniteType w twE6Alpha) :
    GGRootNoCentralAt (⊤ : Subgroup (ggU .twistedE6 n f).K)
      ((ggU .twistedE6 n f).D.rootGroup β) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 f (by omega)
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  obtain ⟨w, hβeq⟩ := hs
  have hαmem : twE6Alpha ∈ (ggU .twistedE6 n f).D.roots := twE6_alpha_mem_roots θ
  have hNC : GGRootNoCentralAt (⊤ : Subgroup (ggU .twistedE6 n f).K)
      ((ggU .twistedE6 n f).D.rootGroup twE6Alpha) := by
    change GGRootNoCentralAt (⊤ : Subgroup (twistedE6Group 2 f))
      ((twistedE6Datum 2 f).rootGroup twE6Alpha)
    exact ggRootNoCentral_twistedE6_shortHighest (f := f) hf
  have hact := CFSG.LieType.Steinberg.actsAs_nrep
    (D := (ggU .twistedE6 n f).D) hct w
  have hmap : ((ggU .twistedE6 n f).D.rootGroup twE6Alpha).map
      (MulAut.conj (CFSG.LieType.Steinberg.nrep
        (D := (ggU .twistedE6 n f).D) hct w)).toMonoidHom =
        (ggU .twistedE6 n f).D.rootGroup β := by
    rw [hact twE6Alpha hαmem, ← hβeq]
  have h := CFSG.StandardType.ggRootNoCentralAt_top_map_mulEquiv
    (MulAut.conj (CFSG.LieType.Steinberg.nrep
      (D := (ggU .twistedE6 n f).D) hct w)) hNC
  rwa [hmap] at h

theorem ggRootNoCentral_twistedE6_short
    {n f : ℕ} (hf : 2 ≤ f) {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hs : ∃ w : GGWeyl (ggU .twistedE6 n f).D,
      β = weylAction (ggU .twistedE6 n f).D.isFiniteType w twE6Alpha)
    (u : (ggU .twistedE6 n f).K) :
    GGRootNoCentralAt (⊤ : Subgroup (ggU .twistedE6 n f).K)
      (ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u) := by
  have hNC := l10sw3_noCentral_short (f := f) hf hs
  have hmap : ((ggU .twistedE6 n f).D.rootGroup β).map
      (MulAut.conj u).toMonoidHom =
        ggRootSub (ggU .twistedE6 n f).D (MonoidHom.id (ggU .twistedE6 n f).K) β u := by
    simp only [ggRootSub, Subgroup.map_id]
  have h := CFSG.StandardType.ggRootNoCentralAt_top_map_mulEquiv (MulAut.conj u) hNC
  rwa [hmap] at h

theorem ggRootNoCentralAt_ggU_twistedE6_short
    {n f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X] [Finite X]
    (φ : (ggU .twistedE6 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hs : ∃ w : GGWeyl (ggU .twistedE6 n f).D,
      β = weylAction (ggU .twistedE6 n f).D.isFiniteType w twE6Alpha)
    (u : (ggU .twistedE6 n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .twistedE6 n f).D φ β u) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hK : Nat.card k = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, θ c = c ^ (2 ^ f) := fun c => frobQ_apply 2 f c
  have hoddπ : Odd (Nat.card
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ).ker) :=
    CFSG.StandardType.RootDetectTwE6.odd_card_ker f
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ) (fun _ => rfl)
  have hker_le : φ.ker ≤
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ).ker := by
    rw [CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC (by omega) hK θ hσ]
    exact hker
  have hodd : Odd (Nat.card φ.ker) :=
    Odd.of_dvd_nat hoddπ (Subgroup.card_dvd_of_le hker_le)
  have hβmem : β ∈ (twistedDatum k θ).roots := by
    obtain ⟨w, hβeq⟩ := hs
    rw [hβeq]
    exact weylAction_mem_roots (twE6_alpha_mem_roots θ) w
  have hR : IsPGroup 2 (ggRootSub (ggU .twistedE6 n f).D
      (MonoidHom.id (ggU .twistedE6 n f).K) β u) := by
    rw [ggRootSub, Subgroup.map_id]
    exact IsPGroup.map
      (CFSG.StandardType.LieKnownR2.Short.isPGroup_two_twistedRootGroup θ hβmem)
      (MulAut.conj u).toMonoidHom
  have hbase := ggRootNoCentral_twistedE6_short (f := f) hf hs u
  have h := SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker φ hker hodd hR hbase
  have hgoal : ggRootSub (ggU .twistedE6 n f).D φ β u =
      (ggRootSub (ggU .twistedE6 n f).D
        (MonoidHom.id (ggU .twistedE6 n f).K) β u).map φ :=
    CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map (ggU .twistedE6 n f).D φ β u
  rw [hgoal]
  exact h

private theorem l10sw3_inner_range
    {n f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X]
    (φ : (ggU .twistedE6 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hs : ∃ w : GGWeyl (ggU .twistedE6 n f).D,
      β = weylAction (ggU .twistedE6 n f).D.isFiniteType w twE6Alpha)
    (u : (ggU .twistedE6 n f).K) :
    GGRootNormInner ((ggRootSub (ggU .twistedE6 n f).D φ β u).subgroupOf φ.range) := by
  let k := GaloisField 2 (2 * f)
  let θ : k →+* k := frobQ 2 f
  have hK : Nat.card k = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hk4 : 4 ≤ Nat.card k := by
    change 4 ≤ Nat.card (GaloisField 2 (2 * f))
    rw [GaloisField.card 2 (2 * f) (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hσ : ∀ c, θ c = c ^ (2 ^ f) := fun c => frobQ_apply 2 f c
  have hθ : ∀ c, θ (θ c) = c := frobQ_frobQ 2 f (by omega)
  have hαmem : twE6Alpha ∈ (ggU .twistedE6 n f).D.roots := twE6_alpha_mem_roots θ
  have hβmem : β ∈ (ggU .twistedE6 n f).D.roots := by
    obtain ⟨w, hβeq⟩ := hs
    rw [hβeq]
    exact weylAction_mem_roots hαmem w
  let π0 : (ggU .twistedE6 n f).K →* graphFixedRootGroup TwistTag.E6 k θ :=
    CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ
  have hoddπ0 : Odd (Nat.card π0.ker) :=
    CFSG.StandardType.RootDetectTwE6.odd_card_ker f
      (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ) (fun _ => rfl)
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  obtain ⟨w, hβeq⟩ := hs
  set nw : (ggU .twistedE6 n f).K :=
    CFSG.LieType.Steinberg.nrep (D := (ggU .twistedE6 n f).D) hct w with hnw
  have hαI : GGRootNormInner
      (((ggU .twistedE6 n f).D.rootGroup twE6Alpha).map π0) := by
    change GGRootNormInner
      (((twistedDatum k θ).rootGroup twE6Alpha).map
        (CFSG.SeitzReduction.F4Pilot.twistedIsogenyC (by omega) hK θ hσ))
    exact ggRootNormInner_adj_twistedE6_shortHighest (f := f) hf hK θ hσ
  have hcomp : ∀ a : (ggU .twistedE6 n f).K,
      π0.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (π0 a)).toMonoidHom.comp π0 := by
    intro a
    apply MonoidHom.ext
    intro x
    change π0 (a * x * a⁻¹) = π0 a * π0 x * (π0 a)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hact : ActsAs (ggU .twistedE6 n f).D nw w := by
    rw [hnw]
    exact CFSG.LieType.Steinberg.actsAs_nrep (D := (ggU .twistedE6 n f).D) hct w
  have hmapβ : ((ggU .twistedE6 n f).D.rootGroup β).map π0 =
      (((ggU .twistedE6 n f).D.rootGroup twE6Alpha).map π0).map
        (MulAut.conj (π0 nw)).toMonoidHom := by
    rw [hβeq, ← hact twE6Alpha hαmem, Subgroup.map_map, hcomp nw, ← Subgroup.map_map]
  have hadj : GGRootNormInner (((ggU .twistedE6 n f).D.rootGroup β).map π0) := by
    rw [hmapβ]
    exact CFSG.StandardType.ggRootNormInner_map_mulEquiv (MulAut.conj (π0 nw)) hαI
  have hkerπ0 : φ.ker ≤ π0.ker :=
    hker.trans (le_of_eq
      (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC (by omega) hK θ hσ).symm)
  haveI : Finite ((ggU .twistedE6 n f).K) := by
    change Finite (fixedGroup k θ)
    infer_instance
  haveI : Group.IsPerfect ((ggU .twistedE6 n f).K) := by
    change Group.IsPerfect (fixedGroup k θ)
    exact fixedGroup_isPerfect_of_four_le_card (k := k) (θ := θ) hθ hk4
  haveI : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range (f := φ)
  let π' : ↥φ.range →* graphFixedRootGroup TwistTag.E6 k θ :=
    (QuotientGroup.lift φ.ker π0 hkerπ0).comp
      (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
  have hπ' : ∀ x : (ggU .twistedE6 n f).K, π' (φ.rangeRestrict x) = π0 x := by
    intro x
    change QuotientGroup.lift φ.ker π0 hkerπ0
        ((QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict x)) = π0 x
    have he : (QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict x) =
        QuotientGroup.mk x := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [he, QuotientGroup.lift_mk]
  have hsurj : Function.Surjective π' := by
    intro a
    obtain ⟨s, hs⟩ :=
      CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective (by omega) hK θ hσ a
    exact ⟨φ.rangeRestrict s, by rw [hπ' s]; exact hs⟩
  have hker_eq : π'.ker = (π0.ker).map φ.rangeRestrict := by
    ext r
    constructor
    · intro hr
      obtain ⟨s, hs⟩ := φ.rangeRestrict_surjective r
      refine Subgroup.mem_map.mpr ⟨s, ?_, hs⟩
      rw [MonoidHom.mem_ker, ← hπ' s, hs]
      exact MonoidHom.mem_ker.mp hr
    · rintro ⟨z, hz, rfl⟩
      rw [MonoidHom.mem_ker, hπ' z]
      exact MonoidHom.mem_ker.mp hz
  have hcent : π'.ker ≤ Subgroup.center ↥φ.range := by
    rw [hker_eq]
    rintro r ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨t, ht⟩ := φ.rangeRestrict_surjective y
    have hzZ : z ∈ Subgroup.center ((ggU .twistedE6 n f).K) :=
      (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC (by omega) hK θ hσ).le hz
    have hcomm : (t * z : (ggU .twistedE6 n f).K) = z * t :=
      Subgroup.mem_center_iff.mp hzZ t
    rw [← ht, ← φ.rangeRestrict.map_mul, ← φ.rangeRestrict.map_mul, hcomm]
  have hodd : Odd (Nat.card π'.ker) := by
    have hdvd : Nat.card π'.ker ∣ Nat.card π0.ker := by
      rw [hker_eq]
      exact Subgroup.card_map_dvd (H := π0.ker) (f := φ.rangeRestrict)
    exact Odd.of_dvd_nat hoddπ0 hdvd
  set Rbar : Subgroup ↥φ.range :=
    (ggRootSub (ggU .twistedE6 n f).D φ β u).subgroupOf φ.range with hRbar_def
  have hR : IsPGroup 2 Rbar := by
    rw [hRbar_def]
    have hS : IsPGroup 2
        (((ggU .twistedE6 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) :=
      IsPGroup.map
        (CFSG.StandardType.LieKnownR2.Short.isPGroup_two_twistedRootGroup θ hβmem)
        (MulAut.conj u).toMonoidHom
    exact IsPGroup.comap_subtype (hS.map φ) (K := φ.range)
  have hRmap : Rbar.map π' =
      (((ggU .twistedE6 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map π0 := by
    rw [hRbar_def]
    ext a
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : (r : X) ∈ ggRootSub (ggU .twistedE6 n f).D φ β u :=
        Subgroup.mem_subgroupOf.mp hr
      rw [ggRootSub] at hr'
      obtain ⟨s, hs, hsr⟩ := Subgroup.mem_map.mp hr'
      have hrs : φ.rangeRestrict s = r := Subtype.ext hsr
      exact Subgroup.mem_map.mpr ⟨s, hs, by rw [← hrs, hπ' s]⟩
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_map.mpr ⟨φ.rangeRestrict s, ?_, hπ' s⟩
      rw [Subgroup.mem_subgroupOf, ggRootSub, Subgroup.mem_map]
      exact ⟨s, hs, rfl⟩
  have hmap : Rbar.map π' =
      (((ggU .twistedE6 n f).D.rootGroup β).map π0).map
        (MulAut.conj (π0 u)).toMonoidHom := by
    rw [hRmap, Subgroup.map_map, hcomp u, ← Subgroup.map_map]
  have hI' : GGRootNormInner (Rbar.map π') := by
    rw [hmap]
    exact CFSG.StandardType.ggRootNormInner_map_mulEquiv (MulAut.conj (π0 u)) hadj
  exact Cover.ggRootNormInner_of_map_surjective π' hsurj hcent hodd
    (CFSG.TauCetiBridge.Twisted.center_graphFixedRootGroup_eq_bot (K := k) θ) hR hI'

theorem ggRootInnerAt_ggU_twistedE6_short
    {n f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X]
    (φ : (ggU .twistedE6 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hs : ∃ w : GGWeyl (ggU .twistedE6 n f).D,
      β = weylAction (ggU .twistedE6 n f).D.isFiniteType w twE6Alpha)
    (u : (ggU .twistedE6 n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .twistedE6 n f).D φ β u) := by
  have hI := l10sw3_inner_range (f := f) hf φ hker hs u
  intro Y hY2 hYK hYR hNY
  exact ggRootNormInner_le_sup_centralizer (Subgroup.map_le_range _ _) hYK hYR hY2 hNY hI

theorem itemThree_ggU_twistedE6_short
    {n f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X]
    (ψ : (ggU .twistedE6 n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hs : ∃ w : GGWeyl (ggU .twistedE6 n f).D,
      β = weylAction (ggU .twistedE6 n f).D.isFiniteType w twE6Alpha)
    (u : (ggU .twistedE6 n f).K) {R : Subgroup X}
    (hR : R = ggRootSub (ggU .twistedE6 n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have hI := l10sw3_inner_range (f := f) hf ψ hker hs u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

end CFSG.StandardType.LieKnownR2.TwE6
