module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

abbrev BMPSubquot (p : ℕ) {K : Type} [Group K] (x : K) (C : Subgroup K) : Type :=
  ↥((C.subgroupOf (Subgroup.centralizer {x})).map
    (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({x} : Set K)))))

private noncomputable abbrev gkC_subgroupEquivMap {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') (X : Subgroup G) : ↥X ≃* ↥(X.map e.toMonoidHom) :=
  Subgroup.equivMapOfInjective X e.toMonoidHom (fun _ _ h => e.injective h)

private noncomputable def gkC_quotientPPrimeCoreMap {G G' : Type} [Group G] [Group G']
    (p : ℕ) (e : G ≃* G') (X : Subgroup G) :
    ↥X ⧸ LargeEvenPPrimeCore p ↥X ≃*
      ↥(X.map e.toMonoidHom) ⧸ LargeEvenPPrimeCore p ↥(X.map e.toMonoidHom) :=
  QuotientGroup.congr (LargeEvenPPrimeCore p ↥X)
    (LargeEvenPPrimeCore p ↥(X.map e.toMonoidHom))
    (gkC_subgroupEquivMap e X)
    (CFSG.pPrimeCore_map_iso p (gkC_subgroupEquivMap e X))

private theorem gkC_subgroupOf_map_subgroupEquivMap {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') {J X : Subgroup G} :
    (J.subgroupOf X).map (gkC_subgroupEquivMap e X).toMonoidHom =
      (J.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    exact ⟨x.1, hx, (Subgroup.coe_equivMapOfInjective_apply X e.toMonoidHom
      (fun _ _ h => e.injective h) x).symm⟩
  · intro hz
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hz
    obtain ⟨g, hg, hgz⟩ := hz
    have hgX : g ∈ X := by
      obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp (z.2 : z.1 ∈ X.map e.toMonoidHom)
      have : x = g := e.injective (hxeq.trans hgz.symm)
      rwa [this] at hx
    rw [Subgroup.mem_map]
    refine ⟨⟨g, hgX⟩, hg, ?_⟩
    ext
    exact (Subgroup.coe_equivMapOfInjective_apply X e.toMonoidHom
      (fun _ _ h => e.injective h) ⟨g, hgX⟩).trans hgz

private theorem gkC_subgroupOf_map_quotientPPrimeCoreMap {G G' : Type} [Group G] [Group G']
    (p : ℕ) (e : G ≃* G') (X J : Subgroup G) :
    ((J.subgroupOf X).map
        (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X))).map
          (gkC_quotientPPrimeCoreMap p e X).toMonoidHom =
      ((J.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom)).map
        (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥(X.map e.toMonoidHom))) := by
  have hcomp : MonoidHom.comp (gkC_quotientPPrimeCoreMap p e X).toMonoidHom
        (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)) =
      MonoidHom.comp (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥(X.map e.toMonoidHom)))
        (gkC_subgroupEquivMap e X).toMonoidHom := by
    ext x
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact congrArg (fun H => H.map
    (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥(X.map e.toMonoidHom))))
    (gkC_subgroupOf_map_subgroupEquivMap e (J := J) (X := X))

private theorem gkC_map_map_symm_self {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X : Subgroup G) : (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext g
    simp
  rw [hcomp, Subgroup.map_id]

private theorem gkC_nonempty_subgroupCongr_of_map_eq {A B : Type} [Group A] [Group B]
    (ψ : A ≃* B) {S : Subgroup A} {S' : Subgroup B} (h : S.map ψ.toMonoidHom = S') :
    Nonempty (↥S ≃* ↥S') :=
  ⟨(ψ.subgroupMap S).trans (MulEquiv.subgroupCongr h)⟩

private noncomputable def gkC_quotientCenterMulEquiv {L L' : Type} [Group L] [Group L']
    (e : L ≃* L') :
    L ⧸ Subgroup.center L ≃* L' ⧸ Subgroup.center L' :=
  QuotientGroup.congr (Subgroup.center L) (Subgroup.center L') e (Subgroup.map_center_eq e)

private theorem gkC_commutator_map_top_of_surjective {L L' : Type} [Group L] [Group L']
    (f : L →* L') (hf : Function.Surjective f) (h : commutator L = ⊤) :
    commutator L' = ⊤ := by
  have hperf : Group.IsPerfect L := Group.isPerfect_def.mpr h
  exact (Group.IsPerfect.ofSurjective (f := f) hf).commutator_eq_top

private theorem gkC_largeEvenPComponent_map_of {G G' : Type} [Group G] [Finite G] [Group G']
    [Finite G'] (p : ℕ) (e : G ≃* G') (X L : Subgroup G)
    (h : LargeEvenPComponent p X L) :
    LargeEvenPComponent p (X.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  unfold LargeEvenPComponent at h ⊢
  obtain ⟨hLX, hsub, hcomp, hmax⟩ := h
  refine ⟨Subgroup.map_mono hLX, hsub.map e.toMonoidHom, ?_, ?_⟩
  · have hIC : CFSG.Open.IsComponentOf
        ((L.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X))) ⊤ :=
      CFSG.Assembly.isComponentOf_iff_open.mp hcomp
    have hIC' := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv
      (gkC_quotientPPrimeCoreMap p e X) hIC
    have htop : Subgroup.map (gkC_quotientPPrimeCoreMap p e X).toMonoidHom
        (⊤ : Subgroup (↥X ⧸ LargeEvenPPrimeCore p ↥X)) = ⊤ :=
      Subgroup.map_equiv_top (gkC_quotientPPrimeCoreMap p e X)
    rw [htop] at hIC'
    rw [gkC_subgroupOf_map_quotientPPrimeCoreMap p e X L] at hIC'
    exact CFSG.Assembly.isComponentOf_iff_open.mpr hIC'
  · intro J' hJ'lt hJ'sub heq
    let J : Subgroup G := J'.comap e.toMonoidHom
    have hJmap : J.map e.toMonoidHom = J' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective J'
    have hJX : J ≤ X := by
      intro g hg
      have h1 : g ∈ (X.map e.toMonoidHom).comap e.toMonoidHom :=
        (Subgroup.map_mono hLX) (hJ'lt.le hg)
      rwa [Subgroup.comap_map_eq_self_of_injective e.injective X] at h1
    have hJleL : J ≤ L := by
      intro g hg
      have h1 : e g ∈ L.map e.toMonoidHom := hJ'lt.le hg
      rw [Subgroup.mem_map] at h1
      obtain ⟨l, hl, hle⟩ := h1
      rw [e.injective hle] at hl
      exact hl
    have hJlt : J < L := by
      refine lt_of_le_of_ne hJleL ?_
      intro hJL
      have hJ'eq : J' = L.map e.toMonoidHom := by
        calc J' = (J'.comap e.toMonoidHom).map e.toMonoidHom :=
              (Subgroup.map_comap_eq_self_of_surjective e.surjective J').symm
          _ = J.map e.toMonoidHom := rfl
          _ = L.map e.toMonoidHom := by rw [hJL]
      exact hJ'lt.ne hJ'eq
    have hJsub : IsSubnormal J X := by
      have h0 := CFSG.Assembly.IsSubnormal.comap e.toMonoidHom hJ'sub
      rwa [Subgroup.comap_map_eq_self_of_injective e.injective X] at h0
    have hψJ := gkC_subgroupOf_map_quotientPPrimeCoreMap p e X J
    rw [hJmap] at hψJ
    have hψL := gkC_subgroupOf_map_quotientPPrimeCoreMap p e X L
    have heqmap : ((J.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X))).map
          (gkC_quotientPPrimeCoreMap p e X).toMonoidHom =
        ((L.subgroupOf X).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X))).map
          (gkC_quotientPPrimeCoreMap p e X).toMonoidHom := by
      rw [hψJ, hψL]
      exact heq
    have hinj : Function.Injective (gkC_quotientPPrimeCoreMap p e X).toMonoidHom :=
      fun a b h => (gkC_quotientPPrimeCoreMap p e X).injective h
    exact hmax J hJlt hJsub (Subgroup.map_injective hinj heqmap)

theorem largeEvenPPrimeCore_map_mulEquiv {G G' : Type} [Group G] [Finite G] [Group G']
    [Finite G'] (p : ℕ) (φ : G ≃* G') :
    LargeEvenPPrimeCore p G' = (LargeEvenPPrimeCore p G).map φ.toMonoidHom := by
  exact (CFSG.pPrimeCore_map_iso p φ).symm

theorem largeEvenPComponent_map_mulEquiv {G G' : Type} [Group G] [Finite G] [Group G']
    [Finite G'] (p : ℕ) (e : G ≃* G') (X L : Subgroup G) :
    LargeEvenPComponent p (X.map e.toMonoidHom) (L.map e.toMonoidHom) ↔
      LargeEvenPComponent p X L := by
  constructor
  · intro h
    have h' := gkC_largeEvenPComponent_map_of p e.symm (X.map e.toMonoidHom) (L.map e.toMonoidHom) h
    rwa [gkC_map_map_symm_self e X, gkC_map_map_symm_self e L] at h'
  · exact gkC_largeEvenPComponent_map_of p e X L

theorem largeEvenMarking_true_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : StandardType.LargeEvenMarking L (fun _ _ _ _ _ _ => True)) :
    StandardType.LargeEvenMarking L' (fun _ _ _ _ _ _ => True) := by
  unfold StandardType.LargeEvenMarking CFSG.Assembly.LargeEvenMarkingLegacy at h ⊢
  obtain ⟨hcomm, lab, hlab, hraw⟩ := h
  refine ⟨gkC_commutator_map_top_of_surjective e.toMonoidHom e.surjective hcomm, lab, hlab, ?_⟩
  let Q : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* R, True
  let Q' : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : L' ⧸ Subgroup.center L' ≃* R, True
  have hraw_std : CFSG.StandardType.LargeEvenRawDatum lab Q :=
    (CFSG.StandardType.largeEvenRawDatum_legacy lab Q).mpr hraw
  have hmono : CFSG.StandardType.LargeEvenRawDatum lab Q' :=
    CFSG.StandardType.largeEvenRawDatum_mono (Q := Q) (Q' := Q') (fun R _ I F hQ1 => by
      obtain ⟨hsimple, hna, θ, -⟩ := hQ1
      exact ⟨hsimple, hna, (gkC_quotientCenterMulEquiv e).symm.trans θ, trivial⟩) hraw_std
  exact (CFSG.StandardType.largeEvenRawDatum_legacy lab Q').mp hmono

theorem bmPSubquot_mulEquiv {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K'] (p : ℕ)
    (e : K ≃* K') {x : K} {x' : K'} (hx : e x = x') {C : Subgroup K} {C' : Subgroup K'}
    (hC : C.map e.toMonoidHom = C') : Nonempty (BMPSubquot p x C ≃* BMPSubquot p x' C') := by
  subst hx
  subst hC
  let X : Subgroup K := Subgroup.centralizer ({x} : Set K)
  let X' : Subgroup K' := Subgroup.centralizer ({e x} : Set K')
  have hX : X.map e.toMonoidHom = X' :=
    CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e x
  let φ0 : ↥X ≃* ↥(X.map e.toMonoidHom) := gkC_subgroupEquivMap e X
  let φ : ↥X ≃* ↥X' := φ0.trans (MulEquiv.subgroupCongr hX)
  let q : ↥X →* ↥X ⧸ LargeEvenPPrimeCore p ↥X :=
    QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X)
  let q' : ↥X' →* ↥X' ⧸ LargeEvenPPrimeCore p ↥X' :=
    QuotientGroup.mk' (LargeEvenPPrimeCore p ↥X')
  let ψ : ↥X ⧸ LargeEvenPPrimeCore p ↥X ≃* ↥X' ⧸ LargeEvenPPrimeCore p ↥X' :=
    QuotientGroup.congr (LargeEvenPPrimeCore p ↥X) (LargeEvenPPrimeCore p ↥X') φ
      (largeEvenPPrimeCore_map_mulEquiv p φ).symm
  have hφcoe : ∀ z : ↥X, (φ z : K') = e z.1 := by
    intro z
    show ((MulEquiv.subgroupCongr hX) (φ0 z) : K') = e z.1
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply X e.toMonoidHom
      (fun _ _ h => e.injective h) z
  have hmapC : (C.subgroupOf X).map φ.toMonoidHom =
      (C.map e.toMonoidHom).subgroupOf X' := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      exact ⟨z.1, hz, (hφcoe z).symm⟩
    · intro hy
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hy
      obtain ⟨c, hc, hce⟩ := hy
      have hyX : (y : K') ∈ X.map e.toMonoidHom := by
        rw [hX]
        exact y.2
      obtain ⟨z0, hz0, hz0e⟩ := Subgroup.mem_map.mp hyX
      have hzX : e.symm (y : K') ∈ X := by
        have hz0eq : z0 = e.symm (y : K') := by
          apply e.injective
          change e.toMonoidHom z0 = e.toMonoidHom (e.symm (y : K'))
          rw [hz0e]
          exact (e.apply_symm_apply (y : K')).symm
        rwa [hz0eq] at hz0
      rw [Subgroup.mem_map]
      refine ⟨⟨e.symm (y : K'), hzX⟩, ?_, ?_⟩
      · show e.symm (y : K') ∈ C
        have hc' : e.symm (y : K') = c := by
          rw [← hce]
          exact e.symm_apply_apply c
        rw [hc']
        exact hc
      · exact Subtype.ext ((hφcoe ⟨e.symm (y : K'), hzX⟩).trans
          (e.apply_symm_apply (y : K')))
  have hcompψ : MonoidHom.comp ψ.toMonoidHom q = MonoidHom.comp q' φ.toMonoidHom := by
    ext z
    rfl
  have hS : ((C.subgroupOf X).map q).map ψ.toMonoidHom =
      ((C.map e.toMonoidHom).subgroupOf X').map q' := by
    rw [Subgroup.map_map, hcompψ, ← Subgroup.map_map, hmapC]
  exact gkC_nonempty_subgroupCongr_of_map_eq ψ hS

end CFSG.StandardType.SporadicShape
