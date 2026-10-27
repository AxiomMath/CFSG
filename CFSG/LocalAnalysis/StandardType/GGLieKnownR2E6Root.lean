module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E6Inner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E6NC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverLift
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ItemThree

public section

namespace CFSG.StandardType.LieKnownR2.E6

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.Blueprint.Chevalley
open scoped commutatorElement

private theorem l10se6r_inner_range
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : (ggU .E6 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    {β : Fin (ggU .E6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E6 n f).D.roots)
    (u : (ggU .E6 n f).K) :
    GGRootNormInner ((ggRootSub (ggU .E6 n f).D φ β u).subgroupOf φ.range) := by
  have hβ' : IsRoot .E6 β := by
    have h : β ∈ (e6Datum (GaloisField 2 f)).roots := hβ
    rw [MinData.Valid.minDatum_roots] at h
    exact h
  have hadj : GGRootNormInner
      ((adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup β) :=
    ExcInner.ggRootNormInner_adj_E6 hf (mem_adjDatum_roots.2 hβ')
  let π0 : (ggU .E6 n f).K →* ↥(adjointGroup .E6 (GaloisField 2 f)) :=
    e6Isogeny (GaloisField 2 f)
  have hmapadj : (((ggU .E6 n f).D).rootGroup β).map π0 =
      (adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup β :=
    CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := GaloisField 2 f) hβ'
  haveI : Finite ((ggU .E6 n f).K) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid (GaloisField 2 f)
  haveI : Group.IsPerfect ((ggU .E6 n f).K) :=
    CFSG.LieType.CurtisTits.isPerfect_e6 (GaloisField 2 f)
  haveI : Finite ↥φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range (f := φ)
  have hkerπ0 : φ.ker ≤ π0.ker :=
    hker.trans (center_le_ker_e6Isogeny (K := GaloisField 2 f))
  let π' : ↥φ.range →* ↥(adjointGroup .E6 (GaloisField 2 f)) :=
    (QuotientGroup.lift φ.ker π0 hkerπ0).comp
      (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
  have hπ' : ∀ x : (ggU .E6 n f).K,
      π' (φ.rangeRestrict x) = π0 x := by
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
    obtain ⟨s, hs⟩ := e6Isogeny_surjective (GaloisField 2 f) a
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
    have hzZ : z ∈ Subgroup.center ((ggU .E6 n f).K) :=
      (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center
        (GaloisField 2 f)) hz
    have hcomm : (t * z : (ggU .E6 n f).K) = z * t := Subgroup.mem_center_iff.mp hzZ t
    rw [← ht, ← φ.rangeRestrict.map_mul, ← φ.rangeRestrict.map_mul, hcomm]
  have hodd : Odd (Nat.card π'.ker) := by
    have hdvd : Nat.card π'.ker ∣ Nat.card π0.ker := by
      rw [hker_eq]
      exact Subgroup.card_map_dvd (H := π0.ker) (f := φ.rangeRestrict)
    exact Odd.of_dvd_nat (odd_card_ker_e6Isogeny (K := GaloisField 2 f)) hdvd
  set Rbar : Subgroup ↥φ.range :=
    (ggRootSub (ggU .E6 n f).D φ β u).subgroupOf φ.range with hRbar_def
  have hR : IsPGroup 2 Rbar := by
    rw [hRbar_def]
    have hS : IsPGroup 2
        (((ggU .E6 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
      have h := rootGroup_isPGroup_E6 (β := β) u rfl
      rwa [ggRootSub, Subgroup.map_id] at h
    exact IsPGroup.comap_subtype (hS.map φ) (K := φ.range)
  have hRmap : Rbar.map π' =
      (((ggU .E6 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map π0 := by
    rw [hRbar_def]
    ext a
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : (r : X) ∈ ggRootSub (ggU .E6 n f).D φ β u :=
        Subgroup.mem_subgroupOf.mp hr
      rw [ggRootSub] at hr'
      obtain ⟨s, hs, hsr⟩ := Subgroup.mem_map.mp hr'
      have hrs : φ.rangeRestrict s = r := Subtype.ext hsr
      exact Subgroup.mem_map.mpr ⟨s, hs, by rw [← hrs, hπ' s]⟩
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_map.mpr ⟨φ.rangeRestrict s, ?_, hπ' s⟩
      rw [Subgroup.mem_subgroupOf, ggRootSub, Subgroup.mem_map]
      exact ⟨s, hs, rfl⟩
  have hcomp : π0.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (π0 u)).toMonoidHom.comp π0 := by
    apply MonoidHom.ext
    intro x
    change π0 (u * x * u⁻¹) = π0 u * π0 x * (π0 u)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hRmap2 : (((ggU .E6 n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map π0 =
      (((adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup β).map
        (MulAut.conj (π0 u)).toMonoidHom) := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hmapadj]
  have hmap : Rbar.map π' =
      ((adjDatum (rootOperatorFamily .E6) (GaloisField 2 f)).rootGroup β).map
        (MulAut.conj (π0 u)).toMonoidHom := by
    rw [hRmap, hRmap2]
  have hI' : GGRootNormInner (Rbar.map π') := by
    rw [hmap]
    exact ggRootNormInner_map_mulEquiv (MulAut.conj (π0 u)) hadj
  exact Cover.ggRootNormInner_of_map_surjective π' hsurj hcent hodd
    (center_adjointGroup_eq_bot (τ := .E6) (K := GaloisField 2 f)) hR hI'

theorem ggRootInnerAt_ggU_e6
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : (ggU .E6 n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    {β : Fin (ggU .E6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E6 n f).D.roots)
    (u : (ggU .E6 n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .E6 n f).D φ β u) := by
  have hI := l10se6r_inner_range hf φ hker hβ u
  intro Y hY2 hYK hYR hNY
  exact ggRootNormInner_le_sup_centralizer (Subgroup.map_le_range _ _) hYK hYR hY2 hNY hI

theorem itemThree_ggU_e6
    {n f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (ψ : (ggU .E6 n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    {β : Fin (ggU .E6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E6 n f).D.roots)
    (u : (ggU .E6 n f).K) {R : Subgroup X} (hR : R = ggRootSub (ggU .E6 n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have hI := l10se6r_inner_range hf ψ hker hβ u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

end CFSG.StandardType.LieKnownR2.E6
