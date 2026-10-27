module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import CFSG.GroupTheory.LangNormOneDescent
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LangPositionPart1
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
import CFSG.LocalAnalysis.EvenBN.G2.Automorphisms
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatNo117Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PinnedBaseChange
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FixedTorus
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientActionPart1
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Misc
public import TauCeti.Algebra.CharP.Frobenius.Fixed
public import TauCeti.FieldTheory.Finite.SepClosedSubfield
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.RootBaseChange

open CFSG.StandardType.F4ExplicitPos.PinnedBaseChange

open CFSG.StandardType.F4ExplicitPos.FixedTorus

open CFSG.StandardType.F4ExplicitPos.BruhatNo117

open CFSG.StandardType.F4ExplicitPos.PositiveNo117

namespace CFSG.StandardType.F4ExplicitPos.FixedImage

def prodPinnedXR
    (R : Type*) [CommRing R] {m : ℕ}
    (α : Fin m → Fin Tag.F4.rank → ℤ) (c : Fin m → R) :
    (Module.End R (RootModule Tag.F4 R))ˣ :=
  (List.ofFn fun i => pinnedX Tag.F4 R (α i) (c i)).prod

theorem bcGL_prodPinnedXR
    {R S : Type} [Field R] [Field S] (f : R →+* S) {m : ℕ}
    (α : Fin m → Fin Tag.F4.rank → ℤ) (c : Fin m → R) :
    bcGL (τ := Tag.F4) f (prodPinnedXR R α c) =
      prodPinnedXR S α (fun i => f (c i)) := by
  unfold prodPinnedXR
  rw [map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.2 (funext fun i => bcGL_pinnedX (τ := Tag.F4) f (α i) (c i))

theorem map_bcGL_torusGroup_le
    {R S : Type} [Field R] [Field S] (φ : R →+* S) :
    (torusGroup Tag.F4 R).map (bcGL (τ := Tag.F4) φ) ≤ torusGroup Tag.F4 S := by
  rw [torusGroup, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨y, ⟨⟨i, t⟩, rfl⟩, rfl⟩
  rw [bcGL_torusElt φ i t]
  exact Subgroup.subset_closure ⟨(i, Units.map φ.toMonoidHom t), rfl⟩

theorem fixed_posUnipotent_mem_map_adjointGroup
    {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {u : ModGL Tag.F4 Ω} (hu : u ∈ posUnipotent Tag.F4 Ω)
    (hfix : Units.map (entrywiseHom Fr) u = u) :
    u ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) := by
  classical
  obtain ⟨α, hαinj, hαrange⟩ :=
    exists_rootEnum (finite_of_forall_isRoot_pos (τ := Tag.F4)
      (S := {β : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 β ∧ 0 < height β}) (fun _ h => h))
  have hBij := (f4_positive_root_collection (R := Ω)).2 α hαinj hαrange
  have hFmat : (Units.map (entrywiseHom Fr) : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) = bcGL Fr := by
    rw [bcGL, ← bcEndHom_eq_entrywiseHom Fr]
  have hfixbc : bcGL Fr u = u := by rw [← hFmat]; exact hfix
  obtain ⟨c, hc⟩ := hBij.2.2 hu
  have hc' : prodPinnedXR Ω α c = u := by simpa [prodPinnedXR] using hc
  have hcfix : (fun i => Fr (c i)) = c := by
    apply hBij.2.1 (Set.mem_univ _) (Set.mem_univ _)
    change prodPinnedXR Ω α (fun i => Fr (c i)) = prodPinnedXR Ω α c
    rw [← bcGL_prodPinnedXR Fr α c, hc', hfixbc]
  have hcoord : ∀ i, Fr (c i) = c i := fun i => congrFun hcfix i
  have hrange : ∀ i, c i ∈ Set.range (algebraMap K Ω) := fun i => by
    apply mem_range_algebraMap_of_pow_card_eq
    rw [← hFr (c i), hcoord i]
  choose a ha using hrange
  have hfun : (fun i => algebraMap K Ω (a i)) = c := funext ha
  refine Subgroup.mem_map.2 ⟨prodPinnedXR K α a, ?_, ?_⟩
  · rw [prodPinnedXR]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact pinnedX_mem_adjointGroup (τ := Tag.F4) (α i) (a i)
  · rw [bcGL_prodPinnedXR (algebraMap K Ω) α a, hfun, hc']

theorem f4_finite_field_fixed_eq_map
    {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) =
      adjointGroup Tag.F4 Ω ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id (ModGL Tag.F4 Ω)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.2
      ⟨bcGL_mem_adjointGroup (τ := Tag.F4) (algebraMap K Ω) hg, ?_⟩
    exact units_map_entrywiseHom_bcGL_algebraMap (τ := Tag.F4) Fr hFr g
  · intro x hx
    obtain ⟨hxadj, hxfix⟩ := Subgroup.mem_inf.1 hx
    have hxfix' : Units.map (entrywiseHom Fr) x = x := hxfix
    have hFmatbc : (Units.map (entrywiseHom Fr) : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) =
        bcGL (τ := Tag.F4) Fr := by
      rw [bcGL, ← bcEndHom_eq_entrywiseHom Fr]
    have hfixbc : bcGL (τ := Tag.F4) Fr x = x := by rw [← hFmatbc]; exact hxfix'
    obtain ⟨w, h, hh, u, hu, v, hv, hgfac⟩ := f4_hfactor x hxadj
    set n := canonicalRep (coxeterSystem Tag.F4) Ω w with hn
    have hFr_n : bcGL (τ := Tag.F4) Fr n = n := by
      rw [hn, bcGL_canonicalRep (τ := Tag.F4) Fr (coxeterSystem Tag.F4) w]
    have hFr_h : bcGL (τ := Tag.F4) Fr h ∈ torusGroup Tag.F4 Ω :=
      map_bcGL_torusGroup_le Fr (Subgroup.mem_map_of_mem _ hh)
    have hFr_u : bcGL (τ := Tag.F4) Fr u ∈ posUnipotent Tag.F4 Ω := by
      have hle := map_bcGL_rootSpan_le (τ := Tag.F4) Fr
        ({β : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 β ∧ 0 < height β})
      exact hle (Subgroup.mem_map_of_mem _ hu)
    have hFr_v : bcGL (τ := Tag.F4) Fr v ∈ rootSpan Tag.F4 Ω (inversionSet w) :=
      map_bcGL_rootSpan_le (τ := Tag.F4) Fr (inversionSet w) (Subgroup.mem_map_of_mem _ hv)
    have hfac' : bcGL (τ := Tag.F4) Fr x =
        bcGL (τ := Tag.F4) Fr h * bcGL (τ := Tag.F4) Fr u * n * bcGL (τ := Tag.F4) Fr v := by
      rw [hgfac, map_mul, map_mul, map_mul, hFr_n]
    have hfac'' : x =
        bcGL (τ := Tag.F4) Fr h * bcGL (τ := Tag.F4) Fr u * n * bcGL (τ := Tag.F4) Fr v :=
      hfixbc.symm.trans hfac'
    obtain ⟨hhfix, hufix, hvfix⟩ :=
      f4_sameW_bruhat_unique (w := w) hh hFr_h hu hFr_u hv hFr_v (hgfac.symm.trans hfac'')
    have hfix_h : Units.map (entrywiseHom Fr) h = h := by rw [hFmatbc, ← hhfix]
    have hfix_u : Units.map (entrywiseHom Fr) u = u := by rw [hFmatbc, ← hufix]
    have hfix_v : Units.map (entrywiseHom Fr) v = v := by rw [hFmatbc, ← hvfix]
    have hvU : v ∈ posUnipotent Tag.F4 Ω :=
      rootSpan_le_posUnipotent (fun α hα => inversionSet_pos (w := w) hα) hv
    have hJ : h ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) :=
      fixed_torus_mem_map_adjointGroup (K := K) (Ω := Ω) Fr hFr hh hfix_h
    have hJu : u ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) :=
      fixed_posUnipotent_mem_map_adjointGroup (K := K) (Ω := Ω) Fr hFr hu hfix_u
    have hJv : v ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) :=
      fixed_posUnipotent_mem_map_adjointGroup (K := K) (Ω := Ω) Fr hFr hvU hfix_v
    have hJn : n ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) := by
      rw [hn, ← bcGL_canonicalRep (τ := Tag.F4) (algebraMap K Ω) (coxeterSystem Tag.F4) w]
      exact Subgroup.mem_map_of_mem _
        (canonicalRep_mem_adjointGroup (coxeterSystem Tag.F4) K w)
    rw [hgfac]
    exact mul_mem (mul_mem (mul_mem hJ hJu) hJn) hJv

theorem iotaF4_range
    {K Ω X : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω] [Group X] [Finite X]
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥) :
    (CFSG.StandardType.F4ExplicitPos.AmbientAction.iotaF4 (L := Ω) ψ G0 hG0 hker hcenter).range =
      (CFSG.StandardType.F4ExplicitPos.AmbientAction.jF4 (K := K) (L := Ω)).range := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ :=
      (CFSG.StandardType.F4ExplicitPos.AmbientAction.eF4 ψ G0 hG0 hker hcenter).surjective y
    exact ⟨u, (CFSG.StandardType.F4ExplicitPos.AmbientAction.iotaF4_e ψ G0 hG0 hker hcenter u).symm⟩
  · rintro x ⟨u, rfl⟩
    exact ⟨CFSG.StandardType.F4ExplicitPos.AmbientAction.eF4 ψ G0 hG0 hker hcenter u,
      CFSG.StandardType.F4ExplicitPos.AmbientAction.iotaF4_e ψ G0 hG0 hker hcenter u⟩

section ActualAutomorphismFixedImage
open CFSG.LieType.Chevalley

public def f4FixedImageGroup {K : Type} [Field K] (sigma : K ≃+* K) :
    Subgroup (ModGL Tag.F4 K) :=
  adjointGroup Tag.F4 K ⊓
    (Units.map (entrywiseHom sigma.toRingHom)).eqLocus
      (MonoidHom.id (ModGL Tag.F4 K))

private lemma mapRange_eq_self_iff {K : Type} [Field K] {τ : Tag}
    (sigma : K →+* K) (v : RootModule τ K) :
    Finsupp.mapRange sigma sigma.map_zero v = v ↔ ∀ l, sigma (v l) = v l := by
  constructor
  · intro h l
    have := congrArg (fun x : RootModule τ K => x l) h
    simpa [Finsupp.mapRange_apply] using this
  · intro h
    ext l
    simpa [Finsupp.mapRange_apply] using h l

public lemma units_map_entrywiseHom_eq_self_iff {K : Type} [Field K] {τ : Tag}
    (sigma : K →+* K) (g : ModGL τ K) :
    Units.map (entrywiseHom sigma) g = g ↔
      ∀ b l, sigma
        (((g : Module.End K (RootModule τ K)) (Finsupp.single b 1)) l) =
        (((g : Module.End K (RootModule τ K)) (Finsupp.single b 1)) l) := by
  constructor
  · intro h b l
    have h' : entrywiseHom sigma (g : Module.End K (RootModule τ K)) =
        (g : Module.End K (RootModule τ K)) :=
      congrArg (fun u : ModGL τ K => (u : Module.End K (RootModule τ K))) h
    have hb := congrArg
      (fun A : Module.End K (RootModule τ K) => A (Finsupp.single b 1)) h'
    change entrywiseHom sigma (g : Module.End K (RootModule τ K))
        (Finsupp.single b 1) =
      (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) at hb
    rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.entrywiseHom_single_apply] at hb
    exact (mapRange_eq_self_iff (τ := τ) sigma
      ((g : Module.End K (RootModule τ K)) (Finsupp.single b 1))).mp hb l
  · intro h
    apply Units.ext
    apply CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.end_ext_single_field
    intro b
    change entrywiseHom sigma (g : Module.End K (RootModule τ K))
        (Finsupp.single b 1) =
      (g : Module.End K (RootModule τ K)) (Finsupp.single b 1)
    rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU.entrywiseHom_single_apply]
    exact (mapRange_eq_self_iff (τ := τ) sigma
      ((g : Module.End K (RootModule τ K)) (Finsupp.single b 1))).mpr (fun l => h b l)


public theorem f4FixedImageGroup_eq_map
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K) :
    f4FixedImageGroup sigma =
      (adjointGroup Tag.F4 (fixSubfield sigma)).map
        (bcGL (τ := Tag.F4) (algebraMap ↥(fixSubfield sigma) K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K0 : Subfield K := fixSubfield sigma
  have : Finite ↥K0 := inferInstance
  have : CharP ↥K0 2 := Subfield.charP K0 2
  let : Fintype K := Fintype.ofFinite K
  let : Fintype ↥K0 := Fintype.ofFinite ↥K0
  obtain ⟨e, _he, hK0card_fintype⟩ := FiniteField.card ↥K0 2
  have hK0card : Nat.card ↥K0 = 2 ^ (e : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hK0card_fintype
  let Fr : K →+* K := iterateFrobenius K 2 (e : ℕ)
  have hFr : ∀ c : K, Fr c = c ^ Nat.card ↥K0 := by
    intro c
    rw [hK0card]
    rfl
  have hK0eq : K0 = TauCeti.frobeniusFixedSubfield K 2 (e : ℕ) :=
    TauCeti.eq_frobeniusFixedSubfield_of_natCard (K := K) (p := 2) (n := e) hK0card
  have hK0eq' : K0 = RingHom.eqLocusField Fr (RingHom.id K) := by
    rw [hK0eq]
    ext x
    rw [TauCeti.mem_frobeniusFixedSubfield, RingHom.mem_eqLocusField, hFr, hK0card]
    rfl
  have hfix_iff (x : K) : sigma x = x ↔ Fr x = x := by
    have hmem : x ∈ K0 ↔ x ∈ RingHom.eqLocusField Fr (RingHom.id K) := by rw [hK0eq']
    simpa [K0, mem_fixSubfield, RingHom.mem_eqLocusField] using hmem
  have hEntryEq (g : ModGL Tag.F4 K) :
      Units.map (entrywiseHom sigma.toRingHom) g = g ↔
        Units.map (entrywiseHom Fr) g = g := by
    rw [units_map_entrywiseHom_eq_self_iff, units_map_entrywiseHom_eq_self_iff]
    constructor
    · intro h b l
      exact (hfix_iff _).mp (h b l)
    · intro h b l
      exact (hfix_iff _).mpr (h b l)
  change (adjointGroup Tag.F4 K ⊓
      (Units.map (entrywiseHom sigma.toRingHom)).eqLocus
        (MonoidHom.id (ModGL Tag.F4 K))) = _
  rw [show adjointGroup Tag.F4 K ⊓
        (Units.map (entrywiseHom sigma.toRingHom)).eqLocus
          (MonoidHom.id (ModGL Tag.F4 K)) =
      adjointGroup Tag.F4 K ⊓
        (Units.map (entrywiseHom Fr)).eqLocus
          (MonoidHom.id (ModGL Tag.F4 K)) from by
    ext g
    change (g ∈ adjointGroup Tag.F4 K ∧
        Units.map (entrywiseHom sigma.toRingHom) g = g) ↔
      (g ∈ adjointGroup Tag.F4 K ∧
        Units.map (entrywiseHom Fr) g = g)
    rw [hEntryEq g]]
  exact (f4_finite_field_fixed_eq_map (K := ↥K0) (Ω := K) Fr hFr).symm

public theorem f4FixedImageGroup_eq_map_explicit
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K) :
    (adjointGroup Tag.F4 K ⊓
      (Units.map (entrywiseHom sigma.toRingHom)).eqLocus
        (MonoidHom.id (ModGL Tag.F4 K))) =
      (adjointGroup Tag.F4 (fixSubfield sigma)).map
        (bcGL (τ := Tag.F4) (algebraMap ↥(fixSubfield sigma) K)) := by
  simpa [f4FixedImageGroup] using f4FixedImageGroup_eq_map (K := K) sigma

public noncomputable def f4FixedImageEquiv
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K) :
    ↥(f4FixedImageGroup sigma) ≃*
      ↥(adjointGroup Tag.F4 (fixSubfield sigma)) := by
  classical
  let K0 : Subfield K := fixSubfield sigma
  let H0 : Subgroup (ModGL Tag.F4 ↥K0) := adjointGroup Tag.F4 K0
  let H : Subgroup (ModGL Tag.F4 K) :=
    H0.map (bcGL (τ := Tag.F4) (algebraMap ↥K0 K))
  have hbcGLinj : Function.Injective
      (bcGL (τ := Tag.F4) (algebraMap ↥K0 K)) :=
    bcGL_injective (algebraMap ↥K0 K) (algebraMap ↥K0 K).injective
  let eMap : ↥H ≃* ↥H0 :=
    (Subgroup.equivMapOfInjective H0
      (bcGL (τ := Tag.F4) (algebraMap ↥K0 K)) hbcGLinj).symm
  let eCast : ↥(f4FixedImageGroup sigma) ≃* ↥H :=
    MulEquiv.subgroupCongr (f4FixedImageGroup_eq_map (K := K) sigma)
  exact eCast.trans eMap

public theorem f4FixedImageEquiv_symm_apply_coe
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K)
    (h : ↥(adjointGroup Tag.F4 (fixSubfield sigma))) :
    ((f4FixedImageEquiv (K := K) sigma).symm h : ModGL Tag.F4 K) =
      bcGL (τ := Tag.F4) (algebraMap ↥(fixSubfield sigma) K) h := by
  classical
  let K0 : Subfield K := fixSubfield sigma
  let H0 : Subgroup (ModGL Tag.F4 ↥K0) := adjointGroup Tag.F4 K0
  let H : Subgroup (ModGL Tag.F4 K) :=
    H0.map (bcGL (τ := Tag.F4) (algebraMap ↥K0 K))
  have hbcGLinj : Function.Injective
      (bcGL (τ := Tag.F4) (algebraMap ↥K0 K)) :=
    bcGL_injective (algebraMap ↥K0 K) (algebraMap ↥K0 K).injective
  simp [f4FixedImageEquiv,
    Subgroup.coe_equivMapOfInjective_apply, MulEquiv.subgroupCongr_symm_apply]

public theorem bcGL_f4FixedImageEquiv_apply
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K)
    (x : ↥(f4FixedImageGroup sigma)) :
    bcGL (τ := Tag.F4) (algebraMap ↥(fixSubfield sigma) K)
        (f4FixedImageEquiv (K := K) sigma x) =
      (x : ModGL Tag.F4 K) := by
  classical
  let K0 : Subfield K := fixSubfield sigma
  let H0 : Subgroup (ModGL Tag.F4 ↥K0) := adjointGroup Tag.F4 K0
  let H : Subgroup (ModGL Tag.F4 K) :=
    H0.map (bcGL (τ := Tag.F4) (algebraMap ↥K0 K))
  have hbcGLinj : Function.Injective
      (bcGL (τ := Tag.F4) (algebraMap ↥K0 K)) :=
    bcGL_injective (algebraMap ↥K0 K) (algebraMap ↥K0 K).injective
  let eMap : ↥H ≃* ↥H0 :=
    (Subgroup.equivMapOfInjective H0
      (bcGL (τ := Tag.F4) (algebraMap ↥K0 K)) hbcGLinj).symm
  let eCast : ↥(f4FixedImageGroup sigma) ≃* ↥H :=
    MulEquiv.subgroupCongr (f4FixedImageGroup_eq_map (K := K) sigma)
  have h := (Subgroup.equivMapOfInjective H0
      (bcGL (τ := Tag.F4) (algebraMap ↥K0 K)) hbcGLinj).apply_symm_apply (eCast x)
  change bcGL (τ := Tag.F4) (algebraMap ↥K0 K) (eMap (eCast x)) =
    (x : ModGL Tag.F4 K)
  exact congrArg Subtype.val h


end ActualAutomorphismFixedImage

section FiniteNormLang

open CFSG.GroupTheory CFSG.StandardType.F4ExplicitPos.LangPosition
open CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.F4NativeNormalForm

variable {K : Type} [Field K] [Finite K] [CharP K 2]

set_option maxHeartbeats 1000000 in
theorem f4_finite_norm_one_lang (d : ℕ) (hd : 1 ≤ d) (hcard : Nat.card K = 2 ^ (5 * d))
    (y : adjointGroup Tag.F4 K)
    (hnorm : ((List.range 5).map fun i =>
      ((f4FrobTwist (K := K) d)^[i]) y).prod = 1) :
    ∃ z : adjointGroup Tag.F4 K,
      (z⁻¹ : ModGL Tag.F4 K) * entrywiseFrobGL Tag.F4 K 2 d (z : ModGL Tag.F4 K) =
        (y : ModGL Tag.F4 K) := by
  classical
  let Ω := AlgebraicClosure K
  have : IsAlgClosed Ω := inferInstance
  have : CharP Ω 2 := inferInstance

  let j : adjointGroup Tag.F4 K →* adjointGroup Tag.F4 Ω :=
    ((bcGL (algebraMap K Ω)).comp (adjointGroup Tag.F4 K).subtype).codRestrict
      (adjointGroup Tag.F4 Ω) fun g => bcGL_mem_adjointGroup (algebraMap K Ω) g.2

  have hj : ∀ g, (j g : ModGL Tag.F4 Ω) = bcGL (algebraMap K Ω) (g : ModGL Tag.F4 K) := fun _ => rfl

  have hbc : ∀ g : ModGL Tag.F4 K,
      bcGL (algebraMap K Ω) (entrywiseFrobGL Tag.F4 K 2 d g) =
        entrywiseFrobGL Tag.F4 Ω 2 d (bcGL (algebraMap K Ω) g) := by
    intro g
    have h1K : entrywiseFrobGL Tag.F4 K 2 d g = bcGL (iterateFrobenius K 2 d) g := by
      simp only [entrywiseFrobGL, bcGL, bcEndHom_eq_entrywiseHom]
    have h1Ω : entrywiseFrobGL Tag.F4 Ω 2 d (bcGL (algebraMap K Ω) g) =
        bcGL (iterateFrobenius Ω 2 d) (bcGL (algebraMap K Ω) g) := by
      simp only [entrywiseFrobGL, bcGL, bcEndHom_eq_entrywiseHom]
    rw [h1K, h1Ω, bcGL_comp, bcGL_comp]
    have hcomp : (algebraMap K Ω).comp (iterateFrobenius K 2 d) =
        (iterateFrobenius Ω 2 d).comp (algebraMap K Ω) := by
      ext c
      simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
    rw [hcomp]

  have hnat : ∀ g : adjointGroup Tag.F4 K,
      j ((f4FrobTwist (K := K) d) g) = (f4FrobTwist (K := Ω) d) (j g) := by
    intro g
    apply Subtype.ext
    exact hbc (g : ModGL Tag.F4 K)

  have hnat_iter : ∀ i : ℕ, ∀ g : adjointGroup Tag.F4 K,
      j (((f4FrobTwist (K := K) d)^[i]) g) = ((f4FrobTwist (K := Ω) d)^[i]) (j g) := by
    intro i
    induction i with
    | zero => intro g; simp
    | succ i ih =>
      intro g
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hnat, ih]

  have hnormΩ : ((List.range 5).map fun i =>
      ((f4FrobTwist (K := Ω) d)^[i]) (j y)).prod = 1 := by
    have h := congrArg j hnorm
    rw [MonoidHom.map_list_prod, map_one, List.map_map] at h
    change ((List.range 5).map fun i =>
      j (((f4FrobTwist (K := K) d)^[i]) y)).prod = 1 at h
    have hfun : (fun i : ℕ => j (((f4FrobTwist (K := K) d)^[i]) y)) =
        (fun i : ℕ => ((f4FrobTwist (K := Ω) d)^[i]) (j y)) :=
      funext fun i => hnat_iter i y
    rw [hfun] at h
    exact h

  obtain ⟨zΩ, hzΩadj, hzΩeq⟩ :=
    f4_exists_inv_mul_entrywise_frobenius (Ω := Ω) d hd ((j y).2)

  let zA : adjointGroup Tag.F4 Ω := ⟨zΩ, hzΩadj⟩

  have hzAeq : zA⁻¹ * (f4FrobTwist (K := Ω) d) zA = j y := by
    apply Subtype.ext
    change (zΩ⁻¹ : ModGL Tag.F4 Ω) * entrywiseFrobGL Tag.F4 Ω 2 d zΩ =
      (j y : ModGL Tag.F4 Ω)
    exact hzΩeq

  have hfix_adj : ((f4FrobTwist (K := Ω) d)^[5]) zA = zA := by
    have htelescope := lang_norm_telescope (f4FrobTwist (K := Ω) d) zA 5
    rw [hzAeq] at htelescope
    rw [hnormΩ] at htelescope
    have h1 : zA⁻¹ * ((f4FrobTwist (K := Ω) d)^[5]) zA = 1 := htelescope.symm
    exact (inv_mul_eq_one.mp h1).symm

  have hval_iter : ∀ n : ℕ, ((((f4FrobTwist (K := Ω) d)^[n]) zA : adjointGroup Tag.F4 Ω) :
      ModGL Tag.F4 Ω) = entrywiseFrobGL Tag.F4 Ω 2 (n * d) (zA : ModGL Tag.F4 Ω) := by
    intro n
    induction n with
    | zero => simp [entrywiseFrobGL_zero]
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change entrywiseFrobGL Tag.F4 Ω 2 d ((((f4FrobTwist (K := Ω) d)^[n]) zA :
        adjointGroup Tag.F4 Ω) : ModGL Tag.F4 Ω) =
        entrywiseFrobGL Tag.F4 Ω 2 ((n + 1) * d) (zA : ModGL Tag.F4 Ω)
      rw [ih, entrywiseFrobGL_frobGL, Nat.succ_mul]

  have hfix : entrywiseFrobGL Tag.F4 Ω 2 (5 * d) (zA : ModGL Tag.F4 Ω) =
      (zA : ModGL Tag.F4 Ω) := by
    have h5 := congrArg Subtype.val hfix_adj
    rw [hval_iter 5] at h5
    exact h5

  have hFr : ∀ c : Ω, iterateFrobenius Ω 2 (5 * d) c = c ^ Nat.card K := by
    intro c
    rw [iterateFrobenius_def, ← hcard]

  have hImage := f4_finite_field_fixed_eq_map (K := K) (Ω := Ω)
    (Fr := iterateFrobenius Ω 2 (5 * d)) hFr

  have hzΩInRHS : zΩ ∈ adjointGroup Tag.F4 Ω ⊓
      (Units.map (entrywiseHom (iterateFrobenius Ω 2 (5 * d)))).eqLocus
        (MonoidHom.id (ModGL Tag.F4 Ω)) := by
    refine Subgroup.mem_inf.2 ⟨hzΩadj, ?_⟩
    change Units.map (entrywiseHom (iterateFrobenius Ω 2 (5 * d))) zΩ = zΩ
    simpa only [entrywiseFrobGL] using hfix

  have hzΩInImage : zΩ ∈ (adjointGroup Tag.F4 K).map (bcGL (algebraMap K Ω)) := by
    rw [hImage]
    exact hzΩInRHS

  rw [Subgroup.mem_map] at hzΩInImage
  rcases hzΩInImage with ⟨zK, hzKadj, hzKeq⟩

  refine ⟨⟨zK, hzKadj⟩, ?_⟩
  have hinj : Function.Injective (bcGL (τ := Tag.F4) (algebraMap K Ω)) :=
    bcGL_injective (algebraMap K Ω) (algebraMap K Ω).injective

  apply hinj
  change bcGL (algebraMap K Ω) ((zK⁻¹ : ModGL Tag.F4 K) * entrywiseFrobGL Tag.F4 K 2 d zK) =
    bcGL (algebraMap K Ω) (y : ModGL Tag.F4 K)
  have hbc_zK := hbc zK
  calc
    bcGL (algebraMap K Ω) ((zK⁻¹ : ModGL Tag.F4 K) * entrywiseFrobGL Tag.F4 K 2 d zK)
        = bcGL (algebraMap K Ω) (zK⁻¹ : ModGL Tag.F4 K) *
            bcGL (algebraMap K Ω) (entrywiseFrobGL Tag.F4 K 2 d zK) := by rw [map_mul]
    _ = (bcGL (algebraMap K Ω) zK)⁻¹ *
          entrywiseFrobGL Tag.F4 Ω 2 d (bcGL (algebraMap K Ω) zK) := by rw [map_inv, hbc_zK]
    _ = (zΩ : ModGL Tag.F4 Ω)⁻¹ *
          entrywiseFrobGL Tag.F4 Ω 2 d (zΩ : ModGL Tag.F4 Ω) := by rw [hzKeq]
    _ = (j y : ModGL Tag.F4 Ω) := hzΩeq
    _ = bcGL (algebraMap K Ω) (y : ModGL Tag.F4 K) := rfl


theorem f4_noninner_fifth_power_field_conjugacy
    (α : MulAut (adjointGroup Tag.F4 K)) (hα5 : α ^ 5 = 1)
    (hnoninner : ∀ u : adjointGroup Tag.F4 K, α ≠ MulAut.conj u) :
    ∃ (σ : K ≃+* K) (z : adjointGroup Tag.F4 K),
      σ ≠ 1 ∧ σ ^ 5 = 1 ∧
      ∀ a : adjointGroup Tag.F4 K,
        (z * α a * z⁻¹ : ModGL Tag.F4 K) =
          Units.map (entrywiseHom σ.toRingHom) (z * a * z⁻¹ : ModGL Tag.F4 K) := by
  obtain ⟨d, j, r, σ, h, h', S, D, hd, hj, hj4, hr, hr4, hjr,
    hcard, hσne, hσ5, hSact, hDact, hαeq, hSrel, hnormS, hαr, hnorm'⟩ :=
    f4_field_form_coprime_power α hα5 hnoninner
  have hring : ((frobeniusEquiv K 2) ^ d).toRingHom = iterateFrobenius K 2 d := by
    ext c
    change ((frobeniusEquiv K 2) ^ d) c = iterateFrobenius K 2 d c
    rw [CFSG.LocalAnalysis.EvenBN.G2.frobeniusEquiv_pow_apply, iterateFrobenius_def]
  have hDrest : D.toMonoidHom = f4FrobTwist (K := K) d := by
    apply MonoidHom.ext
    intro a
    apply Subtype.ext
    change (D a : ModGL Tag.F4 K) = entrywiseFrobGL Tag.F4 K 2 d (a : ModGL Tag.F4 K)
    rw [hDact, hring]
  have hpow : ∀ i : ℕ, ∀ a : adjointGroup Tag.F4 K,
      (D ^ i) a = ((f4FrobTwist (K := K) d)^[i]) a := by
    intro i
    induction i with
    | zero => intro a; simp
    | succ i ih =>
      intro a
      rw [pow_succ', MulAut.mul_apply, Function.iterate_succ_apply', ← ih]
      exact congrArg (fun f : adjointGroup Tag.F4 K →* adjointGroup Tag.F4 K =>
        f ((D ^ i) a)) hDrest
  have hnorm : ((List.range 5).map fun i => ((f4FrobTwist (K := K) d)^[i]) h').prod = 1 := by
    have hfun : (fun i => ((f4FrobTwist (K := K) d)^[i]) h') =
        (fun i => (D ^ i) h') := funext fun i => (hpow i h').symm
    rw [hfun]
    exact hnorm'
  obtain ⟨z, hz⟩ := f4_finite_norm_one_lang d hd hcard h' hnorm
  have hzD : z⁻¹ * D z = h' := by
    apply Subtype.ext
    change (z⁻¹ : ModGL Tag.F4 K) * (D z : ModGL Tag.F4 K) = (h' : ModGL Tag.F4 K)
    rw [hDact, hring]
    exact hz
  have hT : MulAut.conj z * α ^ r * (MulAut.conj z)⁻¹ = D := by
    rw [hαr, ← hzD]
    apply MulEquiv.ext
    intro a
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply,
      map_mul, map_inv, mul_inv_rev, inv_inv]
    group
  have hconj := f4_conjugacy_of_coprime_power α hα5 S D j r hSrel hjr (MulAut.conj z) hT
  have hcomp : MulAut.conj z * α = S * MulAut.conj z :=
    (mul_inv_eq_iff_eq_mul).mp hconj
  refine ⟨σ, z, hσne, hσ5, ?_⟩
  intro a
  have ha := congrArg (fun T : MulAut (adjointGroup Tag.F4 K) => T a) hcomp
  have ha' : MulAut.conj z (α a) = S (MulAut.conj z a) := ha
  have hav := congrArg Subtype.val ha'
  rw [hSact] at hav
  simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hav

end FiniteNormLang

end CFSG.StandardType.F4ExplicitPos.FixedImage

end

end
