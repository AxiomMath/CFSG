module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Quasisimple
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FixedImage
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CTNative

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem roots_eq_setOf_isRoot_native (hA : TauCeti.IsFiniteType τ.cartan) :
    CFSG.LieType.RootSystem.roots hA ∅ = {γ | IsRoot τ γ} := by
  ext γ
  constructor
  · rintro (⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩)
    · obtain ⟨ω, rfl⟩ :=
        (CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem.wordProd_surjective w
      induction ω with
      | nil => simpa using IsRoot.basis i
      | cons j ω ih =>
        rw [CoxeterSystem.wordProd_cons, CFSG.LieType.RootSystem.weylAction_mul_apply,
          CFSG.LieType.RootSystem.weylAction_simple, CFSG.LieType.RootSystem.reflection_apply]
        exact IsRoot.reflect j ih
    · exact absurd hi (Set.notMem_empty i)
  · intro h
    induction h with
    | basis j => exact Or.inl ⟨1, j, by simp⟩
    | @reflect i v _ ih =>
      rcases ih with ⟨w, j, hw⟩ | ⟨w, j, hj, -⟩
      · refine Or.inl ⟨(CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem.simple i * w,
          j, ?_⟩
        rw [CFSG.LieType.RootSystem.weylAction_mul_apply, ← hw,
          CFSG.LieType.RootSystem.weylAction_simple, CFSG.LieType.RootSystem.reflection_apply]
        rfl
      · exact absurd hj (Set.notMem_empty j)

theorem weylAction_simple_eq_reflect_native (hA : TauCeti.IsFiniteType τ.cartan)
    (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    CFSG.LieType.RootSystem.weylAction hA
        ((CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem.simple i) γ =
      reflect τ i γ := by
  rw [CFSG.LieType.RootSystem.weylAction_simple, CFSG.LieType.RootSystem.reflection_apply]
  rfl

theorem eq_single_or_neg_of_support_native
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {i : Fin τ.rank} (h : ∀ k, k ≠ i → γ k = 0) :
    γ = Pi.single i 1 ∨ γ = -Pi.single i 1 := by
  have e : γ = γ i • Pi.single i 1 := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [h k hk, Pi.single_eq_of_ne hk]
  rcases hγ.eq_one_or_neg_one_of_eq_smul e with h1 | h1
  · left
    rw [e, h1, one_smul]
  · right
    rw [e, h1, neg_one_smul]

theorem adjDatum_roots_native
    (F : RootOperatorFamily τ) (K : Type) [Field K] :
    (adjDatum F K).roots = {γ | IsRoot τ γ} :=
  roots_eq_setOf_isRoot_native _

theorem mem_adjDatum_roots_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} :
    γ ∈ (adjDatum F K).roots ↔ IsRoot τ γ := by
  rw [adjDatum_roots_native F K]
  rfl

theorem xPar_of_isRoot_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : K) :
    xPar F γ c = F.eltElement ⟨γ, h⟩ c := by
  classical
  exact dite_eq_left h

theorem rootGroup_of_isRoot_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) :
    rootGroup F K γ = F.rootSubgroup K ⟨γ, h⟩ := by
  classical
  exact dite_eq_left h

theorem xPar_mem_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : K) :
    xPar F γ c ∈ rootGroup F K γ := by
  rw [xPar_of_isRoot_native h, rootGroup_of_isRoot_native h]
  exact F.eltElement_mem_rootSubgroup _ c

theorem exists_of_mem_rootGroup_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ)
    {g : adjointGroup τ K} (hg : g ∈ rootGroup F K γ) :
    ∃ c : K, g = F.eltElement ⟨γ, h⟩ c := by
  rw [rootGroup_of_isRoot_native h] at hg
  obtain ⟨c, rfl⟩ := F.mem_rootSubgroup.1 hg
  exact ⟨c, rfl⟩

theorem mem_rootGroup_iff_native
    {F : RootOperatorFamily τ} {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ)
    (g : adjointGroup τ K) : g ∈ rootGroup F K γ ↔ ∃ c, xPar F γ c = g := by
  constructor
  · intro hg
    obtain ⟨c, rfl⟩ := exists_of_mem_rootGroup_native h hg
    exact ⟨c, xPar_of_isRoot_native h c⟩
  · rintro ⟨c, rfl⟩
    exact xPar_mem_native h c

theorem xPar_simple_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (c : K) :
    xPar F (Pi.single i 1) c = F.eltElement (simpleRoot τ i) c :=
  xPar_of_isRoot_native (isRoot_single τ i) c

theorem xPar_neg_simple_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (c : K) :
    xPar F (-Pi.single i 1) c = F.eltElement (-simpleRoot τ i) c :=
  xPar_of_isRoot_native (isRoot_neg_single τ i) c

theorem endHom_eltElement_native
    {F : RootOperatorFamily τ} (α : Root τ) (c : K) :
    endHom K (F.eltElement α c) = F.elt K α c :=
  rfl

theorem xPar_single_mem_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (c : K) :
    xPar F (Pi.single i 1) c ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup F K) i :=
  Subgroup.mem_sup_left (xPar_mem_native (isRoot_single τ i) c)

theorem xPar_neg_single_mem_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (c : K) :
    xPar F (-Pi.single i 1) c ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup F K) i :=
  Subgroup.mem_sup_right (xPar_mem_native (isRoot_neg_single τ i) c)

theorem xyx_eq_weylElt_native
    {F : RootOperatorFamily τ} {i : Fin τ.rank} {t : K} (ht : t ≠ 0) :
    F.eltElement (simpleRoot τ i) t * F.eltElement (-simpleRoot τ i) (-t⁻¹) *
        F.eltElement (simpleRoot τ i) t =
      ⟨weylElt τ K i (Units.mk0 t ht), weylElt_mem_adjointGroup i _⟩ := by
  refine endHom_injective ?_
  rw [map_mul, map_mul, endHom_xElt, endHom_yElt, endHom_apply, coe_weylElt]
  simp

theorem weylElement_xPar_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (t : Kˣ) :
    CFSG.LieType.Steinberg.weylElement (xPar F) i t =
      torusElement τ K i t * CFSG.LieType.Chevalley.weylElement τ K i := by
  rw [CFSG.LieType.Steinberg.weylElement, xPar_simple_native, xPar_neg_simple_native]
  have h := xyx_eq_weylElt_native (F := F) (i := i) (Units.ne_zero t)
  rw [Units.val_inv_eq_inv_val, h]
  refine Subtype.ext ?_
  change weylElt τ K i (Units.mk0 (t : K) _) = torusElt τ K i t * weylElt τ K i 1
  rw [torusElt_mul_weylElt_one, Units.mk0_val]

theorem steinbergWeyl_mem_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (t : Kˣ) :
    CFSG.LieType.Steinberg.weylElement (xPar F) i t ∈
      CFSG.LieType.CurtisTits.rankOne (rootGroup F K) i :=
  mul_mem (mul_mem (xPar_single_mem_rankOne_native i _) (xPar_neg_single_mem_rankOne_native i _))
    (xPar_single_mem_rankOne_native i _)

theorem torusElement_one_eq_native
    (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.torusElement τ K i 1 = 1 :=
  Subtype.ext (torusElt_one i)

theorem weylElement_eq_xPar_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.weylElement τ K i =
      CFSG.LieType.Steinberg.weylElement (xPar F) i 1 := by
  rw [weylElement_xPar_native, torusElement_one_eq_native, one_mul]

theorem weylElement_mem_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) :
    CFSG.LieType.Chevalley.weylElement τ K i ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup F K)
        i := by
  rw [weylElement_eq_xPar_native (F := F) i]
  exact steinbergWeyl_mem_rankOne_native (F := F) i 1

theorem torus_le_rankOne_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) :
    torus K i ≤ CFSG.LieType.CurtisTits.rankOne (rootGroup F K) i := by
  rintro _ ⟨t, rfl⟩
  have h : torusHom K i t = CFSG.LieType.Steinberg.weylElement (xPar F) i t *
      (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ :=
    eq_mul_inv_of_mul_eq (weylElement_xPar_native (F := F) i t).symm
  rw [h]
  exact mul_mem (steinbergWeyl_mem_rankOne_native (F := F) i t)
    (inv_mem (weylElement_mem_rankOne_native (F := F) i))

theorem weylElement_conj_mem_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {x : adjointGroup τ K} (hx : x ∈ rootGroup F K γ) :
    CFSG.LieType.Chevalley.weylElement τ K i * x *
        (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ ∈ rootGroup F K (reflect τ i γ) := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_native hγ x).1 hx
  rw [xPar_of_isRoot_native hγ, F.weylElement_mul_eltElement_mul_inv,
    show simple τ i • (⟨γ, hγ⟩ : Root τ) = ⟨reflect τ i γ, IsRoot.reflect i hγ⟩ from
      Subtype.ext (simple_smul i γ), ← xPar_of_isRoot_native (IsRoot.reflect i hγ)]
  exact xPar_mem_native (IsRoot.reflect i hγ) _

theorem torusElement_conj_mem_native
    {F : RootOperatorFamily τ} (i : Fin τ.rank) (t : Kˣ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {x : adjointGroup τ K} (hx : x ∈ rootGroup F K γ) :
    torusElement τ K i t * x * (torusElement τ K i t)⁻¹ ∈ rootGroup F K γ := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_native hγ x).1 hx
  rw [xPar_of_isRoot_native hγ, F.torusElement_mul_eltElement_mul_inv,
    ← xPar_of_isRoot_native hγ]
  exact xPar_mem_native hγ _

theorem weylElement_braid_native
    (hA : TauCeti.IsFiniteType τ.cartan) (i j : Fin τ.rank) :
    ((CoxeterSystem.braidWord (CFSG.LieType.RootSystem.coxeterMatrix hA) i j).map
        (CFSG.LieType.Chevalley.weylElement τ K)).prod =
      ((CoxeterSystem.braidWord (CFSG.LieType.RootSystem.coxeterMatrix hA) j i).map
        (CFSG.LieType.Chevalley.weylElement τ K)).prod := by
  refine Subtype.ext ?_
  rw [← Subgroup.coe_subtype, map_list_prod, map_list_prod, List.map_map, List.map_map]
  exact prod_braidWord_weylElt hA K i j

theorem iSup_rootGroup_eq_top_native
    {F : RootOperatorFamily τ} :
    ⨆ γ ∈ {γ | IsRoot τ γ}, rootGroup F K γ = ⊤ := by
  set S : Set (ModGL τ K) := {g | ∃ (i : Fin τ.rank) (c : K),
    (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
      (g : Module.End K (RootModule τ K)) = yOp τ K i c}
  have hcl : Subgroup.closure (((↑) : adjointGroup τ K → ModGL τ K) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← hcl, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · have e : g = xPar F (Pi.single i 1) c := endHom_injective (by
      rw [xPar_simple_native, endHom_eltElement_native, F.elt_simple]
      exact hg)
    rw [e]
    exact Subgroup.mem_iSup_of_mem (Pi.single i 1)
      (Subgroup.mem_iSup_of_mem (isRoot_single τ i) (xPar_mem_native (isRoot_single τ i) c))
  · have e : g = xPar F (-Pi.single i 1) c := endHom_injective (by
      rw [xPar_neg_simple_native, endHom_eltElement_native, F.elt_neg_simple]
      exact hg)
    rw [e]
    exact Subgroup.mem_iSup_of_mem (-Pi.single i 1)
      (Subgroup.mem_iSup_of_mem (isRoot_neg_single τ i) (xPar_mem_native (isRoot_neg_single τ i) c))

theorem adjDatum_isCTGroupDatum_native
    (F : RootOperatorFamily τ) (K : Type) [Field K] :
    CFSG.LieType.CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (adjDatum F K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (adjDatum F K).isFiniteType) (adjDatum F K).roots
      (adjDatum F K).rootGroup (CFSG.LieType.Chevalley.weylElement τ K) (torus K) where
  n_mem i := weylElement_mem_rankOne_native (F := F) i
  conj_mem i γ hγ x hx := by
    change _ ∈ rootGroup F K _
    rw [weylAction_simple_eq_reflect_native (isFiniteType_cartan τ)]
    exact weylElement_conj_mem_native (F := F) i (mem_adjDatum_roots_native.1 hγ) hx
  braid i j := weylElement_braid_native (isFiniteType_cartan τ) i j
  H_le i := torus_le_rankOne_native (F := F) i
  sq_mem i := ⟨-1, Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact (weylElt_one_sq τ K i).symm)⟩
  H_conj_mem l γ hγ h hh x hx := by
    obtain ⟨t, rfl⟩ := hh
    exact torusElement_conj_mem_native (F := F) l t (mem_adjDatum_roots_native.1 hγ) hx
  conj_H_mem j l h hh := by
    obtain ⟨t, rfl⟩ := hh
    have e : CFSG.LieType.Chevalley.weylElement τ K j * torusHom K l t *
        (CFSG.LieType.Chevalley.weylElement τ K j)⁻¹ =
          torusHom K l t * torusHom K j (t ^ (-τ.cartan l j)) :=
      Subtype.ext (weylElt_one_mul_torusElt_mul_inv τ K j l t)
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right ⟨t, rfl⟩) (Subgroup.mem_sup_left ⟨_, rfl⟩)
  le_rankOne i γ hγ hsupp := by
    rcases eq_single_or_neg_of_support_native (mem_adjDatum_roots_native.1 hγ) hsupp with
      rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  iSup_eq_top := by
    rw [adjDatum_roots_native F K]
    exact iSup_rootGroup_eq_top_native (F := F)

theorem f4_isCTGroupDatum_native
    (K : Type) [Field K] :
    CFSG.LieType.CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (f4Datum K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (f4Datum K).isFiniteType) (f4Datum K).roots
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.weylElement .F4 K) (torus (τ := .F4) K) :=
  adjDatum_isCTGroupDatum_native (rootOperatorFamily .F4) K

end CFSG.StandardType.F4ExplicitPos.CTNative

public section

namespace CFSG.StandardType.F4ExplicitPos.CTNative

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem isQuasisimple_f4_native
    (k : Type) [Field k] [CharP k 2] [Finite k] :
    CFSG.IsQuasisimple ↥(adjointGroup .F4 k) :=
  Quasisimple.isQuasisimple_f4_native_of_ct k (f4_isCTGroupDatum_native k)

end CFSG.StandardType.F4ExplicitPos.CTNative

public noncomputable section
namespace CFSG.StandardType.F4ExplicitPos.CTNative
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.F4ExplicitPos.FixedImage
open CFSG.HardMathSupport.Solomon.Coordinator

public theorem f4FixedImageGroup_quasisimple
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K) :
    CFSG.IsQuasisimple ↥(f4FixedImageGroup sigma) := by
  classical
  let K0 : Subfield K := fixSubfield sigma
  let H0 : Subgroup (ModGL Tag.F4 ↥K0) := adjointGroup Tag.F4 K0
  let e : ↥(f4FixedImageGroup sigma) ≃* ↥H0 := f4FixedImageEquiv (K := K) sigma
  have hK0quasi : CFSG.IsQuasisimple ↥H0 :=
    CFSG.StandardType.F4ExplicitPos.CTNative.isQuasisimple_f4_native (k := ↥K0)
  exact hK0quasi.of_mulEquiv e

public theorem f4FixedImageGroup_perfect
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K) :
    Group.IsPerfect ↥(f4FixedImageGroup sigma) :=
  (f4FixedImageGroup_quasisimple (K := K) sigma).1

private noncomputable def psiAdjoint {Y : Type} [Group Y] {K : Type} [Field K]
    (psi : Y →* ModGL Tag.F4 K)
    (hpsi_range : psi.range = adjointGroup Tag.F4 K) :
    Y →* ↥(adjointGroup Tag.F4 K) :=
  { toFun := fun y => ⟨psi y, by
      have hy : psi y ∈ psi.range := ⟨y, rfl⟩
      rwa [hpsi_range] at hy⟩
    map_one' := Subtype.ext (map_one psi)
    map_mul' := fun y z => Subtype.ext (map_mul psi y z) }

section

private lemma psiAdjoint_surjective {Y : Type} [Group Y] {K : Type} [Field K]
    (psi : Y →* ModGL Tag.F4 K)
    (hpsi_range : psi.range = adjointGroup Tag.F4 K) :
    Function.Surjective (psiAdjoint psi hpsi_range) := by
  intro q
  have hq : (q : ModGL Tag.F4 K) ∈ psi.range := by
    rw [hpsi_range]
    exact q.2
  obtain ⟨y, hy⟩ := hq
  exact ⟨y, Subtype.ext hy⟩

private lemma psiAdjoint_ker_le {Y : Type} [Group Y] {K : Type} [Field K]
    (psi : Y →* ModGL Tag.F4 K)
    (hpsi_range : psi.range = adjointGroup Tag.F4 K)
    (hpsi_ker : psi.ker ≤ Subgroup.center Y) :
    (psiAdjoint psi hpsi_range).ker ≤ Subgroup.center Y := by
  have hker : (psiAdjoint psi hpsi_range).ker = psi.ker := by
    ext y
    constructor
    · intro h
      have h' : (psiAdjoint psi hpsi_range y : ModGL Tag.F4 K) = 1 :=
        congrArg (fun z : ↥(adjointGroup Tag.F4 K) => (z : ModGL Tag.F4 K)) h
      simpa [psiAdjoint] using h'
    · intro h
      exact Subtype.ext (by simpa [psiAdjoint] using h)
  rw [hker]
  exact hpsi_ker

end

public theorem fixedImage_map_eq
    {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K) (alpha : MulAut Y)
    (psi : Y →* ModGL Tag.F4 K)
    (hpsi_range : psi.range = adjointGroup Tag.F4 K)
    (hpsi_ker : psi.ker ≤ Subgroup.center Y)
    (hintertwine : ∀ y, psi (alpha y) =
      Units.map (entrywiseHom sigma.toRingHom) (psi y)) :
    (alpha.toMonoidHom.eqLocus (MonoidHom.id Y)).map psi =
      f4FixedImageGroup sigma := by
  classical
  let A : Subgroup (ModGL Tag.F4 K) := adjointGroup Tag.F4 K
  let X : Subgroup (ModGL Tag.F4 K) := f4FixedImageGroup sigma
  have hXperfect : Group.IsPerfect ↥X := by
    simpa [X] using f4FixedImageGroup_perfect (K := K) sigma
  have hpsi_rangeA : psi.range = A := hpsi_range
  let psiAd : Y →* ↥A := psiAdjoint psi hpsi_range
  have hkerAd : psiAd.ker ≤ Subgroup.center Y := by
    simpa [psiAd] using psiAdjoint_ker_le psi hpsi_range hpsi_ker
  have hsurjAd : Function.Surjective psiAd := by
    simpa [psiAd] using psiAdjoint_surjective psi hpsi_range
  let E : ModGL Tag.F4 K ≃* ModGL Tag.F4 K :=
    CFSG.ClassicalInvolution.Upgrade.modGLCongr Tag.F4 sigma
  have hE_apply (g : ModGL Tag.F4 K) :
      E g = Units.map (entrywiseHom sigma.toRingHom) g := rfl
  have hEA : A.map E.toMonoidHom = A := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have ha' : a ∈ psi.range := by rw [hpsi_rangeA]; exact ha
      obtain ⟨y, rfl⟩ := ha'
      rw [← hpsi_rangeA]
      refine ⟨alpha y, ?_⟩
      change psi (alpha y) = E (psi y)
      rw [hE_apply, hintertwine y]
    · intro a ha
      have ha' : a ∈ psi.range := by rw [hpsi_rangeA]; exact ha
      obtain ⟨y, rfl⟩ := ha'
      refine ⟨psi (alpha.symm y), ?_, ?_⟩
      · rw [← hpsi_rangeA]
        exact ⟨alpha.symm y, rfl⟩
      · change E (psi (alpha.symm y)) = psi y
        rw [hE_apply, ← hintertwine (alpha.symm y), alpha.apply_symm_apply]
  let beta : MulAut ↥A :=
    (E.subgroupMap A).trans (MulEquiv.subgroupCongr hEA)
  have hbeta_apply (q : ↥A) : (beta q : ModGL Tag.F4 K) = E q := rfl
  have hXA : X ≤ A := by
    change f4FixedImageGroup sigma ≤ adjointGroup Tag.F4 K
    exact inf_le_left
  have hfixBeta : fixSubgroup beta = X.subgroupOf A := by
    ext q
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf]
    constructor
    · intro hq
      have hq' : E q.1 = q.1 := by
        have := congrArg Subtype.val hq
        simpa [hbeta_apply] using this
      refine ⟨q.2, ?_⟩
      change Units.map (entrywiseHom sigma.toRingHom) q.1 = q.1
      rwa [← hE_apply q.1]
    · intro hq
      apply Subtype.ext
      change (beta q).1 = q.1
      rw [hbeta_apply, hE_apply]
      exact hq.2
  have hαβ : ∀ y, psiAd (alpha y) = beta (psiAd y) := by
    intro y
    apply Subtype.ext
    change psi (alpha y) = E (psi y)
    rw [hintertwine y, hE_apply]
  have hmapLe : (fixSubgroup alpha).map psiAd ≤ fixSubgroup beta :=
    map_fixSubgroup_le psiAd hkerAd alpha beta hαβ
  have hXAperfect : Group.IsPerfect ↥(X.subgroupOf A) := by
    have : Group.IsPerfect ↥X := hXperfect
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hXA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXA).symm.surjective
  have hXAcomm : ⁅X.subgroupOf A, X.subgroupOf A⁆ = X.subgroupOf A := by
    have : Group.IsPerfect ↥(X.subgroupOf A) := hXAperfect
    exact Subgroup.commutator_eq_self
  have hXAle : X.subgroupOf A ≤ (fixSubgroup alpha).map psiAd :=
    le_map_fixSubgroup_of_perfect psiAd hkerAd alpha beta hαβ hsurjAd
      (A := X.subgroupOf A) (by rw [hfixBeta]) hXAcomm
  have hmapEq : (fixSubgroup alpha).map psiAd = X.subgroupOf A :=
    le_antisymm (by rwa [hfixBeta] at hmapLe) hXAle
  have hfixedImage : (fixSubgroup alpha).map psi = X := by
    have hcomp : psi = A.subtype.comp psiAd := by
      ext y
      rfl
    calc
      (fixSubgroup alpha).map psi
          = (fixSubgroup alpha).map (A.subtype.comp psiAd) := by rw [hcomp]
      _ = ((fixSubgroup alpha).map psiAd).map A.subtype := by rw [← Subgroup.map_map]
      _ = (X.subgroupOf A).map A.subtype := by rw [hmapEq]
      _ = X := Subgroup.map_subgroupOf_eq_of_le hXA
  show (fixSubgroup alpha).map psi = X
  exact hfixedImage

public theorem exists_noncentral_fixed
    {Y : Type} [Group Y] [Finite Y]
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (sigma : K ≃+* K) (alpha : MulAut Y)
    (psi : Y →* ModGL Tag.F4 K)
    (hpsi_range : psi.range = adjointGroup Tag.F4 K)
    (hpsi_ker : psi.ker ≤ Subgroup.center Y)
    (hintertwine : ∀ y, psi (alpha y) =
      Units.map (entrywiseHom sigma.toRingHom) (psi y)) :
    ∃ z ∈ alpha.toMonoidHom.eqLocus (MonoidHom.id Y),
      z ∉ Subgroup.center Y := by
  classical
  let A : Subgroup (ModGL Tag.F4 K) := adjointGroup Tag.F4 K
  let X : Subgroup (ModGL Tag.F4 K) := f4FixedImageGroup sigma
  have hfixedImage : (alpha.toMonoidHom.eqLocus (MonoidHom.id Y)).map psi = X := by
    simpa [X] using fixedImage_map_eq sigma alpha psi hpsi_range hpsi_ker hintertwine
  have hXquasi : CFSG.IsQuasisimple ↥X := by
    simpa [X] using f4FixedImageGroup_quasisimple (K := K) sigma
  obtain ⟨a, b, hab⟩ : ∃ a b : ↥X, a * b ≠ b * a := by
    obtain ⟨-, -, u, v, huv⟩ := hXquasi
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨a, b, fun h => huv ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  let aA : ↥A := ⟨a.1, a.2.1⟩
  let bA : ↥A := ⟨b.1, b.2.1⟩
  have haA_nc : aA ∉ Subgroup.center ↥A := by
    intro hcenter
    apply hab
    apply Subtype.ext
    have h := Subgroup.mem_center_iff.mp hcenter bA
    exact (congrArg Subtype.val h).symm
  have hx : a.1 ∈ (alpha.toMonoidHom.eqLocus (MonoidHom.id Y)).map psi := by
    rw [hfixedImage]
    exact a.2
  obtain ⟨z, hz, hzx⟩ := hx
  refine ⟨z, hz, ?_⟩
  intro hzcenter
  let psiAd : Y →* ↥A := psiAdjoint psi hpsi_range
  have hsurjAd : Function.Surjective psiAd := by
    simpa [psiAd] using psiAdjoint_surjective psi hpsi_range
  have hzA_center : psiAd z ∈ Subgroup.center ↥A := by
    refine (Subgroup.map_center_le_center (f := psiAd) hsurjAd) ?_
    exact Subgroup.mem_map_of_mem psiAd hzcenter
  have hza : psiAd z = aA := by
    apply Subtype.ext
    change psi z = a.1
    exact hzx
  exact haA_nc (hza ▸ hzA_center)

end CFSG.StandardType.F4ExplicitPos.CTNative
end

end

end

end
