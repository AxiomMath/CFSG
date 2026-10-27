module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart10
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientPairDescentPart1

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Universal
open CFSG.StandardType.F4ExplicitPos.BaseChange
open CFSG.StandardType.F4ExplicitPos.RootBaseChange
open CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
open CFSG.StandardType.F4ExplicitPos.PairStabilizerNative
open CFSG.StandardType.F4ExplicitPos.FixedImage
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.StandardType
open CFSG.SeitzReduction
open scoped CFSG.ConvolutionPoints

namespace CFSG.StandardType.F4ExplicitPos.AmbientPairDescent
variable {τ : Tag} {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]

section F4Native
variable [IsAlgClosed Ω] [CharP Ω 2]

theorem f4_rootSubgroup_conj_weyl_transport
    (w : WeylGroup Tag.F4) {β α : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (hw : w • β = α) (g : ModGL Tag.F4 Ω) :
    (rootSubgroup Tag.F4 Ω α).map (MulAut.conj g).toMonoidHom =
      (rootSubgroup Tag.F4 Ω β).map
        (MulAut.conj (g * canonicalRep (coxeterSystem Tag.F4) Ω w)).toMonoidHom := by
  have hweyl := (canonical_weyl_root_transport Tag.F4 Ω).2.1 w β hβ
  rw [← hw]
  rw [show (MulAut.conj (g * canonicalRep (coxeterSystem Tag.F4) Ω w)).toMonoidHom =
      ((MulAut.conj g).toMonoidHom).comp
        ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) Ω w)).toMonoidHom) from by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group,
    ← Subgroup.map_map, hweyl]

theorem f4_rootSubgroup_conj_weyl_transport_neg
    (w : WeylGroup Tag.F4) {β α : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (hw : w • β = α) (g : ModGL Tag.F4 Ω) :
    (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj g).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-β)).map
        (MulAut.conj (g * canonicalRep (coxeterSystem Tag.F4) Ω w)).toMonoidHom := by
  have hw' : w • (-β) = -α := by rw [smul_neg, hw]
  exact f4_rootSubgroup_conj_weyl_transport (Ω := Ω) w (IsRoot.neg hβ) hw' g

theorem f4_fixed_conj_rootSubgroup
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (β : Fin Tag.F4.rank → ℤ) {u : ModGL Tag.F4 Ω}
    (hu : Units.map (entrywiseHom Fr) u = u) :
    ((rootSubgroup Tag.F4 Ω β).map (MulAut.conj u).toMonoidHom) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id (ModGL Tag.F4 Ω)) =
      ((rootSubgroup Tag.F4 K β).map (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
        (MulAut.conj u).toMonoidHom := by
  rw [map_conj_fixed_eq (Units.map (entrywiseHom Fr)) hu (rootSubgroup Tag.F4 Ω β),
    rootSubgroup_map_bcGL_eq_fixed (τ := Tag.F4) Fr hFr β]

theorem f4_fixed_frobenius_mem_map
    (f : ℕ) (hcard : Nat.card K = 2 ^ f)
    {u : ModGL Tag.F4 Ω}
    (huA : u ∈ adjointGroup Tag.F4 Ω)
    (hufix : entrywiseFrobGL Tag.F4 Ω 2 f u = u) :
    u ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) := by
  have hFr : ∀ c : Ω, iterateFrobenius Ω 2 f c = c ^ Nat.card K := by
    intro c; rw [iterateFrobenius_def, hcard]
  have heq := f4_finite_field_fixed_eq_map (K := K) (Ω := Ω)
    (iterateFrobenius Ω 2 f) hFr
  rw [heq]
  exact Subgroup.mem_inf.2 ⟨huA, hufix⟩

theorem finite_map_map_conj_rootSubgroup
    (β : Fin Tag.F4.rank → ℤ) (uΩ : ModGL Tag.F4 Ω) :
    Finite ↥(((rootSubgroup Tag.F4 K β).map
      (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
      (MulAut.conj uΩ).toMonoidHom) := by
  have : Finite ↥(rootSubgroup Tag.F4 K β) := inferInstance
  refine Finite.of_surjective
    (fun x : ↥(rootSubgroup Tag.F4 K β) =>
      (⟨(MulAut.conj uΩ) (bcGL (τ := Tag.F4) (algebraMap K Ω) x),
        Subgroup.mem_map.2 ⟨bcGL (τ := Tag.F4) (algebraMap K Ω) x,
          Subgroup.mem_map.2 ⟨x, x.2, rfl⟩, rfl⟩⟩ :
        ↥(((rootSubgroup Tag.F4 K β).map
          (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
          (MulAut.conj uΩ).toMonoidHom))) ?_
  rintro ⟨z, hz⟩
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hw
  exact ⟨⟨x, hx⟩, rfl⟩

theorem f4_long_pair_finite_endpoint
    (f : ℕ) (hf : 1 ≤ f) (hcard : Nat.card K = 2 ^ f)
    {g : ModGL Tag.F4 Ω} (hgA : g ∈ adjointGroup Tag.F4 Ω)
    (hstabplus : (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map (MulAut.conj g).toMonoidHom)
    (hstabminus : (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map (MulAut.conj g).toMonoidHom)
    {P Pm : Subgroup (ModGL Tag.F4 Ω)}
    (hPle : P ≤ (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map
      (MulAut.conj g).toMonoidHom)
    (hPmle : Pm ≤ (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map
      (MulAut.conj g).toMonoidHom)
    (hPfix : ∀ x ∈ P, entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hPmfix : ∀ x ∈ Pm, entrywiseFrobGL Tag.F4 Ω 2 f x = x)
    (hPcard : Nat.card P = Nat.card K)
    (hPmcard : Nat.card Pm = Nat.card K) :
    ∃ uK : adjointGroup Tag.F4 K,
      P = ((rootSubgroup Tag.F4 K (highRoot Tag.F4)).map
            (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
            (MulAut.conj (bcGL (τ := Tag.F4) (algebraMap K Ω)
              (uK : ModGL Tag.F4 K))).toMonoidHom ∧
      Pm = ((rootSubgroup Tag.F4 K (-highRoot Tag.F4)).map
            (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
            (MulAut.conj (bcGL (τ := Tag.F4) (algebraMap K Ω)
              (uK : ModGL Tag.F4 K))).toMonoidHom := by
  obtain ⟨uΩ, huΩA, huΩfix, hplusU, hminusU⟩ :=
    f4_long_pair_descent f hf hgA hstabplus hstabminus
  have hFr : ∀ c : Ω, iterateFrobenius Ω 2 f c = c ^ Nat.card K := by
    intro c; rw [iterateFrobenius_def, hcard]
  obtain ⟨uK0, huK0A, huK0⟩ := Subgroup.mem_map.1
    (f4_fixed_frobenius_mem_map (K := K) (Ω := Ω) f hcard huΩA huΩfix)
  refine ⟨⟨uK0, huK0A⟩, ?_, ?_⟩
  · rw [huK0]
    have hPleU : P ≤ (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map
        (MulAut.conj uΩ).toMonoidHom := by rw [hplusU]; exact hPle
    have : Finite ↥(((rootSubgroup Tag.F4 K (highRoot Tag.F4)).map
        (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
        (MulAut.conj uΩ).toMonoidHom) :=
      finite_map_map_conj_rootSubgroup (K := K) (Ω := Ω) (highRoot Tag.F4) uΩ
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hxP
      have hxU := hPleU hxP
      have hxfix : x ∈ (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))).eqLocus
          (MonoidHom.id (ModGL Tag.F4 Ω)) := hPfix x hxP
      have hx : x ∈ ((rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map
          (MulAut.conj uΩ).toMonoidHom) ⊓
          (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))).eqLocus
            (MonoidHom.id (ModGL Tag.F4 Ω)) := ⟨hxU, hxfix⟩
      rw [f4_fixed_conj_rootSubgroup (K := K) (Ω := Ω) (iterateFrobenius Ω 2 f) hFr
        (highRoot Tag.F4) huΩfix] at hx
      exact hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj uΩ).injective,
        Subgroup.card_map_of_injective (bcGL_injective (τ := Tag.F4) (algebraMap K Ω)
          (FaithfulSMul.algebraMap_injective K Ω)),
        card_rootSubgroup]
      exact le_of_eq hPcard.symm
  · rw [huK0]
    have hPmleU : Pm ≤ (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map
        (MulAut.conj uΩ).toMonoidHom := by rw [hminusU]; exact hPmle
    have : Finite ↥(((rootSubgroup Tag.F4 K (-highRoot Tag.F4)).map
        (bcGL (τ := Tag.F4) (algebraMap K Ω))).map
        (MulAut.conj uΩ).toMonoidHom) :=
      finite_map_map_conj_rootSubgroup (K := K) (Ω := Ω) (-highRoot Tag.F4) uΩ
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hxP
      have hxU := hPmleU hxP
      have hxfix : x ∈ (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))).eqLocus
          (MonoidHom.id (ModGL Tag.F4 Ω)) := hPmfix x hxP
      have hx : x ∈ ((rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map
          (MulAut.conj uΩ).toMonoidHom) ⊓
          (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))).eqLocus
            (MonoidHom.id (ModGL Tag.F4 Ω)) := ⟨hxU, hxfix⟩
      rw [f4_fixed_conj_rootSubgroup (K := K) (Ω := Ω) (iterateFrobenius Ω 2 f) hFr
        (-highRoot Tag.F4) huΩfix] at hx
      exact hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj uΩ).injective,
        Subgroup.card_map_of_injective (bcGL_injective (τ := Tag.F4) (algebraMap K Ω)
          (FaithfulSMul.algebraMap_injective K Ω)),
        card_rootSubgroup]
      exact le_of_eq hPmcard.symm

end F4Native

section PairLiftAdapter

variable {X : Type} [Group X]

noncomputable def etaG0
    (f : ℕ) [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X) (G0 : Subgroup X)
    (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥) :
    G0 →* ModGL Tag.F4 Ω :=
  (adjointGroup Tag.F4 Ω).subtype.comp
    ((jF4 (K := GaloisField 2 f) (L := Ω)).comp
      (psiEquiv ψ G0 hG0 hker hcenter).symm.toMonoidHom)

theorem etaG0_apply
    (f : ℕ) [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥) (y : G0) :
    etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter y =
      ((jF4 (K := GaloisField 2 f) (L := Ω)
        ((psiEquiv ψ G0 hG0 hker hcenter).symm y)) : ModGL Tag.F4 Ω) :=
  rfl

theorem f4_rootGroup_map_subtype
    (f : ℕ) (β : Fin Tag.F4.rank → ℤ)
    (hβ : IsRoot Tag.F4 β) :
    ((f4Datum (GaloisField 2 f)).rootGroup β).map
        (adjointGroup Tag.F4 (GaloisField 2 f)).subtype =
      rootSubgroup Tag.F4 (GaloisField 2 f) β := by
  change (rootGroup (rootOperatorFamily Tag.F4) (GaloisField 2 f) β).map
      (adjointGroup Tag.F4 (GaloisField 2 f)).subtype =
    rootSubgroup Tag.F4 (GaloisField 2 f) β
  rw [rootGroup_of_isRoot_no117 (F := rootOperatorFamily Tag.F4) hβ,
    ← RootOperatorFamily.subgroupOf_rootSubgroup_eq (F := rootOperatorFamily Tag.F4)
      (GaloisField 2 f) ⟨β, hβ⟩,
    Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 (rootSubgroup_le_adjointGroup (τ := Tag.F4) β)]

theorem f4_g0_pairLift_adapter
    (n f : ℕ) [Algebra (GaloisField 2 f) Ω]
    (ψ : adjointGroup Tag.F4 (GaloisField 2 f) →* X)
    (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 (GaloisField 2 f)) = ⊥)
    (β : Fin Tag.F4.rank → ℤ) (hβ : IsRoot Tag.F4 β)
    {uΩ : ModGL Tag.F4 Ω}
    (huΩ : uΩ ∈ (adjointGroup Tag.F4 (GaloisField 2 f)).map
      (bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω)))
    (R Rm : Subgroup X) (hRJ : R ≤ G0) (hRmJ : Rm ≤ G0)
    (hR : (R.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter) =
      ((rootSubgroup Tag.F4 (GaloisField 2 f) β).map
        (bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω))).map
        (MulAut.conj uΩ).toMonoidHom)
    (hRm : (Rm.subgroupOf G0).map (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter) =
      ((rootSubgroup Tag.F4 (GaloisField 2 f) (-β)).map
        (bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω))).map
        (MulAut.conj uΩ).toMonoidHom) :
    ∃ u : (ggU .F4 n f).K,
      R = ggRootSub (ggU .F4 n f).D ψ β u ∧
      Rm = ggRootSub (ggU .F4 n f).D ψ (-β) u := by
  let M : LieUniversal :=
    ⟨adjointGroup Tag.F4 (GaloisField 2 f), f4Datum (GaloisField 2 f)⟩
  let ψ0 : M.K →* G0 :=
    { toFun := fun a => ⟨ψ a, hG0 ▸ MonoidHom.mem_range.2 ⟨a, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hψ0 : G0.subtype.comp ψ0 = ψ := by ext a; rfl
  let η : G0 →* ModGL Tag.F4 Ω := etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter
  have hη0 : Function.Injective η := by
    intro x y hxy
    have h1 : jF4 (K := GaloisField 2 f) (L := Ω)
        ((psiEquiv ψ G0 hG0 hker hcenter).symm x) =
        jF4 (K := GaloisField 2 f) (L := Ω)
          ((psiEquiv ψ G0 hG0 hker hcenter).symm y) := Subtype.ext hxy
    exact (psiEquiv ψ G0 hG0 hker hcenter).symm.injective (jF4_injective h1)
  have hsymm : ∀ a : M.K, (psiEquiv ψ G0 hG0 hker hcenter).symm (ψ0 a) = a := by
    intro a
    apply (psiEquiv ψ G0 hG0 hker hcenter).injective
    rw [MulEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [psiEquiv_apply]
    rfl
  have hcomp_pt : ∀ a : M.K, η (ψ0 a) =
      bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω)
        (a : ModGL Tag.F4 (GaloisField 2 f)) := by
    intro a
    show (etaG0 (Ω := Ω) f ψ G0 hG0 hker hcenter (ψ0 a) : ModGL Tag.F4 Ω) = _
    change ((jF4 (K := GaloisField 2 f) (L := Ω)
      ((psiEquiv ψ G0 hG0 hker hcenter).symm (ψ0 a)) : adjointGroup Tag.F4 Ω) :
        ModGL Tag.F4 Ω) = _
    rw [hsymm]
    exact jF4_apply a
  have hcomp : η.comp ψ0 = (bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω)).comp
      (adjointGroup Tag.F4 (GaloisField 2 f)).subtype :=
    MonoidHom.ext hcomp_pt
  have hv : uΩ ∈ (η.comp ψ0).range := by
    obtain ⟨uK, huKA, huK⟩ := Subgroup.mem_map.1 huΩ
    rw [hcomp]
    exact MonoidHom.mem_range.2 ⟨⟨uK, huKA⟩, huK⟩
  have hplus : (M.D.rootGroup β).map (η.comp ψ0) =
      (rootSubgroup Tag.F4 (GaloisField 2 f) β).map
        (bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω)) := by
    rw [hcomp, ← Subgroup.map_map, f4_rootGroup_map_subtype f β hβ]
  have hminus : (M.D.rootGroup (-β)).map (η.comp ψ0) =
      (rootSubgroup Tag.F4 (GaloisField 2 f) (-β)).map
        (bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω)) := by
    rw [hcomp, ← Subgroup.map_map, f4_rootGroup_map_subtype f (-β) (IsRoot.neg hβ)]
  obtain ⟨u, -, hRu, hRmu⟩ :=
    CFSG.StandardType.F4ExplicitPos.PairLift.exists_common_root_pair_lift M ψ0 η hη0 β
      ((rootSubgroup Tag.F4 (GaloisField 2 f) β).map
        (bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω)))
      ((rootSubgroup Tag.F4 (GaloisField 2 f) (-β)).map
        (bcGL (τ := Tag.F4) (algebraMap (GaloisField 2 f) Ω)))
      (R.subgroupOf G0) (Rm.subgroupOf G0) uΩ hv hplus hminus hR hRm
  refine ⟨u, ?_, ?_⟩
  · have hmap := congrArg (fun H : Subgroup G0 => H.map G0.subtype) hRu
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRJ, ggRootSub,
      Subgroup.map_map, hψ0] at hmap
    exact hmap
  · have hmap := congrArg (fun H : Subgroup G0 => H.map G0.subtype) hRmu
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRmJ, ggRootSub,
      Subgroup.map_map, hψ0] at hmap
    exact hmap

end PairLiftAdapter

end CFSG.StandardType.F4ExplicitPos.AmbientPairDescent

end

end
