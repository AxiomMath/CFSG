module

public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeDefs
public import CFSG.RankThree.PartOne.KE6.EqpOpp
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.LangNormalizerInvolutionTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.StandardType.N2E6Native

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KE6 CFSG.LieType.Steinberg.Adjoint
open scoped Matrix

@[expose] def e6NativeC : List (Fin Tag.E6.rank → ℤ) := List.ofFn e6NativeGamma

theorem e6NativeC_check : e6NativeC.Nodup ∧
    (∀ β ∈ e6NativeC, List.ofFn β ∈ Tag.E6.artifactRoots) ∧
    (∀ β ∈ e6NativeC, ∀ β' ∈ e6NativeC, β ≠ β' → iform β β' = 0) ∧
    ∀ l ∈ Tag.E6.artifactRoots,
      e6NativeC.foldr (fun β v => v - corootPair β v • β) (toVec Tag.E6.rank l) =
        e6NativeW (toVec Tag.E6.rank l) := by
  decide +kernel

section Certs


theorem e6NativeC_isRoot {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ e6NativeC) : IsRoot Tag.E6 β := by
  rw [isRoot_iff_mem_artifactRoots]
  exact e6NativeC_check.2.1 β hβ

theorem e6NativeGamma_isRoot (i : Fin 4) : IsRoot Tag.E6 (e6NativeGamma i) :=
  e6NativeC_isRoot (List.mem_ofFn' _ _ |>.mpr ⟨i, rfl⟩)

@[expose] def nativeW : WeylGroup Tag.E6 := (e6NativeC.map rootReflection).prod

theorem nativeW_smul_root {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    nativeW • γ = e6NativeW γ := by
  rw [nativeW, prod_rootReflection_smul (fun β hβ => e6NativeC_isRoot hβ)]
  have h := e6NativeC_check.2.2.2 (List.ofFn γ) (isRoot_iff_mem_artifactRoots.mp hγ)
  rwa [toVec_ofFn] at h

section Field

variable {Ω : Type} [Field Ω]

theorem e6NativeC_pairwise_commute (M N : SL2 Ω) :
    e6NativeC.Pairwise fun β γ => Commute (rootSL2 Tag.E6 Ω β M) (rootSL2 Tag.E6 Ω γ N) := by
  refine List.Pairwise.imp_of_mem (fun {β γ} hβ hγ hne => ?_) e6NativeC_check.1
  have h0 := e6NativeC_check.2.2.1 β hβ γ hγ hne
  exact rootSL2_commute_of_orth (e6NativeC_isRoot hβ) (e6NativeC_isRoot hγ) h0
    (e6_not_isRoot_add_of_orth (e6NativeC_isRoot hβ) (e6NativeC_isRoot hγ) h0)
    (e6_not_isRoot_sub_of_orth (e6NativeC_isRoot hβ) (e6NativeC_isRoot hγ) h0) M N

@[expose] def nativeCas (M : SL2 Ω) : ModGL Tag.E6 Ω :=
  (e6NativeC.map fun β => rootSL2 Tag.E6 Ω β M).prod

theorem nativeCas_mul (M N : SL2 Ω) : nativeCas (M * N) = nativeCas M * nativeCas N := by
  unfold nativeCas
  simp only [map_mul]
  exact list_prod_map_mul_of_pairwise _ _ _ (e6NativeC_pairwise_commute N M)

theorem nativeCas_mem_adjointGroup (M : SL2 Ω) : nativeCas M ∈ adjointGroup Tag.E6 Ω := by
  unfold nativeCas
  refine (adjointGroup Tag.E6 Ω).list_prod_mem fun x hx => ?_
  obtain ⟨β, -, rfl⟩ := List.mem_map.mp hx
  exact rootSL2_mem_adjointGroup β M

theorem canonicalRep_nativeW [CharP Ω 2] :
    canonicalRep (coxeterSystem Tag.E6) Ω nativeW = nativeCas (eqpW : SL2 Ω) := by
  have h := map_list_prod (eqpCanonicalHom Ω) (e6NativeC.map rootReflection)
  change eqpCanonicalHom Ω _ = _
  rw [nativeW, h, List.map_map]
  unfold nativeCas
  congr 1
  exact List.map_congr_left fun β hβ => canonicalRep_rootReflection_eq (e6NativeC_isRoot hβ)

end Field

section Frob

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem entrywiseFrobGL_rootSL2 (f : ℕ) {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (M : SL2 Ω) :
    entrywiseFrobGL Tag.E6 Ω 2 f (rootSL2 Tag.E6 Ω β M) =
      rootSL2 Tag.E6 Ω β (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (entrywiseFrobGL Tag.E6 Ω 2 f).comp (rootSL2 Tag.E6 Ω β) =
      (rootSL2 Tag.E6 Ω β).comp (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f)) := by
    refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := Ω)) fun g hg => ?_
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change entrywiseFrobGL Tag.E6 Ω 2 f (rootSL2 Tag.E6 Ω β (uSL c)) =
        rootSL2 Tag.E6 Ω β (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (uSL c))
      rw [rootSL2_uSL_of_charTwo hβ, entrywiseFrobGL_pinnedX, map_uSL,
        rootSL2_uSL_of_charTwo hβ]
    · change entrywiseFrobGL Tag.E6 Ω 2 f (rootSL2 Tag.E6 Ω β (vSL c)) =
        rootSL2 Tag.E6 Ω β (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) (vSL c))
      rw [rootSL2_vSL_of_charTwo hβ, entrywiseFrobGL_pinnedX, map_vSL,
        rootSL2_vSL_of_charTwo hβ]
  exact DFunLike.congr_fun h M

theorem entrywiseFrobGL_nativeCas (f : ℕ) (M : SL2 Ω) :
    entrywiseFrobGL Tag.E6 Ω 2 f (nativeCas M) =
      nativeCas (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) M) := by
  unfold nativeCas
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun β hβ => entrywiseFrobGL_rootSL2 f (e6NativeC_isRoot hβ) M

theorem entrywiseFrobGL_nativeCas_eq (f : ℕ) {A : SL2 Ω}
    (hA : A⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 f) A = eqpW) :
    entrywiseFrobGL Tag.E6 Ω 2 f (nativeCas A) =
      nativeCas A * canonicalRep (coxeterSystem Tag.E6) Ω nativeW := by
  rw [entrywiseFrobGL_nativeCas, canonicalRep_nativeW, ← nativeCas_mul, ← hA,
    mul_inv_cancel_left]

end Frob

end Certs

end CFSG.StandardType.N2E6Native

end
