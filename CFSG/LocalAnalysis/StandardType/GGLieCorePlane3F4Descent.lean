module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGLangAlgebraicRestriction
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShSetupE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.Sporadic.Schreier.Fi22Schreier
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E8D4Family

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

attribute [local instance] ZMod.algebra algebraicClosure.isAlgClosure IsAlgClosure.isAlgClosed

private theorem l10lG1_baseChangeGL_rootDiagUnit
    {R S : Type} [Field R] [Field S] (f : R →+* S) {τ : Tag} (a : Fin τ.rank → Rˣ) :
    baseChangeGL f (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map f.toMonoidHom (a i) := by
  refine Units.ext (end_ext_single fun b => ?_)
  rw [baseChangeGL_apply_single]
  change Finsupp.mapRange f f.map_zero (rootDiag a (Finsupp.single b 1)) =
    rootDiag (fun i => Units.map f.toMonoidHom (a i)) (Finsupp.single b 1)
  rcases b with i | α
  · rw [rootDiag_single_inl, rootDiag_single_inl, Finsupp.mapRange_single, map_one]
  · rw [rootDiag_single_inr, rootDiag_single_inr, Finsupp.smul_single_one,
      Finsupp.smul_single_one, Finsupp.mapRange_single]
    congr 1
    simp [map_prod, map_zpow₀]

private theorem l10lG1_map_baseChangeGL_rootSpan_le
    {τ : Tag} {K L : Type} [Field K] [Field L] (ι : K →+* L) (T : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ K T).map (baseChangeGL ι) ≤ rootSpan τ L T := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun γ hγ => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  show baseChangeGL ι (pinnedX τ K γ c) ∈ rootSpan τ L T
  rw [baseChangeGL_pinnedX]
  have hmem : pinnedX τ L γ (ι c) ∈ rootSubgroup τ L γ :=
    Subgroup.subset_closure ⟨ι c, rfl⟩
  exact (le_iSup₂_of_le (f := fun α (_ : α ∈ T) => rootSubgroup τ L α) γ hγ le_rfl) hmem

private theorem l10lG1_mk_eq_mk_of_kernelRoots_subset
    {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ ⊆ kernelRoots χ')
    {x y : kernelRoots χ} (hxy : (⟦x⟧ : KernelComponent χ) = ⟦y⟧) :
    (⟦⟨x.1, h x.2⟩⟧ : KernelComponent χ') = ⟦⟨y.1, h y.2⟩⟧ := by
  have hr : Relation.EqvGen _ x y := Quotient.exact hxy
  clear hxy
  apply Quotient.sound
  change Relation.EqvGen _ _ _
  induction hr with
  | rel a b hab => exact Relation.EqvGen.rel _ _ hab
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

private theorem l10lG1_componentRoots_eq_of_kernelRoots_eq
    {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ = kernelRoots χ')
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) (hα' : α ∈ kernelRoots χ') :
    componentRoots χ ⟦⟨α, hα⟩⟧ = componentRoots χ' ⟦⟨α, hα'⟩⟧ := by
  ext β
  constructor
  · rintro ⟨hβ, hβα⟩
    exact ⟨h.le hβ,
      l10lG1_mk_eq_mk_of_kernelRoots_subset h.le (x := ⟨β, hβ⟩) (y := ⟨α, hα⟩) hβα⟩
  · rintro ⟨hβ, hβα⟩
    exact ⟨h.ge hβ,
      l10lG1_mk_eq_mk_of_kernelRoots_subset h.ge (x := ⟨β, hβ⟩) (y := ⟨α, hα'⟩) hβα⟩

private theorem l10lG1_exists_componentRoots_eq
    {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ = kernelRoots χ') (i : KernelComponent χ) :
    ∃ j : KernelComponent χ', componentRoots χ i = componentRoots χ' j := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  have hx' : (x : Fin τ.rank → ℤ) ∈ kernelRoots χ' := h ▸ x.2
  exact ⟨⟦⟨x, hx'⟩⟧, l10lG1_componentRoots_eq_of_kernelRoots_eq h x.2 hx'⟩

private theorem l10lG1_exists_units_of_pow_three
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin Tag.F4.rank → Lˣ} (h3 : ∀ j, a j ^ 3 = 1) :
    ∃ b : Fin Tag.F4.rank → (algebraicClosure (ZMod 2) L)ˣ,
      ∀ j, Units.map (algebraMap (algebraicClosure (ZMod 2) L) L).toMonoidHom (b j) = a j := by
  have halg : ∀ j, (a j : L) ∈ algebraicClosure (ZMod 2) L := by
    intro j
    have h4u : a j ^ 4 = a j := by
      have h : a j ^ 4 = a j ^ 3 * a j := by
        show a j ^ (3 + 1) = a j ^ 3 * a j
        rw [pow_succ]
      rw [h, h3 j, one_mul]
    have h4 : (a j : L) ^ 4 = (a j : L) := by
      rw [← Units.val_pow_eq_pow_val, h4u]
    exact mem_algebraicClosure_iff.2 ⟨Polynomial.X ^ 4 - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod 2) (by norm_num), by simp [h4]⟩
  refine ⟨fun j => Units.mk0 (⟨a j, halg j⟩ : algebraicClosure (ZMod 2) L) ?_, ?_⟩
  · intro h
    exact (a j).ne_zero (congrArg Subtype.val h)
  · intro j
    exact Units.ext rfl

private theorem l10lG1_spanModel_mulEquiv
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (S0 : LangSetup Tag.F4 (algebraicClosure (ZMod 2) L) 5) (S : LangSetup Tag.F4 L 5)
    (hmodel : S0.D.model.map (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) =
      S.D.model)
    (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    Nonempty (↥(rootSpan Tag.F4 (algebraicClosure (ZMod 2) L) Ψ ⊓ S0.D.model) ≃*
      ↥(rootSpan Tag.F4 L Ψ ⊓ S.D.model)) := by
  classical
  have hS : ((rootSpan Tag.F4 (algebraicClosure (ZMod 2) L) Ψ) ⊓ S0.D.model).map
        (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) =
      (rootSpan Tag.F4 L Ψ) ⊓ S.D.model := by
    apply le_antisymm
    · calc ((rootSpan Tag.F4 (algebraicClosure (ZMod 2) L) Ψ) ⊓ S0.D.model).map
            (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L))
          ≤ (rootSpan Tag.F4 (algebraicClosure (ZMod 2) L) Ψ).map
              (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) ⊓
            S0.D.model.map (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) :=
            Subgroup.map_inf_le _ _ _
        _ ≤ (rootSpan Tag.F4 L Ψ) ⊓ S.D.model :=
            inf_le_inf (l10lG1_map_baseChangeGL_rootSpan_le
              (algebraMap (algebraicClosure (ZMod 2) L) L) Ψ) (le_of_eq hmodel)
    · intro g hg
      obtain ⟨hgL, hgG⟩ := hg
      rw [← hmodel] at hgG
      change g ∈ Subgroup.map (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L))
        S0.D.model at hgG
      rw [Subgroup.mem_map] at hgG
      obtain ⟨g0, hg0, rfl⟩ := hgG
      refine Subgroup.mem_map.mpr ⟨g0, ⟨?_, hg0⟩, rfl⟩
      exact CFSG.LieType.AlgebraicGroups.mem_rootSpan_of_baseChangeGL_mem_algClosed
        (algebraMap (algebraicClosure (ZMod 2) L) L) Ψ hgL
  exact ⟨(Subgroup.equivMapOfInjective _
      (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L))
      (baseChangeGL_injective (algebraMap (algebraicClosure (ZMod 2) L) L))).trans
    (MulEquiv.subgroupCongr hS)⟩

theorem ggLieF4Plane_descent
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    (i : KernelComponent (jointChar a₁ a₂)) :
    ∃ (b₁ b₂ : Fin Tag.F4.rank → (algebraicClosure (ZMod 2) L)ˣ)
      (D₀ : LangDatum Tag.F4 (algebraicClosure (ZMod 2) L))
      (j : KernelComponent (jointChar b₁ b₂)),
      D₀.q = D.q ∧ GGLieF4PlaneHyp D₀ ρ b₁ b₂ ∧
      componentRoots (jointChar b₁ b₂) j = componentRoots (jointChar a₁ a₂) i ∧
      Nonempty (↥(rootSpan Tag.F4 (algebraicClosure (ZMod 2) L)
          (componentRoots (jointChar b₁ b₂) j) ⊓ D₀.model) ≃*
        ↥(rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model)) := by
  classical
  obtain ⟨f, hf, hq⟩ := h.hq
  obtain ⟨S, rfl, rfl⟩ := exists_langSetup_of_datum D ρ h.frob h.finite hf hq
  obtain ⟨S0, hq0, hρ0, hAlg0, hn0, hg00, hΦ0, hmodel0, hΓ0, htorus0, hE0⟩ :=
    S.exists_algebraicRestriction
  have : CharP (algebraicClosure (ZMod 2) L) 2 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 2) (algebraicClosure (ZMod 2) L)) 2 (by norm_num)
  obtain ⟨b₁, hb₁⟩ := l10lG1_exists_units_of_pow_three (a := a₁)
    (pow_eq_one_of_rootDiagUnit_pow h.pow₁)
  obtain ⟨b₂, hb₂⟩ := l10lG1_exists_units_of_pow_three (a := a₂)
    (pow_eq_one_of_rootDiagUnit_pow h.pow₂)
  have hbc₁ : baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)
      (rootDiagUnit Tag.F4 b₁) = rootDiagUnit Tag.F4 a₁ := by
    rw [l10lG1_baseChangeGL_rootDiagUnit, funext hb₁]
  have hbc₂ : baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)
      (rootDiagUnit Tag.F4 b₂) = rootDiagUnit Tag.F4 a₂ := by
    rw [l10lG1_baseChangeGL_rootDiagUnit, funext hb₂]
  have hmem₁ : rootDiagUnit Tag.F4 b₁ ∈ S0.D.torus := by
    have h : baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)
        (rootDiagUnit Tag.F4 b₁) ∈ S.D.torus := by
      rw [hbc₁]; exact h.mem₁
    rw [← htorus0, Subgroup.mem_map] at h
    obtain ⟨g, hg, hgmap⟩ := h
    exact (baseChangeGL_injective (algebraMap (algebraicClosure (ZMod 2) L) L) hgmap) ▸ hg
  have hmem₂ : rootDiagUnit Tag.F4 b₂ ∈ S0.D.torus := by
    have h : baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)
        (rootDiagUnit Tag.F4 b₂) ∈ S.D.torus := by
      rw [hbc₂]; exact h.mem₂
    rw [← htorus0, Subgroup.mem_map] at h
    obtain ⟨g, hg, hgmap⟩ := h
    exact (baseChangeGL_injective (algebraMap (algebraicClosure (ZMod 2) L) L) hgmap) ▸ hg
  have hpow₁ : rootDiagUnit Tag.F4 b₁ ^ 3 = 1 := by
    apply baseChangeGL_injective (algebraMap (algebraicClosure (ZMod 2) L) L)
    rw [map_pow, hbc₁, h.pow₁, map_one]
  have hpow₂ : rootDiagUnit Tag.F4 b₂ ^ 3 = 1 := by
    apply baseChangeGL_injective (algebraMap (algebraicClosure (ZMod 2) L) L)
    rw [map_pow, hbc₂, h.pow₂, map_one]
  have hcard : Nat.card ↥(Subgroup.closure {rootDiagUnit Tag.F4 b₁, rootDiagUnit Tag.F4 b₂}) =
      3 ^ 2 := by
    have hmap : (Subgroup.closure {rootDiagUnit Tag.F4 b₁, rootDiagUnit Tag.F4 b₂}).map
          (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L)) =
        Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [Set.image_pair, hbc₁, hbc₂]
    have hcard' : Nat.card
          ↥(Subgroup.closure {rootDiagUnit Tag.F4 b₁, rootDiagUnit Tag.F4 b₂}) =
        Nat.card ↥((Subgroup.closure {rootDiagUnit Tag.F4 b₁, rootDiagUnit Tag.F4 b₂}).map
          (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L))) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _
        (baseChangeGL (algebraMap (algebraicClosure (ZMod 2) L) L))
        (baseChangeGL_injective (algebraMap (algebraicClosure (ZMod 2) L) L))).toEquiv
    rw [hmap, h.card] at hcard'
    exact hcard'
  have hkr : kernelRoots (jointChar b₁ b₂) = kernelRoots (jointChar a₁ a₂) := by
    ext γ
    constructor
    · rintro ⟨hroot, hχ⟩
      have hb1 : rootChar b₁ γ = 1 := by
        simpa [jointChar, rootCharHom] using congrArg Prod.fst hχ
      have hb2 : rootChar b₂ γ = 1 := by
        simpa [jointChar, rootCharHom] using congrArg Prod.snd hχ
      refine ⟨hroot, ?_⟩
      have ha1 : rootChar a₁ γ = 1 := by
        have h := rootChar_map_tuple (algebraMap (algebraicClosure (ZMod 2) L) L) b₁ γ
        rw [funext hb₁] at h
        rw [h, hb1, map_one]
      have ha2 : rootChar a₂ γ = 1 := by
        have h := rootChar_map_tuple (algebraMap (algebraicClosure (ZMod 2) L) L) b₂ γ
        rw [funext hb₂] at h
        rw [h, hb2, map_one]
      simpa [jointChar, rootCharHom] using (Prod.mk_eq_one.2 ⟨ha1, ha2⟩)
    · rintro ⟨hroot, hχ⟩
      have ha1 : rootChar a₁ γ = 1 := by
        simpa [jointChar, rootCharHom] using congrArg Prod.fst hχ
      have ha2 : rootChar a₂ γ = 1 := by
        simpa [jointChar, rootCharHom] using congrArg Prod.snd hχ
      refine ⟨hroot, ?_⟩
      have hb1 : rootChar b₁ γ = 1 := by
        have h := rootChar_map_tuple (algebraMap (algebraicClosure (ZMod 2) L) L) b₁ γ
        rw [funext hb₁] at h
        apply Units.map_injective (f := (algebraMap (algebraicClosure (ZMod 2) L) L).toMonoidHom)
          (algebraMap (algebraicClosure (ZMod 2) L) L).injective
        rw [map_one, ← h, ha1]
      have hb2 : rootChar b₂ γ = 1 := by
        have h := rootChar_map_tuple (algebraMap (algebraicClosure (ZMod 2) L) L) b₂ γ
        rw [funext hb₂] at h
        apply Units.map_injective (f := (algebraMap (algebraicClosure (ZMod 2) L) L).toMonoidHom)
          (algebraMap (algebraicClosure (ZMod 2) L) L).injective
        rw [map_one, ← h, ha2]
      simpa [jointChar, rootCharHom] using (Prod.mk_eq_one.2 ⟨hb1, hb2⟩)
  obtain ⟨j, hj⟩ := l10lG1_exists_componentRoots_eq hkr.symm i
  have hHyp : GGLieF4PlaneHyp S0.D S.ρ b₁ b₂ :=
    { frob := hρ0 ▸ S0.frob
      finite := S0.finite
      hq := ⟨f, hf, hq0.trans hq⟩
      mem₁ := hmem₁
      mem₂ := hmem₂
      pow₁ := hpow₁
      pow₂ := hpow₂
      card := hcard }
  refine ⟨b₁, b₂, S0.D, j, hq0, hHyp, hj.symm, ?_⟩
  rw [hj.symm]
  exact l10lG1_spanModel_mulEquiv S0 S hmodel0 _

end CFSG.StandardType.LieCore
