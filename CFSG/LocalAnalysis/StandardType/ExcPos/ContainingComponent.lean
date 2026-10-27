module

public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.PeriodicPts.Lemmas
import CFSG.LieType.AlgebraicGroups.ToralTwistPinningGeneral
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus (componentOrbitLength)
open scoped Matrix

variable {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
  {χD : Multiplicative (Fin τ.rank → ℤ) →* M} {χe : Multiplicative (Fin τ.rank → ℤ) →* M'}

@[expose] def containingComponent (hker : kernelRoots χD ⊆ kernelRoots χe) :
    KernelComponent χD → KernelComponent χe :=
  Quotient.map (fun α => ⟨α.1, hker α.2⟩) fun _ _ h =>
    Quotient.exact (OddToralOrdinary.mk_eq_mk_of_kernelRoots_subset hker (Quotient.sound h))

@[simp] theorem containingComponent_mk (hker : kernelRoots χD ⊆ kernelRoots χe)
    (α : kernelRoots χD) :
    containingComponent hker ⟦α⟧ = ⟦⟨α.1, hker α.2⟩⟧ :=
  rfl

theorem kernelRoots_finite {χ : Multiplicative (Fin τ.rank → ℤ) →* M} :
    (kernelRoots χ).Finite := by
  have hroot : {v : Fin τ.rank → ℤ | IsRoot τ v} =
      (fun p : WeylGroup τ × Fin τ.rank => p.1 • Pi.single p.2 (1 : ℤ)) '' Set.univ := by
    ext v
    rw [Set.mem_image]
    constructor
    · intro hv
      obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hv
      exact ⟨(w, j), Set.mem_univ _, hwj⟩
    · rintro ⟨⟨w, j⟩, -, rfl⟩
      exact isRoot_iff_exists_smul_single.2 ⟨w, j, rfl⟩
  have hfin : ({v : Fin τ.rank → ℤ | IsRoot τ v}).Finite := by
    rw [hroot]
    exact Set.finite_univ.image _
  exact hfin.subset fun v hv => hv.1

theorem componentRoots_subset_containingComponent (hker : kernelRoots χD ⊆ kernelRoots χe)
    (i : KernelComponent χD) :
    componentRoots χD i ⊆ componentRoots χe (containingComponent hker i) := by
  rintro α ⟨h, rfl⟩
  exact ⟨hker h, rfl⟩

theorem eq_containingComponent_of_mem (hker : kernelRoots χD ⊆ kernelRoots χe)
    {i : KernelComponent χD} {j : KernelComponent χe} {α : Fin τ.rank → ℤ}
    (hαi : α ∈ componentRoots χD i) (hαj : α ∈ componentRoots χe j) :
    j = containingComponent hker i := by
  obtain ⟨hαD, hi⟩ := hαi
  obtain ⟨hαe, hj⟩ := hαj
  rw [← hj, ← hi, containingComponent_mk]

theorem mk_apply_eq_of_mk_eq {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : Set.MapsTo ρ (kernelRoots χ) (kernelRoots χ))
    (hform : ∀ α β, iform (ρ α) (ρ β) = iform α β) {x y : kernelRoots χ}
    (hxy : (⟦x⟧ : KernelComponent χ) = ⟦y⟧) :
    (⟦⟨ρ x, hρ x.2⟩⟧ : KernelComponent χ) = ⟦⟨ρ y, hρ y.2⟩⟧ := by
  let r : kernelRoots χ → kernelRoots χ → Prop := fun a b =>
    (a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (b : Fin τ.rank → ℤ)) ≠ 0
  have hrel : ∀ a b : kernelRoots χ, r a b →
      r ⟨ρ a, hρ a.2⟩ ⟨ρ b, hρ b.2⟩ := by
    intro a b h
    change (a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ
      (b : Fin τ.rank → ℤ)) ≠ 0 at h
    change (ρ a : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ
      (ρ b : Fin τ.rank → ℤ)) ≠ 0
    rw [dotProduct_mulVec_eq_iform] at h ⊢
    exact fun h0 => h (by rw [← hform]; exact h0)
  have hresp : ∀ a b : kernelRoots χ, r a b →
      (⟦⟨ρ a, hρ a.2⟩⟧ : KernelComponent χ) = ⟦⟨ρ b, hρ b.2⟩⟧ :=
    fun a b hab => Quotient.sound (Relation.EqvGen.rel _ _ (hrel a b hab))
  have h := congrArg
    (Quot.lift (fun a : kernelRoots χ => (⟦⟨ρ a, hρ a.2⟩⟧ : KernelComponent χ)) hresp)
    (Quot.eqvGen_sound (r := r) (Quotient.exact hxy))
  simpa using h

theorem exists_image_componentRoots {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : Set.MapsTo ρ (kernelRoots χ) (kernelRoots χ))
    (hform : ∀ α β, iform (ρ α) (ρ β) = iform α β) (i : KernelComponent χ) :
    ∃ i₂ : KernelComponent χ, ρ '' componentRoots χ i = componentRoots χ i₂ := by
  have hfin : (kernelRoots χ).Finite := kernelRoots_finite
  have hmaps : Set.MapsTo (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
      (kernelRoots χ) (kernelRoots χ) := hρ
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 ρ.injective.injOn
  have hsymm : ∀ δ ∈ kernelRoots χ, ρ.symm δ ∈ kernelRoots χ := by
    intro δ hδ
    obtain ⟨γ, hγ, rfl⟩ := hbij.surjOn hδ
    simpa using hγ
  have hform' : ∀ α β, iform (ρ.symm α) (ρ.symm β) = iform α β := by
    intro α β
    simpa only [Equiv.apply_symm_apply] using (hform (ρ.symm α) (ρ.symm β)).symm
  let σ : kernelRoots χ → kernelRoots χ := fun γ => ⟨ρ γ, hρ (x := γ) γ.2⟩
  obtain ⟨γ₀, rfl⟩ := Quotient.exists_rep i
  refine ⟨⟦σ γ₀⟧, ?_⟩
  ext δ
  constructor
  · rintro ⟨γ, ⟨hγ, hγi⟩, rfl⟩
    refine ⟨hρ (x := γ) hγ, ?_⟩
    exact mk_apply_eq_of_mk_eq hρ hform hγi
  · rintro ⟨hδ, hδi⟩
    refine ⟨ρ.symm δ, ⟨hsymm δ hδ, ?_⟩, by simp⟩
    have h2 := mk_apply_eq_of_mk_eq (ρ := ρ.symm) (hρ := hsymm) hform' hδi
    have h3 : (⟨ρ.symm (σ γ₀), hsymm (σ γ₀) (σ γ₀).2⟩ : kernelRoots χ) = γ₀ :=
      Subtype.ext (by simp [σ])
    rwa [h3] at h2

theorem containingComponent_equivariant (hker : kernelRoots χD ⊆ kernelRoots χe)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρe : Set.MapsTo ρ (kernelRoots χe) (kernelRoots χe))
    (hform : ∀ α β, iform (ρ α) (ρ β) = iform α β) {i i₂ : KernelComponent χD}
    (h : ρ '' componentRoots χD i = componentRoots χD i₂) :
    ρ '' componentRoots χe (containingComponent hker i) =
      componentRoots χe (containingComponent hker i₂) := by
  obtain ⟨j₂, hj₂⟩ := exists_image_componentRoots hρe hform (containingComponent hker i)
  obtain ⟨α, rfl⟩ := Quotient.exists_rep i
  have hαD : (α : Fin τ.rank → ℤ) ∈ componentRoots χD ⟦α⟧ := ⟨α.2, rfl⟩
  have hαe : (α : Fin τ.rank → ℤ) ∈
      componentRoots χe (containingComponent hker ⟦α⟧) :=
    componentRoots_subset_containingComponent hker ⟦α⟧ hαD
  have hραD : ρ (α : Fin τ.rank → ℤ) ∈ componentRoots χD i₂ := by
    rw [← h]
    exact ⟨α, hαD, rfl⟩
  have hραe : ρ (α : Fin τ.rank → ℤ) ∈ componentRoots χe j₂ := by
    rw [← hj₂]
    exact ⟨α, hαe, rfl⟩
  rw [hj₂, eq_containingComponent_of_mem hker hραD hραe]

theorem componentOrbitLength_eq_minimalPeriod (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) :
    componentOrbitLength ρ Ψ = Function.minimalPeriod (Set.image ρ) Ψ := by
  rw [componentOrbitLength, Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq, Function.IsPeriodicPt, Function.IsFixedPt, Set.image_iterate_eq]

theorem componentOrbitLength_componentRoots_pos {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : Set.MapsTo ρ (kernelRoots χ) (kernelRoots χ))
    (i : KernelComponent χ) : 0 < componentOrbitLength ρ (componentRoots χ i) := by
  rw [componentOrbitLength_eq_minimalPeriod]
  apply Function.minimalPeriod_pos_of_mem_periodicPts
  have hfin : (kernelRoots χ).Finite := kernelRoots_finite
  obtain ⟨d, hd, hfix⟩ :=
    CFSG.LieType.AlgebraicGroups.exists_iterate_eq_of_mapsTo hfin hρ ρ.injective.injOn
  refine ⟨d, by omega, ?_⟩
  rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Set.image_iterate_eq]
  ext δ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [hfix γ hγ.1]
    exact hγ
  · intro hδ
    exact ⟨δ, hδ, hfix δ hδ.1⟩

theorem componentOrbitLength_containingComponent_dvd (hker : kernelRoots χD ⊆ kernelRoots χe)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρe : Set.MapsTo ρ (kernelRoots χe) (kernelRoots χe))
    (hform : ∀ α β, iform (ρ α) (ρ β) = iform α β) (i : KernelComponent χD) :
    componentOrbitLength ρ (componentRoots χe (containingComponent hker i)) ∣
      componentOrbitLength ρ (componentRoots χD i) := by
  have hperD : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ
      (componentRoots χD i)] '' componentRoots χD i = componentRoots χD i := by
    have h := Function.isPeriodicPt_minimalPeriod (Set.image ρ) (componentRoots χD i)
    rw [← componentOrbitLength_eq_minimalPeriod] at h
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Set.image_iterate_eq] at h
    exact h
  have hperb : (ρ ^ componentOrbitLength ρ (componentRoots χD i) :
      Equiv.Perm (Fin τ.rank → ℤ)) '' componentRoots χD i = componentRoots χD i := by
    rwa [Equiv.Perm.coe_pow]
  have hformb : ∀ n : ℕ, ∀ α β, iform ((ρ ^ n) α) ((ρ ^ n) β) = iform α β := by
    intro n
    induction n with
    | zero => intro α β; simp
    | succ n ih =>
      intro α β
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hform, ih]
  have hρeb : Set.MapsTo (ρ ^ componentOrbitLength ρ (componentRoots χD i))
      (kernelRoots χe) (kernelRoots χe) := Set.MapsTo.perm_pow hρe _
  have heq : (ρ ^ componentOrbitLength ρ (componentRoots χD i) :
      Equiv.Perm (Fin τ.rank → ℤ)) ''
      componentRoots χe (containingComponent hker i) =
      componentRoots χe (containingComponent hker i) :=
    containingComponent_equivariant hker hρeb
      (hformb (componentOrbitLength ρ (componentRoots χD i))) hperb
  have hperE : Function.IsPeriodicPt (Set.image ρ)
      (componentOrbitLength ρ (componentRoots χD i))
      (componentRoots χe (containingComponent hker i)) := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Set.image_iterate_eq]
    simpa only [Equiv.Perm.coe_pow] using heq
  rw [componentOrbitLength_eq_minimalPeriod ρ
    (componentRoots χe (containingComponent hker i))]
  exact hperE.minimalPeriod_dvd

theorem componentOrbitLength_containingComponent_eq_one (hker : kernelRoots χD ⊆ kernelRoots χe)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρe : Set.MapsTo ρ (kernelRoots χe) (kernelRoots χe))
    (hform : ∀ α β, iform (ρ α) (ρ β) = iform α β) {i : KernelComponent χD}
    (hi : componentOrbitLength ρ (componentRoots χD i) = 1) :
    componentOrbitLength ρ (componentRoots χe (containingComponent hker i)) = 1 :=
  Nat.dvd_one.mp (hi ▸ componentOrbitLength_containingComponent_dvd hker hρe hform i)

end CFSG.StandardType.LieKnownR2.ExcPos
