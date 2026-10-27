module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcToral
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
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
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.OrbitSelection

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

open CFSG.Assembly

open CFSG.LieType.Steinberg.Adjoint

open Matrix

open scoped commutatorElement

variable {τ : Tag} {L : Type} [Field L]

theorem orbit_eqvGen_map {X : Type*} {r : X → X → Prop} (f : X → X)
    (hf : ∀ x y, r x y → r (f x) (f y)) {x y : X} (h : Relation.EqvGen r x y) :
    Relation.EqvGen r (f x) (f y) := by
  induction h with
  | rel x y h => exact .rel _ _ (hf x y h)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

theorem orbit_eqvGen_equiv_iff {X : Type*} {r : X → X → Prop} (e : X ≃ X)
    (hr : ∀ x y, r (e x) (e y) ↔ r x y) (x y : X) :
    Relation.EqvGen r (e x) (e y) ↔ Relation.EqvGen r x y := by
  refine ⟨fun h => ?_, orbit_eqvGen_map e fun x y h => (hr x y).2 h⟩
  have := orbit_eqvGen_map e.symm
    (fun a b h => (hr (e.symm a) (e.symm b)).1 (by simpa using h)) h
  simpa using this

theorem orbit_kernelComponent_eq_iff {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (x y : kernelRoots χ) :
    (⟦x⟧ : KernelComponent χ) = ⟦y⟧ ↔ Relation.EqvGen
      (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y :=
  Quotient.eq (r := kernelRootSetoid χ)

theorem orbit_iform_iterate {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (k : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((ρ : (Fin τ.rank → ℤ) → _)^[k] x) ((ρ : (Fin τ.rank → ℤ) → _)^[k] y) = iform x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hform]

theorem orbit_iterate_mem_kernelRoots {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) : (ρ : (Fin τ.rank → ℤ) → _)^[k] γ ∈ kernelRoots χ := by
  induction k with
  | zero => exact hγ
  | succ k ih => rw [Function.iterate_succ_apply']; exact hker _ ih

theorem orbit_rationalRoots_subset_kernelRoots {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    rationalRoots ρ χ i ⊆ kernelRoots χ := by
  rintro _ ⟨k, δ, ⟨hδ, -⟩, rfl⟩
  exact orbit_iterate_mem_kernelRoots hker k hδ

theorem orbit_rationalRoots_closed {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ rationalRoots ρ χ i) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ kernelRoots χ)
    (h : (⟦⟨β, hβ⟩⟧ : KernelComponent χ) =
      ⟦⟨γ, orbit_rationalRoots_subset_kernelRoots hker i hγ⟩⟧) :
    β ∈ rationalRoots ρ χ i := by
  classical
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α h => h.1
  have : Finite (kernelRoots χ) := hfin.to_subtype
  let σ : kernelRoots χ → kernelRoots χ := fun x => ⟨ρ x, hker x x.2⟩
  have hσinj : Function.Injective σ := fun x y h =>
    Subtype.ext (ρ.injective (congrArg Subtype.val h))
  let e : Equiv.Perm (kernelRoots χ) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have he_iter : ∀ (k : ℕ) (x : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = (ρ : (Fin τ.rank → ℤ) → _)^[k] x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      show ρ (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = _
      rw [ih, Function.iterate_succ_apply']
  have hr : ∀ (k : ℕ) (x y : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) ⬝ᵥ
          (τ.symmetrizedCartan *ᵥ (((e ^ k) y : kernelRoots χ) : Fin τ.rank → ℤ)) ≠ 0 ↔
        (x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0 := by
    intro k x y
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, he_iter, he_iter,
      orbit_iform_iterate hform]
  obtain ⟨k, δ, ⟨hδ, hδi⟩, rfl⟩ := hγ
  set y : kernelRoots χ := (e ^ k)⁻¹ ⟨β, hβ⟩ with hy
  have hey : (e ^ k) y = ⟨β, hβ⟩ := by simp [hy]
  have hex : (e ^ k) ⟨δ, hδ⟩ =
      ⟨(ρ : (Fin τ.rank → ℤ) → _)^[k] δ, orbit_iterate_mem_kernelRoots hker k hδ⟩ :=
    Subtype.ext (he_iter k ⟨δ, hδ⟩)
  have hyx : (⟦y⟧ : KernelComponent χ) = ⟦⟨δ, hδ⟩⟧ := by
    rw [orbit_kernelComponent_eq_iff]
    refine (orbit_eqvGen_equiv_iff (e ^ k) (hr k) y ⟨δ, hδ⟩).1 ?_
    rw [hey, hex]
    exact (orbit_kernelComponent_eq_iff _ _).1 h
  refine ⟨k, y, ⟨y.2, hyx.trans hδi⟩, ?_⟩
  have := congrArg Subtype.val hey
  rw [he_iter] at this
  exact this.symm

theorem orbit_rationalRoots_mapsTo {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ} (i : KernelComponent χ) :
    Set.MapsTo (ρ : (Fin τ.rank → ℤ) → _) (rationalRoots ρ χ i) (rationalRoots ρ χ i) := by
  rintro _ ⟨k, δ, hδ, rfl⟩
  exact ⟨k + 1, δ, hδ, by rw [Function.iterate_succ_apply']⟩

theorem orbit_rationalRoots_of_apply_mem
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) {δ : Fin τ.rank → ℤ} (h : ρ δ ∈ rationalRoots ρ χ i) :
    δ ∈ rationalRoots ρ χ i := by
  have hfin : (rationalRoots ρ χ i).Finite :=
    ((finite_setOf_isRoot τ).subset fun α hα => hα.1 : (kernelRoots χ).Finite).subset
      (orbit_rationalRoots_subset_kernelRoots hker i)
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (orbit_rationalRoots_mapsTo i)).1
    ρ.injective.injOn
  obtain ⟨γ, hγ, hγδ⟩ := hbij.surjOn h
  exact ρ.injective hγδ ▸ hγ

theorem orbit_rationalRoots_of_iterate_mem
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) (n : ℕ) {δ : Fin τ.rank → ℤ}
    (h : (ρ : (Fin τ.rank → ℤ) → _)^[n] δ ∈ rationalRoots ρ χ i) :
    δ ∈ rationalRoots ρ χ i := by
  induction n generalizing δ with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact orbit_rationalRoots_of_apply_mem hker i (ih h)

theorem orbit_iterate_mem_rationalRoots {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (i : KernelComponent χ) (n : ℕ) {γ : Fin τ.rank → ℤ}
    (h : γ ∈ rationalRoots ρ χ i) : (ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ rationalRoots ρ χ i := by
  obtain ⟨k, δ, hδ, rfl⟩ := h
  exact ⟨n + k, δ, hδ, by rw [Function.iterate_add_apply]⟩

theorem orbit_rationalRoots_subset_of_mem_inter
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ rationalRoots ρ χ i) (hj : δ ∈ rationalRoots ρ χ j) :
    rationalRoots ρ χ j ⊆ rationalRoots ρ χ i := by
  obtain ⟨n, δ₂, ⟨hδ₂, hδ₂j⟩, rfl⟩ := hj
  have hδ₂i : δ₂ ∈ rationalRoots ρ χ i := orbit_rationalRoots_of_iterate_mem hker i n hi
  rintro _ ⟨l, ε₂, ⟨hε₂, hε₂j⟩, rfl⟩
  exact orbit_iterate_mem_rationalRoots i l
    (orbit_rationalRoots_closed hker hform i hδ₂i hε₂ (hε₂j.trans hδ₂j.symm))

theorem orbit_rationalRoots_eq_of_mem_inter
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ rationalRoots ρ χ i) (hj : δ ∈ rationalRoots ρ χ j) :
    rationalRoots ρ χ i = rationalRoots ρ χ j :=
  le_antisymm (orbit_rationalRoots_subset_of_mem_inter hker hform hj hi)
    (orbit_rationalRoots_subset_of_mem_inter hker hform hi hj)

theorem orbit_commute_rootSpan_rationalRoots
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    (hcomm : ∀ i j : KernelComponent χ, i ≠ j →
      ∀ u ∈ componentRootSpan L χ i, ∀ v ∈ componentRootSpan L χ j, Commute u v)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    (hij : rationalRoots ρ χ i ≠ rationalRoots ρ χ j) :
    ∀ x ∈ rootSpan τ L (rationalRoots ρ χ i), ∀ y ∈ rootSpan τ L (rationalRoots ρ χ j),
      Commute x y := by
  have hle : rootSpan τ L (rationalRoots ρ χ i) ≤
      Subgroup.centralizer (rootSpan τ L (rationalRoots ρ χ j) : Set (ModGL τ L)) := by
    refine iSup₂_le fun γ hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hγk := orbit_rationalRoots_subset_kernelRoots hker i hγ
    have hδk := orbit_rationalRoots_subset_kernelRoots hker j hδ
    have hne : (⟦⟨γ, hγk⟩⟧ : KernelComponent χ) ≠ ⟦⟨δ, hδk⟩⟧ := fun h =>
      hij (orbit_rationalRoots_eq_of_mem_inter hker hform
        (orbit_rationalRoots_closed hker hform i hγ hδk h.symm) hδ)
    exact (hcomm _ _ hne y (rootSubgroup_le_componentRootSpan (K := L) ⟨γ, hγk⟩ hy)
      x (rootSubgroup_le_componentRootSpan (K := L) ⟨δ, hδk⟩ hx)).eq.symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

theorem orbit_step_mem_rootSpan
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (D : LangDatum τ L) (hρ : FrobRootMap D ρ)
    {T : Set (Fin τ.rank → ℤ)} (hT : ∀ γ ∈ T, IsRoot τ γ)
    (hρT : Set.MapsTo (ρ : (Fin τ.rank → ℤ) → _) T T) {x : ModGL τ L}
    (hx : x ∈ rootSpan τ L T) : D.step x ∈ rootSpan τ L T := by
  have h1 : D.step x ∈ (rootSpan τ L T).map D.step := Subgroup.mem_map_of_mem _ hx
  have h2 : (rootSpan τ L T).map D.step =
      rootSpan τ L ((ρ : (Fin τ.rank → ℤ) → _) '' T) := by
    simp only [rootSpan, Subgroup.map_iSup]
    rw [iSup_image]
    exact iSup_congr fun γ => iSup_congr fun hγ => hρ.map_rootSubgroup γ (hT γ hγ)
  rw [h2] at h1
  exact rootSpan_mono hρT.image_subset h1

theorem comp_le_or_commutator_eq_bot {G : Type*} [Group G]
    {X K U : Subgroup G} [Finite ↥X] (hK : IsComponentOf K X) (hU : IsSubnormal U X) :
    K ≤ U ∨ ⁅K, U⁆ = ⊥ := by
  have hUX : U ≤ X := hU.le
  have hK' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hK.1).1 hK
  rcases CFSG.LocalCores.component_subnormal_subgroup hK' hU.subgroupOf with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hK.1 h)
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_of_le_left hUX] at this

theorem isSubnormal_of_le_of_le' {G : Type*} [Group G] {K C M : Subgroup G}
    (h : IsSubnormal K C) (hKM : K ≤ M) (hMC : M ≤ C) : IsSubnormal K M := by
  have := h.inf M
  rwa [inf_eq_left.2 hKM, inf_eq_right.2 hMC] at this

theorem exists_noncomm_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Assembly.IsQuasisimple Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => h b a
  have := hQ.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

theorem perfect_le_kernelRootSpan
    (a : Fin τ.rank → Lˣ)
    (hgen : toralCentralizer τ L a ≤
      torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    {P : Subgroup (ModGL τ L)}
    (hP : P ≤ toralCentralizer τ L a) (hperf : ⁅P, P⁆ = P) :
    P ≤ rootSpan τ L (kernelRoots (rootCharHom a)) := by
  calc P = ⁅P, P⁆ := hperf.symm
    _ ≤ ⁅torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)),
          torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))⁆ :=
        Subgroup.commutator_mono (hP.trans hgen) (hP.trans hgen)
    _ ≤ rootSpan τ L (kernelRoots (rootCharHom a)) :=
        CFSG.StandardType.LayerExc.commutator_torus_sup_rootSpan_le
          (K := L) (S := kernelRoots (rootCharHom a)) (fun _ hα => hα.1)

end CFSG.StandardType.F4ExplicitPos.OrbitSelection
end

end
