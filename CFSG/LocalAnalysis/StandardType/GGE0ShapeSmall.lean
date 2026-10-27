module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGLangFamily
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ2
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3T
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

private theorem rho_iterate_eq_self_or_neg {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hsign : (∀ α, ρ α = α) ∨ (∀ α, ρ α = -α)) (k : ℕ) (δ : Fin τ.rank → ℤ) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ = δ ∨
      (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ = -δ := by
  rcases hsign with h | h
  · left
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, h]
  · induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', h]
      rcases ih with h1 | h1
      · exact Or.inr (by rw [h1])
      · exact Or.inl (by rw [h1, neg_neg])

private theorem orbitRoots_eq_componentRoots {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (hsign : (∀ α, ρ α = α) ∨ (∀ α, ρ α = -α)) (i : KernelComponent χ) :
    {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ componentRoots χ i ∧
      γ = (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ} = componentRoots χ i := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    rcases rho_iterate_eq_self_or_neg hsign k δ with h | h
    · rwa [h]
    · rw [h]
      exact (isRootComponent_componentRoots (χ := χ) i).neg_mem δ hδ
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

private theorem e6_symmetrizer_one (i : Fin Tag.E6.rank) : Tag.E6.symmetrizer i i = 1 := by
  simp [Tag.symmetrizer]

private theorem iform_self_eq_two_E6
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) :
    iform α α = 2 :=
  SimplyLacedCover.iform_self_eq_two e6_symmetrizer_one hα

private theorem ncard_a2roots_E6
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α)
    (hβ : IsRoot .E6 β) (h : iform α β = -1) : (a2roots α β).ncard = 6 := by
  classical
  have hαα : iform α α = 2 := iform_self_eq_two_E6 hα
  have hββ : iform β β = 2 := iform_self_eq_two_E6 hβ
  have hcomm : iform β α = iform α β := iform_comm β α
  let φ : (Fin Tag.E6.rank → ℤ) → ℤ × ℤ := fun v => (iform v α, iform v β)
  have hφ : [φ α, φ β, φ (α + β), φ (-α), φ (-β), φ (-(α + β))].Nodup := by
    simp only [φ, iform_add_left, SimplyLacedCover.iform_neg_left, hcomm, hαα, hββ, h]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      Prod.mk.injEq, not_or, and_true, not_and, not_false_eq_true]
    omega
  have hnd : [α, β, α + β, -α, -β, -(α + β)].Nodup := List.Nodup.of_map φ hφ
  have hset : a2roots α β = ↑([α, β, α + β, -α, -β, -(α + β)].toFinset) := by
    ext x
    simp only [a2roots, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
      List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  rfl

private theorem a2roots_subset_of_isRootComponent_E6
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {α β : Fin Tag.E6.rank → ℤ} (hα : α ∈ Ψ) (hβ : β ∈ Ψ) (h : iform α β = -1) :
    a2roots α β ⊆ Ψ := by
  have hαr : IsRoot .E6 α := hΨ.isRoot α hα
  have hβr : IsRoot .E6 β := hΨ.isRoot β hβ
  have hββ : iform β β = 2 := iform_self_eq_two_E6 hβr
  have hne : α ≠ -β := by
    intro heq
    have h1 : iform α β = iform (-β) β := congrArg (fun v => iform v β) heq
    rw [SimplyLacedCover.iform_neg_left, hββ, h] at h1
    norm_num at h1
  have hlt : iform α β < 0 := by omega
  have hsum : α + β ∈ Ψ :=
    hΨ.add_mem α hα β hβ (isRoot_add_of_iform_neg hαr hβr hne hlt)
  intro γ hγ
  simp only [a2roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hα
  · exact hΨ.neg_mem α hα
  · exact hβ
  · exact hΨ.neg_mem β hβ
  · exact hsum
  · exact hΨ.neg_mem (α + β) hsum

private theorem small_component_classification
    {L : Type} [Field L]
    (a : Fin 2 → Fin Tag.E6.rank → Lˣ)
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* (Fin 2 → Lˣ))
    (i : KernelComponent χ)
    (hker : kernelRoots χ = familyKernel a)
    (hsmall : (familyKernel a).ncard ≤ 6)
    (J : Subgroup (ModGL .E6 L))
    (hJi : J ≤ rootSpan .E6 L (componentRoots χ i)) :
    (∃ α ∈ familyKernel a, J ≤ rootSpan .E6 L {α, -α}) ∨
    (∃ α β, familyKernel a = a2roots α β ∧ J ≤ rootSpan .E6 L (a2roots α β)) := by
  classical
  set Ψ : Set (Fin Tag.E6.rank → ℤ) := componentRoots χ i with hΨdef
  have hcomp : IsRootComponent Ψ := isRootComponent_componentRoots (χ := χ) i
  have hΨsub : Ψ ⊆ familyKernel a := fun x hx => hker ▸ hx.1
  have hFKfin : (familyKernel a).Finite :=
    (finite_setOf_isRoot .E6).subset fun x hx => hx.1
  have hΨfin : Ψ.Finite := (finite_setOf_isRoot .E6).subset fun x hx => hx.1.1
  have hsmallΨ : Ψ.ncard ≤ 6 := (Set.ncard_le_ncard hΨsub hFKfin).trans hsmall
  obtain ⟨x, hx⟩ : Ψ.Nonempty := by
    obtain ⟨q, hq⟩ := Quotient.exists_rep i
    exact ⟨q.1, ⟨q.2, hq⟩⟩
  have hxroot : IsRoot .E6 x := hx.1.1
  have hnegx : -x ∈ Ψ := hcomp.neg_mem x hx
  have hxne : x ≠ -x := by
    intro heq
    have h1 : iform x x = iform x (-x) := congrArg (fun v => iform x v) heq
    rw [SimplyLacedCover.iform_neg_right, iform_self_eq_two_E6 hxroot] at h1
    norm_num at h1
  by_cases h2 : Ψ.ncard ≤ 2
  · left
    have hpair : ({x, -x} : Set (Fin Tag.E6.rank → ℤ)).ncard = 2 := Set.ncard_pair hxne
    have hsubset : ({x, -x} : Set (Fin Tag.E6.rank → ℤ)) ⊆ Ψ := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hx
      · exact hnegx
    have hle : Ψ.ncard ≤ ({x, -x} : Set (Fin Tag.E6.rank → ℤ)).ncard := by
      rw [hpair]; exact h2
    have heq : ({x, -x} : Set (Fin Tag.E6.rank → ℤ)) = Ψ :=
      Set.eq_of_subset_of_ncard_le hsubset hle hΨfin
    refine ⟨x, hker ▸ hx.1, ?_⟩
    rw [heq]
    exact hJi
  · right
    push Not at h2
    obtain ⟨δ, hδ, hxδ⟩ := exists_adjacent_root (Or.inl rfl) i h2 hx
    have hδroot : IsRoot .E6 δ := hδ.1.1
    have hβroot : IsRoot .E6 (-δ) := IsRoot.neg hδroot
    have hxβ : iform x (-δ) = -1 := by
      rw [SimplyLacedCover.iform_neg_right, hxδ]
    have hβmem : -δ ∈ Ψ := hcomp.neg_mem δ hδ
    have hsubA2 : a2roots x (-δ) ⊆ Ψ :=
      a2roots_subset_of_isRootComponent_E6 hcomp hx hβmem hxβ
    have hcnt : (a2roots x (-δ)).ncard = 6 := ncard_a2roots_E6 hxroot hβroot hxβ
    have hΨle : Ψ.ncard ≤ (a2roots x (-δ)).ncard := by rw [hcnt]; exact hsmallΨ
    have heqΨ : a2roots x (-δ) = Ψ := Set.eq_of_subset_of_ncard_le hsubA2 hΨle hΨfin
    have hsubFK : a2roots x (-δ) ⊆ familyKernel a := fun y hy => hΨsub (heqΨ ▸ hy)
    have hFKle : (familyKernel a).ncard ≤ (a2roots x (-δ)).ncard := by
      rw [hcnt]; exact hsmall
    have hFKeq : a2roots x (-δ) = familyKernel a :=
      Set.eq_of_subset_of_ncard_le hsubFK hFKle hFKfin
    refine ⟨x, -δ, hFKeq.symm, ?_⟩
    rw [heqΨ]
    exact hJi

theorem small_component_support
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (S : LangSetup .E6 L 5) (a : Fin 2 → Fin Tag.E6.rank → Lˣ)
    (ha : ∀ i, rootDiagUnit .E6 (a i) ∈ S.D.torus)
    (h3 : ∀ i j, a i j ^ 3 = 1)
    (hsign : (∀ α, S.ρ α = α) ∨ (∀ α, S.ρ α = -α))
    (hsmall : (familyKernel a).ncard ≤ 6)
    (J : Subgroup (ModGL .E6 L))
    (hJ : CFSG.Assembly.IsComponentOf J
      (S.Γ ⊓ Subgroup.centralizer (planeGroup a : Set _))) :
    (∃ α ∈ familyKernel a, J ≤ rootSpan .E6 L {α, -α}) ∨
    (∃ α β, familyKernel a = a2roots α β ∧ J ≤ rootSpan .E6 L (a2roots α β)) := by
  classical
  have hcent : Subgroup.centralizer (planeGroup a : Set (ModGL .E6 L)) =
      Subgroup.centralizer (Set.range fun i => rootDiagUnit .E6 (a i)) := by
    rw [planeGroup, Subgroup.centralizer_closure]
  have hp0 : (3 : L) ≠ 0 := by
    rintro h3z
    have hdvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h3z
    norm_num at hdvd
  have hJopen : CFSG.Open.IsComponentOf J
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit .E6 (a i))) := by
    have h' := (CFSG.Assembly.isComponentOf_iff_open).1 hJ
    rwa [hcent] at h'
  obtain ⟨i, hJi⟩ := LangRat.langFamilyComponentsInRootSpan .E6 L 5 3 S
    (Or.inr (Or.inl rfl)) Nat.prime_three (by norm_num) hp0 (Fin 2) a ha h3 J hJopen
  let χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* (Fin 2 → Lˣ) :=
    Pi.monoidHom fun u => CFSG.LieType.AlgebraicGroups.rootCharHom (a u)
  have hker : kernelRoots χ = familyKernel a := by
    have hχ : χ = familyChar a := rfl
    rw [hχ, kernelRoots_familyChar]
  have horbit := orbitRoots_eq_componentRoots χ S.ρ hsign i
  rw [horbit] at hJi
  exact small_component_classification a χ i hker hsmall J hJi

end CFSG.StandardType