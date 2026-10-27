module

public import CFSG.LocalAnalysis.StandardType.GGLangFamily
public import CFSG.LocalAnalysis.StandardType.GGLangAlgebraicRestriction
public import CFSG.LocalAnalysis.StandardType.GGFamTrivialRoots
public import CFSG.LocalAnalysis.StandardType.GGFamTrivialGamma
public import CFSG.LocalAnalysis.StandardType.GGFamNoDiagram
public import CFSG.LocalAnalysis.StandardType.GGFamOuterEField
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelKind

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Assembly (LargeEvenLabel)
open CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (isComponentOf_eq_of_isQuasisimple)

private theorem compRank_allRoots_eq_rank {τ : Tag} :
    compRank ({α : Fin τ.rank → ℤ | IsRoot τ α}) = τ.rank := by
  unfold compRank
  have htop : Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) ''
      {α : Fin τ.rank → ℤ | IsRoot τ α}) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k, v k • (Pi.single k (1 : ℚ) : Fin τ.rank → ℚ) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]
    rw [hv]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨Pi.single k 1, IsRoot.basis k, ?_⟩
    funext j
    simp [Pi.single_apply]
  rw [htop]
  simp

theorem langFamilyCompLabel_trivial
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) (h1 : ∀ u, rootDiagUnit τ (a u) = 1)
    (i : KernelComponent (famCharHom a))
    {K : Subgroup (ModGL τ L)}
    (hK : IsComponentOf K
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)))) :
    ∃ n : ℕ, 2 ^ n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) ∧
      GGCompLabelAt
        (componentLabel (compRank (componentRoots (famCharHom a) i))
          (componentRoots (famCharHom a) i).ncard
          (twistKindOf S.ρ (componentRoots (famCharHom a) i)) n) K := by
  classical
  have ha1 : ∀ u, a u = 1 := fun u => rootDiagUnit_injective (by rw [h1 u, rootDiagUnit_one])
  have hχ : ∀ γ : Fin τ.rank → ℤ, famCharHom a (Multiplicative.ofAdd γ) = 1 := by
    intro γ
    funext u
    change rootChar (a u) γ = 1
    rw [ha1 u, rootChar_one_tuple']
  have hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus := fun u => by
    rw [h1 u]
    exact Subgroup.one_mem _
  have hcent : Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨u, rfl⟩
    simp [h1 u]
  have hK' : IsComponentOf K S.Γ := by simpa [hcent] using hK
  obtain ⟨t, f, h2f, hLie, hqΓ, htag⟩ := famTrivial_Γ_data_tag hτ S
  have hKΓ : K = S.Γ := isComponentOf_eq_of_isQuasisimple hK' hqΓ
  have hroots : componentRoots (famCharHom a) i = {γ : Fin τ.rank → ℤ | IsRoot τ γ} :=
    famTrivial_componentRoots_eq_univ hτ (famCharHom a) hχ i
  have horbit : componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 :=
    famTrivial_componentOrbitLength_eq_one hτ S.ρ (fun γ => S.frob.isRoot_iff γ)
      (famCharHom a) hχ i
  have hf1 : 1 ≤ f := by
    have hq1 : 1 < S.D.q := S.hqpow.1.one_lt
    rcases Nat.eq_zero_or_pos f with hf | hf
    · subst hf
      rw [pow_zero] at h2f
      omega
    · exact hf
  refine ⟨f, ?_, ?_⟩
  · rw [horbit, pow_one]
    exact h2f
  · rcases hτ with rfl | rfl | rfl
    ·
      rw [hroots, hKΓ]
      have hrank6 : compRank ({γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}) = 6 :=
        compRank_allRoots_eq_rank (τ := Tag.E6)
      have hS6 : KernelSizes (famCharHom a) [72] :=
        (ComponentCert.kernelSizes_of_check (S := famTrivial_certE6) (inS := fun _ => true)
          (fun k _ => ⟨fun _ => hχ _, fun _ => rfl⟩) famTrivial_certE6_check).of_perm
          (by rw [famTrivial_certE6_sizes])
      have hncard6 : ({γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}).ncard = 72 := by
        rw [← hroots, hS6.componentRoots_eq i]
        exact hS6.ncard_eq
      have horb6 : componentOrbitLength S.ρ {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ} = 1 := by
        rw [← hroots]
        exact horbit
      rcases htag with ⟨-, ht, hinner⟩ | ⟨-, ht, hni⟩ | ⟨h7, -⟩ | ⟨h8, -⟩
      · rw [ht] at hLie
        have hinner_orb : twistInner {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[
              componentOrbitLength S.ρ {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}]) := by
          rw [horb6, Function.iterate_one]
          exact hinner
        have hkind : twistKindOf S.ρ {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ} = .inner :=
          twistKindOf_eq_inner_of_twistInner S.ρ _ hinner_orb
        have hlab : componentLabel 6 72 .inner f = (⟨.E6, 0, f⟩ : LargeEvenLabel) :=
          componentLabel_inner_E6 (N := 72) f rfl
        rw [hrank6, hncard6, hkind, hlab]
        exact ggCompLabelAt_E6 f hf1 hLie
      · rw [ht] at hLie
        have hni_orb : ¬ twistInner {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[
              componentOrbitLength S.ρ {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}]) := by
          rw [horb6, Function.iterate_one]
          exact hni
        have hkind : twistKindOf S.ρ {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ} = .exc :=
          twistKindOf_eq_exc_of_E6 S.ρ _ hni_orb hrank6 hncard6
        have hlab : componentLabel 6 72 .exc f = (⟨.twE6, 0, f⟩ : LargeEvenLabel) :=
          componentLabel_exc_E6 (N := 72) f rfl
        rw [hrank6, hncard6, hkind, hlab]
        exact ggCompLabelAt_twE6 f hf1 hLie
      · exact absurd h7 (by decide)
      · exact absurd h8 (by decide)
    ·
      rw [hroots, hKΓ]
      have hrank7 : compRank ({γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}) = 7 :=
        compRank_allRoots_eq_rank (τ := Tag.E7)
      have hS7 : KernelSizes (famCharHom a) [126] :=
        (ComponentCert.kernelSizes_of_check (S := famTrivial_certE7) (inS := fun _ => true)
          (fun k _ => ⟨fun _ => hχ _, fun _ => rfl⟩) famTrivial_certE7_check).of_perm
          (by rw [famTrivial_certE7_sizes])
      have hncard7 : ({γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}).ncard = 126 := by
        rw [← hroots, hS7.componentRoots_eq i]
        exact hS7.ncard_eq
      rcases htag with ⟨h6, -⟩ | ⟨h6', -⟩ | ⟨-, ht⟩ | ⟨h8, -⟩
      · exact absurd h6 (by decide)
      · exact absurd h6' (by decide)
      · rw [ht] at hLie
        have hno : ¬ HasDiagramSymmetryType (componentRoots (famCharHom a) i) := by
          rw [hroots]
          exact famOuterE_not_diagramSymm (Or.inl ⟨hrank7, hncard7⟩)
        have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
          fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
        have hinner : twistInner (componentRoots (famCharHom a) i)
            ((S.ρ : (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ))^[
              componentOrbitLength S.ρ (componentRoots (famCharHom a) i)]) :=
          fam_twistInner_of_noDiagram S (famCharHom a) i hρ hno
        have hinner_orb : twistInner {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}
            ((S.ρ : (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ))^[
              componentOrbitLength S.ρ {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ}]) := by
          rw [← hroots]
          exact hinner
        have hkind : twistKindOf S.ρ {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ} = .inner :=
          twistKindOf_eq_inner_of_twistInner S.ρ _ hinner_orb
        have hlab : componentLabel 7 126 .inner f = (⟨.E7, 0, f⟩ : LargeEvenLabel) :=
          componentLabel_inner_E7 (N := 126) f rfl
        rw [hrank7, hncard7, hkind, hlab]
        exact ggCompLabelAt_E7 f hf1 hLie
      · exact absurd h8 (by decide)
    ·
      rw [hroots, hKΓ]
      have hrank8 : compRank ({γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ}) = 8 :=
        compRank_allRoots_eq_rank (τ := Tag.E8)
      have hS8 : KernelSizes (famCharHom a) [240] :=
        (ComponentCert.kernelSizes_of_check (S := famTrivial_certE8) (inS := fun _ => true)
          (fun k _ => ⟨fun _ => hχ _, fun _ => rfl⟩) famTrivial_certE8_check).of_perm
          (by rw [famTrivial_certE8_sizes])
      have hncard8 : ({γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ}).ncard = 240 := by
        rw [← hroots, hS8.componentRoots_eq i]
        exact hS8.ncard_eq
      rcases htag with ⟨h6, -⟩ | ⟨h6', -⟩ | ⟨h7, -⟩ | ⟨-, ht⟩
      · exact absurd h6 (by decide)
      · exact absurd h6' (by decide)
      · exact absurd h7 (by decide)
      · rw [ht] at hLie
        have hno : ¬ HasDiagramSymmetryType (componentRoots (famCharHom a) i) := by
          rw [hroots]
          exact famOuterE_not_diagramSymm (Or.inr ⟨hrank8, hncard8⟩)
        have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
          fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
        have hinner : twistInner (componentRoots (famCharHom a) i)
            ((S.ρ : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ))^[
              componentOrbitLength S.ρ (componentRoots (famCharHom a) i)]) :=
          fam_twistInner_of_noDiagram S (famCharHom a) i hρ hno
        have hinner_orb : twistInner {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ}
            ((S.ρ : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ))^[
              componentOrbitLength S.ρ {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ}]) := by
          rw [← hroots]
          exact hinner
        have hkind : twistKindOf S.ρ {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ} = .inner :=
          twistKindOf_eq_inner_of_twistInner S.ρ _ hinner_orb
        have hlab : componentLabel 8 240 .inner f = (⟨.E8, 0, f⟩ : LargeEvenLabel) :=
          componentLabel_inner_E8 (N := 240) f rfl
        rw [hrank8, hncard8, hkind, hlab]
        exact ggCompLabelAt_E8 f hf1 hLie

end CFSG.StandardType.TableCRes

end
