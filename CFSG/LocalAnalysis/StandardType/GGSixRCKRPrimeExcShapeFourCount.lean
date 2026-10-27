module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit
import CFSG.LocalAnalysis.ComponentClassification.HSFLitCong
import CFSG.RankThree.Chevalley.SteinbergBIWE8

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)

theorem rck_four_dvd_ncard {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} (hfin : Ψ.Finite) (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ)
    (hroot : ∀ γ, IsRoot τ (ρ γ) ↔ IsRoot τ γ) (hneg : ∀ γ, ρ (-γ) = -ρ γ)
    (hsq : ∀ γ, IsRoot τ γ → ρ (ρ γ) = -γ) (hstab : ∀ γ ∈ Ψ, ρ γ ∈ Ψ) : 4 ∣ Ψ.ncard := by
  classical
  have hρ4 : ∀ γ, IsRoot τ γ → ρ (ρ (ρ (ρ γ))) = γ := by
    intro γ hγ
    rw [hsq γ hγ, hneg γ, hneg (ρ γ), hsq γ hγ, neg_neg]
  have hiff : ∀ x, x ∈ Ψ ↔ ρ x ∈ Ψ := by
    intro x
    refine ⟨hstab x, fun hx => ?_⟩
    have hxr : IsRoot τ x := (hroot x).1 (hΨ _ hx)
    have h := hstab _ (hstab _ (hstab _ hx))
    rwa [hρ4 x hxr] at h
  let P : Equiv.Perm Ψ := ρ.subtypePerm fun x => (hiff x).symm
  haveI : Fintype Ψ := hfin.fintype
  have hP4 : P ^ 4 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    have hxr := hΨ x x.2
    show ρ (ρ (ρ (ρ (x : Fin τ.rank → ℤ)))) = x
    exact hρ4 x hxr
  have hfix : Fintype.card (Function.fixedPoints ⇑(P ^ 2)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    have hxr := hΨ x x.2
    have h1 : ((P ^ 2) x : Fin τ.rank → ℤ) = -x := hsq x hxr
    have h2 : ((P ^ 2) x : Fin τ.rank → ℤ) = x := congrArg Subtype.val hx
    have h3 : (x : Fin τ.rank → ℤ) = 0 := by
      funext i
      have := congrFun (h1.symm.trans h2) i
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega
    exact hxr.ne_zero h3
  have hmod := CFSG.ComponentClassification.HSFLit.card_modEq_card_fixedPoints_sq P hP4
  rw [hfix] at hmod
  have h4 : 4 ∣ Fintype.card Ψ := (Nat.modEq_zero_iff_dvd).1 hmod.symm
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact h4

theorem rck_comp_dichotomy
    {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (hstab : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    (∀ α ∈ componentRoots χ i, ρ α ∈ componentRoots χ i) ∨
      (∀ α ∈ componentRoots χ i, ρ α ∉ componentRoots χ i) := by
  by_cases h : ∃ α₀ ∈ componentRoots χ i, ρ α₀ ∈ componentRoots χ i
  · left
    obtain ⟨α₀, hα₀, hρα₀⟩ := h
    have hstep : ∀ x y : kernelRoots χ, (kernelRootSetoid χ).r x y →
        (ρ x ∈ componentRoots χ i ↔ ρ y ∈ componentRoots χ i) := by
      intro x y hxy
      unfold kernelRootSetoid at hxy
      induction hxy with
      | rel x y hxy =>
        rw [dotProduct_mulVec_eq_iform] at hxy
        have h2 : iform (ρ x) (ρ y) ≠ 0 := by rw [hform]; exact hxy
        exact ⟨fun hx => rck_mem_comp_of_iform_ne hx (hstab y y.2) h2,
          fun hy => rck_mem_comp_of_iform_ne hy (hstab x x.2) (by rw [iform_comm]; exact h2)⟩
      | refl x => exact Iff.rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    intro β hβ
    obtain ⟨hβk, hβi⟩ := hβ
    obtain ⟨hαk, hαi⟩ := hα₀
    have hrel : (kernelRootSetoid χ).r ⟨β, hβk⟩ ⟨α₀, hαk⟩ :=
      Quotient.exact (hβi.trans hαi.symm)
    exact (hstep _ _ hrel).2 hρα₀
  · right
    exact fun α hα hρ => h ⟨α, hα, hρ⟩

theorem rck_ncard_ne_126
    {a : Fin Tag.E8.rank → GGLˣ} {ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    (hroot : ∀ γ, IsRoot Tag.E8 (ρ γ) ↔ IsRoot Tag.E8 γ) (hneg : ∀ γ, ρ (-γ) = -ρ γ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (hsq : ∀ γ, IsRoot Tag.E8 γ → ρ (ρ γ) = -γ)
    (hstab : ∀ γ ∈ kernelRoots (rootCharHom a), ρ γ ∈ kernelRoots (rootCharHom a))
    (i : KernelComponent (rootCharHom a)) :
    (componentRoots (rootCharHom a) i).ncard ≠ 126 := by
  intro h126
  have hΨroot : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot Tag.E8 γ :=
    fun γ hγ => hγ.1.1
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot Tag.E8).subset hΨroot
  rcases rck_comp_dichotomy hform hstab i with hst | hdis
  · have h4 := rck_four_dvd_ncard hfin hΨroot hroot hneg hsq hst
    rw [h126] at h4
    omega
  · have himg : (ρ '' componentRoots (rootCharHom a) i).ncard = 126 := by
      rw [Set.ncard_image_of_injective _ ρ.injective, h126]
    have hdisj : Disjoint (componentRoots (rootCharHom a) i)
        (ρ '' componentRoots (rootCharHom a) i) := by
      rw [Set.disjoint_left]
      rintro x hx ⟨y, hy, rfl⟩
      exact hdis y hy hx
    have hsub : componentRoots (rootCharHom a) i ∪ ρ '' componentRoots (rootCharHom a) i ⊆
        {γ | IsRoot Tag.E8 γ} := by
      rintro x (hx | ⟨y, hy, rfl⟩)
      · exact hΨroot x hx
      · exact (hroot y).2 (hΨroot y hy)
    have hle := Set.ncard_le_ncard hsub (finite_setOf_isRoot Tag.E8)
    rw [Set.ncard_union_eq hdisj hfin (hfin.image _), h126, himg,
      CFSG.RankThree.Chevalley.WeylE8.card_roots] at hle
    omega

theorem rck_ncard_ne_240
    {a : Fin Tag.E8.rank → GGLˣ} (ha1 : rootDiagUnit Tag.E8 a ≠ 1)
    (i : KernelComponent (rootCharHom a)) :
    (componentRoots (rootCharHom a) i).ncard ≠ 240 := by
  intro h240
  have hΨroot : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot Tag.E8 γ :=
    fun γ hγ => hγ.1.1
  have hall : componentRoots (rootCharHom a) i = {γ | IsRoot Tag.E8 γ} := by
    refine Set.eq_of_subset_of_ncard_le hΨroot ?_ (finite_setOf_isRoot Tag.E8)
    rw [h240, CFSG.RankThree.Chevalley.WeylE8.card_roots]
  have hker : ∀ γ, IsRoot Tag.E8 γ → rootChar a γ = 1 := fun γ hγ => by
    have hγΨ : γ ∈ componentRoots (rootCharHom a) i := by rw [hall]; exact hγ
    exact hγΨ.1.2
  have ha : a = 1 := by
    funext j
    have h := rootChar_nsmul_single a j 1
    rw [one_smul, pow_one] at h
    rw [← h]
    exact hker _ (isRoot_single Tag.E8 j)
  exact ha1 (by rw [ha, rootDiagUnit_one])

end CFSG.StandardType.RCKRP
