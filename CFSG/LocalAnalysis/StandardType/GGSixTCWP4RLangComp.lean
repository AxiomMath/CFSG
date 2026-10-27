module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Components

theorem tc_components_eq {G : Type*} [Group G] {Y L₁ L₂ J : Subgroup G} [Finite ↥Y]
    (h₁ : IsComponentOf L₁ Y) (h₂ : IsComponentOf L₂ Y) (hJ₁ : J ≤ L₁) (hJ₂ : J ≤ L₂)
    (hJ : ∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a) : L₁ = L₂ := by
  by_contra hne
  have hA : IsComponentOf (L₁.subgroupOf Y) ⊤ :=
    (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf h₁.1).mp h₁
  have hB : IsComponentOf (L₂.subgroupOf Y) ⊤ :=
    (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf h₂.1).mp h₂
  have hne' : L₁.subgroupOf Y ≠ L₂.subgroupOf Y := by
    intro h
    have h' := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr h₁.1, inf_eq_left.mpr h₂.1] at h'
    exact hne h'
  obtain ⟨a, ha, b, hb, hab⟩ := hJ
  have haY : a ∈ Y := h₁.1 (hJ₁ ha)
  have hbY : b ∈ Y := h₁.1 (hJ₁ hb)
  have hmul := CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hA hB hne'
    (a := (⟨a, haY⟩ : ↥Y)) (b := (⟨b, hbY⟩ : ↥Y))
    (Subgroup.mem_subgroupOf.mpr (hJ₁ ha)) (Subgroup.mem_subgroupOf.mpr (hJ₂ hb))
  exact hab (congrArg Subtype.val hmul)

theorem tc_exists_noncomm_of_isComponentOf {G : Type*} [Group G] {K Y : Subgroup G}
    (h : IsComponentOf K Y) : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ h.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', a'.2, b', b'.2, fun e => hab ?_⟩
  have e' : a' * b' = b' * a' := Subtype.ext e
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e']

end Components

section Centralizer

variable {τ : Tag} {Lf : Type} [Field Lf] [IsAlgClosed Lf] {p₀ : ℕ}

theorem tc_le_centralizer_of_kernel_le
    (S : LangSetup τ Lf p₀) {Dg : Subgroup (ModGL τ Lf)} (a : ↥Dg → Fin τ.rank → Lfˣ)
    (ha : ∀ u : ↥Dg, (u : ModGL τ Lf) = rootDiagUnit τ (a u))
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (xg : ↥Dg)
    (i' : KernelComponent (famCharHom (fun _ : PUnit.{1} => a xg)))
    (hsub : componentRoots (famCharHom (fun _ : PUnit.{1} => a xg)) i' ⊆
      kernelRoots (famCharHom a))
    {Lg : Subgroup (ModGL τ Lf)}
    (hL : Lg ≤ rootSpan τ Lf (famOrbit S.ρ (fun _ : PUnit.{1} => a xg) i')) :
    Lg ≤ Subgroup.centralizer (Dg : Set (ModGL τ Lf)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hxC : ∀ u : ↥Dg, x ∈ Subgroup.centralizer ({rootDiagUnit τ (a u)} : Set (ModGL τ Lf)) := by
    intro u
    have hb1 : ∀ γ ∈ componentRoots (famCharHom (fun _ : PUnit.{1} => a xg)) i',
        rootChar (a u) γ = 1 := by
      intro γ hγ
      exact ((mem_kernelRoots_famChar a).1 (hsub hγ)).2 u
    exact rootSpan_rationalRoots_le_centralizer S (fun _ : PUnit.{1} => a xg) i'
      (hT u) hb1 (hL hx)
  have h2 := (Subgroup.mem_centralizer_iff.mp (hxC ⟨d, hd⟩))
    (rootDiagUnit τ (a ⟨d, hd⟩)) (Set.mem_singleton _)
  rw [← ha ⟨d, hd⟩] at h2
  exact h2

end Centralizer

end CFSG.StandardType.TableCRes

end
