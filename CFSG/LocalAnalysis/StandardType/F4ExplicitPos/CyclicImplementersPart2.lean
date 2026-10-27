module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart25
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicImplementersPart1

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.CyclicImplementers
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.Proving
open scoped Pointwise
variable {τ : Tag} {K : Type} [Field K]

section ComponentTorus
variable {L : Type} [Field L]

theorem exists_mem_componentRootSpan_conj_eq_of_mem_torusGroup_good
    {τ : Tag} [IsAlgClosed L]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) {y : ModGL τ L} (hy : y ∈ torusGroup τ L) :
    ∃ g ∈ componentRootSpan L χ i, ∀ x ∈ componentRootSpan L χ i,
      y * x * y⁻¹ = g * x * g⁻¹ := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  set Δ := simpleRoots Ψ with hΔdef
  set e : Fin Δ.card ≃ Δ := Δ.equivFin.symm with he
  set ν : Fin Δ.card → Fin τ.rank → ℤ := fun k => (e k : Fin τ.rank → ℤ) with hν
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  obtain ⟨t, ht⟩ := exists_torus_char_interpolation_good (L := L) i l
  refine ⟨rootDiagUnit τ (graphTorusChar ν t),
    rootDiagUnit_graphTorusChar_mem_componentRootSpan_good i ν
      (fun j => simpleRoots_subset (e j).2) t,
    fun x hx => ?_⟩
  have hK : componentRootSpan L χ i ≤
      (MulAut.conj (rootDiagUnit τ l)).toMonoidHom.eqLocus
        (MulAut.conj (rootDiagUnit τ (graphTorusChar ν t))).toMonoidHom := by
    rw [componentRootSpan]
    refine iSup₂_le fun α hα => ?_
    intro z hz
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hz
    have hαr : IsRoot τ α := isRoot_of_mem_componentRoots hα
    have h1 := rootDiagUnit_conj_pinnedX l hαr c
    have h2 := rootDiagUnit_conj_pinnedX (graphTorusChar ν t) hαr c
    have hchar : rootChar (graphTorusChar ν t) α = rootChar l α := by
      have ht' := ht α hα
      simpa [ν, e] using ht'
    change rootDiagUnit τ l * pinnedX τ L α c * (rootDiagUnit τ l)⁻¹ =
      rootDiagUnit τ (graphTorusChar ν t) * pinnedX τ L α c *
        (rootDiagUnit τ (graphTorusChar ν t))⁻¹
    rw [h1, h2, hchar]
  exact hK hx

theorem pinnedX_eq_coe_xPar
    {τ : Tag} {L : Type} [Field L]
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : L) :
    pinnedX τ L α c =
      ((xPar (rootOperatorFamily τ) α (((rootOperatorFamily τ).pinnedFamilySign α : L) * c) :
        adjointGroup τ L) : ModGL τ L) := by
  rw [(rootOperatorFamily τ).pinnedX_eq_eltUnit L hα,
    xPar_of_isRoot_without117 (rootOperatorFamily τ) hα,
    RootOperatorFamily.coe_eltElement]

theorem f4_commute_rootSubgroup_of_mk_ne
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {α β : kernelRoots χ} (h : (⟦α⟧ : KernelComponent χ) ≠ ⟦β⟧)
    (K : Type) [Field K] :
    ∀ x ∈ rootSubgroup Tag.F4 K (α : Fin Tag.F4.rank → ℤ),
      ∀ y ∈ rootSubgroup Tag.F4 K (β : Fin Tag.F4.rank → ℤ), Commute x y := by
  intro x hx y hy
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  have hne' : (α : Fin Tag.F4.rank → ℤ) ≠ -(β : Fin Tag.F4.rank → ℤ) := by
    intro e
    apply h
    have hif : iform (α : Fin Tag.F4.rank → ℤ) (β : Fin Tag.F4.rank → ℤ) ≠ 0 := by
      rw [e, iform_neg_left]
      exact neg_ne_zero.mpr (ne_of_gt (iform_self_pos β.2.1.ne_zero))
    exact mk_eq_of_iform_ne_zero hif
  have hne0 : (α : Fin Tag.F4.rank → ℤ) + (β : Fin Tag.F4.rank → ℤ) ≠ 0 :=
    fun e => hne' (eq_neg_iff_add_eq_zero.mpr e)
  have h1 : ¬IsRoot Tag.F4 ((α : Fin Tag.F4.rank → ℤ) + (β : Fin Tag.F4.rank → ℤ)) := by
    have := not_isRoot_of_mk_ne (τ := Tag.F4) h (a := 1) (b := 1) (by norm_num) (by norm_num)
    simpa using this
  have hcomm := commute_xPar_without117 (rootOperatorFamily Tag.F4)
    CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117
    noG2_F4 α.2.1 β.2.1 hne0 h1
    (((rootOperatorFamily Tag.F4).pinnedFamilySign α : K) * c)
    (((rootOperatorFamily Tag.F4).pinnedFamilySign β : K) * d)
  rw [pinnedX_eq_coe_xPar α.2.1 c, pinnedX_eq_coe_xPar β.2.1 d]
  exact hcomm.map (adjointGroup Tag.F4 K).subtype

theorem componentRootSpan_le_centralizer_good
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {i j : KernelComponent χ} (hij : i ≠ j) (K : Type) [Field K] :
    componentRootSpan K χ i ≤
      Subgroup.centralizer (componentRootSpan K χ j : Set (ModGL Tag.F4 K)) := by
  refine iSup₂_le fun α ⟨hα, hαi⟩ => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun β ⟨hβ, hβj⟩ => ?_
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hne : (⟦⟨α, hα⟩⟧ : KernelComponent χ) ≠ ⟦⟨β, hβ⟩⟧ := by rw [hαi, hβj]; exact hij
  exact (f4_commute_rootSubgroup_of_mk_ne (K := K) hne x hx y hy).eq

theorem exists_mem_componentRootSpan_conj_eq_of_mem_rootSpan_good
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) {u : ModGL Tag.F4 L}
    (hu : u ∈ rootSpan Tag.F4 L (kernelRoots χ)) :
    ∃ g ∈ componentRootSpan L χ i, ∀ x ∈ componentRootSpan L χ i,
      u * x * u⁻¹ = g * x * g⁻¹ := by
  classical
  set S := componentRootSpan L χ i with hS
  let H : Subgroup (ModGL Tag.F4 L) :=
    { carrier := {u | ∃ g ∈ S, ∀ x ∈ S, u * x * u⁻¹ = g * x * g⁻¹}
      one_mem' := ⟨1, one_mem S, by intro x _; simp⟩
      mul_mem' := by
        rintro u₁ u₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
        refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, fun x hx => ?_⟩
        have hx₂ : u₂ * x * u₂⁻¹ ∈ S := by
          rw [h₂ x hx]
          exact mul_mem (mul_mem hg₂ hx) (inv_mem hg₂)
        calc (u₁ * u₂) * x * (u₁ * u₂)⁻¹
            = u₁ * (u₂ * x * u₂⁻¹) * u₁⁻¹ := by group
          _ = g₁ * (u₂ * x * u₂⁻¹) * g₁⁻¹ := h₁ _ hx₂
          _ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := by rw [h₂ x hx]
          _ = (g₁ * g₂) * x * (g₁ * g₂)⁻¹ := by group
      inv_mem' := by
        rintro u ⟨g, hg, h⟩
        refine ⟨g⁻¹, inv_mem hg, fun x hx => ?_⟩
        have hy : g⁻¹ * x * g ∈ S := mul_mem (mul_mem (inv_mem hg) hx) hg
        have hux : u * (g⁻¹ * x * g) * u⁻¹ = x := by
          rw [h _ hy]
          group
        calc u⁻¹ * x * u = u⁻¹ * (u * (g⁻¹ * x * g) * u⁻¹) * u := by rw [hux]
          _ = g⁻¹ * x * g := by group }
  have hgen : ∀ α ∈ kernelRoots χ, rootSubgroup Tag.F4 L α ≤ H := by
    intro α hα z hz
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hz
    by_cases hαi : α ∈ componentRoots χ i
    · exact ⟨pinnedX Tag.F4 L α c, pinnedX_mem_rootSpan hαi c, fun x _ => rfl⟩
    · have hclass : (⟦⟨α, hα⟩⟧ : KernelComponent χ) ≠ i := fun h => hαi ⟨hα, h⟩
      have hmem : pinnedX Tag.F4 L α c ∈ componentRootSpan L χ ⟦⟨α, hα⟩⟧ :=
        rootSubgroup_le_componentRootSpan (K := L) ⟨α, hα⟩
          (Subgroup.subset_closure ⟨c, rfl⟩)
      have hcomm : ∀ x ∈ S, pinnedX Tag.F4 L α c * x = x * pinnedX Tag.F4 L α c :=
        fun x hx => (Subgroup.mem_centralizer_iff.1
          (componentRootSpan_le_centralizer_good hclass L hmem) x hx).symm
      refine ⟨1, one_mem S, fun x hx => ?_⟩
      rw [hcomm x hx]
      group
  have hrootSpan_le : rootSpan Tag.F4 L (kernelRoots χ) ≤ H := by
    rw [rootSpan]
    exact iSup₂_le hgen
  exact hrootSpan_le hu

theorem exists_mem_componentRootSpan_conj_eq_of_mem_Z_good
    [IsAlgClosed L]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ) {y : ModGL Tag.F4 L}
    (hy : y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (kernelRoots χ)) :
    ∃ g ∈ componentRootSpan L χ i, ∀ x ∈ componentRootSpan L χ i,
      y * x * y⁻¹ = g * x * g⁻¹ := by
  classical
  have hnorm : torusGroup Tag.F4 L ≤ Subgroup.normalizer
      (rootSpan Tag.F4 L (kernelRoots χ) : Set (ModGL Tag.F4 L)) :=
    torusGroup_le_normalizer_rootSpan (K := L) (fun _ hα => hα.1)
  have hcoe : (↑(torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (kernelRoots χ)) :
      Set (ModGL Tag.F4 L)) =
      (torusGroup Tag.F4 L : Set (ModGL Tag.F4 L)) *
        (rootSpan Tag.F4 L (kernelRoots χ) : Set (ModGL Tag.F4 L)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hy' : y ∈ (torusGroup Tag.F4 L : Set (ModGL Tag.F4 L)) *
      (rootSpan Tag.F4 L (kernelRoots χ) : Set (ModGL Tag.F4 L)) := by
    rw [← hcoe]
    exact hy
  obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.1 hy'
  obtain ⟨gt, hgt, hgt'⟩ := exists_mem_componentRootSpan_conj_eq_of_mem_torusGroup_good
    (χ := χ) i ht
  obtain ⟨gu, hgu, hgu'⟩ := exists_mem_componentRootSpan_conj_eq_of_mem_rootSpan_good i hu
  refine ⟨gt * gu, mul_mem hgt hgu, fun x hx => ?_⟩
  have hx' : gu * x * gu⁻¹ ∈ componentRootSpan L χ i :=
    mul_mem (mul_mem hgu hx) (inv_mem hgu)
  calc t * u * x * (t * u)⁻¹
      = t * (u * x * u⁻¹) * t⁻¹ := by group
    _ = t * (gu * x * gu⁻¹) * t⁻¹ := by rw [hgu' x hx]
    _ = gt * (gu * x * gu⁻¹) * gt⁻¹ := hgt' _ hx'
    _ = (gt * gu) * x * (gt * gu)⁻¹ := by group

theorem exists_hinner_of_mem_Z
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i : KernelComponent χ)
    {B : Type*} [Group B]
    (α : B →* MulAut (rootSpan Tag.F4 Ω (componentRoots χ i)))
    (hX : ∀ b : B, ∃ y ∈ torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (kernelRoots χ),
      ∀ x : rootSpan Tag.F4 Ω (componentRoots χ i),
        ((α b x : rootSpan Tag.F4 Ω (componentRoots χ i)) : ModGL Tag.F4 Ω) =
          y * (x : ModGL Tag.F4 Ω) * y⁻¹) :
    ∀ b : B, ∃ g : rootSpan Tag.F4 Ω (componentRoots χ i), MulAut.conj g = α b := by
  intro b
  obtain ⟨y, hy, hyα⟩ := hX b
  obtain ⟨g, hg, hgconj⟩ := exists_mem_componentRootSpan_conj_eq_of_mem_Z_good (L := Ω) i hy
  refine ⟨⟨g, hg⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (hgconj x x.2).symm.trans (hyα x).symm

end ComponentTorus

end CFSG.StandardType.F4ExplicitPos.CyclicImplementers

end

end
