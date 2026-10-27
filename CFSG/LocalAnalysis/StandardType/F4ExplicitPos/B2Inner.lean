module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Table
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
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

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.B2Inner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction.F4Pilot
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem wordW_conj_mem_closure
    {Ψ : Set (Fin (Tag.rank .F4) → ℤ)} {v : WeylGroup .F4}
    (hA : v • v0100 ∈ Ψ) (hB : v • v0010 ∈ Ψ)
    (ω : List ℕ) (hω : ∀ i ∈ ω, i = 1 ∨ i = 2) :
    v * wordW ω * v⁻¹ ∈
      Subgroup.closure {s : WeylGroup .F4 | ∃ γ ∈ Ψ, s = rootReflection γ} := by
  revert hω
  induction ω with
  | nil =>
    intro _
    rw [wordW, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | cons i ω ih =>
    intro hω
    rw [wordW]
    have hω' : ∀ j ∈ ω, j = 1 ∨ j = 2 := fun j hj => hω j (List.mem_cons_of_mem i hj)
    have hmem := ih hω'
    have hi : i = 1 ∨ i = 2 := hω i List.mem_cons_self
    rw [show v * (wordW ω * simple .F4 (Tag.F4.idx i)) * v⁻¹ =
        (v * wordW ω * v⁻¹) * (v * simple .F4 (Tag.F4.idx i) * v⁻¹) by group]
    refine mul_mem hmem ?_
    rcases hi with rfl | rfl
    · have hs : (Pi.single (Tag.F4.idx 1) (1 : ℤ) : Fin (Tag.rank .F4) → ℤ) = v0100 := by
        decide
      have hconj : rootReflection (v • v0100) = v * simple .F4 (Tag.F4.idx 1) * v⁻¹ :=
        rootReflection_eq_conj (β := v • v0100) (w := v) (j := Tag.F4.idx 1) (by rw [hs])
      rw [← hconj]
      exact Subgroup.subset_closure ⟨v • v0100, hA, rfl⟩
    · have hs : (Pi.single (Tag.F4.idx 2) (1 : ℤ) : Fin (Tag.rank .F4) → ℤ) = v0010 := by
        decide
      have hconj : rootReflection (v • v0010) = v * simple .F4 (Tag.F4.idx 2) * v⁻¹ :=
        rootReflection_eq_conj (β := v • v0010) (w := v) (j := Tag.F4.idx 2) (by rw [hs])
      rw [← hconj]
      exact Subgroup.subset_closure ⟨v • v0010, hB, rfl⟩

open scoped CFSG.Decide.Bounded in
theorem b2List_mem_cases :
    ∀ γ ∈ b2List, γ = v0100 ∨ γ = v0120 ∨ γ = v0010 ∨ γ = v0110 ∨
      γ = -v0100 ∨ γ = -v0120 ∨ γ = -v0010 ∨ γ = -v0110 := by
  decide +kernel

theorem b2_isometry_twistInner
    {Ψ : Set (Fin (Tag.rank .F4) → ℤ)} (_hΨ : IsRootComponent Ψ) {v : WeylGroup .F4}
    (hshape : Ψ = (v • ·) '' b2LeviRoots)
    {f : (Fin (Tag.rank .F4) → ℤ) → Fin (Tag.rank .F4) → ℤ} (hf : IsIsometry Ψ f) :
    twistInner Ψ f := by
  classical
  have hmem_image : ∀ β ∈ b2LeviRoots, v • β ∈ Ψ := by
    intro β hβ
    rw [hshape]
    exact ⟨β, hβ, rfl⟩
  have hv0100 : v0100 ∈ b2LeviRoots :=
    mem_b2LeviRoots.2 ⟨mem_rootFinset.1 (by decide +kernel), rfl, rfl⟩
  have hv0010 : v0010 ∈ b2LeviRoots :=
    mem_b2LeviRoots.2 ⟨mem_rootFinset.1 (by decide +kernel), rfl, rfl⟩
  have hv0110 : v0100 + v0010 ∈ b2LeviRoots :=
    mem_b2LeviRoots.2 ⟨mem_rootFinset.1 (by decide +kernel), rfl, rfl⟩
  have hv0120 : (v0100 + v0010) + v0010 ∈ b2LeviRoots :=
    mem_b2LeviRoots.2 ⟨mem_rootFinset.1 (by decide +kernel), rfl, rfl⟩
  have hA' : v • v0100 ∈ Ψ := hmem_image _ hv0100
  have hB' : v • v0010 ∈ Ψ := hmem_image _ hv0010
  have hAB : v • v0100 + v • v0010 ∈ Ψ := by
    rw [← smul_add]
    exact hmem_image _ hv0110
  have hA2B : (v • v0100 + v • v0010) + v • v0010 ∈ Ψ := by
    rw [← smul_add, ← smul_add]
    exact hmem_image _ hv0120
  have hpre : ∀ x ∈ Ψ, v⁻¹ • x ∈ b2LeviRoots := by
    intro x hx
    rw [hshape] at hx
    obtain ⟨β, hβ, rfl⟩ := hx
    rwa [inv_smul_smul]
  have hfA' : f (v • v0100) ∈ Ψ := hf.bijOn.mapsTo hA'
  have hfB' : f (v • v0010) ∈ Ψ := hf.bijOn.mapsTo hB'
  have hiform0100 : iform v0100 v0100 = 4 := by decide +kernel
  have hiform0010 : iform v0010 v0010 = 2 := by decide +kernel
  have hiform0100_0010 : iform v0100 v0010 = -2 := by decide +kernel
  have hXX : iform (v⁻¹ • f (v • v0100)) (v⁻¹ • f (v • v0100)) = 4 := by
    rw [iform_smul, hf.iform_eq (v • v0100) hA' (v • v0100) hA', iform_smul, hiform0100]
  have hYY : iform (v⁻¹ • f (v • v0010)) (v⁻¹ • f (v • v0010)) = 2 := by
    rw [iform_smul, hf.iform_eq (v • v0010) hB' (v • v0010) hB', iform_smul, hiform0010]
  have hXY : iform (v⁻¹ • f (v • v0100)) (v⁻¹ • f (v • v0010)) = -2 := by
    rw [iform_smul, hf.iform_eq (v • v0100) hA' (v • v0010) hB', iform_smul, hiform0100_0010]
  obtain ⟨ω, hωmem, hωX, hωY⟩ := b2LeviRoots_pair_table
    (v⁻¹ • f (v • v0100)) (hpre _ hfA') (v⁻¹ • f (v • v0010)) (hpre _ hfB') hXX hYY hXY
  have hωletters : ∀ i ∈ ω, i = 1 ∨ i = 2 := b2Words_letters ω hωmem
  have hAu : f (v • v0100) = (v * wordW ω * v⁻¹) • (v • v0100) := by
    rw [mul_smul, mul_smul, inv_smul_smul, wordW_smul_eq_wordAct, hωX, smul_inv_smul]
  have hBu : f (v • v0010) = (v * wordW ω * v⁻¹) • (v • v0010) := by
    rw [mul_smul, mul_smul, inv_smul_smul, wordW_smul_eq_wordAct, hωY, smul_inv_smul]
  have hABu : f (v • v0100 + v • v0010) =
      (v * wordW ω * v⁻¹) • (v • v0100 + v • v0010) := by
    have h := (eq_add_iff_of_iform hf.iform_eq hA' hB' hAB).2 rfl
    rw [h, hAu, hBu]
    simp only [smul_add]
  have hA2Bu : f ((v • v0100 + v • v0010) + v • v0010) =
      (v * wordW ω * v⁻¹) • ((v • v0100 + v • v0010) + v • v0010) := by
    have h := (eq_add_iff_of_iform hf.iform_eq hAB hB' hA2B).2 rfl
    rw [h, hABu, hBu]
    simp only [smul_add]
  have hneg : ∀ γ ∈ Ψ, f γ = (v * wordW ω * v⁻¹) • γ →
      f (-γ) = (v * wordW ω * v⁻¹) • (-γ) := by
    intro γ hγ h
    rw [hf.neg γ hγ, h, smul_neg]
  have h1 : f (v • v0100) = (v * wordW ω * v⁻¹) • (v • v0100) := hAu
  have h2 : f (v • v0120) = (v * wordW ω * v⁻¹) • (v • v0120) := by
    rw [show v0120 = (v0100 + v0010) + v0010 from by decide +kernel, smul_add, smul_add]
    exact hA2Bu
  have h3 : f (v • v0010) = (v * wordW ω * v⁻¹) • (v • v0010) := hBu
  have h4 : f (v • v0110) = (v * wordW ω * v⁻¹) • (v • v0110) := by
    rw [show v0110 = v0100 + v0010 from by decide +kernel, smul_add]
    exact hABu
  have hm2 : v • v0120 ∈ Ψ := by
    rw [show v0120 = (v0100 + v0010) + v0010 from by decide +kernel, smul_add, smul_add]
    exact hA2B
  have hm4 : v • v0110 ∈ Ψ := by
    rw [show v0110 = v0100 + v0010 from by decide +kernel, smul_add]
    exact hAB
  have hn1 : f (v • -v0100) = (v * wordW ω * v⁻¹) • (v • -v0100) := by
    rw [smul_neg]
    exact hneg (v • v0100) hA' hAu
  have hn2 : f (v • -v0120) = (v * wordW ω * v⁻¹) • (v • -v0120) := by
    rw [smul_neg]
    exact hneg (v • v0120) hm2 h2
  have hn3 : f (v • -v0010) = (v * wordW ω * v⁻¹) • (v • -v0010) := by
    rw [smul_neg]
    exact hneg (v • v0010) hB' hBu
  have hn4 : f (v • -v0110) = (v * wordW ω * v⁻¹) • (v • -v0110) := by
    rw [smul_neg]
    exact hneg (v • v0110) hm4 h4
  refine ⟨v * wordW ω * v⁻¹,
    wordW_conj_mem_closure hA' hB' ω hωletters, ?_⟩
  intro γ hγ
  rw [hshape] at hγ
  obtain ⟨β, hβ, rfl⟩ := hγ
  have hβl : β ∈ b2List := mem_b2List_of_mem_b2LeviRoots_narrow hβ
  rcases b2List_mem_cases β hβl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact hn1
  · exact hn2
  · exact hn3
  · exact hn4

theorem b2_component_rho_twistInner
    {Ω : Type} [Field Ω]
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin (Tag.rank .F4) → ℤ) →* M}
    {D : LangDatum Tag.F4 Ω} {ρ : Equiv.Perm (Fin (Tag.rank .F4) → ℤ)} (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ) {v : WeylGroup .F4}
    (hshape : componentRoots χ i = (v • ·) '' b2LeviRoots)
    (hstable : (fun γ => ρ γ) '' componentRoots χ i = componentRoots χ i) :
    twistInner (componentRoots χ i) ρ := by
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have hbij : Set.BijOn (fun γ => ρ γ) (componentRoots χ i) (componentRoots χ i) :=
    ⟨fun γ hγ => by rw [← hstable]; exact ⟨γ, hγ, rfl⟩,
      ρ.injective.injOn,
      fun γ hγ => by
        rw [← hstable] at hγ
        obtain ⟨δ, hδ, hδγ⟩ := hγ
        exact ⟨δ, hδ, hδγ⟩⟩
  have hf : IsIsometry (componentRoots χ i) (fun γ => ρ γ) :=
    ⟨hbij, fun γ _ δ _ => hρ.iform_eq γ δ, fun γ _ => hρ.neg_eq γ⟩
  exact b2_isometry_twistInner (Ψ := componentRoots χ i) (v := v) hΨ hshape hf

end CFSG.StandardType.F4ExplicitPos.B2Inner

end

end
