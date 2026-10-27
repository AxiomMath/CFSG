module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LeviCore
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddShapesPart2
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4F4
public import CFSG.LocalAnalysis.StandardType.GGTBJLeviAssemble
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResidual

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def f4LeviDel : Finset (Finset (Fin 4)) :=
  {{0}, {3}, {0, 1}, {2, 3}, {0, 3}}

section Kac

open CFSG.RankThree.PartOne.KF4 CFSG.SeitzReduction.F4Pilot
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof

private theorem f4lv_compRank_pair_le (j : Fin Tag.F4.rank) :
    compRank ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) ≤ 1 := by
  classical
  unfold compRank
  let e : Fin Tag.F4.rank → ℚ := fun i => ((Pi.single j (1 : ℤ) : Fin Tag.F4.rank → ℤ) i : ℚ)
  have himg : (fun γ (i : Fin Tag.F4.rank) => (γ i : ℚ)) ''
      ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) = {e, -e} := by
    rw [Set.image_pair]
    congr 1
  rw [himg, Set.pair_comm, Submodule.span_insert_eq_span
    (Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton e)))]
  exact (finrank_span_le_card ({e} : Set (Fin Tag.F4.rank → ℚ))).trans (by simp)

private theorem f4lv_B3_eq :
    f4LeviB3 = {j : Fin Tag.F4.rank | j ∉ ({3} : Finset (Fin Tag.F4.rank))} := by
  ext j
  simp only [f4LeviB3, Set.mem_range, Set.mem_setOf_eq]
  fin_cases j <;> decide

private theorem f4lv_C3_eq :
    f4LeviC3 = {j : Fin Tag.F4.rank | j ∉ ({0} : Finset (Fin Tag.F4.rank))} := by
  ext j
  simp only [f4LeviC3, Set.mem_range, Set.mem_setOf_eq]
  fin_cases j <;> decide

private theorem f4lv_long_eq :
    f4LongSupport = {j : Fin Tag.F4.rank | j ∉ ({2, 3} : Finset (Fin Tag.F4.rank))} := by
  ext j
  simp only [f4LongSupport, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  fin_cases j <;> decide

private theorem f4lv_short_eq :
    f4ShortSupport = {j : Fin Tag.F4.rank | j ∉ ({0, 1} : Finset (Fin Tag.F4.rank))} := by
  ext j
  simp only [f4ShortSupport, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  fin_cases j <;> decide

private theorem f4lv_B2_eq :
    nodesTU = {j : Fin Tag.F4.rank | j ∉ ({0, 3} : Finset (Fin Tag.F4.rank))} := by
  ext j
  simp only [nodesTU, Set.mem_setOf_eq]
  fin_cases j <;> decide

theorem f4_class_levi
    {L : Type} [Field L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot (ζ : L) p) (a : Fin Tag.F4.rank → Lˣ) (ha : ∀ i, a i ^ p = 1)
    (ha1 : ∃ j, a j ≠ 1) (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (v : WeylGroup .F4) (S : Finset (Fin 4)), S ∈ f4LeviDel ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots .F4 {j | j ∉ S} := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f : L →+* AlgebraicClosure L := algebraMap L (AlgebraicClosure L)
  let a' : Fin Tag.F4.rank → (AlgebraicClosure L)ˣ := fun j => Units.map f.toMonoidHom (a j)
  have hfu : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have hker : kernelRoots (rootCharHom a) = kernelRoots (rootCharHom a') := by
    ext γ
    constructor
    · rintro ⟨hr, h1⟩
      refine ⟨hr, ?_⟩
      change rootChar a' γ = 1
      change rootChar a γ = 1 at h1
      rw [CFSG.RankThree.PartOne.KE.rootChar_map_tuple f a γ, h1, map_one]
    · rintro ⟨hr, h1⟩
      refine ⟨hr, ?_⟩
      change rootChar a γ = 1
      change rootChar a' γ = 1 at h1
      rw [CFSG.RankThree.PartOne.KE.rootChar_map_tuple f a γ] at h1
      exact hfu (h1.trans (map_one _).symm)
  obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep i
  have hα' : α ∈ kernelRoots (rootCharHom a') := hker ▸ hα
  have hcomp := CFSG.LieType.Chevalley.OddToralOrdinary.componentRoots_eq_of_kernelRoots_eq
    hker hα hα'
  rw [hcomp] at h2 ⊢
  have hpL : (p : L) ≠ 0 := hζ.neZero'.out
  have hpΩ : (p : AlgebraicClosure L) ≠ 0 := by
    rw [← map_natCast f p]
    exact fun h => hpL (f.injective (h.trans (map_zero f).symm))
  have haN : ∀ j, a' j ^ p = 1 := fun j => by
    change Units.map f.toMonoidHom (a j) ^ p = 1
    rw [← map_pow, ha j, map_one]
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have ha1' : rootDiagUnit Tag.F4 a' ≠ 1 := by
    intro h1
    have h1' : a' = 1 :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    obtain ⟨j, hj⟩ := ha1
    apply hj
    apply hfu
    rw [map_one]
    exact congrFun h1' j
  by_cases h3 : 3 ≤ compRank (componentRoots (rootCharHom a') ⟦⟨α, hα'⟩⟧)
  · obtain ⟨v, J, hJ, hΨ, -, -⟩ :=
      f4_rank_ge_three_component_is_levi_odd_of_coord hp.pos hodd hpΩ haN ha1' _ h3
    rcases hJ with rfl | rfl
    · exact ⟨v, {3}, by decide, by rw [hΨ, f4lv_B3_eq]; rfl⟩
    · exact ⟨v, {0}, by decide, by rw [hΨ, f4lv_C3_eq]; rfl⟩
  · obtain ⟨v, hcases⟩ :=
      f4_rank_le_two_component_shape_odd_of_coord hp.pos hodd hpΩ haN ⟦⟨α, hα'⟩⟧ (by omega)
    rcases hcases with ⟨j, hΨ⟩ | hΨ | hΨ | hΨ
    · exfalso
      rw [hΨ, compRank_image] at h2
      have := f4lv_compRank_pair_le j
      omega
    · exact ⟨v, {2, 3}, by decide, by rw [hΨ, f4lv_long_eq]; rfl⟩
    · exact ⟨v, {0, 1}, by decide, by rw [hΨ, f4lv_short_eq]; rfl⟩
    · exact ⟨v, {0, 3}, by decide, by rw [hΨ, b2LeviRoots, f4lv_B2_eq]; rfl⟩

end Kac

section Datum

open CFSG CFSG.Assembly CFSG.Monster.B.Geometry

private theorem f4lv_parabolic_weyl {S : Finset (Fin 4)} (hne : Nonempty {i : Fin 4 // i ∉ S})
    (hdel : GGDeletedConnectedS CoxeterMatrix.F₄ S) :
    GGIsWeylMatrix (parMatrix CoxeterMatrix.F₄ {i | i ∉ S}) :=
  l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S CoxeterMatrix.F₄ (Tag.cartan .F4)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 4), by ext i j; rfl⟩)))))
    FrameRoute.ggIntCartan_F₄_tag hdel hne

theorem ggF4LeviDatum_of_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {Bs X J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Fin 4 → MulAut ↥Bs} {h : Fin 4 → V} {α : Fin 4 → Module.Dual (ZMod p) V}
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (Tag.cartan .F4 i j : ZMod p))
    {f : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (CoxeterMatrix.F₄.simple i) : MulAut ↥Bs) = φ i)
    (hclos : ggAutomizer X Bs = Subgroup.closure (Set.range φ))
    (u : CoxeterMatrix.F₄.Group) {S : Finset (Fin 4)} (hS : S ∈ f4LeviDel)
    (hJ : ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Fin 4 // j ∉ S} =>
      (f u : MulAut ↥Bs) * φ j * (f u : MulAut ↥Bs)⁻¹)) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hWM : GGIsWeylMatrix (CoxeterMatrix.F₄ : CoxeterMatrix (Fin 4)) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 4), by ext i j; rfl⟩))))
  have hMC : GGIntCartan CoxeterMatrix.F₄ (Tag.cartan .F4) := FrameRoute.ggIntCartan_F₄_tag
  have hind : LinearIndependent (ZMod p) h := by
    refine ggLeviDatum_linearIndependent_of_pair (C := Tag.cartan .F4) ?_ h α hpair
    rw [det_cartan_F4, Int.cast_one]
    exact isUnit_one
  obtain ⟨h', α', f', hlin', hrefl', hpair', hf', hclos', hind'⟩ :=
    ggLeviDatum_conj hlin hrefl hpair hf hclos u
  let ψ : Fin 4 → MulAut ↥Bs := fun i => (f u : MulAut ↥Bs) * φ i * (f u : MulAut ↥Bs)⁻¹
  have hS' : S = {0} ∨ S = {3} ∨ S = {0, 1} ∨ S = {2, 3} ∨ S = {0, 3} := by
    simpa [f4LeviDel] using hS
  rcases hS' with rfl | rfl | rfl | rfl | rfl
  ·
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 4 // j ≠ 0} => ψ j) := by
      rw [hJ, ← ggLeviDatum_range_ne_eq ψ (S := ({0} : Finset (Fin 4))) rfl]
    have hWMJ : GGIsWeylMatrix (parMatrix CoxeterMatrix.F₄ {j : Fin 4 | j ≠ 0}) :=
      ggLeviDatum_side_weyl (f4lv_parabolic_weyl (S := {0}) ⟨⟨1, by decide⟩⟩
        (ggDeletedConnectedS_of_reach (by decide +kernel)))
    exact Or.inl (ggResSideDatum_of_indep hp hWM hMC hlin' hrefl' hpair' (hind' hind) hf' hclos'
      0 hJ' hWMJ)
  ·
    have hJ' : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Fin 4 // j ≠ 3} => ψ j) := by
      rw [hJ, ← ggLeviDatum_range_ne_eq ψ (S := ({3} : Finset (Fin 4))) rfl]
    have hWMJ : GGIsWeylMatrix (parMatrix CoxeterMatrix.F₄ {j : Fin 4 | j ≠ 3}) :=
      ggLeviDatum_side_weyl (f4lv_parabolic_weyl (S := {3}) ⟨⟨0, by decide⟩⟩
        (ggDeletedConnectedS_of_reach (by decide +kernel)))
    exact Or.inl (ggResSideDatum_of_indep hp hWM hMC hlin' hrefl' hpair' (hind' hind) hf' hclos'
      3 hJ' hWMJ)
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.F₄ {j : Fin 4 | j ∉ ({0, 1} : Finset (Fin 4))}) :=
      f4lv_parabolic_weyl (S := {0, 1}) ⟨⟨2, by decide⟩⟩
        (ggDeletedConnectedS_of_reach (by decide +kernel))
    exact Or.inr (ggResLeviSideDatumLE3_of_indep hp hWM hMC hlin' hrefl' hpair' (hind' hind) hf'
      hclos' ({0, 1} : Finset (Fin 4)) (by decide) (by decide) hJ hWMJ)
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.F₄ {j : Fin 4 | j ∉ ({2, 3} : Finset (Fin 4))}) :=
      f4lv_parabolic_weyl (S := {2, 3}) ⟨⟨0, by decide⟩⟩
        (ggDeletedConnectedS_of_reach (by decide +kernel))
    exact Or.inr (ggResLeviSideDatumLE3_of_indep hp hWM hMC hlin' hrefl' hpair' (hind' hind) hf'
      hclos' ({2, 3} : Finset (Fin 4)) (by decide) (by decide) hJ hWMJ)
  ·
    have hWMJ : GGIsWeylMatrix
        (parMatrix CoxeterMatrix.F₄ {j : Fin 4 | j ∉ ({0, 3} : Finset (Fin 4))}) :=
      f4lv_parabolic_weyl (S := {0, 3}) ⟨⟨1, by decide⟩⟩
        (ggDeletedConnectedS_of_reach (by decide +kernel))
    exact Or.inr (ggResLeviSideDatumLE3_of_indep hp hWM hMC hlin' hrefl' hpair' (hind' hind) hf'
      hclos' ({0, 3} : Finset (Fin 4)) (by decide) (by decide) hJ hWMJ)

end Datum

end CFSG.StandardType

end
