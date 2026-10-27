module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Base
public import CFSG.LocalAnalysis.StandardType.GGIrred937CompLemmas
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4TorA
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BAssembly
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Toral
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Transfer
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTMain
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThreeCCentHolds
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem frameTorus_toral_F4_two
    (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) :
    ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ (TableBF4TwoTB.tE K).range,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup Tag.F4 K) :
        ModGL Tag.F4 K) * g ∈ torusGroup Tag.F4 (AlgebraicClosure K) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K' : Type := FiniteField.Extension K 2 2
  set L : Type := AlgebraicClosure K
  have h3 : 3 ∣ Nat.card K' - 1 :=
    TableBExcTwoFusion.three_dvd_natCard_ext_sub_one (K := K) hK
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K') (p := 3) h3
  haveI : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.of_finite K K'
  let φ : K' →+* L := (IsAlgClosed.lift (R := K) (S := K') (M := L)).toRingHom
  have hφι : φ.comp (algebraMap K K') = algebraMap K L := by
    ext x
    exact (IsAlgClosed.lift (R := K) (S := K') (M := L)).commutes x
  set G : adjointGroup Tag.F4 K' := ExcFrameIso.langEltF4 (K := K) hωo with hG
  refine ⟨TableBExcTwo.adjointMap Tag.F4 φ G, (TableBExcTwo.adjointMap Tag.F4 φ G).2, ?_⟩
  intro x hx
  have hrel :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1F4Conj.map_conj_range_tE_eq_torusPow (K := K) hK hωo
  have hmem : G⁻¹ * TableBExcTwo.adjointMap Tag.F4 (algebraMap K K') x * G ∈
      TableBExc.torusPow Tag.F4 K' 3 := by
    rw [← hrel]
    exact ⟨TableBExcTwo.adjointMap Tag.F4 (algebraMap K K') x, ⟨x, hx, rfl⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hG]⟩
  have hmemT : ((G⁻¹ * TableBExcTwo.adjointMap Tag.F4 (algebraMap K K') x * G :
      adjointGroup Tag.F4 K') : ModGL Tag.F4 K') ∈ torusGroup Tag.F4 K' :=
    (TableBExc.mem_torusPow.1 hmem).1
  have htorus : baseChangeGL φ ((G⁻¹ * TableBExcTwo.adjointMap Tag.F4 (algebraMap K K') x * G :
      adjointGroup Tag.F4 K') : ModGL Tag.F4 K') ∈ torusGroup Tag.F4 L :=
    CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup φ hmemT
  have htorus' : (baseChangeGL φ (G : ModGL Tag.F4 K'))⁻¹ *
      baseChangeGL (algebraMap K L) ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) *
      baseChangeGL φ (G : ModGL Tag.F4 K') ∈ torusGroup Tag.F4 L := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, TableBExcTwo.coe_adjointMap,
      map_inv, map_mul,
      CFSG.SeitzReduction.F4Pilot.baseChangeGL_baseChangeGL, hφι]
      using htorus
  refine (show (TableBExcTwo.adjointMap Tag.F4 φ G : ModGL Tag.F4 L)⁻¹ *
      baseChangeGL (algebraMap K L) ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) *
      (TableBExcTwo.adjointMap Tag.F4 φ G : ModGL Tag.F4 L) ∈
        torusGroup Tag.F4 L from ?_)
  rw [TableBExcTwo.coe_adjointMap]
  exact htorus'

theorem f4_toral_of_fixCompCyclic
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hq : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup Tag.F4 K)), x ^ 3 = 1 → x ∈ E)
    (e : adjointGroup Tag.F4 K) (he : e ∈ E) (he1 : e ≠ 1)
    (hfix : GGFixCompCyclic 3 (MulAut.conj e)) :
    ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup Tag.F4 K) :
        ModGL Tag.F4 K) * g ∈ torusGroup Tag.F4 (AlgebraicClosure K) := by
  by_cases hq2 : 2 < Nat.card K
  · exact toral_of_fixCompCyclic f4ThreeKernelDichotomy_holds f4ThreeEighteenToral_holds
      f4ThreeA2A2TwoComponents_holds K hq hq2 E hE e he he1 hfix
  · have hK : Nat.card K = 2 := by
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    classical
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    by_cases hconj : ∃ c : adjointGroup Tag.F4 K,
        E = (TableBF4TwoTB.tE K).range.map (MulAut.conj c).toMonoidHom
    · obtain ⟨c, hc⟩ := hconj
      obtain ⟨g, hg, hgtor⟩ := frameTorus_toral_F4_two K hK
      refine ⟨baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.F4 K) * g,
        mul_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ c.2) hg, ?_⟩
      intro x hx
      rw [hc] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rcases hyx with rfl
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        map_mul, map_inv]
      have hY := hgtor y hy
      convert hY using 1
      group
    · exfalso
      have hS : TableBF4TwoTB.GGF4TwoNonToralSolv K :=
        F4TwoNonToral.ggF4TwoNonToralSolvInput_of_cent
          SmallExc.F4Two.ggF4TwoThreeCCentInput_holds K hK
      have hSC' : ∀ g : adjointGroup Tag.F4 K, g ^ 3 = 1 →
          (∀ e ∈ E, g * e = e * g) → g ∈ E := by
        intro g hg3 hcomm
        exact hSC g (by
          rw [Subgroup.mem_centralizer_iff]
          intro e he
          exact (hcomm e he).symm) hg3
      have hsolv : Group.IsSolvable
          (Subgroup.centralizer ({e} : Set (adjointGroup Tag.F4 K))) :=
        hS E hE hcard hSC' hconj e he he1
      have hgf : ggFix (MulAut.conj e) =
          Subgroup.centralizer ({e} : Set (adjointGroup Tag.F4 K)) := by
        ext x
        rw [mem_ggFix, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
        constructor
        · intro h
          calc x * e = (e * x * e⁻¹) * e := by rw [h]
            _ = e * x := by group
        · intro h
          calc e * x * e⁻¹ = (e * x) * e⁻¹ := by group
            _ = (x * e) * e⁻¹ := by rw [h]
            _ = x := by group
      have hs : IsSolvable (ggFix (MulAut.conj e)) := by rw [hgf]; exact hsolv
      exact (not_ggFixCompCyclic_of_solvable (MulAut.conj e) hs) hfix

theorem f4CompIrred_holds
    (K : Type) [Field K] [Finite K] [CharP K 2] (hpq : 3 ∣ Nat.card K + 1) :
    ∀ E : Subgroup (TableBF4.RecipeGroup K), IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      (∀ g : TableBF4.RecipeGroup K, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E) →
      (∃ e ∈ E, e ≠ 1 ∧ GGFixCompCyclic 3 (MulAut.conj e : MulAut (TableBF4.RecipeGroup K))) →
      GGWeylIrred E := by
  intro E hE hcard hSC hline
  classical
  let f : TableBF4.RecipeGroup K ≃* adjointGroup Tag.F4 K := TableBF4.recipeEquiv K
  let E' : Subgroup (adjointGroup Tag.F4 K) := E.map f.toMonoidHom
  have hE' : IsElemAbelian 3 E' := TableB.isElemAbelian_map hE f.toMonoidHom
  have hcard' : 3 ^ 3 ≤ Nat.card E' := by
    rw [Subgroup.card_map_of_injective f.injective]
    exact hcard
  have hSC' : ∀ x ∈ Subgroup.centralizer (E' : Set (adjointGroup Tag.F4 K)),
      x ^ 3 = 1 → x ∈ E' := by
    intro x hx hx3
    have hx' : f.symm x ∈ E := by
      refine hSC (f.symm x) ?_ ?_
      · intro e he
        have h := (Subgroup.mem_centralizer_iff.1 hx) (f e)
          (Subgroup.mem_map_of_mem f.toMonoidHom he)
        apply f.injective
        rw [map_mul, map_mul, f.apply_symm_apply]
        exact h.symm
      · have hmap : (f.symm x) ^ 3 = f.symm (x ^ 3) := (map_pow f.symm x 3).symm
        rw [hmap, hx3, map_one]
    exact Subgroup.mem_map.mpr ⟨f.symm x, hx', f.apply_symm_apply x⟩
  obtain ⟨e, he, he1, hfix⟩ := hline
  have he' : f e ∈ E' := Subgroup.mem_map_of_mem f.toMonoidHom he
  have he1' : f e ≠ 1 := fun h => he1 (f.injective (by rw [h, map_one]))
  have hfix' : GGFixCompCyclic 3 (MulAut.conj (f e)) :=
    (ggFixCompCyclic_conj_of_mulEquiv f e).mp hfix
  have htor := f4_toral_of_fixCompCyclic K hpq E' hE' hcard' hSC' (f e) he' he1' hfix'
  have hwirr := f4_weylIrred_of_toral K hpq E' hE' htor hcard' hSC'
  have hthis := ggWeylIrred_map f.symm hwirr
  have hEE : (E.map f.toMonoidHom).map f.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hcomp : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [hcomp, Subgroup.map_id]
  rwa [hEE] at hthis

theorem ggNbrKGF4ThreeAddSC_holds :
    GGNbrKGF4ThreeAddSC := by
  intro K _ _ _ hpq
  haveI : Finite (adjointGroup Tag.F4 K) := Subtype.finite
  haveI : Finite (TableBF4.RecipeGroup K) :=
    Finite.of_equiv (adjointGroup Tag.F4 K) (TableBF4.recipeEquiv K).toEquiv.symm
  exact ggTorusNbrSCrComp_of_compIrred (TableBF4.center_recipeGroup_eq_bot K)
    (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ)
    (ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num))
    (f4CompIrred_holds K hpq)

end Irred937

end CFSG.StandardType

end
