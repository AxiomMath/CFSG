module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneFixed
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticComponent
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticComponentBounds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightSpGood
public import CFSG.LieType.CurtisTits.Recognition

private theorem sympA6_su_not_a6 {m q : ℕ} {E : Type} [Field E] [Fintype E]
    (hcard : Fintype.card E = q ^ 2) (hm : 3 ≤ m)
    (h : Nonempty ((↥(CFSG.Open.StatedSU m q E) ⧸
      Subgroup.center ↥(CFSG.Open.StatedSU m q E)) ≃* alternatingGroup (Fin 6))) : False :=
  (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suAltSixFacts_holds E m q hcard hm).false h.some

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG.Open CFSG.RankThree.PartOne CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.StandardType.QTwoSymplecticCav
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.GLTheoremA.T173O
open CFSG.ClassicalGroups.UnitaryFlag
open Polynomial

open scoped commutatorElement

private theorem sympA6_unitary_not_a6
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) {r : ℕ} [NeZero r]
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hself : reciprocalPolynomial (X ^ 2 + X + 1 : K[X]) = X ^ 2 + X + 1)
    (hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (spEnd x))
    {J : Subgroup (StatedProj (StatedSp r K))}
    (hQ : CFSG.IsQuasisimple ↥⁅spSupported x {X ^ 2 + X + 1},
      spSupported x {X ^ 2 + X + 1}⁆)
    (hJeq : J = (⁅spSupported x {X ^ 2 + X + 1},
      spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))
    (hA6 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6))) : False := by
  classical
  have hr : 1 ≤ r := Nat.pos_of_neZero r
  haveI : Fintype K := Fintype.ofFinite K
  have blocks := spPrimaryBlocks_of_order_three hK hr hx3 hx1
  let fac : primaryFactors (spEnd x) := ⟨X ^ 2 + X + 1, hmem⟩
  have hfac : (fac : K[X]) = X ^ 2 + X + 1 := rfl
  haveI : Fact (Irreducible (fac : K[X])) := ⟨irreducible_of_mem_primaryFactors fac.2⟩
  have hdn : (fac : K[X]) ≠ X - 1 := by
    rw [hfac]
    exact CFSG.HardMathSupport.Dickson.Bal207.X_sq_add_X_add_one_ne
  have hself' : reciprocalPolynomial (fac : K[X]) = fac := by
    rw [hfac]; exact hself
  obtain ⟨d, hdeg, hpd, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ, hφ⟩ :=
    (blocks.selfDual fac hdn hself').exists_half
  let g : ℕ := 1 * d
  have hm4 : 4 ≤ primaryMultiplicity (spEnd x) (X ^ 2 + X + 1) :=
    movingMultiplicity_ge_four_of_quasisimple_derived hK hr hx3 hx1 hQ
  have hm3 : 3 ≤ primaryMultiplicity (spEnd x) (X ^ 2 + X + 1) := by omega
  have hfing : Module.finrank (AdjoinRoot (fac : K[X]))
      (primaryComponent (spEnd x) (fac : K[X])) =
      primaryMultiplicity (spEnd x) (X ^ 2 + X + 1) := by
    rw [Module.finrank_eq_card_basis e, Fintype.card_fin]
  have hm1 : 1 ≤ Module.finrank (AdjoinRoot (fac : K[X]))
      (primaryComponent (spEnd x) (fac : K[X])) := by rw [hfing]; omega
  haveI : Finite (AdjoinRoot (fac : K[X])) := hE.finite
  haveI : Fintype (AdjoinRoot (fac : K[X])) := Fintype.ofFinite _
  have hEcard : Fintype.card (AdjoinRoot (fac : K[X])) = (2 ^ g) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hE.card_eq_sq
  have hnq : (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1), 2 ^ g) ≠ (3, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  have hSUdata := suFactorFacts_holds (AdjoinRoot (fac : K[X]))
    (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1)) (2 ^ g) hEcard hm3 hnq
  obtain ⟨e1⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE e
    (G := (1 : Matrix (Fin (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1)))
      (Fin (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1))) (AdjoinRoot (fac : K[X]))))
    (fun i j => by rw [he i j, Matrix.one_apply])
  have hSUeq : StatedSU (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1)) (2 ^ g)
      (AdjoinRoot (fac : K[X])) =
      gramSU hE (1 : Matrix (Fin (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1)))
        (Fin (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1))) (AdjoinRoot (fac : K[X]))) :=
    unitarySU_eq_gramSU hE _
  let eSU : ↥(sesqSpecialUnitaryGroup Hf) ≃*
      ↥(StatedSU (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1)) (2 ^ g)
        (AdjoinRoot (fac : K[X]))) :=
    e1.trans (MulEquiv.subgroupCongr hSUeq.symm)
  let A : Subgroup (StatedSp r K) := spSupported x {X ^ 2 + X + 1}
  obtain ⟨ψ, hψi, hψrange⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.H1431c.lieSEightSp_exists_range_of_special_equiv
      (G := StatedSp r K) hE hHf hHfl hm1 φ hSUdata.perfect eSU
  let XU : Type := ↥(StatedSU (primaryMultiplicity (spEnd x) (X ^ 2 + X + 1)) (2 ^ g)
    (AdjoinRoot (fac : K[X])))
  let gX : XU →* ↥⁅A, A⁆ := ψ.codRestrict ⁅A, A⁆ (fun y => by
    rw [← hψrange]; exact ⟨y, rfl⟩)
  have hgXi : Function.Injective gX := fun a b h => hψi (Subtype.ext_iff.mp h)
  have hgXs : Function.Surjective gX := by
    intro b
    have hb : (b : StatedSp r K) ∈ ψ.range := by rw [hψrange]; exact b.2
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, Subtype.ext ha⟩
  let eA : XU ≃* ↥⁅A, A⁆ := MulEquiv.ofBijective gX ⟨hgXi, hgXs⟩
  have hproj_inj : Function.Injective (proj r K) :=
    symplectic_proj_injective_of_card_two hK r
  let eJ : ↥J ≃* ↥⁅A, A⁆ :=
    (MulEquiv.subgroupCongr hJeq).trans
      (((⁅A, A⁆).equivMapOfInjective (proj r K) hproj_inj).symm)
  have hquotA6 : Nonempty (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆ ≃*
      alternatingGroup (Fin 6)) :=
    ⟨(QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥⁅A, A⁆) eJ
        (Subgroup.map_center_eq eJ)).symm.trans hA6.some⟩
  have hquotX : Nonempty (XU ⧸ Subgroup.center XU ≃* alternatingGroup (Fin 6)) :=
    ⟨(QuotientGroup.congr (Subgroup.center XU) (Subgroup.center ↥⁅A, A⁆) eA
        (Subgroup.map_center_eq eA)).trans hquotA6.some⟩
  exact sympA6_su_not_a6 (E := AdjoinRoot (fac : K[X]))
    (m := primaryMultiplicity (spEnd x) (X ^ 2 + X + 1)) (q := 2 ^ g) hEcard hm3 hquotX

private theorem sympA6_fixed_dim_four
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) {r : ℕ} [NeZero r]
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {J : Subgroup (StatedProj (StatedSp r K))}
    (hQ : CFSG.IsQuasisimple ↥⁅spFixedFactor x, spFixedFactor x⁆)
    (hJeq : J = (⁅spFixedFactor x, spFixedFactor x⁆).map (proj r K))
    (hA6 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6))) :
    spFixedDim x = 4 := by
  classical
  have hr : 1 ≤ r := Nat.pos_of_neZero r
  haveI : Fintype K := Fintype.ofFinite K
  have blocks := spPrimaryBlocks_of_order_three hK hr hx3 hx1
  have h4 : 4 ≤ spFixedDim x :=
    fixedDim_ge_four_of_quasisimple_derived_fixed hK hr hx3 hx1 hQ
  by_contra hne
  have hmemFix : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) :=
    X_sub_one_mem_primaryFactors x (by omega)
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmemFix
  let B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1))
  have hB : B.IsAlt := fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    exists_mulEquiv_sesqUnitaryGroup_statedSp (B := B) hB blocks.fixed_nondegenerate
  let eF : ↥(spFixedFactor x) ≃* ↥(StatedSp s K) := φ.trans e
  have hs3 : 3 ≤ s := by
    have hd : spFixedDim x = 2 * s := hs
    omega
  have hlist : SpFixedListed x := by
    refine ⟨?_, ?_⟩
    · have hd : spFixedDim x = 2 * s := hs
      omega
    · have hd : spFixedDim x = 2 * s := hs
      rintro ⟨h2, -⟩
      omega
  have h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2) := fun h => hne h.1
  have hFq : CFSG.IsQuasisimple ↥(spFixedFactor x) :=
    spFixedFactor_isQuasisimple (ℓ := 2) (f := 1) (p := 3) (by rw [hK]; norm_num)
      Nat.prime_two (by norm_num) blocks hlist h42
  have hF'eq : (⁅spFixedFactor x, spFixedFactor x⁆ : Subgroup (StatedSp r K)) =
      spFixedFactor x := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hFq
      ((⁅spFixedFactor x, spFixedFactor x⁆).subgroupOf (spFixedFactor x)) with hle | htop
    · exfalso
      have hcomm : ∀ a b : ↥⁅spFixedFactor x, spFixedFactor x⁆, a * b = b * a := by
        intro a b
        apply Subtype.ext
        have ha : (⟨a.1, Subgroup.commutator_le_self (spFixedFactor x) a.2⟩ :
            ↥(spFixedFactor x)) ∈ Subgroup.center ↥(spFixedFactor x) := hle a.2
        have hb : (⟨b.1, Subgroup.commutator_le_self (spFixedFactor x) b.2⟩ :
            ↥(spFixedFactor x)) ∈ Subgroup.center ↥(spFixedFactor x) := hle b.2
        have h := (Subgroup.mem_center_iff.mp ha)
          (⟨b.1, Subgroup.commutator_le_self (spFixedFactor x) b.2⟩ : ↥(spFixedFactor x))
        simpa using (congrArg Subtype.val h).symm
      haveI : Group.IsSolvable ↥⁅spFixedFactor x, spFixedFactor x⁆ :=
        Group.isSolvable_of_comm hcomm
      haveI : Group.IsPerfect ↥⁅spFixedFactor x, spFixedFactor x⁆ := hQ.1
      haveI : Nontrivial ↥⁅spFixedFactor x, spFixedFactor x⁆ := by
        obtain ⟨a, b, hab⟩ := hQ.2.2
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        exact ⟨a, b, fun h => hab (by rw [h])⟩
      exact Group.IsPerfect.not_isSolvable ↥⁅spFixedFactor x, spFixedFactor x⁆ inferInstance
    · exact le_antisymm (Subgroup.commutator_le_self (spFixedFactor x))
        (Subgroup.subgroupOf_eq_top.mp htop)
  have hproj_inj : Function.Injective (proj r K) :=
    symplectic_proj_injective_of_card_two hK r
  let eJ : ↥J ≃* ↥⁅spFixedFactor x, spFixedFactor x⁆ :=
    (MulEquiv.subgroupCongr hJeq).trans
      (((⁅spFixedFactor x, spFixedFactor x⁆).equivMapOfInjective (proj r K) hproj_inj).symm)
  have hquotA6 : Nonempty (↥⁅spFixedFactor x, spFixedFactor x⁆ ⧸
      Subgroup.center ↥⁅spFixedFactor x, spFixedFactor x⁆ ≃* alternatingGroup (Fin 6)) :=
    ⟨(QuotientGroup.congr (Subgroup.center ↥J)
        (Subgroup.center ↥⁅spFixedFactor x, spFixedFactor x⁆) eJ
        (Subgroup.map_center_eq eJ)).symm.trans hA6.some⟩
  rw [hF'eq] at hquotA6
  have hquotS : Nonempty ((↥(StatedSp s K) ⧸ Subgroup.center ↥(StatedSp s K)) ≃*
      alternatingGroup (Fin 6)) :=
    ⟨(QuotientGroup.congr (Subgroup.center ↥(spFixedFactor x))
        (Subgroup.center ↥(StatedSp s K)) eF (Subgroup.map_center_eq eF)).symm.trans
      hquotA6.some⟩
  exact (spAltSixFacts_holds K s (by omega) (by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega)).false hquotS.some

theorem sp_a6_component_position
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) {r : ℕ} [NeZero r]
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {J : Subgroup (StatedProj (StatedSp r K))}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj r K x))))
    (hA6 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6))) :
    spFixedDim x = 4 ∧ J = (⁅spFixedFactor x, spFixedFactor x⁆).map (proj r K) := by
  classical
  have hr : 1 ≤ r := Nat.pos_of_neZero r
  haveI : Fintype K := Fintype.ofFinite K
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have blocks := spPrimaryBlocks_of_order_three hK hr hx3 hx1
  have hsq := (CFSG.RankThree.Classical.altPrimaryData_spLin h3K hx3).squarefree
  haveI : Finite (CFSG.RankThree.Classical.reciprocalOrbits
      (CFSG.RankThree.Classical.spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  obtain ⟨O, hQO, hJeq⟩ :=
    components_conj_of_orbit_family (proj r K)
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective hZc x
      (fun O : CFSG.RankThree.Classical.reciprocalOrbits
          (CFSG.RankThree.Classical.spEnd x) =>
        CFSG.RankThree.Classical.spSupported x (O : Set K[X]))
      (fun i j hij a ha b hb =>
        hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin (fun O => quasisimple_or_solvable_spSupported (by norm_num) (by norm_num)
        hsq blocks O) J hJ
  obtain ⟨Oset, h, hh, rfl⟩ := O
  have hrecip : reciprocalPolynomial h = h := by
    by_cases h1 : h = X - 1
    · subst h1
      exact CFSG.RankThree.PartOne.KCSpIsotypic.reciprocalPolynomial_X_sub_one
    · have hq : h = X ^ 2 + X + 1 := eq_quad_of_mem_primaryFactors hK hx3 hh h1
      subst hq
      exact CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one
  have hset : ({h, reciprocalPolynomial h} : Set K[X]) = ({h} : Set K[X]) := by
    rw [hrecip, Set.pair_eq_singleton]
  have hQO' : CFSG.IsQuasisimple ↥⁅spSupported x ({h} : Set K[X]),
      spSupported x ({h} : Set K[X])⁆ := by
    change CFSG.IsQuasisimple ↥⁅spSupported x ({h, reciprocalPolynomial h} : Set K[X]),
      spSupported x ({h, reciprocalPolynomial h} : Set K[X])⁆ at hQO
    rw [hset] at hQO
    exact hQO
  have hJeq' : J = (⁅spSupported x ({h} : Set K[X]), spSupported x ({h} : Set K[X])⁆).map
      (proj r K) := by
    change J = (⁅spSupported x ({h, reciprocalPolynomial h} : Set K[X]),
      spSupported x ({h, reciprocalPolynomial h} : Set K[X])⁆).map (proj r K) at hJeq
    rw [hset] at hJeq
    exact hJeq
  by_cases h1 : h = X - 1
  · subst h1
    have hQ' : CFSG.IsQuasisimple ↥⁅spFixedFactor x, spFixedFactor x⁆ := by
      change CFSG.IsQuasisimple ↥⁅spSupported x ({X - 1} : Set K[X]),
        spSupported x ({X - 1} : Set K[X])⁆
      exact hQO'
    have hJ' : J = (⁅spFixedFactor x, spFixedFactor x⁆).map (proj r K) := by
      change J = (⁅spSupported x ({X - 1} : Set K[X]),
        spSupported x ({X - 1} : Set K[X])⁆).map (proj r K)
      exact hJeq'
    exact ⟨sympA6_fixed_dim_four hK hx3 hx1 hQ' hJ' hA6, hJ'⟩
  · have hq : h = X ^ 2 + X + 1 := eq_quad_of_mem_primaryFactors hK hx3 hh h1
    subst hq
    exact (sympA6_unitary_not_a6 hK hx3 hx1 hrecip hh hQO' hJeq' hA6).elim

end CFSG.StandardType.S2MathAs4B2der1822

end
