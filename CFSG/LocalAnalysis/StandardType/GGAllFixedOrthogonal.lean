module

public import CFSG.LieType.SemisimpleCentralizers.OrthogonalCentralizerSolvable
public import CFSG.LocalAnalysis.StandardType.GGAllFixedLinear
public import CFSG.LocalAnalysis.StandardType.GGAllFixedTwA
public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.SemisimpleCentralizers
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

private theorem fixedSolvable_of_inner_isomorphism
    {S R : Type} [Group S] [Finite S] [Group R] {p : ℕ}
    (e : S ≃* R) (hZ : Subgroup.center S = ⊥)
    (hcent : ∀ A : Subgroup S, IsElemAbelian p A →
      CFSG.HasNormalPComplement p ↥(⁅Subgroup.centralizer (A : Set S),
        Subgroup.centralizer (A : Set S)⁆) →
      Group.IsSolvable ↥(Subgroup.centralizer (A : Set S)))
    (E : Subgroup (MulAut R)) (hEI : (E : Set (MulAut R)) ⊆ LargeEvenInnSet R)
    (hE : IsElemAbelian p E)
    (hNPC : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have hZR : Subgroup.center R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxS : e.symm x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      simpa using Subgroup.mem_center_iff.mp hx (e y)
    have hx1 : e.symm x = 1 := Subgroup.mem_bot.mp (hZ ▸ hxS)
    simpa using congrArg e hx1
  have hconj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZR
  have hErange : E ≤ (MulAut.conj : R →* MulAut R).range := fun a ha => hEI ha
  let A0 : Subgroup R := E.comap (MulAut.conj : R →* MulAut R)
  have hA0 : IsElemAbelian p A0 := hE.comap hconj
  have hA0map : A0.map (MulAut.conj : R →* MulAut R) = E :=
    Subgroup.map_comap_eq_self hErange
  have hfix : ggFixedSubgroup E = Subgroup.centralizer (A0 : Set R) := by
    rw [← hA0map, ggFixedSubgroup_map_conj_eq_centralizer]
  let A : Subgroup S := A0.map e.symm.toMonoidHom
  have hA : IsElemAbelian p A := hA0.map e.symm.toMonoidHom
  have hcentMap : (Subgroup.centralizer (A0 : Set R)).map e.symm.toMonoidHom =
      Subgroup.centralizer (A : Set S) :=
    CFSG.Glauberman.map_centralizer_eq_of_equiv e.symm A0
  let C0 := Subgroup.centralizer (A0 : Set R)
  let C := Subgroup.centralizer (A : Set S)
  let eC : C0 ≃* C :=
    (C0.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (MulEquiv.subgroupCongr hcentMap)
  have hNPC0 : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥C0) :=
    (congrArg (fun H : Subgroup R =>
      CFSG.HasNormalPComplement p ↥(_root_.commutator ↥H)) hfix).mp hNPC
  have hNPCmap : CFSG.HasNormalPComplement p
      ↥((_root_.commutator ↥C0).map eC.toMonoidHom) :=
    CFSG.hasNormalPComplement_of_equiv p
      ((_root_.commutator ↥C0).equivMapOfInjective eC.toMonoidHom eC.injective) hNPC0
  have hmapD : (_root_.commutator ↥C0).map eC.toMonoidHom = _root_.commutator ↥C := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr eC.surjective, ← commutator_def]
  have hNPCC : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥C) := by
    rwa [hmapD] at hNPCmap
  have hNPCamb : CFSG.HasNormalPComplement p ↥(⁅C, C⁆) := by
    have h := CFSG.hasNormalPComplement_of_equiv p
      ((_root_.commutator ↥C).equivMapOfInjective C.subtype C.subtype_injective) hNPCC
    rwa [Subgroup.map_subtype_commutator C] at h
  haveI : Group.IsSolvable ↥C := hcent A hA hNPCamb
  have hsolv0 : Group.IsSolvable ↥C0 :=
    Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
  change Group.IsSolvable ↥(Subgroup.centralizer (A0 : Set R)) at hsolv0
  rwa [← hfix] at hsolv0

theorem ggFixedSubgroup_isSolvable_of_recipe_omegaPlus
    {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K n)))))
    (hEI : (E : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K n))))) ⊆
      LargeEvenInnSet _) (hE : IsElemAbelian p E)
    (hNPC : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  let π := spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn)
  obtain ⟨hbij, hZ⟩ := OrthRest.spinPlus_bij (K := K) hn
  let e : spinGroup (quadPlus n K) ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K n)) := MulEquiv.ofBijective π hbij
  letI : Finite (spinGroup (quadPlus n K)) := Finite.of_injective e e.injective
  refine fixedSolvable_of_inner_isomorphism e hZ ?_ E hEI hE hNPC
  intro A hA hNPCA
  let πS : spinGroup (quadPlus n K) →* spinGroup (quadPlus n K) := MonoidHom.id _
  have hdiag : ∀ a ∈ A,
      GGPsiInnerDiag (plusDatum n K hn) πS a := by
    intro a ha
    refine ⟨a⁻¹, ⟨a⁻¹, rfl⟩, ?_⟩
    intro γ hγ
    exact ⟨1, one_mem _, fun z hz => by simp [πS]⟩
  have hrange : πS.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (fun x => ⟨x, rfl⟩)
  have hs := isSolvable_spinPlus_centralizer_of_hasNormalPComplement
    (ψ := πS) hn (by simp [πS]) hp hp2 hpK hA.isPGroup
    (fun a ha b hb => hA.comm ha hb) hdiag (by rw [hrange, top_inf_eq]; exact hNPCA)
  rw [hrange, top_inf_eq] at hs
  exact hs

theorem ggFixedSubgroup_isSolvable_of_recipe_omegaMinus
    {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))))
    (hEI : (E : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))) ⊆
      LargeEvenInnSet _) (hE : IsElemAbelian p E)
    (hNPC : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have hn : 4 ≤ m + 1 := by omega
  have hinj : Function.Injective (spinMatrix (quadMinus (m + 1) K b c)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero)
  let eSpin : spinGroup (quadMinus (m + 1) K b c) ≃*
      StatedOmega (StatedQuadMinus (m + 1) K b c) :=
    (MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (range_spinMatrix_quadMinus hn hirr))
  let e : spinGroup (quadMinus (m + 1) K b c) ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) :=
    (eSpin.trans (LayerCyc.largeEvenOmegaMinusEquiv m K b c).symm).trans
      (TableBOrth.projMkEquiv (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot b c))
  letI : Finite (spinGroup (quadMinus (m + 1) K b c)) := Finite.of_injective e e.injective
  have hZ := (OrthRest.spinMinus_bij (K := K) hn hirr).2
  refine fixedSolvable_of_inner_isomorphism e hZ ?_ E hEI hE hNPC
  intro A hA hNPCA
  let πS : spinGroup (quadMinus (m + 1) K b c) →*
      spinGroup (quadMinus (m + 1) K b c) := MonoidHom.id _
  have hdiag : ∀ a ∈ A,
      GGPsiInnerDiag (minusDatum (m + 1) hirr) πS a := by
    intro a ha
    refine ⟨a⁻¹, ⟨a⁻¹, rfl⟩, ?_⟩
    intro γ hγ
    exact ⟨1, one_mem _, fun z hz => by simp [πS]⟩
  have hrange : πS.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (fun x => ⟨x, rfl⟩)
  have hs := isSolvable_spinMinus_centralizer_of_hasNormalPComplement
    (ψ := πS) hirr hn (by simp [πS]) hp hp2 hpK hA.isPGroup
    (fun a ha b hb => hA.comm ha hb) hdiag (by rw [hrange, top_inf_eq]; exact hNPCA)
  rw [hrange, top_inf_eq] at hs
  exact hs

theorem largeEvenLabelAll_orthogonal_fullFixedSolvable
    {lab : LargeEvenLabel} (htag : lab.tag = .D ∨ lab.tag = .twD)
    (hr : 3 ≤ lab.rank) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  rcases htag with htag | htag
  · by_cases h3 : lab.rank = 3
    · have hQA : LargeEvenRawDatum ⟨.A, 3, lab.n⟩ Q := by
        simpa [LargeEvenRawDatum, htag, h3] using hQ
      have hres : LargeEvenRawDatum ⟨.A, 3, lab.n⟩ (fun R _ I F =>
          Q R I F ∧ ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
            IsElemAbelian p E →
            CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
              Group.IsSolvable ↥(ggFixedSubgroup E)) := by
        refine largeEvenRawDatum_mono ?_
          (largeEvenLabelAll_A_fullFixedSolvable (lab := ⟨.A, 3, lab.n⟩) rfl hp hpq Q hQA)
        rintro R _ I F ⟨hQ, hsolv⟩
        exact ⟨hQ, fun E hEI hE hNPC => hsolv E hEI hE.isPGroup hNPC⟩
      simpa [LargeEvenRawDatum, htag, h3] using hres
    have hr4 : 4 ≤ lab.rank := by omega
    have hrecipe : LargeEvenRecipeOmegaPlus lab.rank (2 ^ lab.n) Q := by
      simpa only [LargeEvenRawDatum, htag, if_neg (by omega : lab.rank ≠ 3)] using hQ
    obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hrecipe
    letI := fieldK
    letI := finiteK
    letI : Fintype K := Fintype.ofFinite K
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have hres : LargeEvenRecipeOmegaPlus lab.rank (2 ^ lab.n)
        (fun R _ I F => Q R I F ∧
          ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
            CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
              Group.IsSolvable ↥(ggFixedSubgroup E)) := by
      refine ⟨K, fieldK, finiteK, hK, hQK, ?_⟩
      intro E hEI hE hNPC
      exact ggFixedSubgroup_isSolvable_of_recipe_omegaPlus (by omega) hp hp2
        (by rwa [hK]) E hEI hE hNPC
    simpa only [LargeEvenRawDatum, htag, if_neg (by omega : lab.rank ≠ 3)] using hres
  · by_cases h3 : lab.rank = 3
    · exact largeEvenLabelAll_unitary_fullFixedSolvable (Or.inr ⟨htag, h3⟩) hp hp2 hpq Q hQ
    have hr4 : 4 ≤ lab.rank := by omega
    have hrecipe : LargeEvenRecipeOmegaMinus (lab.rank - 1) (2 ^ lab.n) Q := by
      simpa only [LargeEvenRawDatum, htag, if_neg (by omega : lab.rank ≠ 2),
        if_neg (by omega : lab.rank ≠ 3)] using hQ
    obtain ⟨K, fieldK, finiteK, hK, b, c, hirr, hQK⟩ := hrecipe
    letI := fieldK
    letI := finiteK
    letI : Fintype K := Fintype.ofFinite K
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have hres : LargeEvenRecipeOmegaMinus (lab.rank - 1) (2 ^ lab.n)
        (fun R _ I F => Q R I F ∧
          ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
            CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
              Group.IsSolvable ↥(ggFixedSubgroup E)) := by
      refine ⟨K, fieldK, finiteK, hK, b, c, hirr, hQK, ?_⟩
      intro E hEI hE hNPC
      exact ggFixedSubgroup_isSolvable_of_recipe_omegaMinus (by omega) hirr hp hp2
        (by rwa [hK]) E hEI hE hNPC
    simpa only [LargeEvenRawDatum, htag, if_neg (by omega : lab.rank ≠ 2),
      if_neg (by omega : lab.rank ≠ 3)] using hres

theorem isSolvable_inf_centralizer_of_orthogonal_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      ((lab.tag = .D ∨ lab.tag = .twD) ∧ 3 ≤ lab.rank) ∧
      p ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian p (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => ((lab.tag = .D ∨ lab.tag = .twD) ∧ 3 ≤ lab.rank) ∧
      p ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun _ _ hs => largeEvenLabelAll_orthogonal_fullFixedSolvable hs.1.1 hs.1.2 hp hp2 hs.2)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hN, hEI, hE⟩, hrow⟩ := hP
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end CFSG.StandardType
