module

public import CFSG.LieType.SemisimpleCentralizers.SymplecticCentralizerSolvable
public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LieType.SemisimpleCentralizers

theorem ggFixedSubgroup_isSolvable_of_recipe_symplectic
    {n : ℕ} [NeZero n] {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K n))))
    (hEI : (E : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K n)))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K n)) (LargeEvenGSpSet K n))
    (hE : IsPGroup p E)
    (hNPC : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  let R := LargeEvenProj (LargeEvenSpGroup K n)
  have hconj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.mulAutConj_injective_of_center_eq_bot TableBSymp.center_spProj_eq_bot
  have hErange : E ≤ (MulAut.conj : R →* MulAut R).range :=
    fun a ha => TableBSymp.sp_I_subset_inn (hEI ha)
  let A0 : Subgroup R := E.comap (MulAut.conj : R →* MulAut R)
  have hA0 : IsPGroup p A0 := hE.comap_of_injective _ hconj
  have hA0map : A0.map (MulAut.conj : R →* MulAut R) = E :=
    Subgroup.map_comap_eq_self hErange
  have hfix : ggFixedSubgroup E = Subgroup.centralizer (A0 : Set R) := by
    rw [← hA0map, ggFixedSubgroup_map_conj_eq_centralizer]
  let φ : R ≃* StatedSp n K := TableBSymp.spProjEquivSp
  let A : Subgroup (StatedSp n K) := A0.map φ.toMonoidHom
  have hA : IsPGroup p A := hA0.map φ.toMonoidHom
  have hcent : (Subgroup.centralizer (A0 : Set R)).map φ.toMonoidHom =
      Subgroup.centralizer (A : Set (StatedSp n K)) :=
    CFSG.Glauberman.map_centralizer_eq_of_equiv φ A0
  let C0 := Subgroup.centralizer (A0 : Set R)
  let C := Subgroup.centralizer (A : Set (StatedSp n K))
  let eC : C0 ≃* C :=
    (C0.equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hcent)
  have hNPC0 : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥C0) := by
    exact (congrArg (fun H : Subgroup R =>
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
  haveI : Group.IsSolvable ↥C :=
    isSolvable_statedSp_centralizer_of_hasNormalPComplement hp hp2 hpK hA hNPCamb
  have hsolv0 : Group.IsSolvable ↥C0 :=
    Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
  change Group.IsSolvable ↥(Subgroup.centralizer (A0 : Set R)) at hsolv0
  rwa [← hfix] at hsolv0

theorem largeEvenLabelAll_symplectic_fullFixedSolvable
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .B ∨ lab.tag = .C)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsPGroup p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  have hr : 2 ≤ lab.rank := by
    rcases htag with htag | htag
    · have h := hlab.2
      rw [htag] at h
      exact h.1
    · have h := hlab.2
      rw [htag] at h
      exact h.1
  haveI : NeZero lab.rank := ⟨by omega⟩
  have hrecipe : LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false Q := by
    rcases htag with htag | htag <;> simpa only [LargeEvenRawDatum, htag] using hQ
  obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hrecipe
  letI := fieldK
  letI := finiteK
  letI : Fintype K := Fintype.ofFinite K
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hres : LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false
      (fun R _ I F => Q R I F ∧
        ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsPGroup p E →
          CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
            Group.IsSolvable ↥(ggFixedSubgroup E)) := by
    refine ⟨K, fieldK, finiteK, hK, hQK, ?_⟩
    intro E hEI hE hNPC
    exact ggFixedSubgroup_isSolvable_of_recipe_symplectic hp hp2 (by rwa [hK]) E hEI hE hNPC
  rcases htag with htag | htag <;> simpa only [LargeEvenRawDatum, htag] using hres

theorem isSolvable_inf_centralizer_of_symplectic_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsPGroup p (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsPGroup p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
          Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab hlab hs => largeEvenLabelAll_symplectic_fullFixedSolvable hlab hs.1 hp hp2 hs.2)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hN, hEI, hE⟩, hrow⟩ := hP
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end CFSG.StandardType
