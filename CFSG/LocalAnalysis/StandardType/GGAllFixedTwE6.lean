module

public import CFSG.LocalAnalysis.StandardType.GGAllFixedE6Three
public import CFSG.LocalAnalysis.StandardType.GGFamCentralizerSolvable
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourModel
public import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreFrame
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd
public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.RankThree.PartOne.KE6.EqpA24
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldDescent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.ExcFramesHalf
open scoped commutatorElement



theorem twE6_full_toral_fixed_solvable
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hpq : p ∣ (2 ^ n) ^ 2 - 1)
    (A : Subgroup (ModGL .E6 K)) (hAI : A ≤ twistedE6InndiagGL K σ)
    (hAp : ∀ x ∈ A, x ^ p = 1)
    (hT : SCFourCover.E6AdToral (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))))
    (hNPC : CFSG.HasNormalPComplement p
      ↥(_root_.commutator ↥(twistedE6RootGroup K σ ⊓
        Subgroup.centralizer (A : Set (ModGL .E6 K))))) :
    Group.IsSolvable ↥(twistedE6RootGroup K σ ⊓
      Subgroup.centralizer (A : Set (ModGL .E6 K))) := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := by
    intro c
    simp only [Fr, iterateFrobenius_def]
  have hXR : A.map (baseChangeGL (algebraMap K L)) ≤
      CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.Rgrp L Fr := by
    rintro _ ⟨a, ha, rfl⟩
    have hfix := map_twistedE6InndiagGL_le_twistedFixedGroup
      Nat.prime_two hn hK σ hσ Fr hFr ⟨a, hAI ha, rfl⟩
    exact hfix
  obtain ⟨v, g0, hg0, hlang, hA⟩ :=
    SCFourCover.e6AdLangToral_of_toral hn Fr hFr hXR hT
  obtain ⟨S, hSD, hΓ, -, -⟩ :=
    TwE6D5Core.exists_langSetup_ofTwist_twE6_spec σ hK hσ
      (ringChar.eq K 2) hFr hg0 hlang
  let f : ModGL .E6 K →* ModGL .E6 L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K L))
  have hf : Function.Injective f :=
    (MulAut.conj g0⁻¹).injective.comp (baseChangeGL_injective (algebraMap K L))
  have hGT : (twistedE6RootGroup K σ).map f = S.Γ := by
    have hΓ' : (f.comp (twistedE6RootGroup K σ).subtype).range = S.Γ := by
      have hc : f.comp (twistedE6RootGroup K σ).subtype =
          (MulAut.conj g0⁻¹).toMonoidHom.comp
            ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) := by
        ext z
        rfl
      rw [hc]
      with_unfolding_all exact hΓ
    calc
      (twistedE6RootGroup K σ).map f =
          (f.comp (twistedE6RootGroup K σ).subtype).range := by
        exact ((MonoidHom.range_comp f (twistedE6RootGroup K σ).subtype).trans
          (congrArg (Subgroup.map f) (Subgroup.range_subtype _))).symm
      _ = S.Γ := hΓ'
  have hmem : ∀ a : A, f a ∈ S.D.torus := by
    intro a
    have ha := hA _ (Subgroup.mem_map_of_mem _ a.2)
    obtain ⟨t, ht, heq⟩ := ha
    have hfa : f a = t := by
      change g0⁻¹ * baseChangeGL (algebraMap K L) a * g0 = t
      rw [← heq]
      change g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t
      group
    rw [hfa, hSD]
    exact ht
  choose afam hafam using fun a : A =>
    exists_rootDiagUnit_eq_of_mem_torusGroup
      (mem_twistedTorusOf.1 (by
        have h := hmem a
        rw [hSD] at h
        exact h)).1
  have haf : ∀ a : A, rootDiagUnit .E6 (afam a) = f a := fun a => (hafam a).symm
  have hTfam : ∀ a, rootDiagUnit .E6 (afam a) ∈ S.D.torus := by
    intro a
    rw [haf]
    exact hmem a
  have hpfam : ∀ a j, afam a j ^ p = 1 := by
    intro a j
    have hpow : (afam a) ^ p = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective
      rw [← rootDiagUnit_pow, rootDiagUnit_one, haf, ← map_pow, hAp a a.2, map_one]
    exact congrFun hpow j
  let C : Subgroup (ModGL .E6 K) := twistedE6RootGroup K σ ⊓
    Subgroup.centralizer (A : Set (ModGL .E6 K))
  let H : Subgroup (ModGL .E6 L) := S.Γ ⊓
    Subgroup.centralizer (Set.range fun a : A => rootDiagUnit .E6 (afam a))
  have hCH : C.map f = H := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hGT ▸ Subgroup.mem_map_of_mem f hz.1, ?_⟩
      change f z ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, rfl⟩
      change rootDiagUnit .E6 (afam a) * f z = f z * rootDiagUnit .E6 (afam a)
      rw [haf, ← map_mul, ← map_mul]
      exact congrArg f (Subgroup.mem_centralizer_iff.1 hz.2 a a.2)
    · intro hy
      obtain ⟨z, hz, rfl⟩ := hGT.symm ▸ hy.1
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      change z ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      apply hf
      rw [map_mul, map_mul]
      have h := Subgroup.mem_centralizer_iff.1 hy.2 _ ⟨⟨a, ha⟩, rfl⟩
      simpa only [haf] using h
  let e : ↥C ≃* ↥H := (C.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hCH)
  have hNPC_H : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥H) :=
    CFSG.hasNormalPComplement_of_equiv p e.commutatorCongr hNPC
  let eD : ↥(_root_.commutator ↥H) ≃* ↥⁅H, H⁆ :=
    ((_root_.commutator ↥H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator H))
  have hNPC_amb : CFSG.HasNormalPComplement p ↥⁅H, H⁆ :=
    CFSG.hasNormalPComplement_of_equiv p eD hNPC_H
  have hpqS : p ∣ S.D.q ^ 2 - 1 := by
    rw [hSD]
    exact hpq
  have hsolv : Group.IsSolvable ↥H :=
    TableCRes.isSolvable_familyToral (τ := .E6) (L := L) (p₀ := 5) (p := p) S
      (Or.inr (Or.inl rfl)) hp hpodd afam hTfam hpfam hpqS hNPC_amb
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem twE6_full_nontorsion_fixed_solvable
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3)
    (hpq : p ∣ (2 ^ n) ^ 2 - 1)
    (A : Subgroup (ModGL .E6 K)) (hAI : A ≤ twistedE6InndiagGL K σ)
    (hA : IsElemAbelian p A)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(_root_.commutator ↥(twistedE6RootGroup K σ ⊓
        Subgroup.centralizer (A : Set (ModGL .E6 K))))) :
    Group.IsSolvable ↥(twistedE6RootGroup K σ ⊓
      Subgroup.centralizer (A : Set (ModGL .E6 K))) := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL .E6 K) := finite_modGL
  let A' := A.map (baseChangeGL (algebraMap K L))
  have : Finite ↥A' := Finite.of_equiv A
    (A.equivMapOfInjective _ (baseChangeGL_injective (algebraMap K L))).toEquiv
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have hA' : A' ≤ adjointGroup .E6 L := by
    rintro _ ⟨a, ha, rfl⟩
    exact (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ
      (iterateFrobenius L 2 n) (fun c => by simp only [L, iterateFrobenius_def])
      ⟨a, hAI ha, rfl⟩).1
  have hT : IsToralSubgroup .E6 L A' :=
    LieCore.isToralSubgroup_of_nonTorsion hp hp2 (fun _ => hp3)
      (by intro h; cases h) hp2.symm (CFSG.RankThree.PartOne.KE6.eqp_halg K L)
      hA' (by infer_instance) (hA.map _)
  have hT' : SCFourCover.E6AdToral A' := by
    obtain ⟨g, hg, h⟩ := hT
    exact ⟨g⁻¹, inv_mem hg, fun x hx => by simpa only [inv_inv] using h x hx⟩
  exact twE6_full_toral_fixed_solvable hn hK σ hσ hp hpodd hpq
    A hAI hA.2 hT' hNPC

theorem ggFixedSubgroup_isSolvable_of_recipe_twE6_nonTorsion
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3)
    (hpq : p ∣ (2 ^ n) ^ 2 - 1)
    (E : Subgroup (MulAut (TwE6Delta.RecipeR K n)))
    (hEI : (E : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hE : IsElemAbelian p E)
    (hNPC : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj hn hK
  have hErange : E ≤ (TwE6Transport.recipeConj σ ε).range := fun a ha => (hε a).2 (hEI ha)
  let A := TwE6Transport.recipeMat σ ε E
  have hAI : A ≤ twistedE6InndiagGL K σ := TwE6Transport.recipeMat_le σ ε E
  have hAp : IsElemAbelian p A := TwE6Transport.isElemAbelian_recipeMat σ ε hn hK hσ hE
  let C : Subgroup (ModGL TwistTag.E6.tag K) := twistedE6RootGroup K σ ⊓
    Subgroup.centralizer (A : Set (ModGL TwistTag.E6.tag K))
  let ψ : ↥C →* ↥(ggFixedSubgroup E) :=
    { toFun := fun c => ⟨ε ⟨(c : ModGL TwistTag.E6.tag K), c.2.1⟩, by
        rw [ggFixedSubgroup_eq_commonFixed]
        simp only [CFSG.GroupTheory.FixedCentralQuotientFamily.commonFixed,
          Subgroup.mem_iInf]
        intro a
        exact TwE6Transport.apply_eq_of_forall_commute_recipeMat σ ε hErange c.2.1
          (fun x hx => (Subgroup.mem_centralizer_iff.1 c.2.2 x hx).symm) a.2⟩
      map_one' := by apply Subtype.ext; exact map_one ε
      map_mul' := by
        intro c d
        apply Subtype.ext
        change ε (⟨(c : ModGL TwistTag.E6.tag K), c.2.1⟩ *
            ⟨(d : ModGL TwistTag.E6.tag K), d.2.1⟩) =
          ε ⟨(c : ModGL TwistTag.E6.tag K), c.2.1⟩ *
            ε ⟨(d : ModGL TwistTag.E6.tag K), d.2.1⟩
        exact map_mul ε _ _ }
  have hψinj : Function.Injective ψ := by
    intro c d h
    apply Subtype.ext
    have hεcd : ε ⟨(c : ModGL TwistTag.E6.tag K), c.2.1⟩ =
        ε ⟨(d : ModGL TwistTag.E6.tag K), d.2.1⟩ := congrArg Subtype.val h
    exact congrArg (fun z : graphFixedRootGroup TwistTag.E6 K σ.toRingHom =>
      (z : ModGL TwistTag.E6.tag K)) (ε.injective hεcd)
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨r, hr⟩
    have hrfix : ∀ a ∈ E, a r = r := by
      rw [ggFixedSubgroup_eq_commonFixed] at hr
      simp only [CFSG.GroupTheory.FixedCentralQuotientFamily.commonFixed,
        Subgroup.mem_iInf] at hr
      exact fun a ha => hr ⟨a, ha⟩
    have hrcent : (ε.symm r : ModGL TwistTag.E6.tag K) ∈
        Subgroup.centralizer (A : Set (ModGL TwistTag.E6.tag K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have h := hrfix _ hw
      rw [TwE6Transport.recipeConj_apply] at h
      have hm := congrArg Subtype.val
        (ε.injective (h.trans (ε.apply_symm_apply r).symm))
      rw [RecipeExcLang.coe_twConj] at hm
      exact (mul_inv_eq_iff_eq_mul).1 hm
    refine ⟨⟨ε.symm r, (ε.symm r).2, hrcent⟩, ?_⟩
    apply Subtype.ext
    exact ε.apply_symm_apply r
  let e : ↥C ≃* ↥(ggFixedSubgroup E) := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hNPC_C : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥C) :=
    CFSG.hasNormalPComplement_of_equiv p e.symm.commutatorCongr hNPC
  have hsolvC : Group.IsSolvable ↥C := by
    with_unfolding_all exact
      twE6_full_nontorsion_fixed_solvable hn hK σ hσ hp hpodd hp3 hpq A hAI hAp hNPC_C
  let := hsolvC
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem largeEvenLabelAll_twE6_nonTorsion_fullFixedSolvable
    {l n p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3)
    (hpq : p ∣ (2 ^ n) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.twE6, l, n⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  refine recipeTwisted_and (P := fun R _ I _ =>
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsElemAbelian p E →
      CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
  intro K _ _ hK E hEI hE hNPC
  have hn : 1 ≤ n := by
    have h := Finite.one_lt_card (α := K)
    by_contra hc
    have hn0 : n = 0 := by omega
    rw [hK, hn0] at h
    norm_num at h
  exact ggFixedSubgroup_isSolvable_of_recipe_twE6_nonTorsion hn hK hp hpodd hp3 hpq
    E hEI hE hNPC

theorem isSolvable_inf_centralizer_of_twE6_nonTorsion_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab.tag = .twE6 ∧ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian p (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twE6 ∧ p ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
      CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab _ hs => by
      cases lab with
      | mk tag rank n =>
        obtain ⟨rfl, hpq⟩ := hs
        exact largeEvenLabelAll_twE6_nonTorsion_fullFixedSolvable hp hpodd hp3 hpq)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hN, hEI, hE⟩, hrow⟩ := hP
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

section RankThree


theorem twE6_full_three_rank_three_fixed_solvable
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ (2 ^ n) ^ 2 - 1)
    (A : Subgroup (ModGL .E6 K)) (hAI : A ≤ twistedE6InndiagGL K σ)
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 3 ≤ Nat.card A)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(twistedE6RootGroup K σ ⊓
        Subgroup.centralizer (A : Set (ModGL .E6 K))))) :
    Group.IsSolvable ↥(twistedE6RootGroup K σ ⊓
      Subgroup.centralizer (A : Set (ModGL .E6 K))) := by
  classical
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL .E6 K) := finite_modGL
  let ι := baseChangeGL (τ := .E6) (algebraMap K L)
  have hι : Function.Injective ι := baseChangeGL_injective (algebraMap K L)
  let E := A.map ι
  have : Finite ↥E := Finite.of_equiv A (A.equivMapOfInjective ι hι).toEquiv
  have hEadj : E ≤ adjointGroup .E6 L := by
    rintro _ ⟨a, ha, rfl⟩
    exact (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ
      (iterateFrobenius L 2 n) (fun c => by simp only [L, iterateFrobenius_def])
      ⟨a, hAI ha, rfl⟩).1
  have hEab : IsElemAbelian 3 E := hA.map ι
  have hEcard : Nat.card E = Nat.card A := Subgroup.card_map_of_injective hι
  by_cases hT : IsToralSubgroup .E6 L E
  · have hT' : SCFourCover.E6AdToral E := by
      obtain ⟨g, hg, h⟩ := hT
      exact ⟨g⁻¹, inv_mem hg, fun x hx => by simpa only [inv_inv] using h x hx⟩
    exact twE6_full_toral_fixed_solvable hn hK σ hσ Nat.prime_three (by decide)
      h3 A hAI hA.2 hT' hNPC
  · by_cases h4 : 3 ^ 4 ≤ Nat.card A
    · have hK3 : ¬ 3 ∣ Nat.card K := by
        intro hd
        have : Fintype K := Fintype.ofFinite K
        obtain ⟨f, -, hf⟩ := FiniteField.card K 2
        rw [Nat.card_eq_fintype_card, hf] at hd
        exact (by decide : (3 : ℕ) ≠ 2)
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
            (Nat.prime_three.dvd_of_dvd_pow hd))
      have hlt : Nat.card E < 3 ^ 5 := by
        by_contra h
        have h5 : 3 ^ 5 ≤ Nat.card E := by omega
        exact hT (bigElemAbelianToralBar_E6_three K hK3 E hEadj
          (fun x hx y hy => hEab.comm hx hy) hEab.2 h5)
      obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
      have hk4 : k = 4 := by
        have hlo : 4 ≤ k := (Nat.pow_le_pow_iff_right (by decide)).1 (hk ▸ h4)
        have hhi : k < 5 := (Nat.pow_lt_pow_iff_right (by decide)).1 (hk ▸ (hEcard ▸ hlt))
        omega
      have hcardE : Nat.card E = 3 ^ 4 := hEcard.trans (hk4 ▸ hk)
      obtain ⟨hcomm, -, -⟩ := ggL45E6NonToralThreeCent_holds K E hEadj hEab hT hcardE
      let C : Subgroup (ModGL .E6 K) := twistedE6RootGroup K σ ⊓
        Subgroup.centralizer (A : Set (ModGL .E6 K))
      have hrootI : twistedE6RootGroup K σ ≤ twistedE6InndiagGL K σ := le_sup_left
      have hCcomm : ∀ x y : C, x * y = y * x := by
        intro x y
        apply Subtype.ext
        apply hι
        change ι ((x : ModGL .E6 K) * (y : ModGL .E6 K)) =
          ι ((y : ModGL .E6 K) * (x : ModGL .E6 K))
        rw [map_mul, map_mul]
        have hx : ι (x : ModGL .E6 K) ∈ adjointGroup .E6 L :=
          (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ
            (iterateFrobenius L 2 n) (fun c => by simp only [L, iterateFrobenius_def])
            ⟨(x : ModGL .E6 K), hrootI x.2.1, rfl⟩).1
        have hy : ι (y : ModGL .E6 K) ∈ adjointGroup .E6 L :=
          (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ
            (iterateFrobenius L 2 n) (fun c => by simp only [L, iterateFrobenius_def])
            ⟨(y : ModGL .E6 K), hrootI y.2.1, rfl⟩).1
        apply hcomm _ hx _ hy
        · rintro _ ⟨a, ha, rfl⟩
          rw [← map_mul, ← map_mul]
          exact congrArg ι ((Subgroup.mem_centralizer_iff.1 x.2.2 a ha).symm)
        · rintro _ ⟨a, ha, rfl⟩
          rw [← map_mul, ← map_mul]
          exact congrArg ι ((Subgroup.mem_centralizer_iff.1 y.2.2 a ha).symm)
      let : IsMulCommutative C := ⟨⟨hCcomm⟩⟩
      change Group.IsSolvable ↥C
      infer_instance

    · 
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, hk⟩ := hA.isPGroup.exists_card_eq
      have hk3 : k = 3 := by
        have hlo : 3 ≤ k := (Nat.pow_le_pow_iff_right (by decide)).1 (hk ▸ hcard)
        have hhi : k < 4 := (Nat.pow_lt_pow_iff_right (by decide)).1 (hk ▸ lt_of_not_ge h4)
        omega
      have hcard3 : Nat.card A = 3 ^ 3 := hk3 ▸ hk
      have hAIR : A ≤ RecipeExcLang.inndiagGroup .E6 K :=
        hAI.trans ((twistedE6InndiagGL_le_e6InndiagGL K σ).trans
          (TwE6FieldCore.e6InndiagGL_le_inndiagGroup K))
      have hrootR : twistedE6RootGroup K σ ≤ RecipeExcLang.inndiagGroup .E6 K := by
        intro x hx
        apply RecipeExcLang.adjointGroup_le_inndiagGroup
        exact twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom
          (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hx)
      exact CFSG.LieType.Chevalley.E6Three.PositionCentralizer.isSolvable_of_le_inndiag_centralizer_of_not_toral_three
        A hAIR hA hcard3 hT _ (inf_le_inf hrootR le_rfl) hNPC

theorem ggFixedSubgroup_isSolvable_of_recipe_twE6_three_rank_three
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ (2 ^ n) ^ 2 - 1)
    (E : Subgroup (MulAut (TwE6Delta.RecipeR K n)))
    (hEI : (E : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 3 ≤ Nat.card E)
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj hn hK
  have hErange : E ≤ (TwE6Transport.recipeConj σ ε).range := fun a ha => (hε a).2 (hEI ha)
  let A := TwE6Transport.recipeMat σ ε E
  have hAI : A ≤ twistedE6InndiagGL K σ := TwE6Transport.recipeMat_le σ ε E
  have hAp : IsElemAbelian 3 A := TwE6Transport.isElemAbelian_recipeMat σ ε hn hK hσ hE
  let C : Subgroup (ModGL TwistTag.E6.tag K) := twistedE6RootGroup K σ ⊓
    Subgroup.centralizer (A : Set (ModGL TwistTag.E6.tag K))
  let ψ : ↥C →* ↥(ggFixedSubgroup E) :=
    { toFun := fun c => ⟨ε ⟨(c : ModGL TwistTag.E6.tag K), c.2.1⟩, by
        rw [ggFixedSubgroup_eq_commonFixed]
        simp only [CFSG.GroupTheory.FixedCentralQuotientFamily.commonFixed,
          Subgroup.mem_iInf]
        intro a
        exact TwE6Transport.apply_eq_of_forall_commute_recipeMat σ ε hErange c.2.1
          (fun x hx => (Subgroup.mem_centralizer_iff.1 c.2.2 x hx).symm) a.2⟩
      map_one' := by apply Subtype.ext; exact map_one ε
      map_mul' := by
        intro c d
        apply Subtype.ext
        change ε (⟨(c : ModGL TwistTag.E6.tag K), c.2.1⟩ *
            ⟨(d : ModGL TwistTag.E6.tag K), d.2.1⟩) =
          ε ⟨(c : ModGL TwistTag.E6.tag K), c.2.1⟩ *
            ε ⟨(d : ModGL TwistTag.E6.tag K), d.2.1⟩
        exact map_mul ε _ _ }
  have hψinj : Function.Injective ψ := by
    intro c d h
    apply Subtype.ext
    have hεcd : ε ⟨(c : ModGL TwistTag.E6.tag K), c.2.1⟩ =
        ε ⟨(d : ModGL TwistTag.E6.tag K), d.2.1⟩ := congrArg Subtype.val h
    exact congrArg (fun z : graphFixedRootGroup TwistTag.E6 K σ.toRingHom =>
      (z : ModGL TwistTag.E6.tag K)) (ε.injective hεcd)
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨r, hr⟩
    have hrfix : ∀ a ∈ E, a r = r := by
      rw [ggFixedSubgroup_eq_commonFixed] at hr
      simp only [CFSG.GroupTheory.FixedCentralQuotientFamily.commonFixed,
        Subgroup.mem_iInf] at hr
      exact fun a ha => hr ⟨a, ha⟩
    have hrcent : (ε.symm r : ModGL TwistTag.E6.tag K) ∈
        Subgroup.centralizer (A : Set (ModGL TwistTag.E6.tag K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      have h := hrfix _ hw
      rw [TwE6Transport.recipeConj_apply] at h
      have hm := congrArg Subtype.val
        (ε.injective (h.trans (ε.apply_symm_apply r).symm))
      rw [RecipeExcLang.coe_twConj] at hm
      exact (mul_inv_eq_iff_eq_mul).1 hm
    refine ⟨⟨ε.symm r, (ε.symm r).2, hrcent⟩, ?_⟩
    apply Subtype.ext
    exact ε.apply_symm_apply r
  let e : ↥C ≃* ↥(ggFixedSubgroup E) := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hNPC_C : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥C) :=
    CFSG.hasNormalPComplement_of_equiv 3 e.symm.commutatorCongr hNPC
  have hcardA : 3 ^ 3 ≤ Nat.card A :=
    (TwE6Transport.card_recipeMat σ ε hn hK hσ hErange).symm ▸ hcard
  have hsolvC : Group.IsSolvable ↥C := by
    with_unfolding_all exact
      twE6_full_three_rank_three_fixed_solvable hn hK σ hσ h3 A hAI hAp hcardA hNPC_C
  let := hsolvC
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem largeEvenLabelAll_twE6_three_rank_three_fullFixedSolvable
    {l n : ℕ} (h3 : 3 ∣ (2 ^ n) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.twE6, l, n⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
        CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  refine recipeTwisted_and (P := fun R _ I _ =>
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
  intro K _ _ hK E hEI hE hcard hNPC
  have hn : 1 ≤ n := by
    have h := Finite.one_lt_card (α := K)
    by_contra hc
    have hn0 : n = 0 := by omega
    rw [hK, hn0] at h
    norm_num at h
  exact ggFixedSubgroup_isSolvable_of_recipe_twE6_three_rank_three hn hK h3 E hEI hE hcard hNPC

theorem isSolvable_inf_centralizer_of_twE6_three_rank_three_marking
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab.tag = .twE6 ∧ 3 ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian 3 (ggBeta (G := G) (L := X) θ hN).range ∧
        3 ^ 3 ≤ Nat.card (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .twE6 ∧ 3 ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian 3 E → 3 ^ 3 ≤ Nat.card E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab _ hs => by
      cases lab with
      | mk tag rank n =>
        obtain ⟨rfl, h3⟩ := hs
        exact largeEvenLabelAll_twE6_three_rank_three_fullFixedSolvable h3)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hN, hEI, hE, hcard⟩, hrow⟩ := hP
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE hcard
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end RankThree

end CFSG.StandardType
