module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma97
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Theorem26
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.problem_7_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Lemma 9.8

The first half of the source proof is a purely local Peterfalvi calculation.
If the derived subgroup of `E` has trivial intersection with `V`, then the
anti-fixed closure is exactly `I` and the decomposition from Corollary 9.6 is
Frobenius.  The remaining contradiction, using `[II1; 2.6]`, is kept below
this checked algebraic core.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-! ## Earlier-book permutation inputs -/

/-- Direct ambient right-conjugation form of double transitivity. -/
@[expose] public def ConjugationTwoTransitiveOn
    {G : Type*} [Group G] (H : Subgroup G) (Z : Set G) : Prop :=
  ∀ {a b c d : G},
    a ∈ Z → b ∈ Z → c ∈ Z → d ∈ Z →
    a ≠ b → c ≠ d →
      ∃ h : H,
        rightConjugateElem a (h : G) = c ∧
          rightConjugateElem b (h : G) = d

/-- The conjugation specialization of `[II1; Theorem 2.6]` used in Lemma
9.8.  The stability premise records that `H` acts on `Z`; regularity of `K`
alone supplies only `K`-stability. -/
@[expose] public def II1Theorem26Conjugation
    {G : Type u} [Group G] [Finite G] : Prop :=
  ∀ (H K : Subgroup G) (Z : Set G),
    K ≤ H →
    (∀ z, z ∈ Z → ∀ h, h ∈ H →
      rightConjugateElem z h ∈ Z) →
    ConjugationRegularOn K Z →
    (∀ x, x ∈ K → x ≠ 1 →
      elementCentralizerIn H x = K) →
    ConjugationTwoTransitiveOn H Z ∨
      (H : Set G) =
        ((H ⊓ Subgroup.centralizer Z : Subgroup G) : Set G) *
          (normalizerIn H K : Set G)

/-- The conjugation specialization of `[II1; Theorem 2.6]`, obtained from
the proved action form by letting `H` act on the subtype of the stable set
`Z`. -/
public theorem ii1Theorem26Conjugation_of_action
    {G : Type u} [Group G] [Finite G] :
    II1Theorem26Conjugation (G := G) := by
  classical
  intro H K Z hKleH hstable hregular hcentral
  by_cases hZ : Z.Nonempty
  · let f : H →* ConjAct G :=
      ConjAct.toConjAct.toMonoidHom.comp H.subtype
    let conjAction : MulDistribMulAction H G :=
      MulDistribMulAction.compHom G f
    letI : SMul H G := conjAction.toSMul
    letI : MulAction H G := conjAction.toMulAction
    letI : MulDistribMulAction H G := conjAction
    have smul_eq (h : H) (z : G) :
        h • z = (h : G) * z * (h : G)⁻¹ := by
      change f h • z = _
      simp [f, ConjAct.toConjAct_smul]
    let Zact : SubMulAction H G :=
      { carrier := Z
        smul_mem' := by
          intro h z hz
          have hhInv : (h : G)⁻¹ ∈ H := H.inv_mem h.property
          rw [smul_eq]
          simpa [rightConjugateElem]
            using hstable z hz (h : G)⁻¹ hhInv }
    letI : Nonempty Zact := ⟨⟨hZ.choose, hZ.choose_spec⟩⟩
    let Ksub : Subgroup H := K.subgroupOf H
    have hreg : IsRegularOn Ksub (Set.univ : Set Zact) := by
      intro a b _ _
      obtain ⟨g, hgPair, hgUnique⟩ :=
        hregular.2 a.1 a.2 b.1 b.2
      let gH : H := ⟨g⁻¹, H.inv_mem (hKleH hgPair.1)⟩
      let gK : Ksub := ⟨gH, K.inv_mem hgPair.1⟩
      refine ⟨gK, ?_, ?_⟩
      · apply Subtype.ext
        change gH • (a : G) = (b : G)
        rw [smul_eq]
        simpa [gH, rightConjugateElem] using hgPair.2.symm
      · intro l hl
        let lG : G := (l : G)⁻¹
        have hlG : lG ∈ K := K.inv_mem l.property
        have hlPair : lG ∈ K ∧ b.1 = rightConjugateElem a.1 lG := by
          refine ⟨hlG, ?_⟩
          have hlVal := congrArg Subtype.val hl
          simpa [lG, Zact, smul_eq, f, ConjAct.toConjAct_smul,
            rightConjugateElem] using hlVal.symm
        have hleq : lG = g := hgUnique lG hlPair
        apply Subtype.ext
        apply Subtype.ext
        simpa [lG, gK, gH] using congrArg Inv.inv hleq
    have hcent : ∀ x : H, x ∈ Ksub → x ≠ 1 →
        Subgroup.centralizer ({x} : Set H) = Ksub := by
      intro x hxK hxne
      have hxneG : (x : G) ≠ 1 := by
        intro hx
        apply hxne
        exact Subtype.ext hx
      have hCG := hcentral (x : G) hxK hxneG
      ext y
      constructor
      · intro hy
        have hyG : (y : G) ∈ elementCentralizerIn H (x : G) := by
          refine ⟨y.property, ?_⟩
          intro m hm
          simp only [Set.mem_singleton_iff] at hm
          subst m
          exact congrArg Subtype.val (hy x (by simp))
        rw [hCG] at hyG
        exact hyG
      · intro hyK
        have hyG : (y : G) ∈ elementCentralizerIn H (x : G) := by
          rw [hCG]
          exact hyK
        intro m hm
        simp only [Set.mem_singleton_iff] at hm
        subst m
        apply Subtype.ext
        exact hyG.2 (x : G) (by simp)
    rcases ii1Theorem26Action Ksub hreg hcent with htwo | hfactor
    · left
      intro a b c d ha hb hc hd hab hcd
      let aZ : Zact := ⟨a, ha⟩
      let bZ : Zact := ⟨b, hb⟩
      let cZ : Zact := ⟨c, hc⟩
      let dZ : Zact := ⟨d, hd⟩
      have habZ : aZ ≠ bZ := fun h => hab (congrArg Subtype.val h)
      have hcdZ : cZ ≠ dZ := fun h => hcd (congrArg Subtype.val h)
      obtain ⟨h, hac, hbd⟩ :=
        (MulAction.is_two_pretransitive_iff.mp htwo) habZ hcdZ
      refine ⟨h⁻¹, ?_, ?_⟩
      · have hacVal := congrArg Subtype.val hac
        simpa [aZ, cZ, Zact, smul_eq, rightConjugateElem]
          using hacVal
      · have hbdVal := congrArg Subtype.val hbd
        simpa [bZ, dZ, Zact, smul_eq, rightConjugateElem]
          using hbdVal
    · right
      have hcoreImage :
          H.subtype '' (pointStabilizerCore H Zact : Set H) =
            ((H ⊓ Subgroup.centralizer Z : Subgroup G) : Set G) := by
        ext g
        constructor
        · rintro ⟨h, hh, rfl⟩
          refine ⟨h.property, ?_⟩
          intro z hz
          let zZ : Zact := ⟨z, hz⟩
          have hhFix : h • zZ = zZ := by
            rw [pointStabilizerCore] at hh
            have hhStab : h ∈ MulAction.stabilizer H zZ :=
              (Subgroup.mem_iInf.mp hh) zZ
            exact hhStab
          have hhVal := congrArg Subtype.val hhFix
          change h • (z : G) = z at hhVal
          rw [smul_eq] at hhVal
          calc
            z * (h : G) = ((h : G) * z * (h : G)⁻¹) * (h : G) := by
              rw [hhVal]
            _ = (h : G) * z := by group
        · rintro ⟨hgH, hgC⟩
          let h : H := ⟨g, hgH⟩
          refine ⟨h, ?_, rfl⟩
          rw [pointStabilizerCore]
          apply Subgroup.mem_iInf.mpr
          intro zZ
          change h • zZ = zZ
          apply Subtype.ext
          change h • (zZ : G) = (zZ : G)
          rw [smul_eq]
          have hcomm : (zZ : G) * g = g * (zZ : G) :=
            hgC (zZ : G) zZ.property
          calc
            g * (zZ : G) * g⁻¹ = (zZ : G) * g * g⁻¹ := by rw [hcomm]
            _ = (zZ : G) := by simp
      have hnormalizerImage :
          H.subtype '' (Subgroup.normalizer (Ksub : Set H) : Set H) =
            (normalizerIn H K : Set G) := by
        ext g
        constructor
        · rintro ⟨h, hhN, rfl⟩
          refine ⟨h.property, ?_⟩
          change (h : G) ∈ Subgroup.normalizer (K : Set G)
          change h ∈ Subgroup.normalizer (Ksub : Set H) at hhN
          rw [Subgroup.mem_normalizer_iff] at hhN ⊢
          intro k
          constructor
          · intro hk
            let kH : H := ⟨k, hKleH hk⟩
            have hkSub : kH ∈ Ksub := hk
            have := (hhN kH).mp hkSub
            exact this
          · intro hk
            have hkH : k ∈ H := by
              have hconjH : (h : G) * k * (h : G)⁻¹ ∈ H := hKleH hk
              have hcalc :
                  (h : G)⁻¹ * ((h : G) * k * (h : G)⁻¹) * (h : G) ∈ H :=
                H.mul_mem
                  (H.mul_mem (H.inv_mem h.property) hconjH) h.property
              simpa [mul_assoc] using hcalc
            let kH : H := ⟨k, hkH⟩
            have hkSub : h * kH * h⁻¹ ∈ Ksub := hk
            have := (hhN kH).mpr hkSub
            exact this
        · rintro ⟨hgH, hgN⟩
          let h : H := ⟨g, hgH⟩
          refine ⟨h, ?_, rfl⟩
          change g ∈ Subgroup.normalizer (K : Set G) at hgN
          change h ∈ Subgroup.normalizer (Ksub : Set H)
          rw [Subgroup.mem_normalizer_iff] at hgN ⊢
          intro kH
          constructor
          · intro hk
            exact (hgN (kH : G)).mp hk
          · intro hk
            exact (hgN (kH : G)).mpr hk
      have himage := congrArg
        (fun S : Set H => H.subtype '' S) hfactor
      change H.subtype '' (Set.univ : Set H) =
        H.subtype '' ((pointStabilizerCore H Zact : Set H) *
          (Subgroup.normalizer (Ksub : Set H) : Set H)) at himage
      calc
        (H : Set G) = H.subtype '' (Set.univ : Set H) := by ext; simp
        _ = H.subtype '' ((pointStabilizerCore H Zact : Set H) *
            (Subgroup.normalizer (Ksub : Set H) : Set H)) := himage
        _ = H.subtype '' (pointStabilizerCore H Zact : Set H) *
            H.subtype '' (Subgroup.normalizer (Ksub : Set H) : Set H) :=
          Set.image_mul H.subtype
        _ = ((H ⊓ Subgroup.centralizer Z : Subgroup G) : Set G) *
            (normalizerIn H K : Set G) := by
          rw [hcoreImage, hnormalizerImage]
  · right
    have hZempty : Z = ∅ := Set.not_nonempty_iff_eq_empty.mp hZ
    rw [hZempty]
    ext x
    constructor
    · intro hx
      have hxC : x ∈ Subgroup.centralizer (∅ : Set G) := by
        intro y hy
        simp at hy
      exact ⟨x, ⟨hx, hxC⟩, 1, by simp [normalizerIn], by simp⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact H.mul_mem ha.1 hb.1

/-- The ambient subgroup endpoint of Hering `[II1; 3.1]` needed in Lemma
9.8: double transitivity on the involutions rules out `2`-rank at least two. -/
@[expose] public def II1Hering31Ambient
    {G : Type u} [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G),
    ConjugationTwoTransitiveOn H (involutionsInSet H) →
      ¬ TwoRankAtLeastTwo H

/-- Source Lemma 9.8(b)'s forbidden alternative: `E` is a Frobenius group
whose ambient kernel is the Peterfalvi subgroup `K = I`. -/
@[expose] public def Lemma98FrobeniusCase
    {X : Type u} [Group X]
    (D E : Subgroup X) (t : X) : Prop :=
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  K ≤ E ∧
    (K : Set X) = peterfalviKSet D t ∧
      ∃ R : Subgroup X, R ≤ E ∧
        IsFrobeniusGroupWithKernelComplement
          (K.subgroupOf E) (R.subgroupOf E)

/-! ## The Frobenius reduction -/

private theorem closure_peterfalviKSet_eq_set_of_inf_fixed_eq_bot
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hDodd : Odd (Nat.card D))
    (hKfixed :
      Subgroup.closure (peterfalviKSet D t) ⊓ peterfalviV D t = ⊥) :
    (Subgroup.closure (peterfalviKSet D t) : Set X) =
      peterfalviKSet D t := by
  classical
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  apply Set.Subset.antisymm
  · intro x hxK
    have hKD : K ≤ D := by
      rw [Subgroup.closure_le]
      intro y hy
      exact hy.1
    obtain ⟨hleft, _hright, _hcard⟩ :=
      lemma_a t D ht hDodd hDnorm
    obtain ⟨p, _hp_univ, hp⟩ := hleft.surjOn (hKD hxK)
    have hpV : (p.1 : X) ∈ V := p.1.property
    have hpK : (p.2 : X) ∈ K :=
      Subgroup.subset_closure p.2.property
    have hp1_eq : (p.1 : X) = x * (p.2 : X)⁻¹ := by
      rw [← hp]
      simp [mul_assoc]
    have hp1K : (p.1 : X) ∈ K := by
      rw [hp1_eq]
      exact K.mul_mem hxK (K.inv_mem hpK)
    have hp1bot : (p.1 : X) ∈ (⊥ : Subgroup X) := by
      rw [← hKfixed]
      exact ⟨hp1K, hpV⟩
    have hp1one : (p.1 : X) = 1 := by simpa using hp1bot
    have hx_eq : x = (p.2 : X) := by
      rw [← hp]
      simp [hp1one]
    rw [hx_eq]
    exact p.2.property
  · exact Subgroup.subset_closure

private theorem closure_peterfalviKSet_normal_subgroupOf
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hDodd : Odd (Nat.card D))
    (hKset :
      (Subgroup.closure (peterfalviKSet D t) : Set X) =
        peterfalviKSet D t) :
    (Subgroup.closure (peterfalviKSet D t)).subgroupOf D |>.Normal := by
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  have hclosure_eq :
      K.subgroupOf D =
        Subgroup.closure
          {x : D | rightConjugateElem (x : X) t = (x : X)⁻¹} := by
    apply le_antisymm
    · intro x hx
      apply Subgroup.subset_closure
      have hxI : (x : X) ∈ peterfalviKSet D t := by
        rw [← hKset]
        exact hx
      exact hxI.2
    · rw [Subgroup.closure_le]
      intro x hx
      change (x : X) ∈ Subgroup.closure (peterfalviKSet D t)
      exact (Set.ext_iff.mp hKset (x : X)).mpr ⟨x.property, hx⟩
  rw [hclosure_eq]
  exact lemma_b t D ht hDodd hDnorm

/--
The checked algebraic core of Lemma 9.8.  It uses only the conclusion package
of Corollary 9.6 and the source decomposition `D = V I`; no cardinal
cancellation or external classification theorem is hidden in this helper.
-/
public theorem lemma98_frobenius_of_derived_inf_fixed_eq_bot
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (hIne : ∃ x : X, x ∈ peterfalviKSet D t ∧ x ≠ 1)
    (h96 : Corollary96Conclusion D E t)
    (hderFixed :
      (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t = ⊥) :
    let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
    let R : Subgroup X := E ⊓ peterfalviV D t
    (K : Set X) = peterfalviKSet D t ∧
      IsFrobeniusGroupWithKernelComplement
        (K.subgroupOf E) (R.subgroupOf E) := by
  classical
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  let R : Subgroup X := E ⊓ V
  have hKder : K ≤ (derivedSubgroup E).map E.subtype :=
    h96.closure_le_derived
  have hKE : K ≤ E :=
    hKder.trans (Subgroup.map_subtype_le (derivedSubgroup E))
  have hKfixed : K ⊓ V = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (derivedSubgroup E).map E.subtype ⊓ V :=
        ⟨hKder hx.1, hx.2⟩
      rw [show (derivedSubgroup E).map E.subtype ⊓ V = ⊥ by
        simpa [V] using hderFixed] at hx'
      simpa using hx'
    · exact bot_le
  have hKset : (K : Set X) = peterfalviKSet D t := by
    simpa [K, V] using
      (closure_peterfalviKSet_eq_set_of_inf_fixed_eq_bot
        ht hDnorm hDodd (by simpa [K, V] using hKfixed))
  refine ⟨hKset, ?_⟩
  let Ksub : Subgroup E := K.subgroupOf E
  let Rsub : Subgroup E := R.subgroupOf E
  have hKnormalD : (K.subgroupOf D).Normal := by
    exact closure_peterfalviKSet_normal_subgroupOf
      ht hDnorm hDodd (by simpa [K] using hKset)
  have hDleNormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hKE.trans hED)).mp hKnormalD
  have hKnormalE : Ksub.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).mpr
      (hED.trans hDleNormK)
  have hKRdisjoint : Disjoint Ksub Rsub := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    apply Subtype.ext
    have hxKX : (x : X) ∈ K := hxK
    have hxRX : (x : X) ∈ R := hxR
    have hxbot : (x : X) ∈ (⊥ : Subgroup X) := by
      rw [← hKfixed]
      exact ⟨hxKX, hxRX.2⟩
    simpa using hxbot
  have hKRmul : (Ksub : Set E) * (Rsub : Set E) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxE : (x : X) ∈ (E : Set X) := x.property
    rw [show (E : Set X) = (K : Set X) * (R : Set X) by
      simpa [K, R, V] using h96.eq_mul_fixed] at hxE
    rcases Set.mem_mul.mp hxE with ⟨k, hk, r, hr, hkr⟩
    let kE : E := ⟨k, hKE hk⟩
    let rE : E := ⟨r, hr.1⟩
    apply Set.mem_mul.mpr
    refine ⟨kE, ?_, rE, ?_, ?_⟩
    · exact hk
    · exact hr
    · apply Subtype.ext
      exact hkr
  have hKRcomp : Ksub.IsComplement' Rsub :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hKRdisjoint hKRmul
  have hKne : Ksub ≠ ⊥ := by
    obtain ⟨k, hkI, hkne⟩ := hIne
    intro hbot
    let kE : E := ⟨k, hKE (Subgroup.subset_closure hkI)⟩
    have hkKsub : kE ∈ Ksub := Subgroup.subset_closure hkI
    have hkbot : kE ∈ (⊥ : Subgroup E) := by
      rw [← hbot]
      exact hkKsub
    exact hkne (congrArg Subtype.val (by simpa using hkbot))
  have hRne : Rsub ≠ ⊥ := by
    obtain ⟨r, hrne⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp
        (show R ≠ ⊥ by simpa [R, V] using h96.inf_fixed_ne_bot)
    intro hbot
    let rE : E := ⟨(r : X), r.property.1⟩
    have hrRsub : rE ∈ Rsub := r.property
    have hrbot : rE ∈ (⊥ : Subgroup E) := by
      rw [← hbot]
      exact hrRsub
    apply hrne
    apply Subtype.ext
    have hrEone : rE = 1 := by simpa using hrbot
    exact congrArg (fun z : E => (z : X)) hrEone
  refine (lemma_3_1 Ksub Rsub hKne hRne hKnormalE hKRcomp).mpr ?_
  intro x hxne
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  let xX : X := ((x : E) : X)
  have hxR : xX ∈ R := x.property
  have hxneX : xX ≠ 1 := by
    intro hxone
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    exact hxone
  have hxNotDer : xX ∉ (derivedSubgroup E).map E.subtype := by
    intro hxDer
    have hxbot : xX ∈ (⊥ : Subgroup X) := by
      rw [← hderFixed]
      exact ⟨hxDer, hxR.2⟩
    exact hxneX (by simpa using hxbot)
  have hyK : (y : X) ∈ K := hy.1
  have hyI : (y : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact hyK
  have hycommE : y * (x : E) = (x : E) * y :=
    Subgroup.mem_centralizer_singleton_iff.mp hy.2
  have hycommX : (y : X) * xX = xX * (y : X) :=
    congrArg Subtype.val hycommE
  have hyone : (y : X) = 1 :=
    h96.fixedPointFree xX
      (by simpa [R, V] using hxR) hxNotDer (y : X) hyI hycommX
  apply Subtype.ext
  exact hyone

/-! ## Centralizers in the Frobenius case -/

private theorem frobenius_kernel_centralizer_le
    {G : Type u} [Group G] [Finite G]
    (K R : Subgroup G)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (z : K) (hzne : z ≠ 1) :
    Subgroup.centralizer ({(z : G)} : Set G) ≤ K := by
  letI : K.Normal := hfrob.normal
  exact
    ((External.Isaacs.VII.isaacs_problem_7_1 K R
      hfrob.kernel_ne_bot hfrob.complement_ne_bot
      hfrob.isComplement'.sup_eq_top hfrob.isComplement'.disjoint).2.2.2.2).mpr
        hfrob z hzne

private theorem elementCentralizerIn_le_inf_of_fixedPoints_card_eq_two
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t x : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (hWM : W ≤ M)
    (hxD : x ∈ M ⊓ rightConjugate M t)
    (hcard : Nat.card
      (theorem4bFixedPoints M (Subgroup.zpowers x)) = 2) :
    elementCentralizerIn W x ≤ W ⊓ (M ⊓ rightConjugate M t) := by
  let U : Subgroup X := Subgroup.zpowers x
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hUD : U ≤ M ⊓ rightConjugate M t :=
    Subgroup.zpowers_le.mpr hxD
  have hUM : U ≤ M := hUD.trans inf_le_left
  have hUconj : U ≤ rightConjugate M t := hUD.trans inf_le_right
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) U :=
    theorem4b_baseCoset_mem_fixedPoints hUM
  have hbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) U := by
    intro u hu
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact hUconj hu
  let alphaFixed : theorem4bFixedPoints M U := ⟨alpha, halpha⟩
  let betaFixed : theorem4bFixedPoints M U := ⟨beta, hbeta⟩
  have hbetaAlpha : betaFixed ≠ alphaFixed := by
    intro h
    apply htM
    simpa [alphaFixed, betaFixed, alpha, beta] using
      QuotientGroup.eq.mp (congrArg Subtype.val h).symm
  obtain ⟨gamma, hgamma, hgammaUnique⟩ :=
    (Nat.card_eq_two_iff' alphaFixed).mp hcard
  have hgammaBeta : gamma = betaFixed :=
    (hgammaUnique betaFixed hbetaAlpha).symm
  intro w hw
  have hwM : w ∈ M := hWM hw.1
  have hwAlpha : w • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa [alpha, baseCoset_stabilizer M] using hwM
  have hwcomm : w * x = x * w :=
    Subgroup.mem_centralizer_singleton_iff.mp hw.2
  have hwBetaFixed : w • beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) U := by
    intro y hy
    have hyStab : y • beta = beta := hbeta y hy
    have hyCommX : y * w = w * y := by
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact (show Commute x w from hwcomm.symm).zpow_left n |>.eq
    calc
      y • (w • beta) = (y * w) • beta := by rw [mul_smul]
      _ = (w * y) • beta := by rw [hyCommX]
      _ = w • (y • beta) := by rw [mul_smul]
      _ = w • beta := by rw [hyStab]
  let wBeta : theorem4bFixedPoints M U := ⟨w • beta, hwBetaFixed⟩
  have hwBetaNeAlpha : wBeta ≠ alphaFixed := by
    intro h
    apply hbetaAlpha
    apply Subtype.ext
    exact MulAction.injective w (by
      simpa [wBeta, betaFixed, alphaFixed, hwAlpha] using
        congrArg Subtype.val h)
  have hwBetaGamma : wBeta = gamma :=
    hgammaUnique wBeta hwBetaNeAlpha
  have hwBeta : w • beta = beta := by
    have : wBeta = betaFixed := hwBetaGamma.trans hgammaBeta
    exact congrArg Subtype.val this
  have hwConj : w ∈ rightConjugate M t := by
    have hwStab : w ∈ MulAction.stabilizer X beta :=
      MulAction.mem_stabilizer_iff.mpr hwBeta
    rw [show MulAction.stabilizer X beta = rightConjugate M t by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t] at hwStab
    exact hwStab
  exact ⟨hw.1, hwM, hwConj⟩

private theorem isMulCommutative_of_coe_eq_peterfalviKSet
    {X : Type u} [Group X]
    {D K : Subgroup X} {t : X}
    (hKset : (K : Set X) = peterfalviKSet D t) :
    IsMulCommutative K := by
  refine IsMulCommutative.mk ⟨?_⟩
  intro a b
  apply Subtype.ext
  have haI : (a : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact a.property
  have hbI : (b : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact b.property
  have habI : (a : X) * (b : X) ∈ peterfalviKSet D t := by
    rw [← hKset]
    exact K.mul_mem a.property b.property
  have hinvComm : (a : X)⁻¹ * (b : X)⁻¹ =
      (b : X)⁻¹ * (a : X)⁻¹ := by
    calc
      (a : X)⁻¹ * (b : X)⁻¹ =
          rightConjugateElem (a : X) t *
            rightConjugateElem (b : X) t := by
              rw [haI.2, hbI.2]
      _ = rightConjugateElem ((a : X) * (b : X)) t := by
            simp [rightConjugateElem, mul_assoc]
      _ = ((a : X) * (b : X))⁻¹ := habI.2
      _ = (b : X)⁻¹ * (a : X)⁻¹ := by simp
  have := congrArg Inv.inv hinvComm
  simpa using this.symm

/-- In the Frobenius alternative of Lemma 9.8, every nonidentity element of
the kernel has the source centralizers `C_W(x) = C_E(x) = K`.

Lemma 8.3(c) first forces the centralizer in `W` into the two-point
intersection `E`.  The Frobenius property gives the reverse kernel
containment, while the Peterfalvi description of `K` makes `K` abelian. -/
public theorem lemma98_elementCentralizers_eq
    {X : Type u} [Group X] [Finite X]
    {M W K R : Subgroup X} {t x : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hWM : W ≤ M)
    (hKE : K ≤ W ⊓ (M ⊓ rightConjugate M t))
    (hKset : (K : Set X) =
      peterfalviKSet (M ⊓ rightConjugate M t) t)
    (hfrob : IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf (W ⊓ (M ⊓ rightConjugate M t)))
      (R.subgroupOf (W ⊓ (M ⊓ rightConjugate M t))))
    (hxK : x ∈ K) (hxne : x ≠ 1) :
    elementCentralizerIn W x =
        elementCentralizerIn (W ⊓ (M ⊓ rightConjugate M t)) x ∧
      elementCentralizerIn (W ⊓ (M ⊓ rightConjugate M t)) x = K := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let Ksub : Subgroup E := K.subgroupOf E
  let Rsub : Subgroup E := R.subgroupOf E
  have hKcomm : IsMulCommutative K :=
    isMulCommutative_of_coe_eq_peterfalviKSet hKset
  letI : IsMulCommutative K := hKcomm
  have hxI : x ∈ peterfalviKSet D t := by
    simpa [D] using (show x ∈ peterfalviKSet
      (M ⊓ rightConjugate M t) t by
        rw [← hKset]
        exact hxK)
  have hcard : Nat.card
      (theorem4bFixedPoints M (Subgroup.zpowers x)) = 2 :=
    d83.fixedPoints_card_eq_two (by simpa [D] using hxI) hxne
  have hCWleE : elementCentralizerIn W x ≤ E := by
    simpa [D, E] using
      (elementCentralizerIn_le_inf_of_fixedPoints_card_eq_two
        ht htM hWM hxI.1 hcard)
  have hEW : E ≤ W := inf_le_left
  have hCWCE : elementCentralizerIn W x = elementCentralizerIn E x := by
    apply le_antisymm
    · intro y hy
      exact ⟨hCWleE hy, hy.2⟩
    · intro y hy
      exact ⟨hEW hy.1, hy.2⟩
  have hfrob' : IsFrobeniusGroupWithKernelComplement Ksub Rsub := by
    simpa [D, E, Ksub, Rsub] using hfrob
  let xE : E := ⟨x, hKE hxK⟩
  let xK : Ksub := ⟨xE, hxK⟩
  have hxKne : xK ≠ 1 := by
    intro h
    apply hxne
    simpa [xK, xE] using congrArg (fun z : Ksub => (((z : E) : X))) h
  have hcentELeKsub :
      Subgroup.centralizer ({(xK : E)} : Set E) ≤ Ksub :=
    frobenius_kernel_centralizer_le Ksub Rsub hfrob' xK hxKne
  have hCEleK : elementCentralizerIn E x ≤ K := by
    intro y hy
    let yE : E := ⟨y, hy.1⟩
    have hycommX : y * x = x * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hycentE : yE ∈
        Subgroup.centralizer ({(xK : E)} : Set E) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact hycommX
    exact hcentELeKsub hycentE
  have hKleCE : K ≤ elementCentralizerIn E x := by
    intro y hy
    refine ⟨hKE hy, ?_⟩
    let yK : K := ⟨y, hy⟩
    let xK' : K := ⟨x, hxK⟩
    have hycomm : y * x = x * y := by
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := K)).comm yK xK')
    exact Subgroup.mem_centralizer_singleton_iff.mpr hycomm
  have hCEK : elementCentralizerIn E x = K :=
    le_antisymm hCEleK hKleCE
  exact ⟨by simpa [D, E] using hCWCE, by simpa [D, E] using hCEK⟩

/-! ## The conjugation action and rank transport -/

private theorem conjugationRegularOn_involutionsInSet_of_peterfalviKSet
    {X : Type u} [Group X] [Finite X]
    {M K : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hKset : (K : Set X) =
      peterfalviKSet (M ⊓ rightConjugate M t) t) :
    ConjugationRegularOn K (involutionsInSet M) := by
  constructor
  · intro x hx a haK
    have haI : a ∈ peterfalviKSet (M ⊓ rightConjugate M t) t := by
      rw [← hKset]
      exact haK
    refine ⟨?_, isInvolution_rightConjugateElem hx.2⟩
    dsimp [rightConjugateElem]
    exact M.mul_mem (M.mul_mem (M.inv_mem haI.1.1) hx.1) haI.1.1
  · intro x hx y hy
    obtain ⟨a, haI, haxy⟩ :=
      hM.exists_mem_peterfalviKSet_of_involution_mem
        hx.1 hx.2 ht htM hy.1 hy.2
    have haK : a ∈ K := by
      change a ∈ (K : Set X)
      rw [hKset]
      exact haI
    refine ⟨a, ⟨haK, haxy.symm⟩, ?_⟩
    intro b hb
    let c : X := a * b⁻¹
    have hcK : c ∈ K := K.mul_mem haK (K.inv_mem hb.1)
    have hcI : c ∈ peterfalviKSet
        (M ⊓ rightConjugate M t) t := by
      rw [← hKset]
      exact hcK
    have hxc : rightConjugateElem x c = x := by
      calc
        rightConjugateElem x c =
            rightConjugateElem (rightConjugateElem x a) b⁻¹ := by
              rw [rightConjugateElem_comp]
        _ = rightConjugateElem y b⁻¹ := by rw [haxy]
        _ = rightConjugateElem (rightConjugateElem x b) b⁻¹ := by
              rw [← hb.2]
        _ = rightConjugateElem x (b * b⁻¹) := by
              rw [rightConjugateElem_comp]
        _ = x := by simp [rightConjugateElem]
    have hcCentral : c ∈ Subgroup.centralizer ({x} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun z : X => c * z) hxc
      have hcomm : x * c = c * x := by
        simpa [rightConjugateElem, mul_assoc] using h
      exact hcomm.symm
    have hcOne : c = 1 :=
      hM.eq_one_of_mem_peterfalviKSet_and_centralizes_involution
        hx.1 hx.2 ht htM hcI hcCentral
    have hab : a = b := by
      have h := congrArg (fun z : X => z * b) hcOne
      simpa [c, mul_assoc] using h
    exact hab.symm

private theorem involutionsInSet_eq_of_normalSupplement_odd
    {X : Type u} [Group X] [Finite X]
    {M D W : Subgroup X}
    (hDle : D ≤ M) (hDodd : Odd (Nat.card D))
    (hW : IsNormalSupplement M D W) :
    involutionsInSet M = involutionsInSet W := by
  ext z
  constructor
  · rintro ⟨hzM, hz⟩
    have hzpowM : Subgroup.zpowers z ≤ M :=
      Subgroup.zpowers_le.mpr hzM
    have hzpow2 : IsPGroup 2 (Subgroup.zpowers z) :=
      isPGroup_two_zpowers_of_isInvolution hz
    have hzpowW : Subgroup.zpowers z ≤ W :=
      hW.two_subgroup_le_of_odd hDle hDodd hzpowM hzpow2
    exact ⟨hzpowW (Subgroup.mem_zpowers z), hz⟩
  · rintro ⟨hzW, hz⟩
    exact ⟨hW.le_M hzW, hz⟩

private theorem involutionCoreIn_le_of_normalSupplement_odd
    {X : Type u} [Group X] [Finite X]
    {M D W : Subgroup X}
    (hDle : D ≤ M) (hDodd : Odd (Nat.card D))
    (hW : IsNormalSupplement M D W) :
    involutionCoreIn M ≤ W := by
  rw [involutionCoreIn, Subgroup.map_le_iff_le_comap,
    involutionCore_eq_closure, Subgroup.closure_le]
  intro z hz
  change IsInvolution z at hz
  have hzM : (z : X) ∈ M := z.property
  have hzX : IsInvolution (z : X) :=
    IsInvolution.map_of_injective hz M.subtype M.subtype_injective
  have hzSets : (z : X) ∈ involutionsInSet W := by
    rw [← involutionsInSet_eq_of_normalSupplement_odd hDle hDodd hW]
    exact ⟨hzM, hzX⟩
  exact hzSets.1

private theorem twoRankAtLeastTwo_normalSupplement_of_involutionCore
    {X : Type u} [Group X] [Finite X]
    {M D W : Subgroup X}
    (hDle : D ≤ M) (hDodd : Odd (Nat.card D))
    (hW : IsNormalSupplement M D W)
    (hrank : TwoRankAtLeastTwo (involutionCore M)) :
    TwoRankAtLeastTwo W := by
  have hcoreW : involutionCoreIn M ≤ W :=
    involutionCoreIn_le_of_normalSupplement_odd hDle hDodd hW
  let fX : involutionCore M →* X :=
    M.subtype.comp (involutionCore M).subtype
  let fW : involutionCore M →* W :=
    fX.codRestrict W (by
      intro z
      apply hcoreW
      exact Subgroup.mem_map_of_mem M.subtype z.property)
  have hfW : Function.Injective fW := by
    intro a b hab
    have habX : ((a : M) : X) = ((b : M) : X) := by
      simpa [fW, fX] using congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext habX)
  exact hrank.map_of_injective fW hfW

/-! ## The factorization branch -/

private theorem lemma98_fixedPoints_card_le_of_le
    {X : Type u} [Group X] [Finite X]
    {M A B : Subgroup X} (hAB : A ≤ B) :
    Nat.card (theorem4bFixedPoints M B) ≤
      Nat.card (theorem4bFixedPoints M A) := by
  let f : theorem4bFixedPoints M B → theorem4bFixedPoints M A :=
    fun omega => ⟨omega.1, fun a ha => omega.2 a (hAB ha)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : theorem4bFixedPoints M A =>
        (z : conjugateCosetSpace M)) hxy
  exact Nat.card_le_card_of_injective f hf

private theorem lemma98_normalizerIn_le_inf_of_fixedPoints_card_eq_two
    {X : Type u} [Group X] [Finite X]
    {M W U : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (hWM : W ≤ M)
    (hUD : U ≤ M ⊓ rightConjugate M t)
    (hcard : Nat.card (theorem4bFixedPoints M U) = 2) :
    normalizerIn W U ≤ M ⊓ rightConjugate M t := by
  have hnorm := normalizerIn_eq_inf_of_fixedPoints_card_eq_two
    ht htM hWM hUD hcard
  intro n hn
  have hn' : n ∈ normalizerIn
      (W ⊓ (M ⊓ rightConjugate M t)) U := by
    rw [← hnorm]
    exact hn
  exact hn'.1.2

/-- The source assertion `Ω_K = {α, β}` follows from Lemma 8.3(c) for one
nonidentity element of `K`. -/
private theorem lemma98_fixedPoints_card_K_eq_two
    {X : Type u} [Group X] [Finite X]
    {M K : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hKD : K ≤ M ⊓ rightConjugate M t)
    (hKset : (K : Set X) =
      peterfalviKSet (M ⊓ rightConjugate M t) t)
    (hKne : K ≠ ⊥) :
    Nat.card (theorem4bFixedPoints M K) = 2 := by
  obtain ⟨xK, hxneK⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  let x : X := xK
  have hxK : x ∈ K := xK.property
  have hxne : x ≠ 1 := by
    intro hx
    apply hxneK
    apply Subtype.ext
    exact hx
  have hxI : x ∈ peterfalviKSet
      (M ⊓ rightConjugate M t) t := by
    rw [← hKset]
    exact hxK
  have hzxK : Subgroup.zpowers x ≤ K :=
    Subgroup.zpowers_le.mpr hxK
  have hupper : Nat.card (theorem4bFixedPoints M K) ≤ 2 := by
    exact (lemma98_fixedPoints_card_le_of_le hzxK).trans_eq
      (d83.fixedPoints_card_eq_two hxI hxne)
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) K :=
    theorem4b_baseCoset_mem_fixedPoints (hKD.trans inf_le_left)
  have hbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) K := by
    intro k hk
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact hKD hk |>.2
  let alphaFixed : theorem4bFixedPoints M K := ⟨alpha, halpha⟩
  let betaFixed : theorem4bFixedPoints M K := ⟨beta, hbeta⟩
  have hne : alphaFixed ≠ betaFixed := by
    intro h
    apply htM
    simpa [alphaFixed, betaFixed, alpha, beta] using
      QuotientGroup.eq.mp (congrArg Subtype.val h)
  let f : Bool → theorem4bFixedPoints M K :=
    fun b => if b then betaFixed else alphaFixed
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exact (hne (by simpa [f] using hab)).elim
    · exact (hne (by simpa [f] using hab.symm)).elim
    · rfl
  have hlower : 2 ≤ Nat.card (theorem4bFixedPoints M K) := by
    simpa using Nat.card_le_card_of_injective f hf
  omega

private theorem lemma98_factorization_forces_forbidden_sup
    {X : Type u} [Group X] [Finite X]
    {M W D K : Subgroup X} {Z : Set X}
    (hW : IsNormalSupplement M D W)
    (hDle : D ≤ M)
    (hfactor : (W : Set X) =
      ((W ⊓ Subgroup.centralizer Z : Subgroup X) : Set X) *
        (normalizerIn W K : Set X))
    (hnormD : normalizerIn W K ≤ D) :
    M = (M ⊓ Subgroup.centralizer Z) ⊔ D := by
  apply le_antisymm
  · apply (le_of_eq hW.sup_eq.symm).trans
    apply sup_le
    · intro w hw
      have hwprod : w ∈
          ((W ⊓ Subgroup.centralizer Z : Subgroup X) : Set X) *
            (normalizerIn W K : Set X) := by
        rw [← hfactor]
        exact hw
      rcases Set.mem_mul.mp hwprod with ⟨c, hc, n, hn, rfl⟩
      apply Subgroup.mul_mem
      · exact Subgroup.mem_sup_left ⟨hW.le_M hc.1, hc.2⟩
      · exact Subgroup.mem_sup_right (hnormD hn)
    · exact le_sup_right
  · exact sup_le inf_le_left hDle

private theorem lemma98_factorization_branch_false
    {X : Type u} [Group X] [Finite X]
    {M W K : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hW : IsNormalSupplement M (M ⊓ rightConjugate M t) W)
    (hKset : (K : Set X) =
      peterfalviKSet (M ⊓ rightConjugate M t) t)
    (hKne : K ≠ ⊥)
    (hfactor : (W : Set X) =
      ((W ⊓ Subgroup.centralizer (involutionsInSet M) :
          Subgroup X) : Set X) *
        (normalizerIn W K : Set X))
    (hne : M ≠
      (M ⊓ Subgroup.centralizer (involutionsInSet M)) ⊔
        (M ⊓ rightConjugate M t)) :
    False := by
  have hKD : K ≤ M ⊓ rightConjugate M t := by
    intro k hk
    have hkI : k ∈ peterfalviKSet
        (M ⊓ rightConjugate M t) t := by
      rw [← hKset]
      exact hk
    exact hkI.1
  have hcard : Nat.card (theorem4bFixedPoints M K) = 2 :=
    lemma98_fixedPoints_card_K_eq_two ht htM d83 hKD hKset hKne
  have hnormD : normalizerIn W K ≤
      M ⊓ rightConjugate M t :=
    lemma98_normalizerIn_le_inf_of_fixedPoints_card_eq_two
      ht htM hW.le_M hKD hcard
  apply hne
  exact lemma98_factorization_forces_forbidden_sup
    hW inf_le_left hfactor hnormD

/-! ## Source Lemma 9.8 -/

/-- The Frobenius alternative in Lemma 9.8 is impossible.  The checked
action setup feeds the exact `[II1; 2.6]` dichotomy: Hering eliminates the
two-transitive branch, and Lemma 9.7(a) eliminates the factorization branch. -/
public theorem lemma98_not_frobenius
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (h97 : Lemma97Conclusion M t)
    (h31 : II1Hering31Ambient (G := X)) :
    ¬ Lemma98FrobeniusCase
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  change ¬ Lemma98FrobeniusCase D E t
  intro hFrob
  change K ≤ E ∧
      (K : Set X) = peterfalviKSet D t ∧
        ∃ R : Subgroup X, R ≤ E ∧
          IsFrobeniusGroupWithKernelComplement
            (K.subgroupOf E) (R.subgroupOf E) at hFrob
  rcases hFrob with ⟨hKE, hKset, R, _hRE, hfrob⟩
  have hKleW : K ≤ W := hKE.trans inf_le_left
  have hcentral : ∀ x : X, x ∈ K → x ≠ 1 →
      elementCentralizerIn W x = K := by
    intro x hxK hxne
    obtain ⟨hCWCE, hCEK⟩ :=
      lemma98_elementCentralizers_eq
        (M := M) (W := W) (K := K) (R := R) (t := t) (x := x)
        ht htM d83 hW.prop.le_M
        (by simpa [D, E] using hKE)
        (by simpa [D, K] using hKset)
        (by simpa [D, E, K] using hfrob) hxK hxne
    exact hCWCE.trans hCEK
  have hregular : ConjugationRegularOn K (involutionsInSet M) :=
    conjugationRegularOn_involutionsInSet_of_peterfalviKSet
      hM ht htM (by simpa [D, K] using hKset)
  have hstable : ∀ z, z ∈ involutionsInSet M → ∀ w, w ∈ W →
      rightConjugateElem z w ∈ involutionsInSet M := by
    intro z hz w hw
    have hwM : w ∈ M := hW.prop.le_M hw
    refine ⟨?_, isInvolution_rightConjugateElem hz.2⟩
    dsimp [rightConjugateElem]
    exact M.mul_mem (M.mul_mem (M.inv_mem hwM) hz.1) hwM
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hZeq : involutionsInSet M = involutionsInSet W :=
    involutionsInSet_eq_of_normalSupplement_odd
      (by simpa [D] using (inf_le_left :
        M ⊓ rightConjugate M t ≤ M)) hDodd hW.prop
  have hrankW : TwoRankAtLeastTwo W :=
    twoRankAtLeastTwo_normalSupplement_of_involutionCore
      (by simpa [D] using (inf_le_left :
        M ⊓ rightConjugate M t ≤ M)) hDodd hW.prop hrank
  have hKne : K ≠ ⊥ := by
    obtain ⟨x, hxI, hxne⟩ := hIne
    intro hKbot
    have hxK : x ∈ K := by
      change x ∈ (K : Set X)
      rw [hKset]
      simpa [D] using hxI
    have hxone : x = 1 := by
      simpa [hKbot] using hxK
    exact hxne hxone
  rcases ii1Theorem26Conjugation_of_action W K (involutionsInSet M)
      hKleW hstable hregular hcentral with htwo | hfactor
  · have htwoW :
        ConjugationTwoTransitiveOn W (involutionsInSet W) := by
      rw [← hZeq]
      exact htwo
    exact (h31 W htwoW) hrankW
  · exact lemma98_factorization_branch_false ht htM d83 hW.prop
      (by simpa [D, K] using hKset) hKne hfactor
      h97.ne_centralizer_sup

/-- The two conclusions of source Lemma 9.8. -/
public structure Lemma98Conclusion
    {X : Type u} [Group X]
    (D E : Subgroup X) (t : X) : Prop where
  derived_inf_fixed_ne_bot :
    (derivedSubgroup E).map E.subtype ⊓ peterfalviV D t ≠ ⊥
  not_frobenius : ¬ Lemma98FrobeniusCase D E t

/-- Source Lemma 9.8.  First the permutation-theorem contradiction rules out
the Frobenius alternative.  If `[E,E] ∩ V` were trivial, the checked
Corollary 9.6 reduction would construct precisely that forbidden alternative. -/
public theorem lemma_9_8
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (h96 : Corollary96Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t)
    (h97 : Lemma97Conclusion M t)
    (h31 : II1Hering31Ambient (G := X)) :
    Lemma98Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  let V : Subgroup X := peterfalviV D t
  have hnot : ¬ Lemma98FrobeniusCase D E t := by
    simpa [D, E] using
      lemma98_not_frobenius hM ht htM d83 hW hIne hrank h97 h31
  have hderived : (derivedSubgroup E).map E.subtype ⊓ V ≠ ⊥ := by
    intro hbot
    have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
      simpa [D] using
        inf_rightConjugate_mem_normalizer_of_isInvolution M ht
    have hDodd : Odd (Nat.card D) := by
      simpa [D] using hM.inf_rightConjugate_card_odd htM
    have hED : E ≤ D := inf_le_right
    obtain ⟨hKset, hfrob⟩ :=
      lemma98_frobenius_of_derived_inf_fixed_eq_bot
        (D := D) (E := E) ht hDnorm hDodd hED
        (by simpa [D] using hIne)
        (by simpa [D, E] using h96)
        (by simpa [V] using hbot)
    have hKE : K ≤ E := by
      have hKder : K ≤ (derivedSubgroup E).map E.subtype := by
        simpa [D, E, K] using h96.closure_le_derived
      exact hKder.trans (Subgroup.map_subtype_le (derivedSubgroup E))
    apply hnot
    change K ≤ E ∧
      (K : Set X) = peterfalviKSet D t ∧
        ∃ R : Subgroup X, R ≤ E ∧
          IsFrobeniusGroupWithKernelComplement
            (K.subgroupOf E) (R.subgroupOf E)
    refine ⟨hKE, by simpa [K] using hKset,
      E ⊓ V, inf_le_left, ?_⟩
    simpa [K, V] using hfrob
  exact ⟨by simpa [D, E, V] using hderived, by simpa [D, E] using hnot⟩

end CFSG.BenderSuzuki
