module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.proposition_2_9
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.theorem_1_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki VI.2.3

A finite group with a nontrivial proper subgroup whose distinct conjugates
intersect trivially is a Frobenius group with that subgroup as complement.
The proof follows Suzuki's exceptional-character construction.
-/

noncomputable section

attribute [local instance] Fintype.ofFinite

namespace CFSG.BenderSuzuki.External.Suzuki.VI

universe u

open Section1

private theorem frobeniusTI_relative
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hRne : R ≠ ⊥)
    (hTI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g)) :
    IsTISubsetRelative R (R : Set G) := by
  have hRnontrivial : ∃ r : G, r ∈ (R : Set G) ∧ r ≠ 1 := by
    rw [Subgroup.ne_bot_iff_exists_ne_one] at hRne
    rcases hRne with ⟨r, hr⟩
    exact ⟨r, r.property, fun h => hr (Subtype.ext h)⟩
  apply (suzuki_ch6_proposition_2_8 R (R : Set G)
    (fun _ hx => hx) (Subgroup.le_normalizer (H := R)) hRnontrivial).2
  intro g hgR z hz
  rcases hz with ⟨⟨r, hrR, rfl⟩, hzR⟩
  have hzConj : g * r * g⁻¹ ∈ R.conjBy g := by
    rw [Subgroup.conjBy, Subgroup.mem_map]
    exact ⟨r, hrR, rfl⟩
  have hzOne := Subgroup.disjoint_def.mp (hTI g hgR) hzR hzConj
  simpa using hzOne

private theorem isVirtualCharacter_zsmul_23
    {G : Type u} [Group G] [Finite G]
    (n : ℤ) {chi : ClassFunction G}
    (hchi : Theory.Character.IsVirtualCharacter chi) :
    Theory.Character.IsVirtualCharacter ((n : ℂ) • chi) := by
  classical
  rcases hchi with ⟨r, m, k, rho, rfl⟩
  refine ⟨r, fun i => n * m i, k, rho, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations,
    Finset.mul_sum, mul_assoc]

@[expose] public def frobeniusExceptionalCharacter
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (chi : ClassFunction R) : ClassFunction G :=
  degree chi • principalCharacter G +
    inducedCF R (chi - degree chi • principalCharacter R)

public theorem frobeniusExceptionalCharacter_degree
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (chi : ClassFunction R) :
    degree (frobeniusExceptionalCharacter R chi) = degree chi := by
  unfold frobeniusExceptionalCharacter
  have hind := degree_inducedClassFunction R
    (chi - degree chi • principalCharacter R)
  change degree chi * principalCharacter G 1 +
      inducedCF R (chi - degree chi • principalCharacter R) 1 = degree chi
  change inducedCF R (chi - degree chi • principalCharacter R) 1 =
      (R.index : ℂ) *
        (chi - degree chi • principalCharacter R) 1 at hind
  rw [hind]
  simp [degree]

private theorem frobeniusTheta_virtual
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (chi : ClassFunction R)
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    Theory.Character.IsVirtualCharacter
      (chi - degree chi • principalCharacter R) := by
  rcases hchi with ⟨n, rho, hirr, hchar⟩
  have hchi' : IsIrreducibleCharacterOnGroup chi :=
    ⟨n, rho, hirr, hchar⟩
  have hdegree : degree chi = (n : ℂ) := by
    rw [hchar, degree_representation_character]
    simp
  have hprincipalR : Theory.Character.IsVirtualCharacter
      (principalCharacter R) :=
    Section3.isVirtualCharacter_principalCharacter
  have hscaledR : Theory.Character.IsVirtualCharacter
      (degree chi • principalCharacter R) := by
    rw [hdegree]
    simpa using isVirtualCharacter_zsmul_23 (n : ℤ) hprincipalR
  exact Section3.isVirtualCharacter_sub
    (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hchi') hscaledR

private theorem frobeniusExceptionalCharacter_virtual
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (chi : ClassFunction R)
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    Theory.Character.IsVirtualCharacter
      (frobeniusExceptionalCharacter R chi) := by
  rcases hchi with ⟨n, rho, hirr, hchar⟩
  have hdegree : degree chi = (n : ℂ) := by
    rw [hchar, degree_representation_character]
    simp
  have hprincipalG : Theory.Character.IsVirtualCharacter
      (principalCharacter G) :=
    Section3.isVirtualCharacter_principalCharacter
  have hscaledG : Theory.Character.IsVirtualCharacter
      (degree chi • principalCharacter G) := by
    rw [hdegree]
    simpa using isVirtualCharacter_zsmul_23 (n : ℤ) hprincipalG
  unfold frobeniusExceptionalCharacter
  exact Section3.isVirtualCharacter_add hscaledG
    (Section2.inducedCF_isVirtualCharacter_of_virtualCharacter R
      (frobeniusTheta_virtual R chi ⟨n, rho, hirr, hchar⟩))

private theorem frobeniusExceptionalCharacter_apply_subgroup
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hrel : IsTISubsetRelative R (R : Set G))
    (chi : ClassFunction R) (hchi : IsIrreducibleCharacterOnGroup chi)
    (r : R) (hr : (r : G) ≠ 1) :
    frobeniusExceptionalCharacter R chi (r : G) = chi r := by
  let theta : ClassFunction R :=
    chi - degree chi • principalCharacter R
  have hthetaVirtual : Theory.Character.IsVirtualCharacter theta := by
    exact frobeniusTheta_virtual R chi hchi
  have hvalue := (suzuki_ch6_proposition_2_9 R (R : Set G) hrel theta
    hthetaVirtual (fun r hrnot => False.elim (hrnot r.property))).1
      (r : G) r.property hr
  change degree chi * 1 + inducedCF R theta (r : G) = chi r
  rw [hvalue]
  simp [theta, principalCharacter]

private theorem frobeniusExceptionalCharacter_irreducible
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hrel : IsTISubsetRelative R (R : Set G))
    (chi : ClassFunction R) (hchi : IsIrreducibleCharacterOnGroup chi) :
    IsIrreducibleCharacterOnGroup
      (frobeniusExceptionalCharacter R chi) := by
  classical
  by_cases hprincipal : chi = principalCharacter R
  · subst chi
    have hstar : frobeniusExceptionalCharacter R (principalCharacter R) =
        principalCharacter G := by
      ext g
      simp [frobeniusExceptionalCharacter, degree, principalCharacter,
        inducedCF, inducedClassFunction]
    rw [hstar]
    exact Section3.principalCharacter_isIrreducibleCharacterOnGroup
  · rcases hchi with ⟨n, rho, hirr, hchar⟩
    have hchi' : IsIrreducibleCharacterOnGroup chi :=
      ⟨n, rho, hirr, hchar⟩
    have hnpos : 0 < n := by
      by_contra hn
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
      apply Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup chi hchi'
      rw [hchar, degree_representation_character, hnzero]
      simp
    have hdegree : degree chi = (n : ℂ) := by
      rw [hchar, degree_representation_character]
      simp
    let theta : ClassFunction R :=
      chi - degree chi • principalCharacter R
    let indTheta : ClassFunction G := inducedCF R theta
    have hthetaVirtual : Theory.Character.IsVirtualCharacter theta :=
      frobeniusTheta_virtual R chi hchi'
    have hthetaOne : theta 1 = 0 := by
      simp [theta, degree, principalCharacter]
    have hsupport : ∀ r : R, (r : G) ∉ (R : Set G) → theta r = 0 := by
      intro r hr
      exact False.elim (hr r.property)
    have hchiSelf : scalarProduct R chi chi = 1 :=
      scalarProduct_irreducibleCharacter_self hchi'
    have hprincipalSelfR : scalarProduct R (principalCharacter R)
        (principalCharacter R) = 1 :=
      scalarProduct_irreducibleCharacter_self
        Section3.principalCharacter_isIrreducibleCharacterOnGroup
    have hprincipalSelfG : scalarProduct G (principalCharacter G)
        (principalCharacter G) = 1 :=
      scalarProduct_irreducibleCharacter_self
        Section3.principalCharacter_isIrreducibleCharacterOnGroup
    have hchiPrincipal : scalarProduct R chi (principalCharacter R) = 0 :=
      scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne hchi' hprincipal
    have hprincipalChi : scalarProduct R (principalCharacter R) chi = 0 := by
      rw [← scalarProduct_star_swap (principalCharacter R) chi, hchiPrincipal]
      simp
    have hthetaPrincipal : scalarProduct R theta (principalCharacter R) =
        -degree chi := by
      simp [theta, Section5.scalarProduct_sub_left,
        scalarProduct_smul_left, hchiPrincipal, hprincipalSelfR]
    have hprincipalTheta : scalarProduct R (principalCharacter R) theta =
        -degree chi := by
      simp [theta, Section5.scalarProduct_sub_right,
        scalarProduct_smul_right, hprincipalChi, hprincipalSelfR, hdegree]
    have hthetaSelf : scalarProduct R theta theta =
        1 + degree chi * degree chi := by
      simp [theta, Section5.scalarProduct_sub_left,
        Section5.scalarProduct_sub_right, scalarProduct_smul_left,
        scalarProduct_smul_right, hchiSelf, hchiPrincipal, hprincipalChi,
        hprincipalSelfR, hdegree]
    have h29 := suzuki_ch6_proposition_2_9 R (R : Set G) hrel theta
      hthetaVirtual hsupport
    have hindPrincipal : scalarProduct G indTheta (principalCharacter G) =
        -degree chi := by
      exact h29.2.1.trans hthetaPrincipal
    have hprincipalInd : scalarProduct G (principalCharacter G) indTheta =
        -degree chi := by
      rw [← scalarProduct_star_swap (principalCharacter G) indTheta,
        hindPrincipal]
      simp [hdegree]
    have hindSelf : scalarProduct G indTheta indTheta =
        1 + degree chi * degree chi := by
      exact (h29.2.2 hthetaOne theta hthetaVirtual hsupport).trans hthetaSelf
    have hstarSelf : scalarProduct G
        (frobeniusExceptionalCharacter R chi)
        (frobeniusExceptionalCharacter R chi) = 1 := by
      change scalarProduct G
        (degree chi • principalCharacter G + indTheta)
        (degree chi • principalCharacter G + indTheta) = 1
      simp [scalarProduct_add_left, Section5.scalarProduct_add_right,
        scalarProduct_smul_left, scalarProduct_smul_right,
        hprincipalSelfG, hindPrincipal, hprincipalInd, hindSelf, hdegree]
    have hsigned := Section5.signed_irreducible_of_virtual_norm_one_pf59
      (frobeniusExceptionalCharacter_virtual R chi hchi') hstarSelf
    rcases hsigned with ⟨eps, heps, mu, hmu, hstarMu⟩
    rcases heps with rfl | rfl
    · rw [hstarMu]
      simpa using hmu
    · exfalso
      rcases hmu with ⟨m, sigma, hsigma, hmuChar⟩
      have hmpos : 0 < m := by
        by_contra hm
        have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
        apply Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup mu
          ⟨m, sigma, hsigma, hmuChar⟩
        rw [hmuChar, degree_representation_character, hmzero]
        simp
      have hdegStar := frobeniusExceptionalCharacter_degree R chi
      have hvalue := congrFun hstarMu 1
      change degree (frobeniusExceptionalCharacter R chi) =
        (-1 : ℂ) * degree mu at hvalue
      rw [hdegStar, hdegree, hmuChar, degree_representation_character] at hvalue
      have hre := congrArg Complex.re hvalue
      norm_num at hre
      omega

/-- The exceptional character attached to an irreducible character of a TI
complement is irreducible. -/
public theorem frobeniusExceptionalCharacter_irreducible_of_TI
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hRne : R ≠ ⊥)
    (hTI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g))
    (chi : ClassFunction R) (hchi : IsIrreducibleCharacterOnGroup chi) :
    IsIrreducibleCharacterOnGroup (frobeniusExceptionalCharacter R chi) := by
  exact frobeniusExceptionalCharacter_irreducible R
    (frobeniusTI_relative R hRne hTI) chi hchi

/-- On nonidentity elements of a TI complement, the exceptional character
agrees with its source character. -/
public theorem frobeniusExceptionalCharacter_apply_subgroup_of_TI
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hRne : R ≠ ⊥)
    (hTI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g))
    (chi : ClassFunction R) (hchi : IsIrreducibleCharacterOnGroup chi)
    (r : R) (hr : (r : G) ≠ 1) :
    frobeniusExceptionalCharacter R chi (r : G) = chi r := by
  exact frobeniusExceptionalCharacter_apply_subgroup R
    (frobeniusTI_relative R hRne hTI) chi hchi r hr
private theorem frobeniusExceptionalCharacter_apply_kernelSet
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (chi : ClassFunction R) (x : G)
    (hx : ∀ g : G, g * x * g⁻¹ ∈ R → g * x * g⁻¹ = 1) :
    frobeniusExceptionalCharacter R chi x = degree chi := by
  classical
  let theta : ClassFunction R :=
    chi - degree chi • principalCharacter R
  have hthetaOne : theta 1 = 0 := by
    simp [theta, degree, principalCharacter]
  have hinduced : inducedCF R theta x = 0 := by
    unfold inducedCF inducedClassFunction
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro g _hg
    split
    next hmem =>
      have hone := hx g hmem
      have hsub : (⟨g * x * g⁻¹, hmem⟩ : R) = 1 := Subtype.ext hone
      simp [hsub, hthetaOne]
    next hnot => rfl
  change degree chi * principalCharacter G x + inducedCF R theta x = degree chi
  rw [hinduced]
  simp [principalCharacter]

private theorem exists_irreducibleCharacter_separates_ne_one_23
    {Q : Type u} [Group Q] [Finite Q]
    {q : Q} (hq : q ≠ 1) :
    ∃ chi : ClassFunction Q,
      IsIrreducibleCharacterOnGroup chi ∧ chi q ≠ chi 1 := by
  classical
  rcases Theory.Character.second_orthogonality (G := Q) with
    ⟨ι, hι, chi, hchi, horth⟩
  letI : Fintype ι := hι
  by_contra hnone
  push Not at hnone
  have hvalues : ∀ i : ι,
      chi i (ConjClasses.mk q) = chi i (ConjClasses.mk (1 : Q)) := by
    intro i
    have hirrBook :=
      isBookIrreducibleCharacter_of_representation_irreducible
        (chi i) (hchi.1 i)
    have hirr := isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (ofConjClassFunction (chi i)) hirrBook
    have hi := hnone (ofConjClassFunction (chi i)) hirr
    simpa [ofConjClassFunction] using hi
  have hqclass : ConjClasses.mk q ≠ ConjClasses.mk (1 : Q) := by
    intro hclass
    have hconj : IsConj q (1 : Q) :=
      (ConjClasses.mk_eq_mk_iff_isConj).mp hclass
    exact hq (isConj_one_left.mp hconj)
  have hzero := (horth q 1).2 hqclass
  have hsumEq :
      (∑ i : ι, chi i (ConjClasses.mk q) *
          star (chi i (ConjClasses.mk (1 : Q)))) =
        ∑ i : ι, chi i (ConjClasses.mk (1 : Q)) *
          star (chi i (ConjClasses.mk (1 : Q))) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hvalues i]
  have hone := (horth (1 : Q) (1 : Q)).1 rfl
  have hcard :
      Nat.card {x : Q // x * (1 : Q) = (1 : Q) * x} = Nat.card Q := by
    exact Nat.card_congr
      { toFun := fun x => x.1
        invFun := fun x => ⟨x, by simp⟩
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; rfl }
  have hcardNe : (Nat.card Q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Q)).ne'
  have hsumZero :
      (∑ i : ι, chi i (ConjClasses.mk (1 : Q)) *
          star (chi i (ConjClasses.mk (1 : Q)))) = 0 := by
    rw [← hsumEq]
    exact hzero
  have hsumCard :
      (∑ i : ι, chi i (ConjClasses.mk (1 : Q)) *
          star (chi i (ConjClasses.mk (1 : Q)))) = (Nat.card Q : ℂ) := by
    simpa [hcard] using hone
  exact hcardNe (hsumCard.symm.trans hsumZero)

private theorem frobeniusKernel_exists_with_mem_iff
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hRne : R ≠ ⊥)
    (hTI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g)) :
    ∃ K : Subgroup G, K.Normal ∧
      ∀ x : G, x ∈ K ↔
        ∀ g : G, g * x * g⁻¹ ∈ R → g * x * g⁻¹ = 1 := by
  classical
  let Irr := {chi : ClassFunction R // IsIrreducibleCharacterOnGroup chi}
  let starChi : Irr → ClassFunction G := fun i =>
    frobeniusExceptionalCharacter R i.1
  have hrel := frobeniusTI_relative R hRne hTI
  have hstar : ∀ i : Irr, IsIrreducibleCharacterOnGroup (starChi i) := by
    intro i
    exact frobeniusExceptionalCharacter_irreducible R hrel i.1 i.2
  let dim : Irr → ℕ := fun i => Classical.choose (hstar i)
  let rhoData : ∀ i : Irr,
      ∃ rho : Representation ℂ G (Fin (dim i) → ℂ),
        Representation.IsIrreducible rho ∧ starChi i = rho.character :=
    fun i => Classical.choose_spec (hstar i)
  let rho : (i : Irr) → Representation ℂ G (Fin (dim i) → ℂ) :=
    fun i => Classical.choose (rhoData i)
  have hrho : ∀ i : Irr,
      Representation.IsIrreducible (rho i) ∧ starChi i = (rho i).character :=
    fun i => Classical.choose_spec (rhoData i)
  let K : Subgroup G := ⨅ i : Irr, (rho i).ker
  have hKnormal : K.Normal := by
    exact Subgroup.normal_iInf_normal fun i => (rho i).normal_ker
  refine ⟨K, hKnormal, ?_⟩
  intro x
  constructor
  · intro hx g hxgR
    by_contra hxgone
    let r : R := ⟨g * x * g⁻¹, hxgR⟩
    have hrone : r ≠ 1 := by
      intro hr
      exact hxgone (Subtype.ext_iff.mp hr)
    rcases exists_irreducibleCharacter_separates_ne_one_23 hrone with
      ⟨chi, hchi, hsep⟩
    let i : Irr := ⟨chi, hchi⟩
    have hxker : x ∈ (rho i).ker := (Subgroup.mem_iInf.mp hx) i
    have hygker : g * x * g⁻¹ ∈ (rho i).ker :=
      (rho i).normal_ker.conj_mem x hxker g
    letI : Representation.IsIrreducible (rho i) := (hrho i).1
    have hcharEq := (suzuki_ch6_theorem_1_8_ii (rho i)
      (g * x * g⁻¹)).2 hygker
    have hstarEq : starChi i (g * x * g⁻¹) = starChi i 1 := by
      simpa [hrho i |>.2] using hcharEq
    have hleft : starChi i (g * x * g⁻¹) = chi r := by
      change frobeniusExceptionalCharacter R chi (r : G) = chi r
      exact frobeniusExceptionalCharacter_apply_subgroup R hrel chi hchi r hxgone
    have hright : starChi i 1 = chi 1 := by
      change frobeniusExceptionalCharacter R chi 1 = chi 1
      change degree (frobeniusExceptionalCharacter R chi) = degree chi
      exact frobeniusExceptionalCharacter_degree R chi
    exact hsep (hleft.symm.trans (hstarEq.trans hright))
  · intro hx
    rw [Subgroup.mem_iInf]
    intro i
    letI : Representation.IsIrreducible (rho i) := (hrho i).1
    apply (suzuki_ch6_theorem_1_8_ii (rho i) x).1
    rw [← (hrho i).2]
    have hleft := frobeniusExceptionalCharacter_apply_kernelSet R i.1 x hx
    have hright := frobeniusExceptionalCharacter_degree R i.1
    change starChi i x = starChi i 1
    exact hleft.trans hright.symm

private theorem frobeniusConjugacyClosure_card
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G)
    (hTI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g)) :
    Nat.card {x : G // ∃ r : R, (r : G) ≠ 1 ∧
      ∃ a : G, x = a⁻¹ * (r : G) * a} =
        (Nat.card R - 1) * R.index := by
  classical
  let Omega := Quotient (QuotientGroup.rightRel R)
  let T0 := {r : R // (r : G) ≠ 1}
  let U := {x : G // ∃ r : R, (r : G) ≠ 1 ∧
    ∃ a : G, x = a⁻¹ * (r : G) * a}
  let f : Omega × T0 → U := fun qt =>
    let a : G := Quotient.out qt.1
    ⟨a⁻¹ * (qt.2.1 : G) * a, ⟨qt.2.1, qt.2.2, a, rfl⟩⟩
  have hfBij : Function.Bijective f := by
    constructor
    · intro qt1 qt2 hEq
      rcases qt1 with ⟨q1, t1⟩
      rcases qt2 with ⟨q2, t2⟩
      let a1 : G := Quotient.out q1
      let a2 : G := Quotient.out q2
      have hval : a1⁻¹ * (t1.1 : G) * a1 =
          a2⁻¹ * (t2.1 : G) * a2 := congrArg Subtype.val hEq
      by_cases hq : q1 = q2
      · have ha : a2 = a1 := by
          simpa [a1, a2] using congrArg Quotient.out hq.symm
        have ht : t1 = t2 := by
          apply Subtype.ext
          rw [ha] at hval
          have hc := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, mul_assoc] using hc
        cases hq
        cases ht
        rfl
      · have hgNotR : a2 * a1⁻¹ ∉ R := by
          intro hgR
          apply hq
          calc
            q1 = Quotient.mk'' a1 := (Quotient.out_eq' q1).symm
            _ = Quotient.mk'' a2 :=
              Quotient.sound' (QuotientGroup.rightRel_apply.mpr hgR)
            _ = q2 := Quotient.out_eq' q2
        have hgInvNotR : a1 * a2⁻¹ ∉ R := by
          intro hgR
          apply hgNotR
          have := R.inv_mem hgR
          simpa using this
        have ht1Conj : (t1.1 : G) ∈ R.conjBy (a1 * a2⁻¹) := by
          rw [Subgroup.conjBy, Subgroup.mem_map]
          refine ⟨(t2.1 : G), t2.1.property, ?_⟩
          have hc := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [mul_assoc] using hc.symm
        have ht1one : (t1.1 : G) = 1 :=
          Subgroup.disjoint_def.mp (hTI (a1 * a2⁻¹) hgInvNotR)
            t1.1.property ht1Conj
        exact False.elim (t1.2 ht1one)
    · intro x
      rcases x.2 with ⟨r, hrne, a, hxa⟩
      let q : Omega := Quotient.mk'' a
      let b : G := Quotient.out q
      have habR : a * b⁻¹ ∈ R := by
        have hqb : (Quotient.mk'' b : Omega) = Quotient.mk'' a := by
          change (Quotient.mk'' (Quotient.out q) : Omega) = q
          exact Quotient.out_eq' q
        exact QuotientGroup.rightRel_apply.mp (Quotient.exact' hqb)
      let n : G := a * b⁻¹
      have hnInvR : n⁻¹ ∈ R := R.inv_mem habR
      have hr' : n⁻¹ * (r : G) * n ∈ R :=
        R.mul_mem (R.mul_mem hnInvR r.property) habR
      have hr'ne : n⁻¹ * (r : G) * n ≠ 1 := by
        intro hone
        apply hrne
        have hc := congrArg (fun z : G => n * z * n⁻¹) hone
        simpa [mul_assoc] using hc
      refine ⟨(q, ⟨⟨n⁻¹ * (r : G) * n, hr'⟩, hr'ne⟩), ?_⟩
      apply Subtype.ext
      calc
        (f (q, ⟨⟨n⁻¹ * (r : G) * n, hr'⟩, hr'ne⟩)).1 =
            a⁻¹ * (r : G) * a := by
              simp [f, q, b, n, mul_assoc]
        _ = x := hxa.symm
  have hcardOmega : Nat.card Omega = R.index := by
    calc
      Nat.card Omega = Nat.card (G ⧸ R) := by
        exact Nat.card_congr
          (QuotientGroup.quotientRightRelEquivQuotientLeftRel R)
      _ = R.index := R.index_eq_card.symm
  have hcardT0 : Nat.card T0 = Nat.card R - 1 := by
    dsimp [T0]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [show Fintype.card {r : R // (r : G) ≠ 1} =
        Fintype.card R - Fintype.card {r : R // (r : G) = 1} by
      exact Fintype.card_subtype_compl (fun r : R => (r : G) = 1)]
    simp
  calc
    Nat.card {x : G // ∃ r : R, (r : G) ≠ 1 ∧
        ∃ a : G, x = a⁻¹ * (r : G) * a} = Nat.card (Omega × T0) := by
      exact Nat.card_congr (Equiv.ofBijective f hfBij).symm
    _ = Nat.card Omega * Nat.card T0 := Nat.card_prod _ _
    _ = (Nat.card R - 1) * R.index := by
      rw [hcardOmega, hcardT0, Nat.mul_comm]

/-- Suzuki, *Group Theory II*, Chapter 6, Theorem 2.3. -/
public theorem suzuki_ch6_theorem_2_3
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hRne : R ≠ ⊥) (hRproper : R ≠ ⊤)
    (hTI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g)) :
    ∃ K : Subgroup G, IsFrobeniusGroupWithKernelComplement K R := by
  classical
  rcases frobeniusKernel_exists_with_mem_iff R hRne hTI with
    ⟨K, hKnormal, hKmem⟩
  let U : G → Prop := fun x => ∃ r : R, (r : G) ≠ 1 ∧
    ∃ a : G, x = a⁻¹ * (r : G) * a
  have hnotU_iff (x : G) :
      (¬ U x) ↔ ∀ g : G, g * x * g⁻¹ ∈ R → g * x * g⁻¹ = 1 := by
    constructor
    · intro hx g hxgR
      by_contra hxgone
      apply hx
      refine ⟨⟨g * x * g⁻¹, hxgR⟩, hxgone, g, ?_⟩
      simp [mul_assoc]
    · intro hx hUx
      rcases hUx with ⟨r, hrne, a, rfl⟩
      apply hrne
      have hmem : a * (a⁻¹ * (r : G) * a) * a⁻¹ ∈ R := by
        have heq : a * (a⁻¹ * (r : G) * a) * a⁻¹ = (r : G) := by group
        rw [heq]
        exact r.property
      simpa [mul_assoc] using hx a hmem
  have hK_iff_notU (x : G) : x ∈ K ↔ ¬ U x :=
    (hKmem x).trans (hnotU_iff x).symm
  let eK : K ≃ {x : G // ¬ U x} :=
    { toFun := fun x => ⟨x, (hK_iff_notU x).1 x.property⟩
      invFun := fun x => ⟨x, (hK_iff_notU x).2 x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hUcard : Nat.card {x : G // U x} =
      (Nat.card R - 1) * R.index := by
    exact frobeniusConjugacyClosure_card R hTI
  have hcomplCard : Nat.card {x : G // ¬ U x} =
      Nat.card G - Nat.card {x : G // U x} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl U
  have hKcard : Nat.card K = R.index := by
    calc
      Nat.card K = Nat.card {x : G // ¬ U x} := Nat.card_congr eK
      _ = Nat.card G - Nat.card {x : G // U x} := hcomplCard
      _ = Nat.card G - (Nat.card R - 1) * R.index := by rw [hUcard]
      _ = Nat.card R * R.index - (Nat.card R - 1) * R.index := by
        rw [R.card_mul_index]
      _ = (Nat.card R - (Nat.card R - 1)) * R.index := by
        exact (Nat.sub_mul _ _ _).symm
      _ = R.index := by
        have hRcardPos : 0 < Nat.card R := Nat.card_pos
        have hsub : Nat.card R - (Nat.card R - 1) = 1 := by omega
        rw [hsub, one_mul]
  have hdisjoint : Disjoint K R := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    simpa using (hKmem x).1 hxK 1 (by simpa using hxR)
  have hcomplement : K.IsComplement' R := by
    rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
    constructor
    · calc
        Nat.card K * Nat.card R = R.index * Nat.card R := by rw [hKcard]
        _ = Nat.card R * R.index := Nat.mul_comm _ _
        _ = Nat.card G := R.card_mul_index
    · exact hdisjoint
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hindexOne : R.index = 1 := by
      rw [← hKcard, hKbot]
      simp
    exact hRproper (Subgroup.index_eq_one.mp hindexOne)
  exact ⟨K, hKnormal, hcomplement, hTI, hKne, hRne⟩

end CFSG.BenderSuzuki.External.Suzuki.VI
