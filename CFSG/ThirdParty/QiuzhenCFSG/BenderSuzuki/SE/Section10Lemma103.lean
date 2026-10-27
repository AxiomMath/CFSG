module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma101
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Permutation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PermutationQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PermutationRegular
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Base
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Lemma 10.3

This file develops notation `(10D)` and the normalizer action used in source
Lemma 10.3.  The first layer proves the Witt two-transitivity assertion and
the uniqueness of the involution of `M` centralized by the selected subgroup
`P`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- The source fixed-point set `Omega_P`, as a type carrying the restricted
normalizer action. -/
@[expose] public def lemma103OmegaP
    {X : Type u} [Group X] (M P : Subgroup X) : Type u :=
  {omega : conjugateCosetSpace M //
    omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P}

/-- Source notation `N^* = N_X(P)`. -/
@[expose] public def lemma103NStar
    {X : Type u} [Group X] (P : Subgroup X) : Subgroup X :=
  Subgroup.normalizer (P : Set X)

/-- The canonical action of `N^*` on `Omega_P`. -/
@[reducible, expose] public def lemma103NormalizerAction
    {X : Type u} [Group X] (M P : Subgroup X) :
    MulAction (lemma103NStar P) (lemma103OmegaP M P) :=
  normalizerFixedPointAction X (conjugateCosetSpace M) P

/-- Source notation `N_0^*`, the kernel of the action of `N^*` on
`Omega_P`. -/
@[reducible, expose] public def lemma103NZeroStar
    {X : Type u} [Group X] (M P : Subgroup X) :
    Subgroup (lemma103NStar P) := by
  letI : MulAction (lemma103NStar P) (lemma103OmegaP M P) :=
    lemma103NormalizerAction M P
  exact pointStabilizerCore (lemma103NStar P) (lemma103OmegaP M P)

public instance lemma103NZeroStar_normal
    {X : Type u} [Group X] (M P : Subgroup X) :
    (lemma103NZeroStar M P).Normal := by
  letI : MulAction (lemma103NStar P) (lemma103OmegaP M P) :=
    lemma103NormalizerAction M P
  change (pointStabilizerCore (lemma103NStar P) (lemma103OmegaP M P)).Normal
  exact pointStabilizerCore_normal

/-- Source notation `bar N^* = N^*/N_0^*`. -/
public abbrev lemma103NBar
    {X : Type u} [Group X] (M P : Subgroup X) :=
  lemma103NStar P ⧸ lemma103NZeroStar M P

/-- The canonical faithful quotient action of `bar N^*` on `Omega_P`. -/
@[reducible, expose] public def lemma103QuotientAction
    {X : Type u} [Group X] (M P : Subgroup X) :
    MulAction (lemma103NBar M P) (lemma103OmegaP M P) := by
  letI : MulAction (lemma103NStar P) (lemma103OmegaP M P) :=
    lemma103NormalizerAction M P
  letI :
      (pointStabilizerCore (lemma103NStar P) (lemma103OmegaP M P)).Normal :=
    pointStabilizerCore_normal
  exact pointStabilizerCoreQuotientAction

/-- The quotient action in `(10D)` is faithful. -/
public theorem lemma103QuotientAction_faithful
    {X : Type u} [Group X] (M P : Subgroup X) :
    @FaithfulSMul (lemma103NBar M P) (lemma103OmegaP M P)
      (lemma103QuotientAction M P).toSMul := by
  letI : MulAction (lemma103NStar P) (lemma103OmegaP M P) :=
    lemma103NormalizerAction M P
  letI :
      (pointStabilizerCore (lemma103NStar P) (lemma103OmegaP M P)).Normal :=
    pointStabilizerCore_normal
  exact faithfulSMul_pointStabilizerCoreQuotientAction

/-- The exact Lemma 10.1-to-Witt application: the selected `P` is Sylow in
the stabilizer of the base/`t` injective pair. -/
public theorem Lemma101Conclusion.normalizer_twoTransitiveOn_fixedPoints
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (ht : IsInvolution t) (htM : t ∉ M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    IsTwoTransitiveOn
      (Subgroup.normalizer (d.choice.P : Set X))
      (fixedPointsOfSubgroup X (conjugateCosetSpace M) d.choice.P) := by
  apply witt_normalizer_twoTransitiveOn_fixedPoints
    d.choice.p_prime htwo (baseOutsidePair M t htM) d.choice.P
  rw [stabilizer_baseOutsidePair ht htM]
  exact d.P_sylow_D

/-- Native restricted-action form of Lemma 10.3(a). -/
public theorem Lemma101Conclusion.normalizer_action_twoPretransitive
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (ht : IsInvolution t) (htM : t ∉ M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    letI : MulAction (lemma103NStar d.choice.P)
        (lemma103OmegaP M d.choice.P) :=
      lemma103NormalizerAction M d.choice.P
    MulAction.IsMultiplyPretransitive
      (lemma103NStar d.choice.P) (lemma103OmegaP M d.choice.P) 2 := by
  apply normalizerFixedPointAction_twoPretransitive
  exact d.normalizer_twoTransitiveOn_fixedPoints ht htM htwo

/-- The action kernel fixes the base coset and the coset of `t`; therefore its
ambient image lies in the two-point stabilizer `D = M cap M^t`. -/
public theorem lemma103_pointStabilizerCore_le_pairStabilizer
    {X : Type u} [Group X]
    {M P : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hPD : P ≤ M ⊓ rightConjugate M t) :
    (lemma103NZeroStar M P).map (lemma103NStar P).subtype ≤
      M ⊓ rightConjugate M t := by
  letI : MulAction (lemma103NStar P) (lemma103OmegaP M P) :=
    lemma103NormalizerAction M P
  let alpha : lemma103OmegaP M P :=
    ⟨QuotientGroup.mk 1,
      theorem4b_baseCoset_mem_fixedPoints (hPD.trans inf_le_left)⟩
  have hbetaFixed :
      (QuotientGroup.mk t : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) P := by
    intro p hp
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact (hPD hp).2
  let beta : lemma103OmegaP M P :=
    ⟨QuotientGroup.mk t, hbetaFixed⟩
  rintro x ⟨n, hncore, rfl⟩
  have hnalpha : n • alpha = alpha :=
    MulAction.mem_stabilizer_iff.mp
      (pointStabilizerCore_le_stabilizer alpha hncore)
  have hnbeta : n • beta = beta :=
    MulAction.mem_stabilizer_iff.mp
      (pointStabilizerCore_le_stabilizer beta hncore)
  constructor
  · have hnbase : (n : X) •
        (QuotientGroup.mk 1 : conjugateCosetSpace M) = QuotientGroup.mk 1 :=
      congrArg Subtype.val hnalpha
    have hnbaseStab : (n : X) ∈ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M) :=
      MulAction.mem_stabilizer_iff.mpr hnbase
    simpa [baseCoset_stabilizer] using hnbaseStab
  · have hnt : (n : X) •
        (QuotientGroup.mk t : conjugateCosetSpace M) = QuotientGroup.mk t :=
      congrArg Subtype.val hnbeta
    have hntStab : (n : X) ∈ MulAction.stabilizer X
        (QuotientGroup.mk t : conjugateCosetSpace M) :=
      MulAction.mem_stabilizer_iff.mpr hnt
    simpa [conjugateCoset_stabilizer, ht.inv_eq_self] using hntStab

/-- The left Peterfalvi decomposition `D = V I` makes the element of the
anti-fixed set conjugating a fixed involution unique. -/
public theorem lemma103_peterfalvi_conjugator_unique
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t u0 k l : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hVeq : peterfalviV D t =
      D ⊓ Subgroup.centralizer ({u0} : Set X))
    (hk : k ∈ peterfalviKSet D t)
    (hl : l ∈ peterfalviKSet D t)
    (hku : rightConjugateElem u0 k = rightConjugateElem u0 l) :
    k = l := by
  classical
  let V : Subgroup X := peterfalviV D t
  let I : Set X := peterfalviKSet D t
  let v : X := l * k⁻¹
  have hvD : v ∈ D := D.mul_mem hl.1 (D.inv_mem hk.1)
  have hvC : v ∈ Subgroup.centralizer ({u0} : Set X) :=
    mul_inv_mem_centralizer_singleton_iff_rightConjugateElem_eq.mpr hku.symm
  have hvV : v ∈ V := by
    change v ∈ peterfalviV D t
    rw [hVeq]
    exact ⟨hvD, hvC⟩
  let leftDecomp := (PFchapter1section1.lemma_a t D ht hDodd hDnorm).1
  let pair1 : V × I := (⟨1, V.one_mem⟩, ⟨l, hl⟩)
  let pair2 : V × I := (⟨v, hvV⟩, ⟨k, hk⟩)
  have hpairs : pair1 = pair2 := by
    apply leftDecomp.injOn (Set.mem_univ pair1) (Set.mem_univ pair2)
    change (1 : X) * l = v * k
    simp [v]
  exact (congrArg (fun p : V × I => (p.2 : X)) hpairs).symm

/-- Any involution of `M` centralized by `P` is the selected involution `u`.
This is the source equality `C_{mathcal Z_M}(P) = {u}` in pointwise form. -/
public theorem Lemma101Conclusion.involution_eq_u_of_centralized
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t z : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hzM : z ∈ M) (hz : IsInvolution z)
    (hPz : d.choice.P ≤ Subgroup.centralizer ({z} : Set X)) :
    z = d83.u := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let P : Subgroup X := d.choice.P
  obtain ⟨k, hkI, huk⟩ :=
    hM.exists_mem_peterfalviKSet_of_involution_mem
      d83.u_mem_M d83.u_involution ht htM hzM hz
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hVeq : V = D ⊓ Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [V, D, peterfalviV] using d83.centralizer_eq
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hcard : Nat.card P = 1 := by simp [hPbot]
    exact d.choice.initial.card_P_prime.ne_one (by simpa [P] using hcard)
  obtain ⟨pP, hpne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  let p : X := pP
  have hpP : p ∈ P := pP.property
  have hpneX : p ≠ 1 := by
    intro hp
    apply hpne
    apply Subtype.ext
    exact hp
  have hpV : p ∈ V := by
    simpa [P, V, D] using d.choice.P_le_V hpP
  let kp : X := p * k * p⁻¹
  have hkpI : kp ∈ peterfalviKSet D t :=
    peterfalviKSet_conj_mem_of_mem_V hpV (by simpa [D] using hkI)
  have hpCu : p ∈ Subgroup.centralizer ({d83.u} : Set X) :=
    (hVeq ▸ hpV).2
  have hpCz : p ∈ Subgroup.centralizer ({z} : Set X) := hPz hpP
  have hukp : rightConjugateElem d83.u kp = z := by
    have hpu : Commute p d83.u :=
      Subgroup.mem_centralizer_singleton_iff.mp hpCu
    have hpz : Commute p z :=
      Subgroup.mem_centralizer_singleton_iff.mp hpCz
    have hpuConj : p⁻¹ * d83.u * p = d83.u := by
      calc
        p⁻¹ * d83.u * p = p⁻¹ * (d83.u * p) := by rw [mul_assoc]
        _ = p⁻¹ * (p * d83.u) := by rw [hpu.eq]
        _ = d83.u := by simp
    calc
      rightConjugateElem d83.u kp =
          p * rightConjugateElem d83.u k * p⁻¹ := by
        dsimp [kp, rightConjugateElem]
        calc
          (p * k * p⁻¹)⁻¹ * d83.u * (p * k * p⁻¹) =
              p * k⁻¹ * (p⁻¹ * d83.u * p) * k * p⁻¹ := by group
          _ = p * k⁻¹ * d83.u * k * p⁻¹ := by rw [hpuConj]
          _ = p * (k⁻¹ * d83.u * k) * p⁻¹ := by group
      _ = p * z * p⁻¹ := by rw [huk]
      _ = z := by rw [hpz.eq]; simp
  have hkpeq : kp = k :=
    lemma103_peterfalvi_conjugator_unique ht hDodd hDnorm hVeq
      hkpI (by simpa [D] using hkI) (hukp.trans huk.symm)
  have hcomm : k * p = p * k := by
    have h := congrArg (fun x : X => x * p) hkpeq
    simpa [kp, mul_assoc] using h.symm
  have hkone : k = 1 :=
    d.choice.P_fixedPointFree p hpP hpneX k
      (by simpa [D] using hkI) hcomm
  simpa [hkone, rightConjugateElem] using huk.symm

private theorem lemma103_isMulCommutative_of_forall_sq_one
    {A : Type*} [Group A] (hA : ∀ x : A, x ^ 2 = 1) :
    IsMulCommutative A := by
  refine IsMulCommutative.mk <| Std.Commutative.mk ?_
  intro a b
  have hinv : ∀ x : A, x⁻¹ = x := by
    intro x
    have hx : x * x = 1 := by simpa [pow_two] using hA x
    calc
      x⁻¹ = x⁻¹ * 1 := by simp
      _ = x⁻¹ * (x * x) := by rw [hx]
      _ = x := by simp
  calc
    a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := by simp
    _ = b * a := by rw [hinv a, hinv b]

/-- A strongly embedded subgroup containing exactly one involution forces the
ambient finite group to have 2-rank at most one. -/
public theorem not_twoRankAtLeastTwo_of_unique_involution_in_stronglyEmbedded
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} (hM : IsStronglyEmbedded M)
    {u0 : G} (huM : u0 ∈ M) (hu : IsInvolution u0)
    (hunique : ∀ z : G, z ∈ M → IsInvolution z → z = u0) :
    ¬ TwoRankAtLeastTwo G := by
  classical
  rintro ⟨E, hEcard, hEsq⟩
  have hEne : E ≠ ⊥ := by
    intro hEbot
    have : Nat.card E = 1 := by simp [hEbot]
    omega
  obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEne
  have haInv : IsInvolution (a : G) := by
    refine ⟨?_, ?_⟩
    · intro ha
      apply hane
      exact Subtype.ext ha
    · exact congrArg Subtype.val (hEsq a)
  obtain ⟨g, hag⟩ := hM.involutions_conjugate haInv hu
  let f : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  let E' : Subgroup G := E.map f
  have hE'card : Nat.card E' = 4 := by
    calc
      Nat.card E' = Nat.card E :=
        Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
      _ = 4 := hEcard
  have hE'sq : ∀ x : E', x ^ 2 = 1 := by
    intro x
    rcases x.property with ⟨y, hyE, hyx⟩
    apply Subtype.ext
    have hySq : y ^ 2 = (1 : G) :=
      congrArg Subtype.val (hEsq ⟨y, hyE⟩)
    change (x : G) ^ 2 = 1
    calc
      (x : G) ^ 2 = (f y) ^ 2 := by rw [hyx]
      _ = f (y ^ 2) := (map_pow f y 2).symm
      _ = f 1 := by rw [hySq]
      _ = 1 := map_one f
  have huE' : u0 ∈ E' := by
    apply Subgroup.mem_map.mpr
    refine ⟨(a : G), a.property, ?_⟩
    simpa [f, MulAut.conj_apply, rightConjugateElem] using hag
  letI : IsMulCommutative E' :=
    lemma103_isMulCommutative_of_forall_sq_one hE'sq
  have hE'M : E' ≤ M := by
    intro x hxE
    let xE : E' := ⟨x, hxE⟩
    let uE : E' := ⟨u0, huE'⟩
    have hcomm : x * u0 = u0 * x :=
      congrArg Subtype.val (mul_comm' xE uE)
    exact hM.centralizer_le huM hu
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  have hE'le : E' ≤ Subgroup.zpowers u0 := by
    intro x hxE
    by_cases hxone : x = 1
    · subst x
      exact (Subgroup.zpowers u0).one_mem
    · have hxInv : IsInvolution x := by
        refine ⟨hxone, ?_⟩
        exact congrArg Subtype.val (hE'sq ⟨x, hxE⟩)
      rw [hunique x (hE'M hxE) hxInv]
      exact Subgroup.mem_zpowers u0
  have hzpLe : Subgroup.zpowers u0 ≤ E' :=
    Subgroup.zpowers_le.mpr huE'
  have hE'eq : E' = Subgroup.zpowers u0 :=
    le_antisymm hE'le hzpLe
  have huOrder : orderOf u0 = 2 :=
    (orderOf_eq_prime_iff).2 ⟨hu.sq_eq_one, hu.ne_one⟩
  have hzCard : Nat.card (Subgroup.zpowers u0) = 2 := by
    simp [Nat.card_zpowers, huOrder]
  rw [hE'eq, hzCard] at hE'card
  omega

/-- The normalizer `N^* = N_X(P)` has 2-rank one.  All its involutions
centralize `P`; within the inherited strongly embedded subgroup the preceding
Peterfalvi argument shows that the selected `u` is the unique involution. -/
public theorem Lemma101Conclusion.not_twoRankAtLeastTwo_normalizer
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t) :
    ¬ TwoRankAtLeastTwo (lemma103NStar d.choice.P) := by
  classical
  let P : Subgroup X := d.choice.P
  let N : Subgroup X := lemma103NStar P
  let MN : Subgroup N := M.comap N.subtype
  have htCentP : t ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (d.choice.P_le_V hpP).2
  have htN : t ∈ N := centralizer_le_normalizer P htCentP
  have huCentP : d83.u ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have hpV := d.choice.P_le_V hpP
    change p ∈ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({t} : Set X) at hpV
    rw [d83.centralizer_eq] at hpV
    exact Subgroup.mem_centralizer_singleton_iff.mp hpV.2
  have huN : d83.u ∈ N := centralizer_le_normalizer P huCentP
  let uN : N := ⟨d83.u, huN⟩
  have huNInv : IsInvolution uN :=
    IsInvolution.subtype d83.u_involution huN
  have hproper : MN ≠ ⊤ := by
    intro htop
    let tN : N := ⟨t, htN⟩
    have htTop : tN ∈ (⊤ : Subgroup N) := Subgroup.mem_top tN
    rw [← htop] at htTop
    exact htM htTop
  have huMN : uN ∈ MN := d83.u_mem_M
  have hNstrong : IsStronglyEmbedded MN :=
    hM.comap_of_injective N.subtype Subtype.val_injective hproper
      ⟨uN, huMN, huNInv⟩
  have hinvolutionCentralizesP :
      ∀ z : N, IsInvolution z →
        (z : X) ∈ Subgroup.centralizer (P : Set X) := by
    intro z hz
    obtain ⟨g, hzg⟩ := hNstrong.involutions_conjugate hz huNInv
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    have hgNorm : (g : X) ∈ Subgroup.normalizer (P : Set X) := g.property
    have hqP : (g : X)⁻¹ * p * (g : X) ∈ P :=
      ((Subgroup.mem_normalizer_iff''.mp hgNorm) p).mp hpP
    have huq : ((g : X)⁻¹ * p * (g : X)) * d83.u =
        d83.u * ((g : X)⁻¹ * p * (g : X)) :=
      Subgroup.mem_centralizer_iff.mp huCentP _ hqP
    have hconj : (g : X)⁻¹ * (z : X) * (g : X) = d83.u :=
      congrArg Subtype.val hzg
    have hback : (g : X) * d83.u * (g : X)⁻¹ = (z : X) := by
      rw [← hconj]
      group
    calc
      p * (z : X) = (g : X) *
          (((g : X)⁻¹ * p * (g : X)) * d83.u) * (g : X)⁻¹ := by
        rw [← hback]
        group
      _ = (g : X) *
          (d83.u * ((g : X)⁻¹ * p * (g : X))) * (g : X)⁻¹ := by
        rw [huq]
      _ = ((g : X) * d83.u * (g : X)⁻¹) * p := by group
      _ = (z : X) * p := by rw [hback]
  have huniqueN :
      ∀ z : N, z ∈ MN → IsInvolution z → z = uN := by
    intro z hzMN hz
    have hzCent := hinvolutionCentralizesP z hz
    have hPz : P ≤ Subgroup.centralizer ({(z : X)} : Set X) := by
      intro p hpP
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzCent p hpP
    apply Subtype.ext
    exact d.involution_eq_u_of_centralized hM ht htM d83 hzMN
      (IsInvolution.map_of_injective hz N.subtype Subtype.val_injective) hPz
  exact not_twoRankAtLeastTwo_of_unique_involution_in_stronglyEmbedded
    hNstrong huMN huNInv huniqueN

/-- The kernel `N_0^*` has odd order because it embeds in the odd-order
two-point stabilizer `D`. -/
public theorem Lemma101Conclusion.actionKernel_odd
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M) :
    Odd (Nat.card (lemma103NZeroStar M d.choice.P)) := by
  let N : Subgroup X := lemma103NStar d.choice.P
  let core : Subgroup N := lemma103NZeroStar M d.choice.P
  have hcoreD : core.map N.subtype ≤ M ⊓ rightConjugate M t := by
    exact lemma103_pointStabilizerCore_le_pairStabilizer ht
      (d.choice.P_le_V.trans inf_le_left)
  have hmapOdd : Odd (Nat.card (core.map N.subtype)) :=
    (hM.inf_rightConjugate_card_odd htM).of_dvd_nat
      (Subgroup.card_dvd_of_le hcoreD)
  rw [Subgroup.card_map_of_injective N.subtype_injective] at hmapOdd
  exact hmapOdd

/-- Lemma 10.3(b): quotienting `N^*` by its odd action kernel preserves the
2-rank-one conclusion. -/
public theorem Lemma101Conclusion.quotient_not_twoRankAtLeastTwo
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t) :
    ¬ TwoRankAtLeastTwo (lemma103NBar M d.choice.P) := by
  exact not_twoRankAtLeastTwo_quotient_of_odd
    (lemma103NZeroStar M d.choice.P)
    (d.actionKernel_odd hM ht htM)
    (d.not_twoRankAtLeastTwo_normalizer hM ht htM d83)

/-! ## Lemma 10.3(c) -/

/-- The fixed-point set `Omega_P` has at least three points.  This is the
specialization of the three-fixed-points construction from Proposition 8.4
to the subgroup selected in Lemma 10.1. -/
private theorem lemma103_three_le_omega
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t) :
    3 ≤ Nat.card (lemma103OmegaP M d.choice.P) := by
  apply hM.three_le_fixedPoints_of_le_lemma83V ht htM d83
  intro p hpP
  have hpV := d.choice.P_le_V hpP
  change p ∈ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({t} : Set X) at hpV
  rw [d83.centralizer_eq] at hpV
  exact hpV

/-- The canonical faithful quotient action inherits double transitivity from
the normalizer action. -/
private theorem lemma103_quotient_action_twoPretransitive
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (ht : IsInvolution t) (htM : t ∉ M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    letI : MulAction (lemma103NBar M d.choice.P)
        (lemma103OmegaP M d.choice.P) :=
      lemma103QuotientAction M d.choice.P
    MulAction.IsMultiplyPretransitive
      (lemma103NBar M d.choice.P) (lemma103OmegaP M d.choice.P) 2 := by
  letI : MulAction (lemma103NStar d.choice.P)
      (lemma103OmegaP M d.choice.P) :=
    lemma103NormalizerAction M d.choice.P
  have htwoN := d.normalizer_action_twoPretransitive ht htM htwo
  simpa [lemma103NBar, lemma103NZeroStar, lemma103QuotientAction,
    pointStabilizerCoreQuotientAction] using
      pointStabilizerCoreQuotientAction_twoPretransitive htwoN

/-- An involution remains nontrivial after quotienting by a normal subgroup
of odd order. -/
private theorem lemma103_quotient_involution_of_odd_kernel
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    {z : G} (hz : IsInvolution z) :
    IsInvolution (QuotientGroup.mk' N z) := by
  constructor
  · intro hzq
    have hzN : z ∈ N := (QuotientGroup.eq_one_iff z).mp hzq
    let zN : N := ⟨z, hzN⟩
    have hzNI : IsInvolution zN := IsInvolution.subtype hz hzN
    have horder : orderOf zN = 2 :=
      orderOf_eq_prime hzNI.sq_eq_one hzNI.ne_one
    have hdvd : 2 ∣ Nat.card N := by
      rw [← horder]
      exact orderOf_dvd_natCard zN
    exact hNodd.not_two_dvd_nat hdvd
  · simpa using congrArg (QuotientGroup.mk' N) hz.sq_eq_one

/-- The complete conclusions of source Lemma 10.3.  The package is
Type-valued because Sections 10--11 reuse the chosen regular normal subgroup
`Qbar`. -/
public structure Lemma103Conclusion
    {X : Type u} [Group X] [Finite X]
    (M P : Subgroup X) (u0 : X) where
  uStar : lemma103NStar P
  uStar_eq : (uStar : X) = u0
  uBar : lemma103NBar M P
  uBar_eq : uBar = QuotientGroup.mk' (lemma103NZeroStar M P) uStar
  normalizer_twoPretransitive :
    letI : MulAction (lemma103NStar P) (lemma103OmegaP M P) :=
      lemma103NormalizerAction M P
    MulAction.IsMultiplyPretransitive
      (lemma103NStar P) (lemma103OmegaP M P) 2
  quotient_twoPretransitive :
    letI : MulAction (lemma103NBar M P) (lemma103OmegaP M P) :=
      lemma103QuotientAction M P
    MulAction.IsMultiplyPretransitive
      (lemma103NBar M P) (lemma103OmegaP M P) 2
  quotient_faithful :
    @FaithfulSMul (lemma103NBar M P) (lemma103OmegaP M P)
      (lemma103QuotientAction M P).toSMul
  quotient_not_twoRankAtLeastTwo :
    ¬ TwoRankAtLeastTwo (lemma103NBar M P)
  uBar_involution : IsInvolution uBar
  Qbar : Subgroup (lemma103NBar M P)
  q : ℕ
  q_prime : q.Prime
  Qbar_normal : Qbar.Normal
  Qbar_elementaryAbelian : IsElementaryAbelian q Qbar
  Qbar_ne_bot : Qbar ≠ ⊥
  Qbar_pretransitive :
    letI : MulAction (lemma103NBar M P) (lemma103OmegaP M P) :=
      lemma103QuotientAction M P
    MulAction.IsPretransitive Qbar (lemma103OmegaP M P)
  Qbar_regular :
    letI : MulAction (lemma103NBar M P) (lemma103OmegaP M P) :=
      lemma103QuotientAction M P
    ∀ omega : lemma103OmegaP M P,
      MulAction.stabilizer Qbar omega = ⊥
  Qbar_card_odd : Odd (Nat.card Qbar)
  factorization :
    Qbar ⊔ Subgroup.centralizer ({uBar} : Set (lemma103NBar M P)) = ⊤

/-- Source Lemma 10.3.  The odd action kernel preserves the rank-one
conclusion in the faithful quotient.  Its nontrivial solvable odd core then
contains a regular elementary-abelian minimal normal subgroup; the unique
fixed point of the image of `u` gives the final centralizer factorization. -/
public theorem lemma_10_3
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    Nonempty (Lemma103Conclusion M d.choice.P d83.u) := by
  classical
  let P : Subgroup X := d.choice.P
  let N : Subgroup X := lemma103NStar P
  let Omega : Type u := lemma103OmegaP M P
  letI : Finite Omega := by
    dsimp [Omega, lemma103OmegaP]
    infer_instance
  have hPD : P ≤ M ⊓ rightConjugate M t := by
    exact d.choice.P_le_V.trans inf_le_left
  have hPM : P ≤ M := hPD.trans inf_le_left
  have hP_le_Du : P ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({d83.u} : Set X) := by
    intro p hpP
    have hpV := d.choice.P_le_V hpP
    change p ∈ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({t} : Set X) at hpV
    rw [d83.centralizer_eq] at hpV
    exact hpV
  have huCentP : d83.u ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    exact Subgroup.mem_centralizer_singleton_iff.mp (hP_le_Du hpP).2
  have huN : d83.u ∈ N := centralizer_le_normalizer P huCentP
  let uStar : N := ⟨d83.u, huN⟩
  have huStar : IsInvolution uStar :=
    IsInvolution.subtype d83.u_involution huN

  letI : MulAction N Omega := lemma103NormalizerAction M P
  have htwoN : MulAction.IsMultiplyPretransitive N Omega 2 := by
    simpa [P, N, Omega] using
      d.normalizer_action_twoPretransitive ht htM htwo

  let hcoreNormal : (pointStabilizerCore N Omega).Normal :=
    pointStabilizerCore_normal
  letI : (pointStabilizerCore N Omega).Normal := hcoreNormal
  have hcoreOdd : Odd (Nat.card (pointStabilizerCore N Omega)) := by
    simpa [P, N, Omega, lemma103NZeroStar] using
      d.actionKernel_odd hM ht htM
  let Nbar := N ⧸ pointStabilizerCore N Omega
  letI : MulAction Nbar Omega := pointStabilizerCoreQuotientAction
  have hfaithful : FaithfulSMul Nbar Omega :=
    faithfulSMul_pointStabilizerCoreQuotientAction
  letI : FaithfulSMul Nbar Omega := hfaithful
  have htwoBar : MulAction.IsMultiplyPretransitive Nbar Omega 2 := by
    simpa [Nbar, N, Omega] using
      pointStabilizerCoreQuotientAction_twoPretransitive htwoN
  have htransBar : MulAction.IsPretransitive Nbar Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive

  let uBar : Nbar := QuotientGroup.mk' (pointStabilizerCore N Omega) uStar
  have huBar : IsInvolution uBar :=
    lemma103_quotient_involution_of_odd_kernel
      (pointStabilizerCore N Omega) hcoreOdd huStar

  let alpha : Omega :=
    ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints hPM⟩
  have huBaseAmbient : d83.u •
      (QuotientGroup.mk 1 : conjugateCosetSpace M) = QuotientGroup.mk 1 := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa [baseCoset_stabilizer] using d83.u_mem_M
  have huAlpha : uBar • alpha = alpha := by
    have hrepresentative : uBar • alpha = uStar • alpha := by
      have hmk := @pointStabilizerCoreQuotientAction_mk_smul
        N Omega _ (lemma103NormalizerAction M P) hcoreNormal uStar alpha
      change @SMul.smul Nbar Omega
          (@pointStabilizerCoreQuotientAction N Omega _
            (lemma103NormalizerAction M P) hcoreNormal).toSMul
          (QuotientGroup.mk uStar) alpha = uStar • alpha
      exact hmk
    rw [hrepresentative]
    apply Subtype.ext
    change (uStar : X) • alpha.val = alpha.val
    simpa [uStar, alpha] using huBaseAmbient
  obtain ⟨gamma, hgamma, hgammaUnique⟩ :=
    hM.involution_fixed_coset_unique d83.u_involution
  have huBaseUnique : ∀ omega : conjugateCosetSpace M,
      d83.u • omega = omega → omega = QuotientGroup.mk 1 := by
    intro omega homega
    exact (hgammaUnique omega homega).trans
      (hgammaUnique (QuotientGroup.mk 1) huBaseAmbient).symm
  have huUnique : ∀ omega : Omega, uBar • omega = omega → omega = alpha := by
    intro omega homega
    have hrepresentative : uBar • omega = uStar • omega := by
      have hmk := @pointStabilizerCoreQuotientAction_mk_smul
        N Omega _ (lemma103NormalizerAction M P) hcoreNormal uStar omega
      change @SMul.smul Nbar Omega
          (@pointStabilizerCoreQuotientAction N Omega _
            (lemma103NormalizerAction M P) hcoreNormal).toSMul
          (QuotientGroup.mk uStar) omega = uStar • omega
      exact hmk
    have homegaStar : uStar • omega = omega :=
      hrepresentative.symm.trans homega
    have hval := congrArg Subtype.val homegaStar
    change (uStar : X) • omega.val = omega.val at hval
    have homegaAmbient : d83.u • omega.val = omega.val := by
      simpa [uStar] using hval
    apply Subtype.ext
    exact huBaseUnique omega.val homegaAmbient

  have hRank : ¬ TwoRankAtLeastTwo Nbar := by
    simpa [P, N, Nbar] using
      d.quotient_not_twoRankAtLeastTwo hM ht htM d83
  have hcoreFactor : pPrimeCore 2 Nbar ⊔
      Subgroup.centralizer ({uBar} : Set Nbar) = ⊤ :=
    PFAppendixII.pPrimeCore_sup_centralizer_eq_top_of_not_twoRank hRank huBar
  have hoddCoreNe : pPrimeCore 2 Nbar ≠ ⊥ :=
    pPrimeCore_two_ne_bot_of_factorization
      htransBar huBar alpha huAlpha hcoreFactor
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddCoreOdd : Odd (Nat.card (pPrimeCore 2 Nbar)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := Nbar) (p := 2))
  have hoddCoreSolv : IsSolvable (pPrimeCore 2 Nbar) :=
    odd_order_theorem (pPrimeCore 2 Nbar) hoddCoreOdd
  obtain ⟨Qbar, q, hQnormal, hqPrime, hQelem, hQne,
      hQtrans, hQregular⟩ :=
    exists_regular_elementaryAbelian_normal_of_solvable_normal
      htwoBar (pPrimeCore 2 Nbar) pPrimeCore_normal hoddCoreNe hoddCoreSolv
  have hOmegaCard : 3 ≤ Nat.card Omega := by
    simpa [P, Omega] using lemma103_three_le_omega d hM ht htM d83
  have hQcardEq : Nat.card Qbar = Nat.card Omega :=
    natCard_eq_of_pretransitive_stabilizer_bot hQtrans hQregular alpha
  have hQcard : 3 ≤ Nat.card Qbar := by
    rw [hQcardEq]
    exact hOmegaCard
  have hQodd : Odd (Nat.card Qbar) :=
    elementaryAbelian_card_odd_of_not_twoRank_of_three_le
      hRank hqPrime hQelem hQcard
  letI : Fact q.Prime := ⟨hqPrime⟩
  letI : IsElementaryAbelian q Qbar := hQelem
  have hQcomm : IsMulCommutative Qbar := inferInstance
  have hfactor : Qbar ⊔ Subgroup.centralizer ({uBar} : Set Nbar) = ⊤ :=
    regular_normal_sup_centralizer_eq_top Qbar hQnormal hQcomm
      hQtrans hQregular huBar alpha huAlpha huUnique
  refine ⟨{
    uStar := by simpa [P, N] using uStar
    uStar_eq := rfl
    uBar := by simpa [P, N, Nbar] using uBar
    uBar_eq := rfl
    normalizer_twoPretransitive := by simpa [P, N, Omega] using htwoN
    quotient_twoPretransitive := by
      simpa [P, N, Nbar, Omega, pointStabilizerCoreQuotientAction] using
        htwoBar
    quotient_faithful := lemma103QuotientAction_faithful M d.choice.P
    quotient_not_twoRankAtLeastTwo := by
      simpa [P, N, Nbar] using hRank
    uBar_involution := by simpa [P, N, Nbar] using huBar
    Qbar := by simpa [P, N, Nbar] using Qbar
    q := q
    q_prime := hqPrime
    Qbar_normal := by simpa [P, N, Nbar] using hQnormal
    Qbar_elementaryAbelian := by simpa [P, N, Nbar] using hQelem
    Qbar_ne_bot := by simpa [P, N, Nbar] using hQne
    Qbar_pretransitive := by
      simpa [P, N, Nbar, Omega, pointStabilizerCoreQuotientAction] using
        hQtrans
    Qbar_regular := by
      simpa [P, N, Nbar, Omega, pointStabilizerCoreQuotientAction] using
        hQregular
    Qbar_card_odd := by simpa [P, N, Nbar] using hQodd
    factorization := by simpa [P, N, Nbar] using hfactor }⟩

end CFSG.BenderSuzuki
