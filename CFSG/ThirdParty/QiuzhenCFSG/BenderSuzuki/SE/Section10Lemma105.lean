module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma104
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PermutationQuotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_6

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Lemma 10.5

This file develops the invariant-Sylow, fixed-centralizer, and quotient-action
infrastructure used to prove that `|C_A(P)|` divides `p - 1`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u v

/-- The sharper source form of `(10E)`, retaining its normal `2`-factor and
the selected subgroup `P`. -/
public theorem lemma105_strong_10E
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (q : Nat.Primes) (hqC : q ∈ subgroupPrimeSet (lemma104C d))
    (U : Subgroup X) (hUC : U ≤ lemma104C d) (hUne : U ≠ ⊥)
    (hUq : IsPGroup q.val U) :
    let Y := U ⊔ d.choice.P
    let CY := M ⊓ Subgroup.centralizer (Y : Set X)
    let S := (pCore 2 CY).map CY.subtype
    IsPGroup 2 S ∧
      (normalizerIn (lemma104N d) U : Set X) =
        (S : Set X) *
          ((d.choice.P : Set X) *
            (normalizerIn (lemma104C d) U : Set X)) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let P : Subgroup X := d.choice.P
  let C : Subgroup X := lemma104C d
  let N : Subgroup X := lemma104N d
  let Y : Subgroup X := U ⊔ P
  let CY : Subgroup X := M ⊓ Subgroup.centralizer (Y : Set X)
  let S : Subgroup X := (pCore 2 CY).map CY.subtype
  change IsPGroup 2 S ∧
    (normalizerIn N U : Set X) =
      (S : Set X) * ((P : Set X) * (normalizerIn C U : Set X))
  have hSp : IsPGroup 2 S :=
    (pCore_isPGroup (p := 2) (G := CY)).map CY.subtype
  refine ⟨hSp, ?_⟩
  have hA1V : d.choice.initial.A1 ≤ V := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hUA : U ≤ d.choice.initial.A1 := by
    simpa [C, lemma104C] using hUC.trans inf_le_left
  have hUV : U ≤ V := hUA.trans hA1V
  have hUD : U ≤ D := hUV.trans inf_le_left
  have hUP : U ≤ Subgroup.centralizer (P : Set X) := by
    simpa [C, P, lemma104C] using hUC.trans inf_le_right
  have hqnep : q.val ≠ d.choice.p :=
    d.prime_ne_selected_of_mem_C hqC
  have hNormM : normalizerIn N U = normalizerIn M Y := by
    simpa [D, P, N, Y, lemma104N] using
      lemma104_normalizer_sup_eq d.choice.p_prime q.property hqnep
        hUD hUP hUq d.P_sylow_D
  have hFirst : (normalizerIn M Y : Set X) =
      (S : Set X) * (normalizerIn D Y : Set X) := by
    simpa [D, P, C, Y, CY, S] using
      lemma104_first_factor hM htM d83 h84 d q.property hUA hUP hUne hUq
  have hSecond : (normalizerIn D Y : Set X) =
      (P : Set X) * (normalizerIn C U : Set X) := by
    simpa [D, P, C, Y, lemma104C, normalizerIn] using
      lemma104_normalizerIn_D_sup_eq d q.property hqnep hUC hUq
  rw [hNormM, hFirst, hSecond]

private theorem lemma105_normalComplement_subtype_isComplement
    {X : Type u} [Group X]
    {N C K : Subgroup X}
    (hcomp : IsNormalComplementIn N C K) :
    let Kloc : Subgroup N := K.subgroupOf N
    let Cloc : Subgroup N := C.subgroupOf N
    Kloc.Normal ∧ Kloc.IsComplement' Cloc := by
  classical
  let Kloc : Subgroup N := K.subgroupOf N
  let Cloc : Subgroup N := C.subgroupOf N
  have hKle : K ≤ N := hcomp.le_M
  have hCle : C ≤ N := by
    rw [← hcomp.sup_eq]
    exact le_sup_right
  have hKnormal : Kloc.Normal := by
    simpa [Kloc] using hcomp.normal_in_M
  letI : Kloc.Normal := hKnormal
  have hdisj : Disjoint Kloc Cloc := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxC
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hcomp.disjoint_D) hxK hxC
  refine ⟨hKnormal, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_⟩
  rw [Set.eq_univ_iff_forall]
  intro x
  have hsupTop : Kloc ⊔ Cloc = ⊤ := by
    calc
      Kloc ⊔ Cloc = (K ⊔ C).subgroupOf N :=
        (Subgroup.subgroupOf_sup hKle hCle).symm
      _ = N.subgroupOf N := by rw [hcomp.sup_eq]
      _ = ⊤ := Subgroup.subgroupOf_self N
  have hxSup : x ∈ Kloc ⊔ Cloc := by simp [hsupTop]
  rcases (Subgroup.mem_sup_of_normal_left (s := Kloc) (t := Cloc)).1 hxSup with
    ⟨k, hk, c, hc, hkc⟩
  exact Set.mem_mul.mpr ⟨k, hk, c, hc, hkc⟩

/-- The invariant Sylow choice from the normal complement in Lemma 10.4.
Normality of the selected subgroup in `N` supplies the source containment
`P ≤ P₁`; no strengthened `[IG; 11.21]` callback is required. -/
public theorem lemma105_invariant_sylow_p
    {X : Type u} [Group X] [Finite X]
    {N C K P R : Subgroup X} {p : ℕ}
    (hp : p.Prime)
    (hcomp : IsNormalComplementIn N C K)
    (hHall : IsHallSubgroup (subgroupPrimeSet C) (C.subgroupOf N))
    (hpC : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet C)
    (hRC : R ≤ C)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card K))
    (hRsolv : Group.IsSolvable R)
    (hPp : IsPGroup p P)
    (hPK : P ≤ K)
    (hNPnorm : N ≤ Subgroup.normalizer (P : Set X)) :
    ∃ P1 : Sylow p N,
      P ≤ (P1 : Subgroup N).map N.subtype ∧
      R ≤ Subgroup.normalizer
        (((P1 : Subgroup N).map N.subtype : Subgroup X) : Set X) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let Kloc : Subgroup N := K.subgroupOf N
  let Cloc : Subgroup N := C.subgroupOf N
  have hKle : K ≤ N := hcomp.le_M
  have hCle : C ≤ N := by
    rw [← hcomp.sup_eq]
    exact le_sup_right
  have hKnormal : Kloc.Normal := by
    simpa [Kloc] using hcomp.normal_in_M
  letI : Kloc.Normal := hKnormal
  have hcompLoc : Kloc.IsComplement' Cloc :=
    (lemma105_normalComplement_subtype_isComplement hcomp).2
  have hKHall : IsHallSubgroup (subgroupPrimeSet C)ᶜ Kloc :=
    Section14.section14_complement_isHall_compl_of_isHall hHall hcompLoc.symm
  have hRN : R ≤ N := hRC.trans (by
    rw [← hcomp.sup_eq]
    exact le_sup_right)
  let Rloc : Subgroup N := R.subgroupOf N
  have hRlocsolv : Group.IsSolvable Rloc := by
    let eR : Rloc ≃* R := Subgroup.subgroupOfEquivOfLe hRN
    letI : Group.IsSolvable R := hRsolv
    exact Group.isSolvable_of_surjective (f := eR.symm.toMonoidHom) eR.symm.surjective
  have hRnormK : Rloc ≤ Subgroup.normalizer (Kloc : Set N) := by
    have htop : Subgroup.normalizer (Kloc : Set N) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hKnormal
    simpa [htop] using (show Rloc ≤ (⊤ : Subgroup N) from le_top)
  letI : Subgroup.Normalizes Rloc Kloc := ⟨hRnormK⟩
  letI : MulDistribMulAction Rloc Kloc :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer Rloc Kloc hRnormK
  letI : Group.IsSolvable Rloc := hRlocsolv
  have hcopLoc : Nat.Coprime (Nat.card Rloc) (Nat.card Kloc) := by
    have hRcard : Nat.card Rloc = Nat.card R :=
      natCard_subgroupOf_eq R N hRN
    have hKcard : Nat.card Kloc = Nat.card K :=
      natCard_subgroupOf_eq K N hKle
    simpa only [hRcard, hKcard] using hcop
  obtain ⟨S, hSinv⟩ :=
    exists_invariant_sylow_of_solvable_operator_coprime
      (G := Kloc) (A := Rloc) hcopLoc (p := p)
  have hpcompl : (⟨p, hp⟩ : Nat.Primes) ∈ (subgroupPrimeSet C)ᶜ := by
    exact Set.mem_compl hpC
  obtain ⟨PN, hPNmap⟩ :=
    Section14.section14_sylow_map_to_overgroup_sylow
      (H := N) (K := Kloc) hKHall hpcompl S
  have hPNnormal : (P.subgroupOf N).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show P ≤ N from hPK.trans hKle)).2
    exact hNPnorm
  have hPpN : IsPGroup p (P.subgroupOf N) :=
    hPp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show P ≤ N from hPK.trans hKle)).symm
  have hPPN : P.subgroupOf N ≤ (PN : Subgroup N) := by
    letI : (P.subgroupOf N).Normal := hPNnormal
    exact hPpN.le_sylow_of_normal PN
  have hPmap : P ≤ (PN : Subgroup N).map N.subtype := by
    intro x hx
    let xN : N := ⟨x, hKle (hPK hx)⟩
    exact Subgroup.mem_map.mpr ⟨xN, hPPN hx, rfl⟩
  refine ⟨PN, hPmap, ?_⟩
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨n, hnPN, hnX⟩
    rw [hPNmap] at hnPN
    rcases Subgroup.mem_map.mp hnPN with ⟨k, hkS, hkN⟩
    let rN : N := ⟨r, hRN hr⟩
    let rloc : Rloc := ⟨rN, hr⟩
    let k' : Kloc := rloc • k
    have hk'S : k' ∈ (S : Subgroup Kloc) :=
      (hSinv.invariant rloc k).1 hkS
    have hk'PN : (k' : N) ∈ (PN : Subgroup N) := by
      rw [hPNmap]
      exact Subgroup.mem_map.mpr ⟨k', hk'S, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨(k' : N), hk'PN, ?_⟩
    have hkX : ((k : Kloc) : X) = x := by
      calc
        ((k : Kloc) : X) = (n : X) :=
          congrArg (fun z : N => (z : X)) hkN
        _ = x := hnX
    have hsmulN :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
        Rloc Kloc rloc k
    have hsmulX := congrArg (fun z : N => (z : X)) hsmulN
    simpa [k', rloc, rN, hkX] using hsmulX
  · intro hx
    have hx' : r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ ∈
        ((PN : Subgroup N).map N.subtype : Subgroup X) := by
      rcases Subgroup.mem_map.mp hx with ⟨n, hnPN, hnX⟩
      rw [hPNmap] at hnPN
      rcases Subgroup.mem_map.mp hnPN with ⟨k, hkS, hkN⟩
      let rinvN : N := ⟨r⁻¹, hRN (R.inv_mem hr)⟩
      let rinvloc : Rloc := ⟨rinvN, R.inv_mem hr⟩
      let k' : Kloc := rinvloc • k
      have hk'S : k' ∈ (S : Subgroup Kloc) :=
        (hSinv.invariant rinvloc k).1 hkS
      have hk'PN : (k' : N) ∈ (PN : Subgroup N) := by
        rw [hPNmap]
        exact Subgroup.mem_map.mpr ⟨k', hk'S, rfl⟩
      apply Subgroup.mem_map.mpr
      refine ⟨(k' : N), hk'PN, ?_⟩
      have hkX : ((k : Kloc) : X) = r * x * r⁻¹ := by
        calc
          ((k : Kloc) : X) = (n : X) :=
            congrArg (fun z : N => (z : X)) hkN
          _ = r * x * r⁻¹ := hnX
      have hsmulN :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
          Rloc Kloc rinvloc k
      have hsmulX := congrArg (fun z : N => (z : X)) hsmulN
      simpa [k', rinvloc, rinvN, hkX, mul_assoc] using hsmulX
    simpa [mul_assoc] using hx'

/-- The elementwise core of the source deduction `C_{P₁}(U) = P` from the
strong form of `(10E)`. -/
public theorem lemma105_fixed_centralizer_of_strong_factor
    {X : Type u} [Group X] [Finite X]
    {N C K S P P1 U : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hpne2 : p ≠ 2)
    (hSp : IsPGroup 2 S) (hP1p : IsPGroup p P1)
    (hP_P1 : P ≤ P1) (hP1N : P1 ≤ N)
    (hSK : S ≤ K) (hPK : P ≤ K) (hP1K : P1 ≤ K)
    (hKC : Disjoint K C)
    (hUP : U ≤ Subgroup.centralizer (P : Set X))
    (hfactor : (normalizerIn N U : Set X) =
      (S : Set X) * ((P : Set X) * (normalizerIn C U : Set X))) :
    P1 ⊓ Subgroup.centralizer (U : Set X) = P := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · intro x hx
    have hxNorm : x ∈ normalizerIn N U :=
      ⟨hP1N hx.1, centralizer_le_normalizer U hx.2⟩
    have hxFactor : x ∈
        (S : Set X) * ((P : Set X) * (normalizerIn C U : Set X)) := by
      rw [← hfactor]
      exact hxNorm
    rcases hxFactor with ⟨s, hsS, z, hz, hsz⟩
    rcases hz with ⟨y, hyP, c, hc, hyc⟩
    have hsK : s ∈ K := hSK hsS
    have hyK : y ∈ K := hPK hyP
    have hxK : x ∈ K := hP1K hx.1
    have hcK : c ∈ K := by
      have heq : c = y⁻¹ * (s⁻¹ * x) := by
        calc
          c = y⁻¹ * (y * c) := by simp
          _ = y⁻¹ * z := by
            change y * c = z at hyc
            rw [hyc]
          _ = y⁻¹ * (s⁻¹ * x) := by rw [← hsz]; group
      rw [heq]
      exact K.mul_mem (K.inv_mem hyK) (K.mul_mem (K.inv_mem hsK) hxK)
    have hcC : c ∈ C := hc.1
    have hcOne : c = 1 := by
      have hcBot : c ∈ (⊥ : Subgroup X) := hKC.le_bot ⟨hcK, hcC⟩
      simpa using hcBot
    have hsy : s * y = x := by
      calc
        s * y = s * (y * 1) := by simp
        _ = s * (y * c) := by rw [hcOne]
        _ = s * z := by
          change y * c = z at hyc
          rw [hyc]
        _ = x := hsz
    have hsP1 : s ∈ P1 := by
      have hseq : s = x * y⁻¹ := by
        calc
          s = (s * y) * y⁻¹ := by simp
          _ = x * y⁻¹ := by rw [hsy]
      rw [hseq]
      exact P1.mul_mem hx.1 (P1.inv_mem (hP_P1 hyP))
    have hcop : Nat.Coprime (Nat.card S) (Nat.card P1) :=
      IsPGroup.coprime_card_of_ne 2 p (Ne.symm hpne2) S P1 hSp hP1p
    have hSP1 : Disjoint S P1 := by
      rw [disjoint_iff]
      exact Subgroup.inf_eq_bot_of_coprime hcop
    have hsOne : s = 1 := by
      have hsBot : s ∈ (⊥ : Subgroup X) := hSP1.le_bot ⟨hsS, hsP1⟩
      simpa using hsBot
    have hxy : x = y := by simpa [hsOne] using hsy.symm
    rw [hxy]
    exact hyP
  · intro x hx
    exact ⟨hP_P1 hx, le_centralizer_of_le_centralizer hUP hx⟩

private theorem lemma105_theorem4bIsSylowSubgroupOf_of_card_eq
    {G : Type u} [Group G] [Finite G] {p : ℕ}
    {P D F : Subgroup G}
    (hp : p.Prime)
    (hPsyl : theorem4bIsSylowSubgroupOf p P F)
    (hPD : P ≤ D) (hcard : Nat.card D = Nat.card F) :
    theorem4bIsSylowSubgroupOf p P D := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PF, hP⟩
  have hPcard : Nat.card P = p ^ (Nat.card F).factorization p := by
    rw [hP, Subgroup.card_map_of_injective F.subtype_injective]
    exact Sylow.card_eq_multiplicity PF
  have hPDcard : Nat.card (P.subgroupOf D) =
      p ^ (Nat.card D).factorization p := by
    rw [natCard_subgroupOf_eq P D hPD, hPcard, hcard]
  let PD : Sylow p D := Sylow.ofCard (P.subgroupOf D) hPDcard
  refine ⟨PD, ?_⟩
  have hmap : (P.subgroupOf D).map D.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD]
  simpa [PD] using hmap.symm

/-- In a doubly transitive action, a normal Sylow subgroup of one ordered
two-point stabilizer contains every `p`-subgroup of every ordered two-point
stabilizer. -/
public theorem lemma105_pSubgroup_le_pair_kernel
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega]
    {p : ℕ} (hp : p.Prime)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    {P : Subgroup G} (hPnormal : P.Normal)
    (hPcore : P ≤ pointStabilizerCore G Omega)
    (alpha beta : Omega) (hab : alpha ≠ beta)
    (hPsyl : theorem4bIsSylowSubgroupOf p P
      (MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta))
    {A : Subgroup G} (hAp : IsPGroup p A)
    (gamma delta : Omega) (hgd : gamma ≠ delta)
    (hA_pair : A ≤
      MulAction.stabilizer G gamma ⊓ MulAction.stabilizer G delta) :
    A ≤ P := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rw [MulAction.is_two_pretransitive_iff] at htwo
  obtain ⟨g, hgAlpha, hgBeta⟩ := htwo hab hgd
  let D0 : Subgroup G :=
    MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta
  let D1 : Subgroup G :=
    MulAction.stabilizer G gamma ⊓ MulAction.stabilizer G delta
  have hconj : D0.conjBy g = D1 := by
    dsimp [D0, D1]
    rw [Subgroup.conjBy,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rw [hgAlpha, hgBeta]
  have hcard : Nat.card D1 = Nat.card D0 := by
    rw [← hconj]
    exact section11_card_conjBy D0 g
  have hPD1 : P ≤ D1 := by
    intro x hxP
    exact ⟨pointStabilizerCore_le_stabilizer gamma (hPcore hxP),
      pointStabilizerCore_le_stabilizer delta (hPcore hxP)⟩
  have hPsyl1 : theorem4bIsSylowSubgroupOf p P D1 :=
    lemma105_theorem4bIsSylowSubgroupOf_of_card_eq hp
      (by simpa [D0] using hPsyl) hPD1 hcard
  obtain ⟨S, hSmap⟩ := hPsyl1
  let PD1 : Subgroup D1 := P.subgroupOf D1
  have hSeq : (S : Subgroup D1) = PD1 := by
    apply Subgroup.map_injective D1.subtype_injective
    calc
      (S : Subgroup D1).map D1.subtype = P := hSmap.symm
      _ = PD1.map D1.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPD1).symm
  have hPD1normal : PD1.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPD1).2
    have htop : Subgroup.normalizer (P : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hPnormal
    rw [htop]
    exact le_top
  have hSnormal : (S : Subgroup D1).Normal := by
    rw [hSeq]
    exact hPD1normal
  let A1 : Subgroup D1 := A.subgroupOf D1
  have hA1p : IsPGroup p A1 :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hA_pair).symm
  obtain ⟨T, hA1T⟩ := hA1p.exists_le_sylow
  letI : Unique (Sylow p D1) := Sylow.unique_of_normal S hSnormal
  have hTS : T = S := Subsingleton.elim _ _
  intro x hxA
  let xD1 : D1 := ⟨x, hA_pair hxA⟩
  have hxT : xD1 ∈ (T : Subgroup D1) := hA1T hxA
  rw [hTS, hSeq] at hxT
  exact hxT

/-- A point-fixing subgroup whose nonidentity elements fix no second point
acts fixed-point-freely by conjugation on a regular subgroup. -/
public theorem lemma105_regular_on_regular_normal
    {G : Type u} {Omega : Type v} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    (Q : Subgroup G)
    (hQregular : ∀ omega : Omega, MulAction.stabilizer Q omega = ⊥)
    (P : Subgroup G)
    (hPQnorm : P ≤ Subgroup.normalizer (Q : Set G))
    (alpha : Omega) (hPalpha : P ≤ MulAction.stabilizer G alpha)
    (hpair : ∀ {beta : Omega}, beta ≠ alpha →
      ∀ x : G, x ∈ P → x ∈ MulAction.stabilizer G beta → x = 1) :
    letI : Subgroup.Normalizes P Q := ⟨hPQnorm⟩
    letI : MulDistribMulAction P Q :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer P Q hPQnorm
    ActsRegularly P Q := by
  classical
  letI : Subgroup.Normalizes P Q := ⟨hPQnorm⟩
  letI : MulDistribMulAction P Q :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P Q hPQnorm
  intro a ha
  apply (Subgroup.eq_bot_iff_forall _).2
  intro q hq
  let az : Subgroup.zpowers a := ⟨a, Subgroup.mem_zpowers a⟩
  have hqfix : az • q = q :=
    (FixedPoints.mem_subgroup (M := Subgroup.zpowers a) (a := q)).1 hq az
  have hcomm : (a : G) * (q : G) = (q : G) * (a : G) := by
    have hconj : (a : G) * (q : G) * (a : G)⁻¹ = (q : G) := by
      exact congrArg Subtype.val hqfix
    have hmul := congrArg (fun z : G => z * (a : G)) hconj
    simpa [mul_assoc] using hmul
  let beta : Omega := (q : G) • alpha
  by_cases hbeta : beta = alpha
  · have hqstab : q ∈ MulAction.stabilizer Q alpha := by
      apply MulAction.mem_stabilizer_iff.mpr
      simpa [beta, Subgroup.smul_def] using hbeta
    rw [hQregular alpha] at hqstab
    exact Subgroup.mem_bot.mp hqstab
  · have hbetaFix : (a : G) • beta = beta := by
      have haFix : (a : G) • alpha = alpha :=
        MulAction.mem_stabilizer_iff.mp (hPalpha a.property)
      change (a : G) • ((q : G) • alpha) = (q : G) • alpha
      calc
        (a : G) • ((q : G) • alpha) =
            ((a : G) * (q : G)) • alpha := (mul_smul _ _ _).symm
        _ = ((q : G) * (a : G)) • alpha := by rw [hcomm]
        _ = (q : G) • ((a : G) • alpha) := mul_smul _ _ _
        _ = (q : G) • alpha := by rw [haFix]
    have haone : (a : G) = 1 :=
      hpair hbeta (a : G) a.property
        (MulAction.mem_stabilizer_iff.mpr hbetaFix)
    exact (ha (Subtype.ext haone)).elim

/-- The selected subgroup lies in the kernel of the normalizer action on its
fixed-point set. -/
public theorem lemma105_P_le_actionKernel
    {X : Type u} [Group X] {M P : Subgroup X} :
    P ≤ (lemma103NZeroStar M P).map (lemma103NStar P).subtype := by
  classical
  let N : Subgroup X := lemma103NStar P
  let Omega := lemma103OmegaP M P
  letI : MulAction N Omega := lemma103NormalizerAction M P
  intro x hxP
  have hxN : x ∈ N := Subgroup.le_normalizer hxP
  refine Subgroup.mem_map.mpr ⟨(⟨x, hxN⟩ : N), ?_, rfl⟩
  change (⟨x, hxN⟩ : N) ∈ pointStabilizerCore N Omega
  rw [pointStabilizerCore_eq_ker, MonoidHom.mem_ker]
  apply Equiv.ext
  intro omega
  apply Subtype.ext
  exact omega.property x hxP

/-- A normal subgroup containing a Sylow `p`-subgroup contains every
`p`-subgroup. -/
public theorem lemma105_pSubgroup_le_normal_of_sylow_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime)
    {N H : Subgroup G} (hNnormal : N.Normal)
    (SP : Sylow p G) (hSPN : (SP : Subgroup G) ≤ N)
    (hHp : IsPGroup p H) :
    H ≤ N := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hHT⟩ := hHp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T SP
  intro x hxH
  have hxT : x ∈ (T : Subgroup G) := hHT hxH
  have hxSmul : g * x * g⁻¹ ∈ (SP : Subgroup G) := by
    have hxm : g * x * g⁻¹ ∈ (g • T : Sylow p G) := by
      change g * x * g⁻¹ ∈ ((g • T : Sylow p G) : Subgroup G)
      rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact Subgroup.mem_map.mpr ⟨x, hxT, rfl⟩
    rw [hg] at hxm
    change g * x * g⁻¹ ∈ (SP : Subgroup G) at hxm
    exact hxm
  have hxNconj : g * x * g⁻¹ ∈ N := hSPN hxSmul
  have hxNback : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ ∈ N :=
    hNnormal.conj_mem (g * x * g⁻¹) hxNconj g⁻¹
  simpa [mul_assoc] using hxNback

/-- Every primary subgroup at a prime outside `π(C)` lies in the normal
complement to the Hall subgroup `C`. -/
public theorem lemma105_pSubgroup_le_normal_complement
    {X : Type u} [Group X] [Finite X]
    {N C K H : Subgroup X} {p : ℕ}
    (hp : p.Prime)
    (hcomp : IsNormalComplementIn N C K)
    (hHall : IsHallSubgroup (subgroupPrimeSet C) (C.subgroupOf N))
    (hpC : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet C)
    (hHp : IsPGroup p H) (hHN : H ≤ N) :
    H ≤ K := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let Kloc : Subgroup N := K.subgroupOf N
  let Cloc : Subgroup N := C.subgroupOf N
  have hKnormal : Kloc.Normal :=
    (lemma105_normalComplement_subtype_isComplement hcomp).1
  letI : Kloc.Normal := hKnormal
  have hcompLoc : Kloc.IsComplement' Cloc :=
    (lemma105_normalComplement_subtype_isComplement hcomp).2
  have hKHall : IsHallSubgroup (subgroupPrimeSet C)ᶜ Kloc :=
    Section14.section14_complement_isHall_compl_of_isHall
      hHall hcompLoc.symm
  have hpcompl : (⟨p, hp⟩ : Nat.Primes) ∈ (subgroupPrimeSet C)ᶜ := by
    exact Set.mem_compl hpC
  let S : Sylow p Kloc := Classical.choice (Sylow.nonempty (p := p) (G := Kloc))
  obtain ⟨PN, hPNmap⟩ :=
    Section14.section14_sylow_map_to_overgroup_sylow hKHall hpcompl S
  have hPNK : (PN : Subgroup N) ≤ Kloc := by
    rw [hPNmap]
    exact Subgroup.map_subtype_le (S : Subgroup Kloc)
  let Hloc : Subgroup N := H.subgroupOf N
  have hHlocp : IsPGroup p Hloc :=
    hHp.of_equiv (Subgroup.subgroupOfEquivOfLe hHN).symm
  have hHlocK : Hloc ≤ Kloc :=
    lemma105_pSubgroup_le_normal_of_sylow_le
      hp hKnormal PN hPNK hHlocp
  intro x hx
  exact hHlocK (show (⟨x, hHN hx⟩ : N) ∈ Hloc from hx)

/-- If `C_A(P)` is nontrivial, a Sylow `p`-subgroup of `N_M(P)` containing
`P` is strictly larger than `P`. -/
public theorem lemma105_sylow_normalizer_ne_P
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d104 : Lemma104Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t d)
    (hCne : lemma104C d ≠ ⊥)
    (P1 : Sylow d.choice.p (lemma104N d)) :
    (P1 : Subgroup (lemma104N d)).map (lemma104N d).subtype ≠
      d.choice.P := by
  classical
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  let P : Subgroup X := d.choice.P
  let N : Subgroup X := lemma104N d
  let P1X : Subgroup X := (P1 : Subgroup N).map N.subtype
  have hPp : IsPGroup d.choice.p P := by
    obtain ⟨PD, hPD⟩ := d.P_sylow_D
    change IsPGroup d.choice.p d.choice.P
    rw [hPD]
    exact PD.isPGroup'.map (M ⊓ rightConjugate M t).subtype
  have hPM : P ≤ M :=
    d.choice.P_le_V.trans (inf_le_left.trans inf_le_left)
  let PM : Subgroup M := P.subgroupOf M
  have hPMp : IsPGroup d.choice.p PM :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  obtain ⟨SM, hPMSM⟩ := hPMp.exists_le_sylow
  let Q : Subgroup X := (SM : Subgroup M).map M.subtype
  have hPQ : P ≤ Q := by
    intro x hxP
    exact Subgroup.mem_map.mpr
      ⟨(⟨x, hPM hxP⟩ : M), hPMSM hxP, rfl⟩
  have hQp : IsPGroup d.choice.p Q := SM.isPGroup'.map M.subtype
  have hPQlt : P < Q := by
    refine ⟨hPQ, ?_⟩
    intro hQP
    have hQP_eq : Q = P := le_antisymm hQP hPQ
    apply d104.P_not_sylow_M_of_C_ne_bot hCne
    exact ⟨SM, by simpa [Q, P] using hQP_eq.symm⟩
  obtain ⟨R1, hR1p, hPR1, hR1Q, hR1norm⟩ :=
    exists_larger_normalizer_pSubgroup d.choice.p_prime hQp hPQlt
  have hR1M : R1 ≤ M :=
    hR1Q.trans (Subgroup.map_subtype_le (SM : Subgroup M))
  have hR1N : R1 ≤ N := by
    intro x hx
    exact ⟨hR1M hx, hR1norm hx⟩
  intro hP1eq
  let Ploc : Subgroup N := P.subgroupOf N
  have hPN : P ≤ N := by
    intro x hx
    exact ⟨hPM hx, Subgroup.le_normalizer hx⟩
  have hPlocNormal : Ploc.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).2
    intro x hx
    exact hx.2
  let R1loc : Subgroup N := R1.subgroupOf N
  have hR1locp : IsPGroup d.choice.p R1loc :=
    hR1p.of_equiv (Subgroup.subgroupOfEquivOfLe hR1N).symm
  have hP1lePloc : (P1 : Subgroup N) ≤ Ploc := by
    intro x hx
    have hxmap : (x : X) ∈ P1X :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxP : (x : X) ∈ P := by
      change (x : X) ∈ d.choice.P
      rw [← hP1eq]
      simpa [P1X, N, P] using hxmap
    change (x : X) ∈ P
    exact hxP
  have hR1locP : R1loc ≤ Ploc := by
    letI : Ploc.Normal := hPlocNormal
    exact lemma105_pSubgroup_le_normal_of_sylow_le d.choice.p_prime
      hPlocNormal P1 hP1lePloc hR1locp
  apply hPR1.2
  intro x hx
  exact hR1locP (show (⟨x, hR1N hx⟩ : N) ∈ R1loc from hx)

/-- In the faithful quotient from Lemma 10.3, the image of a `p`-subgroup of
`N_M(P)` has no nontrivial element fixing two points. -/
public theorem lemma105_quotient_pair_stabilizer_trivial
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (ht : IsInvolution t) (htM : t ∉ M)
    {u0 : X} (d103 : Lemma103Conclusion M d.choice.P u0)
    {P1 : Subgroup X}
    (hP1N : P1 ≤ lemma104N d)
    (hP1p : IsPGroup d.choice.p P1) :
    let Nstar := lemma103NStar d.choice.P
    let core := lemma103NZeroStar M d.choice.P
    let P1star : Subgroup Nstar := P1.subgroupOf Nstar
    let Pbar : Subgroup (lemma103NBar M d.choice.P) :=
      P1star.map (QuotientGroup.mk' core)
    let alpha : lemma103OmegaP M d.choice.P :=
      ⟨QuotientGroup.mk 1,
        theorem4b_baseCoset_mem_fixedPoints
          (d.choice.P_le_V.trans (inf_le_left.trans inf_le_left))⟩
    ∀ {beta : lemma103OmegaP M d.choice.P}, beta ≠ alpha →
      ∀ xbar : lemma103NBar M d.choice.P,
        xbar ∈ Pbar →
        @SMul.smul (lemma103NBar M d.choice.P)
          (lemma103OmegaP M d.choice.P)
          (lemma103QuotientAction M d.choice.P).toSMul xbar beta = beta →
        xbar = 1 := by
  classical
  dsimp only
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  let D : Subgroup X := M ⊓ rightConjugate M t
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let core : Subgroup Nstar := lemma103NZeroStar M P
  let Omega := lemma103OmegaP M P
  letI : MulAction Nstar Omega := lemma103NormalizerAction M P
  letI : (pointStabilizerCore Nstar Omega).Normal :=
    pointStabilizerCore_normal
  letI : core.Normal := by
    dsimp [core, Nstar, P]
    infer_instance
  let Nbar := Nstar ⧸ core
  letI : MulAction Nbar Omega := by
    simpa [Nbar, core, Nstar, P] using lemma103QuotientAction M P
  have hP1Nstar : P1 ≤ Nstar := fun _ hx => (hP1N hx).2
  let P1star : Subgroup Nstar := P1.subgroupOf Nstar
  have hP1starp : IsPGroup d.choice.p P1star :=
    hP1p.of_equiv (Subgroup.subgroupOfEquivOfLe hP1Nstar).symm
  let Pbar : Subgroup Nbar := P1star.map (QuotientGroup.mk' core)
  let alpha : Omega :=
    ⟨QuotientGroup.mk 1,
      theorem4b_baseCoset_mem_fixedPoints
        (d.choice.P_le_V.trans (inf_le_left.trans inf_le_left))⟩
  have hPD : P ≤ D := d.choice.P_le_V.trans inf_le_left
  have hgammaFixed :
      (QuotientGroup.mk t : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) P := by
    intro p hpP
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact (hPD hpP).2
  let gamma : Omega := ⟨QuotientGroup.mk t, hgammaFixed⟩
  have hAlphaGamma : alpha ≠ gamma := by
    intro h
    apply htM
    have hval := congrArg Subtype.val h
    simpa [alpha, gamma] using QuotientGroup.eq.mp hval
  intro beta hbeta xbar hxbarP hxbarBeta
  rcases Subgroup.mem_map.mp hxbarP with ⟨x, hxP1star, hxxbar⟩
  have hxAlpha : x • alpha = alpha := by
    apply Subtype.ext
    change (x : X) • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
      QuotientGroup.mk 1
    apply MulAction.mem_stabilizer_iff.mp
    simpa [baseCoset_stabilizer] using (hP1N hxP1star).1
  have hxBeta : x • beta = beta := by
    have hmk := pointStabilizerCoreQuotientAction_mk_smul x beta
    calc
      x • beta = (QuotientGroup.mk' core x : Nbar) • beta := hmk.symm
      _ = xbar • beta := by rw [hxxbar]
      _ = beta := hxbarBeta
  have htwo := d103.normalizer_twoPretransitive
  obtain ⟨g, hgAlpha, hgBeta⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo)
      (Ne.symm hbeta) hAlphaGamma
  have hginvAlpha : g⁻¹ • alpha = alpha :=
    inv_smul_eq_iff.mpr hgAlpha.symm
  have hginvGamma : g⁻¹ • gamma = beta :=
    inv_smul_eq_iff.mpr hgBeta.symm
  let y : Nstar := g * x * g⁻¹
  have hyAlpha : y • alpha = alpha := by
    change (g * x * g⁻¹) • alpha = alpha
    simp only [mul_smul]
    rw [hginvAlpha, hxAlpha, hgAlpha]
  have hyGamma : y • gamma = gamma := by
    change (g * x * g⁻¹) • gamma = gamma
    simp only [mul_smul]
    rw [hginvGamma, hxBeta, hgBeta]
  have hyD : (y : X) ∈ D := by
    constructor
    · have hybase : (y : X) ∈ MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
        apply MulAction.mem_stabilizer_iff.mpr
        exact congrArg Subtype.val hyAlpha
      simpa [baseCoset_stabilizer] using hybase
    · have hyt : (y : X) ∈ MulAction.stabilizer X
          (QuotientGroup.mk t : conjugateCosetSpace M) := by
        apply MulAction.mem_stabilizer_iff.mpr
        exact congrArg Subtype.val hyGamma
      simpa [conjugateCoset_stabilizer, ht.inv_eq_self] using hyt
  let H0 : Subgroup X := D ⊓ Nstar
  have hPH0 : P ≤ H0 := fun _ hz => ⟨hPD hz, Subgroup.le_normalizer hz⟩
  have hPsylH0 : theorem4bIsSylowSubgroupOf d.choice.p P H0 :=
    theorem4bIsSylowSubgroupOf_of_between d.choice.p_prime
      d.P_sylow_D hPH0 inf_le_left
  let P0 : Subgroup H0 := P.subgroupOf H0
  have hP0normal : P0.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPH0).2
    intro z hz
    exact hz.2
  let P1g : Subgroup Nstar :=
    P1star.map (MulAut.conj g).toMonoidHom
  have hP1gp : IsPGroup d.choice.p P1g :=
    hP1starp.map (MulAut.conj g).toMonoidHom
  have hyP1g : y ∈ P1g := Subgroup.mem_map.mpr ⟨x, hxP1star, rfl⟩
  let Z : Subgroup Nstar := Subgroup.zpowers y
  have hZp : IsPGroup d.choice.p Z :=
    hP1gp.to_le (Subgroup.zpowers_le.mpr hyP1g)
  let ZX : Subgroup X := Z.map Nstar.subtype
  have hZXp : IsPGroup d.choice.p ZX := hZp.map Nstar.subtype
  have hZXH0 : ZX ≤ H0 := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨zn, hznZ, rfl⟩
    have hyle : Z ≤ H0.comap Nstar.subtype := by
      apply Subgroup.zpowers_le.mpr
      exact ⟨hyD, y.property⟩
    exact hyle hznZ
  let Z0 : Subgroup H0 := ZX.subgroupOf H0
  have hZ0p : IsPGroup d.choice.p Z0 :=
    hZXp.of_equiv (Subgroup.subgroupOfEquivOfLe hZXH0).symm
  obtain ⟨SP, hSPmap⟩ := hPsylH0
  have hSPP0 : (SP : Subgroup H0) ≤ P0 := by
    intro z hz
    have hzP : (z : X) ∈ P := by
      rw [hSPmap]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    exact hzP
  have hZ0P0 : Z0 ≤ P0 :=
    lemma105_pSubgroup_le_normal_of_sylow_le d.choice.p_prime
      hP0normal SP hSPP0 hZ0p
  have hZXP : ZX ≤ P := by
    intro z hz
    let zH : H0 := ⟨z, hZXH0 hz⟩
    exact hZ0P0 (show zH ∈ Z0 from hz)
  have hyZX : (y : X) ∈ ZX :=
    Subgroup.mem_map.mpr ⟨y, Subgroup.mem_zpowers y, rfl⟩
  have hyP : (y : X) ∈ P := hZXP hyZX
  have hxP : (x : X) ∈ P := by
    have hback : (g : X)⁻¹ * (y : X) * ((g : X)⁻¹)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (Nstar.inv_mem g.property) (y : X)).1 hyP
    simpa [y, mul_assoc] using hback
  have hxCoreMap : (x : X) ∈ core.map Nstar.subtype :=
    lemma105_P_le_actionKernel hxP
  have hxCore : x ∈ core := by
    rcases Subgroup.mem_map.mp hxCoreMap with ⟨z, hzCore, hzx⟩
    have hzx' : z = x := Nstar.subtype_injective hzx
    simpa [hzx'] using hzCore
  rw [← hxxbar]
  exact (QuotientGroup.eq_one_iff (N := core) (x := x)).2 hxCore

/-- The quotient image of the chosen Sylow subgroup acts fixed-point-freely
by conjugation on the regular normal subgroup `Qbar`. -/
public theorem lemma105_Pbar_actsRegularly_Qbar
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t u0 : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d103 : Lemma103Conclusion M d.choice.P u0)
    {P1 : Subgroup X}
    (hP1N : P1 ≤ lemma104N d)
    (hP1p : IsPGroup d.choice.p P1) :
    let Nstar := lemma103NStar d.choice.P
    let core := lemma103NZeroStar M d.choice.P
    let P1star : Subgroup Nstar := P1.subgroupOf Nstar
    let Pbar : Subgroup (lemma103NBar M d.choice.P) :=
      P1star.map (QuotientGroup.mk' core)
    let hPbarQ : Pbar ≤
        Subgroup.normalizer (d103.Qbar : Set (lemma103NBar M d.choice.P)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr d103.Qbar_normal]
      exact le_top
    @ActsRegularly Pbar d103.Qbar _ _
      (Subgroup.conjMulDistribMulActionOfLeNormalizer
        Pbar d103.Qbar hPbarQ) := by
  classical
  dsimp only
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let core : Subgroup Nstar := lemma103NZeroStar M P
  let Nbar := lemma103NBar M P
  let Omega := lemma103OmegaP M P
  letI : Finite Omega := by
    dsimp [Omega, P, lemma103OmegaP]
    infer_instance
  letI : MulAction Nstar Omega := lemma103NormalizerAction M P
  letI : (pointStabilizerCore Nstar Omega).Normal :=
    pointStabilizerCore_normal
  letI : core.Normal := by
    dsimp [core, Nstar, P]
    infer_instance
  letI : MulAction Nbar Omega := lemma103QuotientAction M P
  have hP1Nstar : P1 ≤ Nstar := fun _ hx => (hP1N hx).2
  let P1star : Subgroup Nstar := P1.subgroupOf Nstar
  let Pbar : Subgroup Nbar := P1star.map (QuotientGroup.mk' core)
  let alpha : Omega :=
    ⟨QuotientGroup.mk 1,
      theorem4b_baseCoset_mem_fixedPoints
        (d.choice.P_le_V.trans (inf_le_left.trans inf_le_left))⟩
  have hPbarAlpha : Pbar ≤ MulAction.stabilizer Nbar alpha := by
    intro xbar hxbar
    rcases Subgroup.mem_map.mp hxbar with ⟨x, hxP1star, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    calc
      (QuotientGroup.mk' core x : Nbar) • alpha = x • alpha :=
        pointStabilizerCoreQuotientAction_mk_smul x alpha
      _ = alpha := by
        apply Subtype.ext
        change (x : X) • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
          QuotientGroup.mk 1
        apply MulAction.mem_stabilizer_iff.mp
        simpa [baseCoset_stabilizer] using (hP1N hxP1star).1
  have hpair' : ∀ {beta : Omega}, beta ≠ alpha →
      ∀ xbar : Nbar, xbar ∈ Pbar →
        xbar ∈ MulAction.stabilizer Nbar beta → xbar = 1 := by
    intro beta hbeta xbar hxbar hxstab
    exact lemma105_quotient_pair_stabilizer_trivial
      d ht htM d103 hP1N hP1p hbeta xbar hxbar
        (MulAction.mem_stabilizer_iff.mp hxstab)
  have hPbarQ : Pbar ≤ Subgroup.normalizer (d103.Qbar : Set Nbar) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr d103.Qbar_normal]
    exact le_top
  exact lemma105_regular_on_regular_normal
    d103.Qbar d103.Qbar_regular Pbar hPbarQ alpha hPbarAlpha hpair'

/-- Once a `p`-subgroup image acts fixed-point-freely on `Qbar`, the checked
`[IG; 9.11(ii)]` endpoint gives cyclicity. -/
public theorem lemma105_cyclic_of_regular_Qbar
    {X : Type u} [Group X] [Finite X]
    {M P : Subgroup X} {u0 : X}
    (d103 : Lemma103Conclusion M P u0)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (Pbar : Subgroup (lemma103NBar M P))
    (hPbarp : IsPGroup p Pbar)
    (hQnorm : Pbar ≤
      Subgroup.normalizer (d103.Qbar : Set (lemma103NBar M P)))
    (hregular :
      letI : MulDistribMulAction Pbar d103.Qbar :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer
          Pbar d103.Qbar hQnorm
      ActsRegularly Pbar d103.Qbar) :
    IsCyclic Pbar := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial d103.Qbar :=
    (Subgroup.nontrivial_iff_ne_bot d103.Qbar).2 d103.Qbar_ne_bot
  letI : Subgroup.Normalizes Pbar d103.Qbar := ⟨hQnorm⟩
  letI : MulDistribMulAction Pbar d103.Qbar :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer
      Pbar d103.Qbar hQnorm
  have hcardOdd : Odd (Nat.card Pbar) := by
    obtain ⟨n, hn⟩ := hPbarp.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have htopP : IsPGroup p (⊤ : Subgroup Pbar) := hPbarp.to_subgroup ⊤
  have htopCyclic : IsCyclic (⊤ : Subgroup Pbar) :=
    isCyclic_of_odd_regular_pSubgroup hp hcardOdd hregular htopP
  exact (Subgroup.topEquiv : (⊤ : Subgroup Pbar) ≃* Pbar).isCyclic.mp
    htopCyclic

/-- A `p`-subgroup lying in both the standard pair stabilizer and
`N_X(P)` is contained in the distinguished Sylow subgroup `P`. -/
public theorem lemma105_pSubgroup_le_P_of_pair_normalizer
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    {H : Subgroup X}
    (hHp : IsPGroup d.choice.p H)
    (hHD : H ≤ M ⊓ rightConjugate M t)
    (hHN : H ≤ lemma103NStar d.choice.P) :
    H ≤ d.choice.P := by
  classical
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  let P : Subgroup X := d.choice.P
  let D : Subgroup X := M ⊓ rightConjugate M t
  let Nstar : Subgroup X := lemma103NStar P
  let H0 : Subgroup X := D ⊓ Nstar
  have hPH0 : P ≤ H0 := by
    intro x hx
    exact ⟨d.choice.P_le_V.trans inf_le_left hx, Subgroup.le_normalizer hx⟩
  have hPsylH0 : theorem4bIsSylowSubgroupOf d.choice.p P H0 :=
    theorem4bIsSylowSubgroupOf_of_between d.choice.p_prime
      d.P_sylow_D hPH0 inf_le_left
  let P0 : Subgroup H0 := P.subgroupOf H0
  have hP0normal : P0.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPH0).2
    intro z hz
    exact hz.2
  obtain ⟨SP, hSPmap⟩ := hPsylH0
  have hSPP0 : (SP : Subgroup H0) ≤ P0 := by
    intro z hz
    have hzP : (z : X) ∈ P := by
      rw [hSPmap]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    exact hzP
  obtain ⟨H0sub, hH0sub⟩ := hHp.of_equiv
    (Subgroup.subgroupOfEquivOfLe (show H ≤ H0 from fun x hx =>
      ⟨hHD hx, hHN hx⟩)).symm |>.exists_le_sylow
  letI : Unique (Sylow d.choice.p H0) := Sylow.unique_of_normal SP (by
    have hSPeq : (SP : Subgroup H0) = P0 := by
      apply Subgroup.map_injective H0.subtype_injective
      calc
        (SP : Subgroup H0).map H0.subtype = P := hSPmap.symm
        _ = P0.map H0.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hPH0).symm
    rw [hSPeq]
    exact hP0normal)
  have hH0le : (H0sub : Subgroup H0) ≤ SP := by
    have hEq : H0sub = SP := Subsingleton.elim H0sub SP
    rw [hEq]
  intro x hx
  let xH0 : H0 := ⟨x, ⟨hHD hx, hHN hx⟩⟩
  have hxH0sub : xH0 ∈ (H0sub : Subgroup H0) := hH0sub hx
  have hxSP : xH0 ∈ (SP : Subgroup H0) := hH0le hxH0sub
  change x ∈ P
  rw [hSPmap]
  exact Subgroup.mem_map.mpr ⟨xH0, hxSP, rfl⟩

/-- The action kernel meets a selected ambient `p`-subgroup exactly in the
distinguished subgroup `P`. -/
public theorem lemma105_P1_inf_actionKernel_eq_P
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (ht : IsInvolution t)
    {P1 : Subgroup X}
    (hP1p : IsPGroup d.choice.p P1)
    (hPP1 : d.choice.P ≤ P1) :
    P1 ⊓ (lemma103NZeroStar M d.choice.P).map
      (lemma103NStar d.choice.P).subtype = d.choice.P := by
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let core : Subgroup Nstar := lemma103NZeroStar M P
  let J : Subgroup X := P1 ⊓ core.map Nstar.subtype
  have hJp : IsPGroup d.choice.p J := hP1p.to_le inf_le_left
  have hcoreD : core.map Nstar.subtype ≤ M ⊓ rightConjugate M t := by
    simpa [P, Nstar, core] using
      lemma103_pointStabilizerCore_le_pairStabilizer ht
        (d.choice.P_le_V.trans inf_le_left)
  have hJD : J ≤ M ⊓ rightConjugate M t := inf_le_right.trans hcoreD
  have hJN : J ≤ Nstar := by
    intro x hx
    rcases hx.2 with ⟨n, hn, rfl⟩
    exact n.property
  apply le_antisymm
  · simpa [J, P, Nstar, core] using
      lemma105_pSubgroup_le_P_of_pair_normalizer d hJp hJD hJN
  · intro x hxP
    refine ⟨hPP1 hxP, ?_⟩
    simpa [P, Nstar, core] using lemma105_P_le_actionKernel (M := M) hxP

/-- The quotient `P₁/P` is cyclic, by transport to the regular-action image
inside the faithful rank-one quotient from Lemma 10.3. -/
public theorem lemma105_P1_quotient_cyclic
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t u0 : X}
    (hM : IsStronglyEmbedded M)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d103 : Lemma103Conclusion M d.choice.P u0)
    {P1 : Subgroup X}
    (hP1N : P1 ≤ lemma104N d)
    (hP1p : IsPGroup d.choice.p P1)
    (hPP1 : d.choice.P ≤ P1)
    [(d.choice.P.subgroupOf P1).Normal] :
    IsCyclic (P1 ⧸ (d.choice.P.subgroupOf P1)) := by
  classical
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  let P : Subgroup X := d.choice.P
  let Nstar : Subgroup X := lemma103NStar P
  let core : Subgroup Nstar := lemma103NZeroStar M P
  have hP1Nstar : P1 ≤ Nstar := fun _ hx => (hP1N hx).2
  let P1star : Subgroup Nstar := P1.subgroupOf Nstar
  let Pbar : Subgroup (lemma103NBar M P) :=
    P1star.map (QuotientGroup.mk' core)
  have hPbarReg := lemma105_Pbar_actsRegularly_Qbar d ht htM d103 hP1N hP1p
  have hPbarp : IsPGroup d.choice.p Pbar := by
    have hP1starp : IsPGroup d.choice.p P1star :=
      hP1p.of_equiv (Subgroup.subgroupOfEquivOfLe hP1Nstar).symm
    exact hP1starp.map (QuotientGroup.mk' core)
  have hPodd : Odd (Nat.card P) := by
    have hPD : P ≤ M ⊓ rightConjugate M t :=
      d.choice.P_le_V.trans inf_le_left
    exact (hM.inf_rightConjugate_card_odd htM).of_dvd_nat
      (Subgroup.card_dvd_of_le hPD)
  have hpodd : Odd d.choice.p := by
    simpa [P, d.P_card] using hPodd
  have hPbarcyc : IsCyclic Pbar := by
    letI : Finite (lemma103OmegaP M P) := by
      dsimp [lemma103OmegaP]
      infer_instance
    let hPbarQ : Pbar ≤
        Subgroup.normalizer (d103.Qbar : Set (lemma103NBar M P)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr d103.Qbar_normal]
      exact le_top
    exact lemma105_cyclic_of_regular_Qbar d103 d.choice.p_prime hpodd
      Pbar hPbarp hPbarQ hPbarReg
  let Ploc : Subgroup P1 := P.subgroupOf P1
  letI : Ploc.Normal := by
    simpa [Ploc, P] using
      (inferInstance : (d.choice.P.subgroupOf P1).Normal)
  have hInf := lemma105_P1_inf_actionKernel_eq_P d ht hP1p hPP1
  let eP1 : P1 ≃* P1star :=
    (Subgroup.subgroupOfEquivOfLe hP1Nstar).symm
  have hmap : Ploc.map eP1.toMonoidHom = core.subgroupOf P1star := by
    ext z
    constructor
    · rintro ⟨x, hxPloc, rfl⟩
      change ((eP1 x : P1star) : Nstar) ∈ core
      have hxP : (x : X) ∈ P := by
        change (x : X) ∈ P at hxPloc
        exact hxPloc
      have hxCoreMap : (x : X) ∈ core.map Nstar.subtype := by
        simpa [P, Nstar, core] using lemma105_P_le_actionKernel (M := M) hxP
      rcases Subgroup.mem_map.mp hxCoreMap with ⟨z, hzCore, hzx⟩
      have hz : z = (eP1 x : P1star) := by
        apply Nstar.subtype_injective
        simpa [eP1, P1star] using hzx
      simpa [hz] using hzCore
    · intro hzCore
      let x : P1 := ⟨((z : P1star) : Nstar), z.property⟩
      have hxInf : (x : X) ∈ P1 ⊓ core.map Nstar.subtype := by
        refine ⟨x.property, ?_⟩
        exact Subgroup.mem_map.mpr ⟨(z : P1star), hzCore, rfl⟩
      have hxP : (x : X) ∈ P := by
        have hmem := congrArg
          (fun S : Subgroup X => (x : X) ∈ S) hInf
        exact hmem.mp hxInf
      refine ⟨x, (by
        change (x : X) ∈ P
        exact hxP), ?_⟩
      apply Subtype.ext
      rfl
  let eQuot : (P1 ⧸ Ploc) ≃* (P1star ⧸ core.subgroupOf P1star) :=
    QuotientGroup.congr Ploc (core.subgroupOf P1star) eP1 hmap
  let eRange : (P1star ⧸ core.subgroupOf P1star) ≃* Pbar :=
    quotientSubgroupRangeEquiv P1star core
  have hcyc : IsCyclic (P1 ⧸ Ploc) :=
    (MulEquiv.isCyclic (eQuot.trans eRange)).2 hPbarcyc
  simpa [Ploc, P] using hcyc

/-- A faithful prime-to-`p` action on a nontrivial cyclic `p`-group has actor
order dividing `p - 1`. -/
public theorem lemma105_card_dvd_pred_of_faithful_cyclic_pgroup
    {R : Type u} {H : Type v}
    [Group R] [Finite R] [Group H] [Finite H]
    [MulDistribMulAction R H] [FaithfulSMul R H]
    {p : ℕ} (hp : p.Prime)
    (hRcop : Nat.Coprime (Nat.card R) p)
    (hHp : IsPGroup p H) (hHcyc : IsCyclic H)
    [Nontrivial H] :
    Nat.card R ∣ p - 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic H := hHcyc
  let phi : R →* MulAut H := MulDistribMulAction.toMulAut R H
  have hphi : Function.Injective phi := by
    intro a b hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α := H)
    intro x
    exact congrArg (fun f : MulAut H => f x) hab
  have hdivAut : Nat.card R ∣ Nat.card (MulAut H) :=
    Subgroup.card_dvd_of_injective phi hphi
  obtain ⟨n, hnpos, hHcard⟩ :=
    (IsPGroup.nontrivial_iff_card hHp).mp inferInstance
  have hAutCard : Nat.card (MulAut H) = p ^ (n - 1) * (p - 1) := by
    rw [IsCyclic.card_mulAut, hHcard, Nat.totient_prime_pow hp hnpos]
  have hdiv : Nat.card R ∣ p ^ (n - 1) * (p - 1) := by
    rwa [hAutCard] at hdivAut
  exact (hRcop.pow_right (n - 1)).dvd_of_dvd_mul_left hdiv

/-- Coprime fixed-point lifting turns the source centralizer calculation into
faithfulness on a nontrivial quotient. -/
public theorem lemma105_faithful_quotient_of_fixed_zpowers
    {R : Type u} {G : Type v}
    [Group R] [Finite R] [Group G] [Finite G]
    [MulDistribMulAction R G]
    (hGsolv : Group.IsSolvable G)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card G))
    (H : Subgroup G) [H.Normal]
    (hHinv : IsInvariant R G H)
    [Nontrivial (G ⧸ H)]
    (hfixed : ∀ r : R, r ≠ 1 →
      fixedPointSubgroup (Subgroup.zpowers r) G = H) :
    letI : MulDistribMulAction R (G ⧸ H) :=
      quotientMulDistribMulAction (A := R) (G := G) H hHinv
    FaithfulSMul R (G ⧸ H) := by
  classical
  let quotientActionR : MulDistribMulAction R (G ⧸ H) :=
    quotientMulDistribMulAction (A := R) (G := G) H hHinv
  letI : MulDistribMulAction R (G ⧸ H) := quotientActionR
  have hkernel : ∀ r : R,
      (∀ x : G ⧸ H, r • x = x) → r = 1 := by
    intro r hr
    by_contra hrne
    let A : Subgroup R := Subgroup.zpowers r
    have hAinv : IsInvariant A G H := by
      refine ⟨?_⟩
      intro a x
      simpa only [Subgroup.smul_def] using hHinv.invariant (a : R) x
    let quotientActionA : MulDistribMulAction A (G ⧸ H) :=
      quotientMulDistribMulAction (A := A) (G := G) H hAinv
    letI : MulDistribMulAction A (G ⧸ H) := quotientActionA
    let rA : A := ⟨r, Subgroup.mem_zpowers r⟩
    have hrAfix : ∀ x : G ⧸ H, rA • x = x := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H x
      change QuotientGroup.mk' H (r • g) = QuotientGroup.mk' H g
      simpa [quotientActionR] using hr (QuotientGroup.mk' H g)
    have hAllFixed : ∀ x : G ⧸ H,
        x ∈ fixedPointSubgroup A (G ⧸ H) := by
      intro x
      rw [FixedPoints.mem_subgroup]
      intro a
      exact smul_eq_self_of_mem_zpowers a.property (hrAfix x)
    have hAcardDvd : Nat.card A ∣ Nat.card R :=
      Subgroup.card_subgroup_dvd_card A
    have hcopA : Nat.Coprime (Nat.card A) (Nat.card G) :=
      Nat.Coprime.of_dvd_left hAcardDvd hcop
    have hfixedEq : fixedPointSubgroup A (G ⧸ H) =
        (fixedPointSubgroup A G).map (QuotientGroup.mk' H) := by
      exact fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
        (G := G) (A := A) hGsolv hcopA (∅ : Set Nat.Primes) H hAinv
    have hHmap : H.map (QuotientGroup.mk' H) = ⊥ := by
      apply (Subgroup.eq_bot_iff_forall _).2
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨h, hh, rfl⟩
      exact (QuotientGroup.eq_one_iff (N := H) (x := h)).2 hh
    have hfixedBot : fixedPointSubgroup A (G ⧸ H) = ⊥ := by
      rw [hfixedEq, hfixed r hrne, hHmap]
    obtain ⟨x, hxne⟩ := exists_ne (1 : G ⧸ H)
    have hxbot : x ∈ (⊥ : Subgroup (G ⧸ H)) := by
      rw [← hfixedBot]
      exact hAllFixed x
    exact hxne (Subgroup.mem_bot.mp hxbot)
  refine ⟨?_⟩
  intro a b hab
  have habTriv : ∀ x : G ⧸ H, (a⁻¹ * b) • x = x := by
    intro x
    calc
      (a⁻¹ * b) • x = a⁻¹ • (b • x) := mul_smul _ _ _
      _ = a⁻¹ • (a • x) := by rw [hab x]
      _ = x := by rw [← mul_smul]; simp
  have hinvMul : a⁻¹ * b = 1 := hkernel (a⁻¹ * b) habTriv
  exact inv_mul_eq_one.mp hinvMul

/-- Convert the ambient strong-`(10E)` centralizer equality into the fixed
points of a cyclic subgroup of the acting group. -/
public theorem lemma105_fixed_zpowers_eq_subgroupOf
    {X : Type u} [Group X] [Finite X]
    {R P P1 : Subgroup X}
    (hRP1 : R ≤ Subgroup.normalizer (P1 : Set X))
    (hfixed : ∀ U : Subgroup X, U ≤ R → U ≠ ⊥ →
      P1 ⊓ Subgroup.centralizer (U : Set X) = P) :
    letI : MulDistribMulAction R P1 :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer R P1 hRP1
    ∀ r : R, r ≠ 1 →
      fixedPointSubgroup (Subgroup.zpowers r) P1 = P.subgroupOf P1 := by
  letI : Subgroup.Normalizes R P1 := ⟨hRP1⟩
  letI : MulDistribMulAction R P1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R P1 hRP1
  intro r hr
  let U : Subgroup X := Subgroup.zpowers (r : X)
  have hUR : U ≤ R := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    exact R.zpow_mem r.property n
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hrbot : (r : X) ∈ (⊥ : Subgroup X) := by
      rw [← hbot]
      exact Subgroup.mem_zpowers (r : X)
    exact hr (Subtype.ext (Subgroup.mem_bot.mp hrbot))
  have hcent : P1 ⊓ Subgroup.centralizer (U : Set X) = P :=
    hfixed U hUR hUne
  have helem : elementCentralizerIn P1 (r : X) = P := by
    rw [section10_elementCentralizerIn_eq_subgroupCentralizerIn_zpowers]
    simpa [U, subgroupCentralizerIn] using hcent
  have hfp := fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
    P1 R hRP1 r
  rw [hfp, helem]

/-- Source-shaped faithful-action adapter for `R` on `P₁/P`. -/
public theorem lemma105_faithful_action_on_P1_quotient
    {X : Type u} [Group X] [Finite X]
    {R P P1 : Subgroup X}
    (hRP1 : R ≤ Subgroup.normalizer (P1 : Set X))
    (hPP1 : P ≤ P1)
    (hP1Pnorm : P1 ≤ Subgroup.normalizer (P : Set X))
    (hRPnorm : R ≤ Subgroup.normalizer (P : Set X))
    (hP1solv : Group.IsSolvable P1)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card P1))
    (hPsubne : P.subgroupOf P1 ≠ ⊤)
    (hfixed : ∀ U : Subgroup X, U ≤ R → U ≠ ⊥ →
      P1 ⊓ Subgroup.centralizer (U : Set X) = P) :
    letI : MulDistribMulAction R P1 :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer R P1 hRP1
    let H : Subgroup P1 := P.subgroupOf P1
    let hHnormal : H.Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPP1).2
      exact hP1Pnorm
    letI : H.Normal := hHnormal
    let hHinv : IsInvariant R P1 H := by
      refine ⟨?_⟩
      intro r x
      change (x : X) ∈ P ↔
        (r : X) * (x : X) * (r : X)⁻¹ ∈ P
      exact Subgroup.mem_normalizer_iff.mp (hRPnorm r.property) (x : X)
    letI : MulDistribMulAction R (P1 ⧸ H) :=
      quotientMulDistribMulAction (A := R) (G := P1) H hHinv
    FaithfulSMul R (P1 ⧸ H) := by
  classical
  letI : Subgroup.Normalizes R P1 := ⟨hRP1⟩
  letI : MulDistribMulAction R P1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R P1 hRP1
  let H : Subgroup P1 := P.subgroupOf P1
  have hHnormal : H.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPP1).2
    exact hP1Pnorm
  letI : H.Normal := hHnormal
  have hHinv : IsInvariant R P1 H := by
    refine ⟨?_⟩
    intro r x
    change (x : X) ∈ P ↔
      (r : X) * (x : X) * (r : X)⁻¹ ∈ P
    exact Subgroup.mem_normalizer_iff.mp (hRPnorm r.property) (x : X)
  letI : Nontrivial (P1 ⧸ H) :=
    QuotientGroup.nontrivial_iff.mpr hPsubne
  have hfixedZ : ∀ r : R, r ≠ 1 →
      fixedPointSubgroup (Subgroup.zpowers r) P1 = H := by
    simpa [H] using
      (lemma105_fixed_zpowers_eq_subgroupOf hRP1 hfixed)
  exact lemma105_faithful_quotient_of_fixed_zpowers
    hP1solv hcop H hHinv hfixedZ

/-- If every Sylow prime-power factor of a finite group divides `n`, then the
whole group order divides `n`. -/
public theorem lemma105_natCard_dvd_of_sylow_card_dvd
    {C : Type u} [Group C] [Finite C] {n : ℕ} (hn : n ≠ 0)
    (hSylow : ∀ q : ℕ, q.Prime → q ∈ (Nat.card C).primeFactors →
      ∃ R : Sylow q C, Nat.card (R : Subgroup C) ∣ n) :
    Nat.card C ∣ n := by
  classical
  apply (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hn).1
  intro q
  by_cases hq : q.Prime
  · letI : Fact q.Prime := ⟨hq⟩
    by_cases hqC : q ∈ (Nat.card C).primeFactors
    · obtain ⟨R, hRdvd⟩ := hSylow q hq hqC
      have hpowdvd : q ^ (Nat.card C).factorization q ∣ n := by
        rw [← R.card_eq_multiplicity]
        exact hRdvd
      have hfacq := Nat.factorization_le_factorization_of_dvd_right
        (a := q) hpowdvd (pow_ne_zero _ hq.ne_zero) hn
      rw [Nat.factorization_pow_self hq] at hfacq
      exact hfacq
    · have hqNotDvd : ¬ q ∣ Nat.card C := by
        intro hqDvd
        exact hqC ((Nat.mem_primeFactors).2
          ⟨hq, hqDvd, Nat.card_pos.ne'⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hqNotDvd]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime (Nat.card C) hq]
    exact Nat.zero_le _

/-- Source Lemma 10.5: `|C_A(P)|` divides `p - 1`. -/
public theorem lemma_10_5
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t u0 : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (d103 : Lemma103Conclusion M d.choice.P u0)
    (d104 : Lemma104Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t d) :
    Nat.card (lemma104C d) ∣ d.choice.p - 1 := by
  classical
  let p : ℕ := d.choice.p
  let P : Subgroup X := d.choice.P
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let C : Subgroup X := lemma104C d
  let N : Subgroup X := lemma104N d
  have hp : p.Prime := by simpa [p] using d.choice.p_prime
  letI : Fact p.Prime := ⟨hp⟩
  have hPD : P ≤ D := by
    simpa [P, D] using d.choice.P_le_V.trans inf_le_left
  have hPM : P ≤ M := hPD.trans inf_le_left
  have hPN : P ≤ N := by
    intro x hx
    exact ⟨hPM hx, Subgroup.le_normalizer hx⟩
  have hPp : IsPGroup p P := by
    obtain ⟨PD, hPDmap⟩ := d.P_sylow_D
    have hPp0 : IsPGroup d.choice.p d.choice.P := by
      rw [hPDmap]
      exact PD.isPGroup'.map (M ⊓ rightConjugate M t).subtype
    simpa [p, P] using hPp0
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hPodd : Odd (Nat.card P) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hPD)
  have hpodd : Odd p := by
    simpa [p, P, d.P_card] using hPodd
  have hpne2 : p ≠ 2 := by
    intro h
    apply hpodd.not_two_dvd_nat
    simpa [h]
  have hA1V : d.choice.initial.A1 ≤ V := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hCD : C ≤ D := by
    simpa [C, D, V, lemma104C] using
      (inf_le_left.trans (hA1V.trans inf_le_left))
  have hCodd : Odd (Nat.card C) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hCD)
  have hpC : (⟨p, hp⟩ : Nat.Primes) ∉ subgroupPrimeSet C := by
    intro hmem
    have hmem' : (⟨p, hp⟩ : Nat.Primes) ∈ subgroupPrimeSet
        (d.choice.initial.A1 ⊓ Subgroup.centralizer
          (d.choice.P : Set X)) := by
      change (⟨p, hp⟩ : Nat.Primes) ∈ subgroupPrimeSet
        (d.choice.initial.A1 ⊓ Subgroup.centralizer
          (d.choice.P : Set X)) at hmem
      simpa [C, lemma104C] using hmem
    exact (d.prime_ne_selected_of_mem_C hmem') rfl
  have htwoC : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∉ subgroupPrimeSet C := by
    intro hmem
    have hdiv : (2 : ℕ) ∣ Nat.card C := by
      change (⟨2, Nat.prime_two⟩ : Nat.Primes).val ∣ Nat.card C at hmem
      exact hmem
    exact hCodd.not_two_dvd_nat hdiv
  have hNnormP : N ≤ Subgroup.normalizer (P : Set X) := by
    intro x hx
    exact hx.2
  by_cases hCbot : C = ⊥
  · have hcardC : Nat.card C = 1 := by simp [hCbot]
    rw [hcardC]
    exact one_dvd _
  have hpredne : p - 1 ≠ 0 := by
    have hpgt : 1 < p := hp.one_lt
    omega
  apply lemma105_natCard_dvd_of_sylow_card_dvd hpredne
  intro q hq hqPrimeFactors
  letI : Fact q.Prime := ⟨hq⟩
  let q' : Nat.Primes := ⟨q, hq⟩
  have hqC : q' ∈ subgroupPrimeSet C := by
    have hqdvd : q ∣ Nat.card C := (Nat.mem_primeFactors.mp hqPrimeFactors).2.1
    change (q' : ℕ) ∣ Nat.card C
    exact hqdvd
  let Rq : Sylow q C := Classical.choice (Sylow.nonempty (p := q) (G := C))
  let R : Subgroup X := (Rq : Subgroup C).map C.subtype
  have hRq : IsPGroup q R := by
    exact Rq.isPGroup'.map C.subtype
  have hRC : R ≤ C := Subgroup.map_subtype_le (Rq : Subgroup C)
  have hqnep : q ≠ p := by
    simpa [q', p, C] using d.prime_ne_selected_of_mem_C hqC
  have hRsolv : Group.IsSolvable R := by
    let : Group.IsNilpotent R := hRq.isNilpotent
    infer_instance
  obtain ⟨K, hcomp⟩ := d104.normal_complement
  have hKle : K ≤ N := by simpa [N] using hcomp.le_M
  have hCle : C ≤ N := by simpa [C, N] using d104.C_le_N
  let Kloc : Subgroup N := K.subgroupOf N
  let Cloc : Subgroup N := C.subgroupOf N
  have hKnormal : Kloc.Normal := by
    simpa [Kloc, N] using hcomp.normal_in_M
  letI : Kloc.Normal := hKnormal
  have hdisjLoc : Disjoint Kloc Cloc := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxC
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hcomp.disjoint_D) hxK hxC
  have hsupLoc : Kloc ⊔ Cloc = ⊤ := by
    calc
      Kloc ⊔ Cloc = (K ⊔ C).subgroupOf N :=
        (Subgroup.subgroupOf_sup hKle hCle).symm
      _ = N.subgroupOf N := by simpa [N] using congrArg (fun H : Subgroup X => H.subgroupOf N) hcomp.sup_eq
      _ = ⊤ := Subgroup.subgroupOf_self N
  have hcompLoc : Kloc.IsComplement' Cloc :=
    isComplement'_of_disjoint_sup_eq_top_of_normal Kloc Cloc
      hdisjLoc hsupLoc
  have hCKcop : Nat.Coprime (Nat.card C) (Nat.card K) := by
    have hcopLoc := d104.C_hall_N.card_coprime_index
    have hidx : Cloc.index = Nat.card Kloc := hcompLoc.index_eq_card
    rw [hidx,
      natCard_subgroupOf_eq C N hCle,
      natCard_subgroupOf_eq K N hKle] at hcopLoc
    exact hcopLoc
  have hRcopK : Nat.Coprime (Nat.card R) (Nat.card K) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hRC) hCKcop
  have hPK : P ≤ K :=
    lemma105_pSubgroup_le_normal_complement hp hcomp d104.C_hall_N hpC
      hPp (by simpa [N] using hPN)
  obtain ⟨P1N, hPP1, hRP1⟩ :=
    lemma105_invariant_sylow_p hp hcomp d104.C_hall_N hpC hRC
      hRcopK hRsolv hPp hPK (by simpa [N, P] using hNnormP)
  let P1 : Subgroup X := (P1N : Subgroup N).map N.subtype
  have hP1p : IsPGroup p P1 := by
    exact P1N.isPGroup'.map N.subtype
  have hP1N : P1 ≤ N := Subgroup.map_subtype_le (P1N : Subgroup N)
  have hP1K : P1 ≤ K :=
    lemma105_pSubgroup_le_normal_complement hp hcomp d104.C_hall_N hpC
      hP1p hP1N
  have hP1neP : P1 ≠ P := by
    exact lemma105_sylow_normalizer_ne_P d d104 (by simpa [C] using hCbot)
      P1N
  have hPsubne : P.subgroupOf P1 ≠ ⊤ := by
    intro htop
    apply hP1neP
    apply le_antisymm
    · intro x hx
      let x1 : P1 := ⟨x, hx⟩
      have hxloc : x1 ∈ P.subgroupOf P1 := by
        rw [htop]
        exact Subgroup.mem_top x1
      exact hxloc
    · simpa [P1, P, N] using hPP1
  have hRcopP1 : Nat.Coprime (Nat.card R) (Nat.card P1) :=
    IsPGroup.coprime_card_of_ne q p hqnep R P1 hRq hP1p
  have hRcopP : Nat.Coprime (Nat.card R) p := by
    have hcop := IsPGroup.coprime_card_of_ne q p hqnep R P hRq hPp
    simpa [p, P, d.P_card] using hcop
  have hfixed : ∀ U : Subgroup X, U ≤ R → U ≠ ⊥ →
      P1 ⊓ Subgroup.centralizer (U : Set X) = P := by
    intro U hUR hUne
    have hUC : U ≤ C := hUR.trans hRC
    have hUq : IsPGroup q U := hRq.to_le hUR
    let Y : Subgroup X := U ⊔ P
    let CY : Subgroup X := M ⊓ Subgroup.centralizer (Y : Set X)
    let S : Subgroup X := (pCore 2 CY).map CY.subtype
    have hstrong : IsPGroup 2 S ∧
        (normalizerIn N U : Set X) =
          (S : Set X) * ((P : Set X) * (normalizerIn C U : Set X)) := by
      simpa [p, P, C, N, Y, CY, S] using
        (lemma105_strong_10E hM htM d83 h84 d q' hqC U hUC hUne hUq)
    have hSN : S ≤ N := by
      intro s hs
      rcases Subgroup.mem_map.mp hs with ⟨c, hc, rfl⟩
      have hcCY : (c : X) ∈ CY := c.property
      refine ⟨hcCY.1, ?_⟩
      apply centralizer_le_normalizer P
      rw [Subgroup.mem_centralizer_iff]
      intro p hpP
      exact Subgroup.mem_centralizer_iff.mp hcCY.2 p
        ((le_sup_right : P ≤ Y) hpP)
    have hSK : S ≤ K :=
      lemma105_pSubgroup_le_normal_complement Nat.prime_two hcomp
        d104.C_hall_N htwoC hstrong.1 hSN
    have hUP : U ≤ Subgroup.centralizer (P : Set X) := by
      simpa [C, P, lemma104C] using hUC.trans inf_le_right
    exact lemma105_fixed_centralizer_of_strong_factor hp hpne2
      hstrong.1 hP1p (by simpa [P1, P, N] using hPP1) hP1N
      hSK hPK hP1K hcomp.disjoint_D hUP hstrong.2
  have hP1normP : P1 ≤ Subgroup.normalizer (P : Set X) :=
    hP1N.trans hNnormP
  have hRnormP : R ≤ Subgroup.normalizer (P : Set X) :=
    hRC.trans (by
      intro x hx
      exact centralizer_le_normalizer P (by simpa [C, P, lemma104C] using hx.2))
  have hP1solv : Group.IsSolvable P1 := by
    letI : Group.IsNilpotent P1 := hP1p.isNilpotent
    infer_instance
  letI : Subgroup.Normalizes R P1 := ⟨by simpa [R, P1, N, C] using hRP1⟩
  letI : MulDistribMulAction R P1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R P1
      (by simpa [R, P1, N, C] using hRP1)
  let Ploc : Subgroup P1 := P.subgroupOf P1
  have hPlocNormal : Ploc.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (by simpa [P1, P, N] using hPP1)).2
    exact hP1normP
  letI : Ploc.Normal := hPlocNormal
  have hPlocInv : IsInvariant R P1 Ploc := by
    refine ⟨?_⟩
    intro r x
    change (x : X) ∈ P ↔ (r : X) * (x : X) * (r : X)⁻¹ ∈ P
    exact Subgroup.mem_normalizer_iff.mp (hRnormP r.property) (x : X)
  letI : MulDistribMulAction R (P1 ⧸ Ploc) :=
    quotientMulDistribMulAction (A := R) (G := P1) Ploc hPlocInv
  haveI : Nontrivial (P1 ⧸ Ploc) :=
    QuotientGroup.nontrivial_iff.mpr (by simpa [Ploc] using hPsubne)
  have hfaithful : FaithfulSMul R (P1 ⧸ Ploc) := by
    simpa [Ploc] using
      (lemma105_faithful_action_on_P1_quotient
        (by simpa [R, P1, N, C] using hRP1)
        (by simpa [P1, P, N] using hPP1)
        hP1normP hRnormP hP1solv hRcopP1 hPsubne hfixed)
  letI : FaithfulSMul R (P1 ⧸ Ploc) := hfaithful
  have hcyclic : IsCyclic (P1 ⧸ Ploc) := by
    simpa [Ploc, P, P1, N] using
      (lemma105_P1_quotient_cyclic
        hM d ht htM d103 hP1N hP1p
        (by simpa [P1, P, N] using hPP1))
  have hquotp : IsPGroup p (P1 ⧸ Ploc) := hP1p.to_quotient Ploc
  have hRdvd : Nat.card R ∣ p - 1 :=
    lemma105_card_dvd_pred_of_faithful_cyclic_pgroup
      hp hRcopP hquotp hcyclic
  refine ⟨Rq, ?_⟩
  have hRcard : Nat.card R = Nat.card (Rq : Subgroup C) := by
    change Nat.card ((Rq : Subgroup C).map C.subtype) =
      Nat.card (Rq : Subgroup C)
    exact @Subgroup.card_map_of_injective C _ X _
      (Rq : Subgroup C) C.subtype C.subtype_injective
  simpa [p, hRcard] using hRdvd


end CFSG.BenderSuzuki
