module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingCounting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a

namespace CFSG
end CFSG
open CFSG

/-!
# Source boundary and checked preliminaries for Lemma 8.3

The proof of Lemma 8.3 in `docs/cfsg-vol4.tex` uses Proposition 8.2(a), whose
induction depends on Theorem 2 and Corollary 7.13 from the earlier
minimal-counterexample development.  We isolate exactly the base-point form
needed later: a subgroup of `M` fixing at least three conjugates of `M` is
centralized by an involution of `M`.

The other declarations in this file are consequences of strong embedding and
the checked `[IG; 17.8]` interface.  In particular, the Proposition 3.6(c)
conjugacy and `C_I(s) = 1` facts used in Lemma 8.3 do not remain source leaves.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The base-point specialization of Proposition 8.2(a), isolated as the
smallest minimal-counterexample-dependent input used by Lemma 8.3.

The subgroup `Y ≤ M` fixes the distinguished base coset automatically.  If it
fixes at least three conjugates of `M`, the source produces an involution in
`M` centralizing `Y`. -/
public def Proposition82aAtBase
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) : Prop :=
  ∀ (Y : Subgroup X),
    Y ≤ M →
    3 ≤ Nat.card (theorem4bFixedPoints M Y) →
      ∃ u : X, u ∈ M ∧ IsInvolution u ∧
        Y ≤ Subgroup.centralizer ({u} : Set X)

/-- Checked constructor for the opaque base-point Proposition 8.2(a)
contract. -/
public theorem Proposition82aAtBase.of_forall
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (h : ∀ (Y : Subgroup X),
      Y ≤ M →
      3 ≤ Nat.card (theorem4bFixedPoints M Y) →
        ∃ u : X, u ∈ M ∧ IsInvolution u ∧
          Y ≤ Subgroup.centralizer ({u} : Set X)) :
    Proposition82aAtBase M := by
  exact h

/-- Checked eliminator for the base-point Proposition 8.2(a) contract. -/
public theorem Proposition82aAtBase.exists_involution_centralizing
    {X : Type u} [Group X] [Finite X] {M Y : Subgroup X}
    (h82a : Proposition82aAtBase M)
    (hYM : Y ≤ M)
    (hfixed : 3 ≤ Nat.card (theorem4bFixedPoints M Y)) :
    ∃ u : X, u ∈ M ∧ IsInvolution u ∧
      Y ≤ Subgroup.centralizer ({u} : Set X) := by
  exact h82a Y hYM hfixed

/-- The three conclusions of Lemma 8.3, packaged around the source's chosen
involution `u`. -/
public structure Lemma83Data
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) (t : X) where
  u : X
  u_mem_M : u ∈ M
  u_involution : IsInvolution u
  centralizer_eq :
    (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({t} : Set X) =
      (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({u} : Set X)
  conjugate_le :
    ∀ (Y : Subgroup X),
      Y ≤ M ⊓ rightConjugate M t →
      3 ≤ Nat.card (theorem4bFixedPoints M Y) →
        ∃ d : X, d ∈ M ⊓ rightConjugate M t ∧
          rightConjugate Y d ≤
            (M ⊓ rightConjugate M t) ⊓
              Subgroup.centralizer ({t} : Set X)
  fixedPoints_card_eq_two :
    ∀ {x : X},
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t →
      x ≠ 1 →
        Nat.card (theorem4bFixedPoints M (Subgroup.zpowers x)) = 2

namespace IsStronglyEmbedded

/-- Pointwise form of `C_I(s) = 1`: an element inverted by the outside
involution `t` cannot centralize an involution of `M`, unless it is `1`.

The proof uses only uniqueness of the involution in the right coset
`C_X(s) * t`: both `t` and `x * t` lie in that coset. -/
public theorem eq_one_of_mem_centralizer_and_inverted_by_outside_involution
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {s t x : X}
    (hsM : s ∈ M) (hs : IsInvolution s)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hxC : x ∈ Subgroup.centralizer ({s} : Set X))
    (hxt : rightConjugateElem x t = x⁻¹) :
    x = 1 := by
  have hxM : x ∈ M := hM.centralizer_le hsM hs hxC
  have hxtM : x * t ∉ M := by
    intro hxtM
    apply htM
    have htEq : t = x⁻¹ * (x * t) := by simp
    rw [htEq]
    exact M.mul_mem (M.inv_mem hxM) hxtM
  have hxtNe : x * t ≠ 1 := by
    intro h
    exact hxtM (h.symm ▸ M.one_mem)
  have htInv : t⁻¹ = t := ht.inv_eq_self
  have htx : t * x * t = x⁻¹ := by
    simpa [rightConjugateElem, htInv] using hxt
  have hxtSq : (x * t) ^ 2 = 1 := by
    rw [pow_two]
    calc
      (x * t) * (x * t) = x * (t * x * t) := by group
      _ = x * x⁻¹ := by rw [htx]
      _ = 1 := by simp
  have hxtInv : IsInvolution (x * t) := ⟨hxtNe, hxtSq⟩
  obtain ⟨u, hu, huUnique⟩ :=
    hM.existsUnique_involution_in_centralizer_rightCoset hsM hs htM
  have hxtCoset :
      (x * t) * t⁻¹ ∈ Subgroup.centralizer ({s} : Set X) := by
    simpa [mul_assoc] using hxC
  have htCoset :
      t * t⁻¹ ∈ Subgroup.centralizer ({s} : Set X) := by
    simp
  have hxtu : x * t = u := huUnique _ ⟨hxtCoset, hxtInv⟩
  have htu : t = u := huUnique _ ⟨htCoset, ht⟩
  have hxteq : x * t = t := hxtu.trans htu.symm
  have hcancel := congrArg (fun y : X => y * t⁻¹) hxteq
  simpa [mul_assoc] using hcancel

/-- Source-shaped pointwise `C_I(s) = 1`, with
`I = peterfalviKSet D t`. -/
public theorem eq_one_of_mem_peterfalviKSet_and_centralizes_involution
    {X : Type u} [Group X] [Finite X] {M D : Subgroup X}
    (hM : IsStronglyEmbedded M) {s t x : X}
    (hsM : s ∈ M) (hs : IsInvolution s)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hxI : x ∈ peterfalviKSet D t)
    (hxC : x ∈ Subgroup.centralizer ({s} : Set X)) :
    x = 1 :=
  hM.eq_one_of_mem_centralizer_and_inverted_by_outside_involution
    hsM hs ht htM hxC hxI.2

/-- Set-level form of `C_I(s) = 1`. -/
public theorem peterfalviKSet_inter_centralizer_involution_eq_singleton
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (D : Subgroup X) {s t : X}
    (hsM : s ∈ M) (hs : IsInvolution s)
    (ht : IsInvolution t) (htM : t ∉ M) :
    peterfalviKSet D t ∩
        (Subgroup.centralizer ({s} : Set X) : Set X) = {1} := by
  ext x
  constructor
  · rintro ⟨hxI, hxC⟩
    have hx :=
      hM.eq_one_of_mem_peterfalviKSet_and_centralizes_involution
        hsM hs ht htM hxI hxC
    simp [hx]
  · intro hx
    have hxone : x = 1 := Set.mem_singleton_iff.mp hx
    subst x
    constructor
    · simp [peterfalviKSet, rightConjugateElem]
    · exact (Subgroup.centralizer ({s} : Set X)).one_mem

/-- Lemma 8.3(a): with `D = M ⊓ M^t` and `V = C_D(t)`, there is an
involution `u ∈ M` such that `V = C_D(u)`.

The subgroup `V` fixes the base coset, the coset of `t`, and the unique fixed
coset of `t`.  Proposition 8.2(a) therefore supplies `u`; Proposition 3.6(d)
and the `D`-conjugacy of involutions in `M` give equality of the two finite
centralizers. -/
public theorem lemma_8_3_a_exists_inf_centralizer_eq
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (h82a : Proposition82aAtBase M)
    {t : X} (ht : IsInvolution t) (htM : t ∉ M) :
    ∃ u : X, u ∈ M ∧ IsInvolution u ∧
      (M ⊓ rightConjugate M t) ⊓
          Subgroup.centralizer ({t} : Set X) =
        (M ⊓ rightConjugate M t) ⊓
          Subgroup.centralizer ({u} : Set X) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := D ⊓ Subgroup.centralizer ({t} : Set X)
  have hVM : V ≤ M := inf_le_left.trans inf_le_left
  let baseCoset : conjugateCosetSpace M := QuotientGroup.mk 1
  let betaCoset : conjugateCosetSpace M := QuotientGroup.mk t
  have hbaseFixed :
      baseCoset ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) V :=
    theorem4b_baseCoset_mem_fixedPoints hVM
  have hVConj : V ≤ rightConjugate M t :=
    inf_le_left.trans inf_le_right
  have hbetaFixed :
      betaCoset ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) V := by
    intro v hv
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact hVConj hv
  obtain ⟨gamma, htGamma, hgammaUnique⟩ :=
    hM.involution_fixed_coset_unique ht
  have hgammaFixed :
      gamma ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) V := by
    intro v hv
    have hcomm : (v : X) * t = t * (v : X) :=
      Subgroup.mem_centralizer_singleton_iff.mp hv.2
    apply hgammaUnique
    calc
      t • ((v : X) • gamma) = (t * (v : X)) • gamma := by rw [mul_smul]
      _ = ((v : X) * t) • gamma := by rw [hcomm]
      _ = (v : X) • (t • gamma) := by rw [mul_smul]
      _ = (v : X) • gamma := by rw [htGamma]
  have hbaseNeBeta : baseCoset ≠ betaCoset := by
    intro h
    apply htM
    simpa [baseCoset, betaCoset] using QuotientGroup.eq.mp h
  have hgammaNeBase : gamma ≠ baseCoset := by
    intro h
    apply htM
    have htBase : t • baseCoset = baseCoset := by simpa [h] using htGamma
    have htStab : t ∈ MulAction.stabilizer X baseCoset :=
      MulAction.mem_stabilizer_iff.mpr htBase
    simpa [baseCoset, baseCoset_stabilizer M] using htStab
  have htBetaBase : t • betaCoset = baseCoset := by
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    simp [betaCoset, baseCoset, MulAction.Quotient.smul_mk, htt]
  have hgammaNeBeta : gamma ≠ betaCoset := by
    intro h
    have htBeta : t • betaCoset = betaCoset := by simpa [h] using htGamma
    exact hbaseNeBeta (htBetaBase.symm.trans htBeta)
  let p0 : theorem4bFixedPoints M V := ⟨baseCoset, hbaseFixed⟩
  let p1 : theorem4bFixedPoints M V := ⟨betaCoset, hbetaFixed⟩
  let p2 : theorem4bFixedPoints M V := ⟨gamma, hgammaFixed⟩
  let f : Fin 3 → theorem4bFixedPoints M V := ![p0, p1, p2]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have hij' : p0 = p1 := by simpa [f] using hij
      exfalso
      exact hbaseNeBeta (by simpa [p0, p1] using congrArg Subtype.val hij')
    · have hij' : p2 = p0 := by simpa [f] using hij.symm
      exfalso
      exact hgammaNeBase (by simpa [p0, p2] using congrArg Subtype.val hij')
    · have hij' : p1 = p0 := by simpa [f] using hij
      exfalso
      exact hbaseNeBeta (by
        simpa [p0, p1] using (congrArg Subtype.val hij').symm)
    · rfl
    · have hij' : p2 = p1 := by simpa [f] using hij.symm
      exfalso
      exact hgammaNeBeta (by simpa [p1, p2] using congrArg Subtype.val hij')
    · have hij' : p0 = p2 := by simpa [f] using hij.symm
      exfalso
      exact hgammaNeBase (by
        simpa [p0, p2] using (congrArg Subtype.val hij').symm)
    · have hij' : p2 = p1 := by simpa [f] using hij
      exfalso
      exact hgammaNeBeta (by simpa [p1, p2] using congrArg Subtype.val hij')
    · rfl
  have hVfixed : 3 ≤ Nat.card (theorem4bFixedPoints M V) := by
    simpa using Nat.card_le_card_of_injective f hf
  obtain ⟨u, huM, hu, hVcentral⟩ :=
    h82a.exists_involution_centralizing hVM hVfixed
  refine ⟨u, huM, hu, ?_⟩
  have hVle : V ≤ D ⊓ Subgroup.centralizer ({u} : Set X) :=
    le_inf inf_le_left hVcentral
  obtain ⟨z, hzM, hz⟩ := hM.exists_involution
  have hcardOutsideInside :
      Nat.card V =
        Nat.card (D ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) := by
    simpa [V, D] using
      hM.inf_rightConjugate_outside_inside_centralizer_card_eq
        hzM hz ht htM
  have hcardInside :
      Nat.card (D ⊓ Subgroup.centralizer ({z} : Set X) : Subgroup X) =
        Nat.card (D ⊓ Subgroup.centralizer ({u} : Set X) : Subgroup X) := by
    simpa [D] using
      hM.inf_rightConjugate_centralizer_card_eq
        ht htM hzM hz huM hu
  have hcard :
      Nat.card V =
        Nat.card (D ⊓ Subgroup.centralizer ({u} : Set X) : Subgroup X) :=
    hcardOutsideInside.trans hcardInside
  exact Subgroup.eq_of_le_of_card_ge hVle (le_of_eq hcard.symm)

/-- Lemma 8.3(b), with the target centralizer made explicit: if `Y ≤ D`
fixes at least three conjugates of `M`, then for any involution `u ∈ M`, a
`D`-conjugate of `Y` lies in `C_D(u)`.

Once Lemma 8.3(a) identifies `V` with `C_D(u)`, this is exactly the source
conclusion that `Y` is `D`-conjugate to a subgroup of `V`. -/
public theorem lemma_8_3_b_rightConjugate_le_inf_centralizer
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (h82a : Proposition82aAtBase M)
    {t u : X} (ht : IsInvolution t) (htM : t ∉ M)
    (huM : u ∈ M) (hu : IsInvolution u)
    {Y : Subgroup X}
    (hYD : Y ≤ M ⊓ rightConjugate M t)
    (hfixed : 3 ≤ Nat.card (theorem4bFixedPoints M Y)) :
    ∃ d : X, d ∈ M ⊓ rightConjugate M t ∧
      rightConjugate Y d ≤
        (M ⊓ rightConjugate M t) ⊓
          Subgroup.centralizer ({u} : Set X) := by
  have hYM : Y ≤ M := hYD.trans inf_le_left
  obtain ⟨s, hsM, hs, hYs⟩ :=
    h82a.exists_involution_centralizing hYM hfixed
  obtain ⟨d, hdD, hsd⟩ :=
    hM.involutions_conjugate_by_inf_rightConjugate
      ht htM hsM hs huM hu
  refine ⟨d, hdD, ?_⟩
  intro x hx
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨y, hyY, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact
      (M ⊓ rightConjugate M t).mul_mem
        ((M ⊓ rightConjugate M t).mul_mem
          ((M ⊓ rightConjugate M t).inv_mem hdD) (hYD hyY))
        ((M ⊓ rightConjugate M t).inv_mem
          ((M ⊓ rightConjugate M t).inv_mem hdD))
  · rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hsd]
    have hcomm : y * s = s * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYs hyY)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    change rightConjugateElem y d * rightConjugateElem s d =
      rightConjugateElem s d * rightConjugateElem y d
    calc
      rightConjugateElem y d * rightConjugateElem s d =
          rightConjugateElem (y * s) d := by
            simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (s * y) d := by rw [hcomm]
      _ = rightConjugateElem s d * rightConjugateElem y d := by
            simp [rightConjugateElem, mul_assoc]

/-- Lemma 8.3(c): every nonidentity element of
`I = peterfalviKSet (M ⊓ M^t) t` fixes exactly the two conjugates represented
by the base coset and the coset of `t`.

The only minimal-counterexample-dependent input is the base-point
Proposition 8.2(a) contract. -/
public theorem lemma_8_3_c_fixedPoints_card_eq_two
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (h82a : Proposition82aAtBase M)
    {t x : X} (ht : IsInvolution t) (htM : t ∉ M)
    (hxI : x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t)
    (hxne : x ≠ 1) :
    Nat.card (theorem4bFixedPoints M (Subgroup.zpowers x)) = 2 := by
  have hzpM : Subgroup.zpowers x ≤ M :=
    Subgroup.zpowers_le.mpr hxI.1.1
  let base : theorem4bFixedPoints M (Subgroup.zpowers x) :=
    ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints hzpM⟩
  have hzpConj : Subgroup.zpowers x ≤ rightConjugate M t :=
    Subgroup.zpowers_le.mpr hxI.1.2
  have hbetaFixed :
      (QuotientGroup.mk t : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M)
          (Subgroup.zpowers x) := by
    intro y hy
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact hzpConj hy
  let beta : theorem4bFixedPoints M (Subgroup.zpowers x) :=
    ⟨QuotientGroup.mk t, hbetaFixed⟩
  have hbetaNeBase : beta ≠ base := by
    intro h
    apply htM
    simpa using QuotientGroup.eq.mp (congrArg Subtype.val h).symm
  have hbaseNeBeta : base ≠ beta := Ne.symm hbetaNeBase
  let f : Bool → theorem4bFixedPoints M (Subgroup.zpowers x) :=
    fun b => if b then beta else base
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exact (hbaseNeBeta (by simpa [f] using hab)).elim
    · exact (hbetaNeBase (by simpa [f] using hab)).elim
    · rfl
  have hlower :
      2 ≤ Nat.card (theorem4bFixedPoints M (Subgroup.zpowers x)) := by
    simpa using Nat.card_le_card_of_injective f hf
  have hupper :
      Nat.card (theorem4bFixedPoints M (Subgroup.zpowers x)) ≤ 2 := by
    by_contra hnot
    have hthree :
        3 ≤ Nat.card (theorem4bFixedPoints M (Subgroup.zpowers x)) := by
      omega
    obtain ⟨s, hsM, hs, hcentral⟩ :=
      h82a.exists_involution_centralizing hzpM hthree
    have hxC : x ∈ Subgroup.centralizer ({s} : Set X) :=
      hcentral (Subgroup.mem_zpowers x)
    exact hxne
      (hM.eq_one_of_mem_peterfalviKSet_and_centralizes_involution
        hsM hs ht htM hxI hxC)
  omega

/-- Lemma 8.3 in its complete source-facing package.  All three conclusions
follow from strong embedding plus the isolated Proposition 8.2(a) contract. -/
public noncomputable def lemma_8_3_data
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (h82a : Proposition82aAtBase M)
    {t : X} (ht : IsInvolution t) (htM : t ∉ M) :
    Lemma83Data M t := by
  let hex := hM.lemma_8_3_a_exists_inf_centralizer_eq h82a ht htM
  let u : X := Classical.choose hex
  have huM : u ∈ M := (Classical.choose_spec hex).1
  have hu : IsInvolution u := (Classical.choose_spec hex).2.1
  have hcentralizer :
      (M ⊓ rightConjugate M t) ⊓
          Subgroup.centralizer ({t} : Set X) =
        (M ⊓ rightConjugate M t) ⊓
          Subgroup.centralizer ({u} : Set X) :=
    (Classical.choose_spec hex).2.2
  refine
    { u := u
      u_mem_M := huM
      u_involution := hu
      centralizer_eq := hcentralizer
      conjugate_le := ?_
      fixedPoints_card_eq_two := ?_ }
  · intro Y hYD hfixed
    obtain ⟨d, hdD, hdle⟩ :=
      hM.lemma_8_3_b_rightConjugate_le_inf_centralizer
        h82a ht htM huM hu hYD hfixed
    refine ⟨d, hdD, ?_⟩
    rw [hcentralizer]
    exact hdle
  · intro x hxI hxne
    exact hM.lemma_8_3_c_fixedPoints_card_eq_two
      h82a ht htM hxI hxne

end IsStronglyEmbedded
end CFSG.BenderSuzuki
