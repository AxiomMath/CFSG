module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces

namespace CFSG
end CFSG
open CFSG

/-!
# Permutation-group lemmas for Theorem SE

This file contains the Chapter 1 Witt and Bender normalizer lemmas used in the
proof of Proposition 5.3. The final Bender theorem is the two-transitive case
of [II1; 2.4], which is the only case needed downstream.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped Pointwise

open PFAppendixIII PFchapter1section1

universe u v


/-- An element of a subgroup normalizer preserves that subgroup's fixed-point
set. -/
public theorem fixedPoints_smul_of_mem_normalizer
    {G Omega : Type*} [Group G] [MulAction G Omega]
    {P : Subgroup G} {g : G} {omega : Omega}
    (hg : g ∈ Subgroup.normalizer (P : Set G))
    (homega : omega ∈ fixedPointsOfSubgroup G Omega P) :
    g • omega ∈ fixedPointsOfSubgroup G Omega P := by
  intro p hpP
  have hp' : g⁻¹ * p * g ∈ P :=
    ((Subgroup.mem_normalizer_iff''.mp hg) p).mp hpP
  calc
    p • (g • omega) = g • ((g⁻¹ * p * g) • omega) := by
      simp [smul_smul, mul_assoc]
    _ = g • omega := by rw [homega _ hp']

/-- The canonical action of a subgroup normalizer on that subgroup's fixed
points. -/
@[reducible, expose] public def normalizerFixedPointAction
    (X : Type u) (Omega : Type v) [Group X] [MulAction X Omega]
    (P : Subgroup X) :
    MulAction (Subgroup.normalizer (P : Set X))
      {omega : Omega // omega ∈ fixedPointsOfSubgroup X Omega P} where
  smul n omega :=
    ⟨(n : X) • (omega : Omega),
      fixedPoints_smul_of_mem_normalizer n.property omega.property⟩
  one_smul omega := by
    apply Subtype.ext
    exact one_smul X (omega : Omega)
  mul_smul n m omega := by
    apply Subtype.ext
    exact mul_smul (n : X) (m : X) (omega : Omega)

/-- The ambient-set formulation of double transitivity induces the usual
`MulAction.IsMultiplyPretransitive` formulation on the fixed-point subtype. -/
public theorem normalizerFixedPointAction_twoPretransitive
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (P : Subgroup X)
    (htwo : IsTwoTransitiveOn (Subgroup.normalizer (P : Set X))
      (fixedPointsOfSubgroup X Omega P)) :
    letI : MulAction (Subgroup.normalizer (P : Set X))
        {omega : Omega // omega ∈ fixedPointsOfSubgroup X Omega P} :=
      normalizerFixedPointAction X Omega P
    MulAction.IsMultiplyPretransitive (Subgroup.normalizer (P : Set X))
      {omega : Omega // omega ∈ fixedPointsOfSubgroup X Omega P} 2 := by
  letI : MulAction (Subgroup.normalizer (P : Set X))
      {omega : Omega // omega ∈ fixedPointsOfSubgroup X Omega P} :=
    normalizerFixedPointAction X Omega P
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨n, hnac, hnbd⟩ := htwo
    a.property b.property c.property d.property
    (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
  refine ⟨n, ?_, ?_⟩
  · exact Subtype.ext hnac
  · exact Subtype.ext hnbd

/-- The ambient fixed-point subtype of a subgroup is equivalent to the usual
fixed-point type for the restricted subgroup action. -/
public noncomputable def fixedPointsOfSubgroupEquivFixedPoints
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (P : Subgroup G) :
    {omega : Omega // omega ∈ fixedPointsOfSubgroup G Omega P} ≃
      MulAction.fixedPoints P Omega where
  toFun omega := ⟨omega, by
    rw [MulAction.mem_fixedPoints]
    intro p
    exact omega.property p p.property⟩
  invFun omega := ⟨omega, by
    intro p hp
    let pP : P := ⟨p, hp⟩
    exact MulAction.mem_fixedPoints.mp omega.property pP⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `p`-group fixed-point congruence in the ambient-subgroup notation used
throughout Theorem SE. -/
public theorem IsPGroup.card_modEq_card_fixedPointsOfSubgroup
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Finite Omega] {p : ℕ} [Fact (Nat.Prime p)]
    {P : Subgroup G} (hPp : IsPGroup p P) :
    Nat.card Omega ≡
      Nat.card {omega : Omega //
        omega ∈ fixedPointsOfSubgroup G Omega P} [MOD p] := by
  calc
    Nat.card Omega ≡ Nat.card (MulAction.fixedPoints P Omega) [MOD p] :=
      hPp.card_modEq_card_fixedPoints Omega
    _ = Nat.card {omega : Omega //
        omega ∈ fixedPointsOfSubgroup G Omega P} :=
      (Nat.card_congr (fixedPointsOfSubgroupEquivFixedPoints P)).symm

/-- The one-target form of Witt's argument.  A fixed point in the orbit of the
base point can be reached by an element normalizing the ambient image of the
chosen Sylow subgroup. -/
public theorem witt_normalizer_fixedPoint_transporter
    {G A : Type*} [Group G] [Finite G] [MulAction G A]
    {p : ℕ} (hp : Nat.Prime p)
    (a d : A) (S : Sylow p (MulAction.stabilizer G a))
    (hd : d ∈ fixedPointsOfSubgroup G A
      ((S : Subgroup (MulAction.stabilizer G a)).map
        (MulAction.stabilizer G a).subtype))
    (g : G) (hga : g • a = d) :
    ∃ n : Subgroup.normalizer
        (((S : Subgroup (MulAction.stabilizer G a)).map
          (MulAction.stabilizer G a).subtype : Subgroup G) : Set G),
      (n : G) • a = d := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let D : Subgroup G := MulAction.stabilizer G a
  let P : Subgroup G := (S : Subgroup D).map D.subtype
  let Q : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hQD : Q ≤ D := by
    intro x hxQ
    rcases Subgroup.mem_map.mp hxQ with ⟨y, hyP, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    have hyFix : y • d = d := hd y hyP
    rw [← hga] at hyFix
    have hyFix' := congrArg (fun omega => g⁻¹ • omega) hyFix
    simpa [Q, D, P, MulAut.conj_apply, mul_smul, mul_assoc] using hyFix'
  let QD : Subgroup D := Q.subgroupOf D
  have hPcard : Nat.card P = p ^ (Nat.card D).factorization p := by
    change Nat.card ((S : Subgroup D).map D.subtype) = _
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  have hQDcard : Nat.card QD = p ^ (Nat.card D).factorization p := by
    rw [show Nat.card QD = Nat.card Q from
      natCard_subgroupOf_eq Q D hQD]
    change Nat.card (P.map (MulAut.conj g⁻¹).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hPcard
  let T : Sylow p D := Sylow.ofCard QD hQDcard
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq D S T
  let n : G := g * (e : G)
  have hnNorm : n ∈ Subgroup.normalizer (P : Set G) := by
    have hmapLe : P.map (MulAut.conj n).toMonoidHom ≤ P := by
      rintro _ ⟨x, hxP, rfl⟩
      rcases Subgroup.mem_map.mp hxP with ⟨xD, hxS, rfl⟩
      have hxeT : (MulAut.conj e) xD ∈ (T : Subgroup D) := by
        rw [← he, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul
          xD (MulAut.conj e) (S : Subgroup D) hxS
      have hxeQD : (MulAut.conj e) xD ∈ QD := by
        simpa [T] using hxeT
      have hxeQ : ((e : G) * (xD : G) * (e : G)⁻¹) ∈ Q := by
        have hxeQ' := Subgroup.mem_subgroupOf.mp hxeQD
        simpa [QD, MulAut.conj_apply] using hxeQ'
      rcases Subgroup.mem_map.mp hxeQ with ⟨y, hyP, hy⟩
      have hy' := congrArg (MulAut.conj g) hy
      change (MulAut.conj n) (D.subtype xD) ∈ P
      rw [show (MulAut.conj n) (D.subtype xD) = y by
        simpa [n, MulAut.conj_apply, mul_assoc] using hy'.symm]
      exact hyP
    have hmapCard : Nat.card (P.map (MulAut.conj n).toMonoidHom) =
        Nat.card P :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hmapEq : P.map (MulAut.conj n).toMonoidHom = P :=
      Subgroup.eq_of_le_of_card_ge hmapLe (by rw [hmapCard])
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxP
      have hxMap := Subgroup.mem_map_of_mem
        (MulAut.conj n).toMonoidHom hxP
      rw [hmapEq] at hxMap
      simpa [MulAut.conj_apply] using hxMap
    · intro hnxP
      have hnxMap : (MulAut.conj n) x ∈
          P.map (MulAut.conj n).toMonoidHom := by
        rw [hmapEq]
        simpa [MulAut.conj_apply] using hnxP
      rcases Subgroup.mem_map.mp hnxMap with ⟨y, hyP, hy⟩
      have hyx : y = x := (MulAut.conj n).injective hy
      simpa [hyx] using hyP
  refine ⟨⟨n, hnNorm⟩, ?_⟩
  change n • a = d
  rw [show n = g * (e : G) by rfl, mul_smul,
    MulAction.mem_stabilizer_iff.mp e.property, hga]

/-- Witt's normalizer lemma for the ambient image of a Sylow subgroup of a point
stabilizer. -/
public theorem witt_normalizer_pretransitive_core
    {G A : Type*} [Group G] [Finite G] [MulAction G A]
    {p : ℕ} (hp : Nat.Prime p)
    (htrans : MulAction.IsPretransitive G A)
    (a : A)
    (S : Sylow p (MulAction.stabilizer G a)) :
    let D : Subgroup G := MulAction.stabilizer G a
    let P : Subgroup G := (S : Subgroup D).map D.subtype
    IsTransitiveOn (Subgroup.normalizer (P : Set G))
      (fixedPointsOfSubgroup G A P) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let D : Subgroup G := MulAction.stabilizer G a
  let P : Subgroup G := (S : Subgroup D).map D.subtype
  dsimp only
  intro b c hb hc
  have ha : a ∈ fixedPointsOfSubgroup G A P := by
    intro x hxP
    rcases Subgroup.mem_map.mp hxP with ⟨d, hdS, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp d.property
  have hreach : ∀ d : A,
      d ∈ fixedPointsOfSubgroup G A P →
      ∃ n : Subgroup.normalizer (P : Set G), (n : G) • a = d := by
    intro d hd
    obtain ⟨g, hga⟩ := htrans.1 a d
    simpa [D, P] using
      (witt_normalizer_fixedPoint_transporter hp a d S
        (by simpa [D, P] using hd) g hga)
  obtain ⟨nb, hnb⟩ := hreach b hb
  obtain ⟨nc, hnc⟩ := hreach c hc
  let n : Subgroup.normalizer (P : Set G) := nc * nb⁻¹
  refine ⟨n, ?_⟩
  change ((nc : G) * (nb : G)⁻¹) • b = c
  rw [mul_smul, ← hnb]
  simp [hnc]

/-- Witt's Lemma [II1; 2.3] in the Sylow case, applied to injective
k-tuples. -/
public theorem chapter1_witt_normalizer_pretransitive
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    {p k : ℕ} (hp : Nat.Prime p)
    (htrans : MulAction.IsMultiplyPretransitive G Omega k)
    (a : Fin k ↪ Omega)
    (S : Sylow p (MulAction.stabilizer G a)) :
    let D : Subgroup G := MulAction.stabilizer G a
    let P : Subgroup G := (S : Subgroup D).map D.subtype
    IsTransitiveOn (Subgroup.normalizer (P : Set G))
      (fixedPointsOfSubgroup G (Fin k ↪ Omega) P) := by
  exact witt_normalizer_pretransitive_core hp htrans a S

/-- Transitivity supplied by Witt on fixed injective pairs is exactly double
transitivity on the underlying fixed points. -/
public theorem witt_normalizer_twoTransitiveOn_fixedPoints
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    {p : ℕ} (hp : p.Prime)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a : Fin 2 ↪ Omega) (P : Subgroup G)
    (hPsyl : theorem4bIsSylowSubgroupOf p P
      (MulAction.stabilizer G a)) :
    IsTwoTransitiveOn (Subgroup.normalizer (P : Set G))
      (fixedPointsOfSubgroup G Omega P) := by
  rcases hPsyl with ⟨S, hP⟩
  have hwitt := chapter1_witt_normalizer_pretransitive hp htwo a S
  rw [hP]
  intro alpha beta gamma delta ha hb hc hd hab hcd
  let ab : Fin 2 ↪ Omega :=
    { toFun := ![alpha, beta]
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim (hab (by simpa using hij))
        · exact False.elim (hab (by simpa using hij.symm))
        · rfl }
  let cd : Fin 2 ↪ Omega :=
    { toFun := ![gamma, delta]
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim (hcd (by simpa using hij))
        · exact False.elim (hcd (by simpa using hij.symm))
        · rfl }
  have habFix : ab ∈ fixedPointsOfSubgroup G (Fin 2 ↪ Omega)
      ((S : Subgroup (MulAction.stabilizer G a)).map
        (MulAction.stabilizer G a).subtype) := by
    intro x hx
    apply Function.Embedding.ext
    intro i
    fin_cases i
    · exact ha x (by simpa [hP] using hx)
    · exact hb x (by simpa [hP] using hx)
  have hcdFix : cd ∈ fixedPointsOfSubgroup G (Fin 2 ↪ Omega)
      ((S : Subgroup (MulAction.stabilizer G a)).map
        (MulAction.stabilizer G a).subtype) := by
    intro x hx
    apply Function.Embedding.ext
    intro i
    fin_cases i
    · exact hc x (by simpa [hP] using hx)
    · exact hd x (by simpa [hP] using hx)
  obtain ⟨n, hn⟩ := hwitt habFix hcdFix
  refine ⟨n, ?_, ?_⟩
  · exact congrArg (fun f : Fin 2 ↪ Omega => f 0) hn
  · exact congrArg (fun f : Fin 2 ↪ Omega => f 1) hn

/-- The ordered pair consisting of the base coset and the coset represented by
an element outside the point stabilizer. -/
public def baseOutsidePair
    {X : Type u} [Group X] (M : Subgroup X) (t : X) (htM : t ∉ M) :
    Fin 2 ↪ conjugateCosetSpace M where
  toFun := ![QuotientGroup.mk 1, QuotientGroup.mk t]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      apply htM
      simpa using QuotientGroup.eq.mp hij
    · exfalso
      apply htM
      simpa using QuotientGroup.eq.mp hij.symm
    · rfl

/-- For an involution `t`, the stabilizer of the base/`t` pair is the source
two-point stabilizer `M ⊓ M^t`. -/
public theorem stabilizer_baseOutsidePair
    {X : Type u} [Group X] {M : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M) :
    MulAction.stabilizer X (baseOutsidePair M t htM) =
      M ⊓ rightConjugate M t := by
  ext x
  rw [MulAction.mem_stabilizer_iff]
  change x • baseOutsidePair M t htM = baseOutsidePair M t htM ↔ _
  rw [Function.Embedding.ext_iff]
  constructor
  · intro h
    constructor
    · have hxbase : x ∈ MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) :=
        MulAction.mem_stabilizer_iff.mpr (by
          exact h 0)
      simpa [baseCoset_stabilizer] using hxbase
    · have hxt : x ∈ MulAction.stabilizer X
          (QuotientGroup.mk t : conjugateCosetSpace M) :=
        MulAction.mem_stabilizer_iff.mpr (by
          exact h 1)
      simpa [conjugateCoset_stabilizer, ht.inv_eq_self] using hxt
  · rintro ⟨hxM, hxMt⟩ i
    fin_cases i
    · have hxbase : x ∈ MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
        simpa [baseCoset_stabilizer] using hxM
      have hh := MulAction.mem_stabilizer_iff.mp hxbase
      change (x • baseOutsidePair M t htM) 0 =
        (baseOutsidePair M t htM) 0
      exact hh
    · have hxt : x ∈ MulAction.stabilizer X
          (QuotientGroup.mk t : conjugateCosetSpace M) := by
        simpa [conjugateCoset_stabilizer, ht.inv_eq_self] using hxMt
      have hh := MulAction.mem_stabilizer_iff.mp hxt
      change (x • baseOutsidePair M t htM) 1 =
        (baseOutsidePair M t htM) 1
      exact hh

private theorem two_le_fixedPoints_card
    {G Omega : Type*} [Group G] [MulAction G Omega] [Finite Omega]
    {P : Subgroup G} {a b : Omega}
    (ha : a ∈ fixedPointsOfSubgroup G Omega P)
    (hb : b ∈ fixedPointsOfSubgroup G Omega P) (hab : a ≠ b) :
    2 ≤ Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega P} := by
  let f : Fin 2 → {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega P} :=
    fun i => if i = 0 then ⟨a, ha⟩ else ⟨b, hb⟩
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      exact hab (congrArg Subtype.val hij)
    · exfalso
      exact hab (congrArg Subtype.val hij).symm
    · rfl
  simpa using Nat.card_le_card_of_injective f hf

/-- Normalizer growth inside a finite `p`-group: a proper subgroup is strictly
contained in a larger `p`-subgroup that normalizes it. -/
public theorem exists_larger_normalizer_pSubgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    {P R : Subgroup G} (hRp : IsPGroup p R) (hPR : P < R) :
    ∃ R₁ : Subgroup G,
      IsPGroup p R₁ ∧ P < R₁ ∧ R₁ ≤ R ∧
        R₁ ≤ Subgroup.normalizer (P : Set G) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let PR : Subgroup R := P.subgroupOf R
  have hPRtop : PR < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply (not_le_of_gt hPR)
    intro x hxR
    let xR : R := ⟨x, hxR⟩
    have hxPR : xR ∈ PR := by rw [htop]; trivial
    exact hxPR
  letI : Group.IsNilpotent R := hRp.isNilpotent
  have hPRnorm : PR < Subgroup.normalizer (PR : Set R) :=
    normalizerCondition_of_isNilpotent PR hPRtop
  let NR : Subgroup R := Subgroup.normalizer (PR : Set R)
  let R₁ : Subgroup G := NR.map R.subtype
  have hPR₁ : P ≤ R₁ := by
    intro x hxP
    let xR : R := ⟨x, hPR.le hxP⟩
    apply Subgroup.mem_map.mpr
    refine ⟨xR, ?_, rfl⟩
    exact Subgroup.le_normalizer (show xR ∈ PR from hxP)
  have hR₁R : R₁ ≤ R := by
    simpa [R₁] using Subgroup.map_le_range R.subtype NR
  have hR₁norm : R₁ ≤ Subgroup.normalizer (P : Set G) := by
    have hmap := Subgroup.le_normalizer_map (H := PR) R.subtype
    simpa [R₁, NR, PR, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hPR.le] using hmap
  have hR₁p : IsPGroup p R₁ := by
    exact (hRp.to_subgroup NR).map R.subtype
  have hPR₁lt : P < R₁ := by
    apply lt_of_le_of_ne hPR₁
    intro hPR₁eq
    obtain ⟨y, hyNR, hyPR⟩ := SetLike.exists_of_lt hPRnorm
    apply hyPR
    have hyR₁ : (y : G) ∈ R₁ :=
      Subgroup.mem_map.mpr ⟨y, hyNR, rfl⟩
    rw [← hPR₁eq] at hyR₁
    exact hyR₁
  exact ⟨R₁, hR₁p, hPR₁lt, hR₁R, hR₁norm⟩

private theorem fixed_eq_of_maximal_pSubgroup
    {G Omega : Type*} [Group G] [MulAction G Omega] [Finite Omega]
    {p : ℕ} {P Q : Subgroup G}
    (hmax : Maximal (fun U : Subgroup G =>
      IsPGroup p U ∧
        1 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega U}) P)
    (hQp : IsPGroup p Q) (hPQ : P < Q)
    {a b : Omega}
    (ha : a ∈ fixedPointsOfSubgroup G Omega Q)
    (hb : b ∈ fixedPointsOfSubgroup G Omega Q) :
    a = b := by
  by_contra hab
  have htwo := two_le_fixedPoints_card ha hb hab
  have hQleP := hmax.2 ⟨hQp, by omega⟩ hPQ.le
  exact (not_le_of_gt hPQ) hQleP

private noncomputable def fixedPoints_ofStabilizerEquiv
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (a : Omega) (U : Subgroup (MulAction.stabilizer G a)) :
    let A : Subgroup G := MulAction.stabilizer G a
    let Q : Subgroup G := U.map A.subtype
    let aQ : {omega : Omega //
        omega ∈ fixedPointsOfSubgroup G Omega Q} :=
      ⟨a, fun q hq => by
        rcases Subgroup.mem_map.mp hq with ⟨u, _hu, rfl⟩
        exact MulAction.mem_stabilizer_iff.mp u.property⟩
    {x : SubMulAction.ofStabilizer G a //
        x ∈ fixedPointsOfSubgroup A
          (SubMulAction.ofStabilizer G a) U} ≃
      {y : {omega : Omega //
        omega ∈ fixedPointsOfSubgroup G Omega Q} // y ≠ aQ} := by
  classical
  let A : Subgroup G := MulAction.stabilizer G a
  let Q : Subgroup G := U.map A.subtype
  let aQ : {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega Q} :=
    ⟨a, fun q hq => by
      rcases Subgroup.mem_map.mp hq with ⟨u, _hu, rfl⟩
      exact MulAction.mem_stabilizer_iff.mp u.property⟩
  exact
    { toFun := fun x =>
        ⟨⟨x, by
            intro q hq
            rcases Subgroup.mem_map.mp hq with ⟨u, hu, rfl⟩
            exact congrArg Subtype.val (x.property u hu)⟩,
          by
            intro h
            exact (SubMulAction.neq_of_mem_ofStabilizer G a)
              (congrArg (fun z : {omega : Omega //
                omega ∈ fixedPointsOfSubgroup G Omega Q} => (z : Omega)) h)⟩
      invFun := fun y =>
        ⟨⟨y.1, (SubMulAction.mem_ofStabilizer_iff G a).mpr (by
              intro hya
              apply y.2
              apply Subtype.ext
              exact hya)⟩,
          by
            intro u hu
            apply Subtype.ext
            exact y.1.property (u : G)
              (Subgroup.mem_map_of_mem A.subtype hu)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem fixedPoints_card_ofStabilizer
    {G Omega : Type*} [Group G] [MulAction G Omega] [Finite Omega]
    (a : Omega) (U : Subgroup (MulAction.stabilizer G a)) :
    Nat.card {omega : Omega //
        omega ∈ fixedPointsOfSubgroup G Omega
          (U.map (MulAction.stabilizer G a).subtype)} =
      Nat.card {x : SubMulAction.ofStabilizer G a //
        x ∈ fixedPointsOfSubgroup (MulAction.stabilizer G a)
          (SubMulAction.ofStabilizer G a) U} + 1 := by
  classical
  let A : Subgroup G := MulAction.stabilizer G a
  let Q : Subgroup G := U.map A.subtype
  let aQ : {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega Q} :=
    ⟨a, fun q hq => by
      rcases Subgroup.mem_map.mp hq with ⟨u, _hu, rfl⟩
      exact MulAction.mem_stabilizer_iff.mp u.property⟩
  let e := fixedPoints_ofStabilizerEquiv a U
  change Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega Q} =
    Nat.card {x : SubMulAction.ofStabilizer G a //
      x ∈ fixedPointsOfSubgroup A
        (SubMulAction.ofStabilizer G a) U} + 1
  calc
    Nat.card {omega : Omega //
        omega ∈ fixedPointsOfSubgroup G Omega Q} =
        Nat.card (Option {y : {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega Q} // y ≠ aQ}) :=
      Nat.card_congr (Equiv.optionSubtypeNe aQ).symm
    _ = Nat.card {y : {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega Q} // y ≠ aQ} + 1 :=
      Finite.card_option
    _ = Nat.card {x : SubMulAction.ofStabilizer G a //
          x ∈ fixedPointsOfSubgroup A
            (SubMulAction.ofStabilizer G a) U} + 1 := by
      congr 1
      exact (Nat.card_congr e).symm

private theorem maximal_subgroupOf_stabilizer
    {G Omega : Type*} [Group G] [MulAction G Omega] [Finite Omega]
    {p : ℕ} {P : Subgroup G}
    (hmax : Maximal (fun U : Subgroup G =>
      IsPGroup p U ∧
        2 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega U}) P)
    {a : Omega} (ha : a ∈ fixedPointsOfSubgroup G Omega P) :
    let A : Subgroup G := MulAction.stabilizer G a
    Maximal (fun U : Subgroup A =>
      IsPGroup p U ∧
        1 < Nat.card {x : SubMulAction.ofStabilizer G a //
          x ∈ fixedPointsOfSubgroup A
            (SubMulAction.ofStabilizer G a) U})
      (P.subgroupOf A) := by
  classical
  let A : Subgroup G := MulAction.stabilizer G a
  let PA : Subgroup A := P.subgroupOf A
  have hPA : P ≤ A := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mpr (ha x hxP)
  have hmapPA : PA.map A.subtype = P := by
    change (P.subgroupOf A).map A.subtype = P
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPA]
  dsimp only
  change Maximal (fun U : Subgroup A =>
    IsPGroup p U ∧
      1 < Nat.card {x : SubMulAction.ofStabilizer G a //
        x ∈ fixedPointsOfSubgroup A
          (SubMulAction.ofStabilizer G a) U}) PA
  constructor
  · constructor
    · exact hmax.1.1.of_equiv
        (Subgroup.subgroupOfEquivOfLe hPA).symm
    · have hcard := fixedPoints_card_ofStabilizer a PA
      change Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega (PA.map A.subtype)} =
        Nat.card {x : SubMulAction.ofStabilizer G a //
          x ∈ fixedPointsOfSubgroup A
            (SubMulAction.ofStabilizer G a) PA} + 1 at hcard
      rw [hmapPA] at hcard
      have hPcard : 2 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega P} := hmax.1.2
      omega
  · intro U hU hPAU
    let Q : Subgroup G := U.map A.subtype
    have hPQ : P ≤ Q := by
      intro x hxP
      let xA : A := ⟨x, hPA hxP⟩
      apply Subgroup.mem_map.mpr
      exact ⟨xA, hPAU (show xA ∈ PA from hxP), rfl⟩
    have hQp : IsPGroup p Q := hU.1.map A.subtype
    have hQcard : 2 < Nat.card {omega : Omega //
        omega ∈ fixedPointsOfSubgroup G Omega Q} := by
      have hcard := fixedPoints_card_ofStabilizer a U
      change Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega Q} =
        Nat.card {x : SubMulAction.ofStabilizer G a //
          x ∈ fixedPointsOfSubgroup A
            (SubMulAction.ofStabilizer G a) U} + 1 at hcard
      omega
    have hQP : Q ≤ P := hmax.2 ⟨hQp, hQcard⟩ hPQ
    intro u huU
    change (u : G) ∈ P
    exact hQP (Subgroup.mem_map_of_mem A.subtype huU)

private theorem bender_normalizer_pretransitive
    {G Omega : Type*} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    {p : ℕ} (hp : Nat.Prime p)
    (htrans : MulAction.IsPretransitive G Omega)
    (P : Subgroup G)
    (hmax : Maximal (fun U : Subgroup G =>
      IsPGroup p U ∧
        1 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega U}) P) :
    IsTransitiveOn (Subgroup.normalizer (P : Set G))
      (fixedPointsOfSubgroup G Omega P) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let FixedP := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup G Omega P}
  have hFixedPpos : 0 < Nat.card FixedP :=
    lt_trans Nat.zero_lt_one hmax.1.2
  let aP : FixedP := Classical.choice (Nat.card_pos_iff.mp hFixedPpos).1
  let a : Omega := aP
  have ha : a ∈ fixedPointsOfSubgroup G Omega P := aP.property
  let D : Subgroup G := MulAction.stabilizer G a
  have hPD : P ≤ D := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mpr (ha x hxP)
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
  let R : Subgroup G := (S : Subgroup D).map D.subtype
  have hPR : P ≤ R := by
    intro x hxP
    let xD : D := ⟨x, hPD hxP⟩
    apply Subgroup.mem_map.mpr
    exact ⟨xD, hPDS (show xD ∈ PD from hxP), rfl⟩
  by_cases hPR_eq : P = R
  · rw [hPR_eq]
    simpa [D, R] using
      (witt_normalizer_pretransitive_core hp htrans a S)
  have hPRlt : P < R := lt_of_le_of_ne hPR hPR_eq
  have hRp : IsPGroup p R := S.isPGroup'.map D.subtype
  have hRD : R ≤ D := by
    simpa [R] using Subgroup.map_le_range D.subtype (S : Subgroup D)
  have hRa : a ∈ fixedPointsOfSubgroup G Omega R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR)
  have hRunique : ∀ {b : Omega},
      b ∈ fixedPointsOfSubgroup G Omega R → b = a := by
    intro b hb
    exact fixed_eq_of_maximal_pSubgroup
      hmax hRp hPRlt hb hRa
  let FixedR := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup G Omega R}
  letI : Nonempty FixedR := ⟨⟨a, hRa⟩⟩
  letI : Subsingleton FixedR := ⟨by
    intro x y
    apply Subtype.ext
    exact (hRunique x.property).trans (hRunique y.property).symm⟩
  have hFixedRcard : Nat.card FixedR = 1 := Nat.card_unique
  let fixedEquiv : FixedR ≃ MulAction.fixedPoints R Omega :=
    { toFun := fun omega => ⟨omega, by
        rw [MulAction.mem_fixedPoints]
        intro r
        exact omega.property r r.property⟩
      invFun := fun omega => ⟨omega, by
        intro r hr
        let rR : R := ⟨r, hr⟩
        exact MulAction.mem_fixedPoints.mp omega.property rR⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hMulFixedRcard : Nat.card (MulAction.fixedPoints R Omega) = 1 := by
    rw [← Nat.card_congr fixedEquiv]
    exact hFixedRcard
  have hpOmega : ¬ p ∣ Nat.card Omega := by
    intro hpCard
    apply hp.not_dvd_one
    apply Nat.modEq_zero_iff_dvd.mp
    calc
      1 = Nat.card (MulAction.fixedPoints R Omega) := hMulFixedRcard.symm
      _ ≡ Nat.card Omega [MOD p] :=
        (hRp.card_modEq_card_fixedPoints Omega).symm
      _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpCard
  obtain ⟨R₁, hR₁p, hPR₁, hR₁R, hR₁norm⟩ :=
    exists_larger_normalizer_pSubgroup hp hRp hPRlt
  have hR₁a : a ∈ fixedPointsOfSubgroup G Omega R₁ := by
    intro x hxR₁
    exact hRa x (hR₁R hxR₁)
  have hreach : ∀ b : Omega,
      b ∈ fixedPointsOfSubgroup G Omega P →
      ∃ n : Subgroup.normalizer (P : Set G), (n : G) • a = b := by
    intro b hb
    let E : Subgroup G := MulAction.stabilizer G b
    have hPE : P ≤ E := by
      intro x hxP
      exact MulAction.mem_stabilizer_iff.mpr (hb x hxP)
    let PE : Subgroup E := P.subgroupOf E
    have hPEp : IsPGroup p PE :=
      hmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPE).symm
    obtain ⟨T, hPET⟩ := hPEp.exists_le_sylow
    let Q : Subgroup G := (T : Subgroup E).map E.subtype
    have hPQ : P ≤ Q := by
      intro x hxP
      let xE : E := ⟨x, hPE hxP⟩
      apply Subgroup.mem_map.mpr
      exact ⟨xE, hPET (show xE ∈ PE from hxP), rfl⟩
    by_cases hPQ_eq : P = Q
    · have hw :=
        witt_normalizer_pretransitive_core hp htrans b T
      have hw' : IsTransitiveOn (Subgroup.normalizer (P : Set G))
          (fixedPointsOfSubgroup G Omega P) := by
        rw [hPQ_eq]
        simpa [E, Q] using hw
      exact hw' ha hb
    have hPQlt : P < Q := lt_of_le_of_ne hPQ hPQ_eq
    have hQp : IsPGroup p Q := T.isPGroup'.map E.subtype
    have hQE : Q ≤ E := by
      simpa [Q] using Subgroup.map_le_range E.subtype (T : Subgroup E)
    obtain ⟨Q₁, hQ₁p, hPQ₁, hQ₁Q, hQ₁norm⟩ :=
      exists_larger_normalizer_pSubgroup hp hQp hPQlt
    have hQ₁b : b ∈ fixedPointsOfSubgroup G Omega Q₁ := by
      intro x hxQ₁
      exact MulAction.mem_stabilizer_iff.mp (hQE (hQ₁Q hxQ₁))
    let N : Subgroup G := Subgroup.normalizer (P : Set G)
    let R₁N : Subgroup N := R₁.subgroupOf N
    let Q₁N : Subgroup N := Q₁.subgroupOf N
    have hR₁Np : IsPGroup p R₁N :=
      hR₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hR₁norm).symm
    have hQ₁Np : IsPGroup p Q₁N :=
      hQ₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₁norm).symm
    obtain ⟨SR, hR₁NSR⟩ := hR₁Np.exists_le_sylow
    obtain ⟨SQ, hQ₁NSQ⟩ := hQ₁Np.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N SR SQ
    let A : Subgroup G := (SQ : Subgroup N).map N.subtype
    have hAp : IsPGroup p A := SQ.isPGroup'.map N.subtype
    obtain ⟨delta, hdelta⟩ :=
      hAp.nonempty_fixed_point_of_prime_not_dvd_card Omega hpOmega
    have hdeltaFix : ∀ x : A, x • delta = delta :=
      MulAction.mem_fixedPoints.mp hdelta
    have hQ₁A : Q₁ ≤ A := by
      intro x hxQ₁
      let xN : N := ⟨x, hQ₁norm hxQ₁⟩
      apply Subgroup.mem_map.mpr
      exact ⟨xN, hQ₁NSQ (show xN ∈ Q₁N from hxQ₁), rfl⟩
    have hdeltaQ₁ : delta ∈ fixedPointsOfSubgroup G Omega Q₁ := by
      intro x hxQ₁
      let xA : A := ⟨x, hQ₁A hxQ₁⟩
      exact hdeltaFix xA
    have hdeltaEqB : delta = b :=
      fixed_eq_of_maximal_pSubgroup
        hmax hQ₁p hPQ₁ hdeltaQ₁ hQ₁b
    have hconjR₁A : ∀ x : G, x ∈ R₁ →
        (g : G) * x * (g : G)⁻¹ ∈ A := by
      intro x hxR₁
      let xN : N := ⟨x, hR₁norm hxR₁⟩
      have hxSR : xN ∈ (SR : Subgroup N) :=
        hR₁NSR (show xN ∈ R₁N from hxR₁)
      have hxSQ : (MulAut.conj g) xN ∈ (SQ : Subgroup N) := by
        rw [← hg, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul
          xN (MulAut.conj g) (SR : Subgroup N) hxSR
      apply Subgroup.mem_map.mpr
      refine ⟨(MulAut.conj g) xN, hxSQ, ?_⟩
      rfl
    have hginvDelta : (g : G)⁻¹ • delta ∈
        fixedPointsOfSubgroup G Omega R₁ := by
      intro x hxR₁
      have hconjMem := hconjR₁A x hxR₁
      let yA : A := ⟨(g : G) * x * (g : G)⁻¹, hconjMem⟩
      have hyFix : ((g : G) * x * (g : G)⁻¹) • delta = delta :=
        hdeltaFix yA
      calc
        x • ((g : G)⁻¹ • delta) =
            (g : G)⁻¹ •
              (((g : G) * x * (g : G)⁻¹) • delta) := by
                simp [smul_smul, mul_assoc]
        _ = (g : G)⁻¹ • delta := by rw [hyFix]
    have hginvEqA : (g : G)⁻¹ • delta = a :=
      fixed_eq_of_maximal_pSubgroup
        hmax hR₁p hPR₁ hginvDelta hR₁a
    have hgA : (g : G) • a = delta := by
      rw [← hginvEqA]
      simp
    refine ⟨g, ?_⟩
    rw [hgA, hdeltaEqB]
  intro b c hb hc
  obtain ⟨nb, hnb⟩ := hreach b hb
  obtain ⟨nc, hnc⟩ := hreach c hc
  let n : Subgroup.normalizer (P : Set G) := nc * nb⁻¹
  refine ⟨n, ?_⟩
  change ((nc : G) * (nb : G)⁻¹) • b = c
  rw [mul_smul, ← hnb]
  simp [hnc]

private theorem bender_normalizer_pointStabilizer_pretransitive
    {G Omega : Type*} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    {p : ℕ} (hp : Nat.Prime p)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (P : Subgroup G)
    (hmax : Maximal (fun U : Subgroup G =>
      IsPGroup p U ∧
        2 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega U}) P)
    {a : Omega} (ha : a ∈ fixedPointsOfSubgroup G Omega P) :
    IsTransitiveOn
      (Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G a)
      {omega : Omega |
        omega ∈ fixedPointsOfSubgroup G Omega P ∧ omega ≠ a} := by
  classical
  letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let A : Subgroup G := MulAction.stabilizer G a
  let PA : Subgroup A := P.subgroupOf A
  have hPA : P ≤ A := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mpr (ha x hxP)
  have hmapPA : PA.map A.subtype = P := by
    change (P.subgroupOf A).map A.subtype = P
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPA]
  have hmulti : MulAction.IsMultiplyPretransitive A
      (SubMulAction.ofStabilizer G a) 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  have hpre : MulAction.IsPretransitive A
      (SubMulAction.ofStabilizer G a) :=
    (MulAction.is_one_pretransitive_iff
      (G := A) (α := SubMulAction.ofStabilizer G a)).mp hmulti
  have hmaxPA : Maximal (fun U : Subgroup A =>
      IsPGroup p U ∧
        1 < Nat.card {x : SubMulAction.ofStabilizer G a //
          x ∈ fixedPointsOfSubgroup A
            (SubMulAction.ofStabilizer G a) U}) PA := by
    simpa [A, PA] using maximal_subgroupOf_stabilizer hmax ha
  have htransPA : IsTransitiveOn (Subgroup.normalizer (PA : Set A))
      (fixedPointsOfSubgroup A (SubMulAction.ofStabilizer G a) PA) :=
    bender_normalizer_pretransitive hp hpre PA hmaxPA
  intro b c hb hc
  let bA : SubMulAction.ofStabilizer G a := ⟨b, hb.2⟩
  let cA : SubMulAction.ofStabilizer G a := ⟨c, hc.2⟩
  have hbA : bA ∈ fixedPointsOfSubgroup A
      (SubMulAction.ofStabilizer G a) PA := by
    intro u huPA
    apply Subtype.ext
    exact hb.1 (u : G) huPA
  have hcA : cA ∈ fixedPointsOfSubgroup A
      (SubMulAction.ofStabilizer G a) PA := by
    intro u huPA
    apply Subtype.ext
    exact hc.1 (u : G) huPA
  obtain ⟨n, hn⟩ := htransPA hbA hcA
  have hnMap : ((n : A) : G) ∈
      Subgroup.normalizer ((PA.map A.subtype : Subgroup G) : Set G) := by
    apply Subgroup.le_normalizer_map (H := PA) A.subtype
    exact Subgroup.mem_map_of_mem A.subtype n.property
  have hnNorm : ((n : A) : G) ∈
      Subgroup.normalizer (P : Set G) := by
    simpa [hmapPA] using hnMap
  let nG : ↥(Subgroup.normalizer (P : Set G) ⊓
      MulAction.stabilizer G a) :=
    ⟨(n : A), hnNorm, (n : A).property⟩
  refine ⟨nG, ?_⟩
  exact congrArg Subtype.val hn

/-- Selected-point form of the `k = 1` Bender normalizer argument.  It only
requires maximality among `p`-subgroups which retain the selected fixed point
`a`; global maximality is unnecessary for transitivity on the remaining
fixed points. -/
public theorem chapter1_bender_normalizer_pointStabilizer_pretransitive_of_local
    {G Omega : Type*} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    {p : ℕ} (hp : Nat.Prime p)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (P : Subgroup G) {a : Omega}
    (hmax : Maximal (fun U : Subgroup G =>
      IsPGroup p U ∧ U ≤ MulAction.stabilizer G a ∧
        2 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega U}) P) :
    IsTransitiveOn
      (Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G a)
      {omega : Omega |
        omega ∈ fixedPointsOfSubgroup G Omega P ∧ omega ≠ a} := by
  classical
  letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let A : Subgroup G := MulAction.stabilizer G a
  let PA : Subgroup A := P.subgroupOf A
  have hPA : P ≤ A := hmax.1.2.1
  have hmapPA : PA.map A.subtype = P := by
    change (P.subgroupOf A).map A.subtype = P
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPA]
  have hmulti : MulAction.IsMultiplyPretransitive A
      (SubMulAction.ofStabilizer G a) 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  have hpre : MulAction.IsPretransitive A
      (SubMulAction.ofStabilizer G a) :=
    (MulAction.is_one_pretransitive_iff
      (G := A) (α := SubMulAction.ofStabilizer G a)).mp hmulti
  have hmaxPA : Maximal (fun U : Subgroup A =>
      IsPGroup p U ∧
        1 < Nat.card {x : SubMulAction.ofStabilizer G a //
          x ∈ fixedPointsOfSubgroup A
            (SubMulAction.ofStabilizer G a) U}) PA := by
    constructor
    · constructor
      · exact hmax.1.1.of_equiv
          (Subgroup.subgroupOfEquivOfLe hPA).symm
      · have hcard := fixedPoints_card_ofStabilizer a PA
        have hPcard := hmax.1.2.2
        change Nat.card {omega : Omega //
            omega ∈ fixedPointsOfSubgroup G Omega (PA.map A.subtype)} =
          Nat.card {x : SubMulAction.ofStabilizer G a //
            x ∈ fixedPointsOfSubgroup A
              (SubMulAction.ofStabilizer G a) PA} + 1 at hcard
        rw [hmapPA] at hcard
        omega
    · intro U hU hPAU
      let Q : Subgroup G := U.map A.subtype
      have hPQ : P ≤ Q := by
        intro x hxP
        let xA : A := ⟨x, hPA hxP⟩
        exact Subgroup.mem_map.mpr
          ⟨xA, hPAU (show xA ∈ PA from hxP), rfl⟩
      have hQp : IsPGroup p Q := hU.1.map A.subtype
      have hQA : Q ≤ A := by
        simpa [Q] using Subgroup.map_le_range A.subtype U
      have hQcard : 2 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega Q} := by
        have hcard := fixedPoints_card_ofStabilizer a U
        have hUcard := hU.2
        change Nat.card {omega : Omega //
            omega ∈ fixedPointsOfSubgroup G Omega Q} =
          Nat.card {x : SubMulAction.ofStabilizer G a //
            x ∈ fixedPointsOfSubgroup A
              (SubMulAction.ofStabilizer G a) U} + 1 at hcard
        omega
      have hQP : Q ≤ P := hmax.2 ⟨hQp, hQA, hQcard⟩ hPQ
      intro u huU
      change (u : G) ∈ P
      exact hQP (Subgroup.mem_map_of_mem A.subtype huU)
  have htransPA : IsTransitiveOn (Subgroup.normalizer (PA : Set A))
      (fixedPointsOfSubgroup A (SubMulAction.ofStabilizer G a) PA) :=
    bender_normalizer_pretransitive hp hpre PA hmaxPA
  intro b c hb hc
  let bA : SubMulAction.ofStabilizer G a := ⟨b, hb.2⟩
  let cA : SubMulAction.ofStabilizer G a := ⟨c, hc.2⟩
  have hbA : bA ∈ fixedPointsOfSubgroup A
      (SubMulAction.ofStabilizer G a) PA := by
    intro u huPA
    apply Subtype.ext
    exact hb.1 (u : G) huPA
  have hcA : cA ∈ fixedPointsOfSubgroup A
      (SubMulAction.ofStabilizer G a) PA := by
    intro u huPA
    apply Subtype.ext
    exact hc.1 (u : G) huPA
  obtain ⟨n, hn⟩ := htransPA hbA hcA
  have hnMap : ((n : A) : G) ∈
      Subgroup.normalizer ((PA.map A.subtype : Subgroup G) : Set G) := by
    apply Subgroup.le_normalizer_map (H := PA) A.subtype
    exact Subgroup.mem_map_of_mem A.subtype n.property
  have hnNorm : ((n : A) : G) ∈
      Subgroup.normalizer (P : Set G) := by
    simpa [hmapPA] using hnMap
  let nG : ↑(Subgroup.normalizer (P : Set G) ⊓
      MulAction.stabilizer G a) :=
    ⟨(n : A), hnNorm, (n : A).property⟩
  refine ⟨nG, ?_⟩
  exact congrArg Subtype.val hn

/-- The two-transitive case of Bender's extension of Witt's Lemma
[II1; 2.4]. -/
public theorem chapter1_bender_normalizer_two_pretransitive
    {G Omega : Type*} [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega]
    {p : ℕ} (hp : Nat.Prime p)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (P : Subgroup G)
    (hmax : Maximal (fun U : Subgroup G =>
      IsPGroup p U ∧
        2 < Nat.card {omega : Omega //
          omega ∈ fixedPointsOfSubgroup G Omega U}) P) :
    IsTwoTransitiveOn (Subgroup.normalizer (P : Set G))
      (fixedPointsOfSubgroup G Omega P) := by
  classical
  intro alpha beta gamma delta ha hb hgamma hdelta hab hgammaDelta
  let FixedP := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup G Omega P}
  let alphaP : FixedP := ⟨alpha, ha⟩
  let gammaP : FixedP := ⟨gamma, hgamma⟩
  have hthreeNat : 3 ≤ Nat.card FixedP := by
    have hcard : 2 < Nat.card FixedP := hmax.1.2
    omega
  have hthreeCardinal : (3 : Cardinal) ≤ Cardinal.mk FixedP := by
    rw [← Nat.cast_card]
    exact_mod_cast hthreeNat
  obtain ⟨epsilonP, hepsilonAlphaP, hepsilonGammaP⟩ :=
    Cardinal.exists_ne_ne_of_three_le hthreeCardinal alphaP gammaP
  let epsilon : Omega := epsilonP
  have hepsilon : epsilon ∈ fixedPointsOfSubgroup G Omega P :=
    epsilonP.property
  have halphaEpsilon : alpha ≠ epsilon := by
    intro h
    apply hepsilonAlphaP
    apply Subtype.ext
    exact h.symm
  have hgammaEpsilon : gamma ≠ epsilon := by
    intro h
    apply hepsilonGammaP
    apply Subtype.ext
    exact h.symm
  have htransEpsilon :=
    bender_normalizer_pointStabilizer_pretransitive
      hp htwo P hmax hepsilon
  obtain ⟨n₁, hn₁⟩ := htransEpsilon
    ⟨ha, halphaEpsilon⟩ ⟨hgamma, hgammaEpsilon⟩
  let beta₁ : Omega := (n₁ : G) • beta
  have hbeta₁ : beta₁ ∈ fixedPointsOfSubgroup G Omega P :=
    fixedPoints_smul_of_mem_normalizer n₁.property.1 hb
  have hbeta₁Gamma : beta₁ ≠ gamma := by
    intro h
    apply hab
    apply MulAction.injective (n₁ : G)
    exact hn₁.trans h.symm
  have htransGamma :=
    bender_normalizer_pointStabilizer_pretransitive
      hp htwo P hmax hgamma
  obtain ⟨n₂, hn₂⟩ := htransGamma
    ⟨hbeta₁, hbeta₁Gamma⟩ ⟨hdelta, hgammaDelta.symm⟩
  let n : Subgroup.normalizer (P : Set G) :=
    ⟨(n₂ : G) * (n₁ : G),
      (Subgroup.normalizer (P : Set G)).mul_mem
        n₂.property.1 n₁.property.1⟩
  refine ⟨n, ?_, ?_⟩
  · change ((n₂ : G) * (n₁ : G)) • alpha = gamma
    rw [mul_smul, hn₁]
    exact MulAction.mem_stabilizer_iff.mp n₂.property.2
  · change ((n₂ : G) * (n₁ : G)) • beta = delta
    rw [mul_smul]
    exact hn₂

end CFSG.BenderSuzuki
