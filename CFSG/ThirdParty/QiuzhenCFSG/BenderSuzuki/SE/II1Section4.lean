module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingCounting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_16
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Part II, Chapter I, Section 4

This file proves the three Section 4 consequences used in the Bender--Suzuki
argument.  They are placed below Sections 9--11 because they are earlier-volume
inputs, not conclusions of those later sections.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise IsMulCommutative

universe u

set_option maxHeartbeats 1000000

/-- Pointwise notation for `C_I(g) = 1`, where
`I = peterfalviKSet D t`. -/
@[expose] public def PeterfalviCentralizersTrivial
    {X : Type u} [Group X]
    (D : Subgroup X) (t : X) (P : Subgroup X) : Prop :=
  ∀ g : X, g ∈ P → g ≠ 1 →
      ∀ x : X, x ∈ peterfalviKSet D t → x * g = g * x → x = 1

/-- Triviality of the centralizer in `I` of the whole subgroup `P`.

This is the hypothesis used in Peterfalvi `[II1; 4.3(a)]`; the stronger
pointwise condition above is the separate hypothesis of `[II1; 4.3(b)]`. -/
@[expose] public def PeterfalviSubgroupCentralizerTrivial
    {X : Type u} [Group X]
    (D : Subgroup X) (t : X) (P : Subgroup X) : Prop :=
  ∀ x : X, x ∈ peterfalviKSet D t →
    x ∈ Subgroup.centralizer (P : Set X) → x = 1

/-- The pointwise hypothesis of `[II1; 4.3(b)]` implies the subgroup
centralizer hypothesis of `[II1; 4.3(a)]` for a nontrivial subgroup. -/
public theorem PeterfalviCentralizersTrivial.subgroup
    {X : Type u} [Group X]
    {D P : Subgroup X} {t : X}
    (hPne : P ≠ ⊥) (h : PeterfalviCentralizersTrivial D t P) :
    PeterfalviSubgroupCentralizerTrivial D t P := by
  intro x hxI hxC
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  exact h (g : X) g.property (by simpa using hg1) x hxI
    ((Subgroup.mem_centralizer_iff.mp hxC (g : X) g.property).symm)

/-- The exact prime-transfer consequence of Peterfalvi `[II1; 4.2]`. -/
@[expose] public def II1Lemma42PrimeTransfer
    {X : Type u} [Group X] [Finite X] : Prop :=
  ∀ (D : Subgroup X) (t : X),
    Odd (Nat.card D) →
    IsInvolution t →
    t ∈ Subgroup.normalizer (D : Set X) →
    ∀ r : ℕ, Nat.Prime r →
      r ∣ Nat.card (Subgroup.closure (peterfalviKSet D t)) →
      r ∣ Nat.card {x : X // x ∈ peterfalviKSet D t}

/-- The coprimality conclusion of Peterfalvi `[II1; 4.3(a)]`. -/
@[expose] public def II1Lemma43aCoprime
    {X : Type u} [Group X] [Finite X] : Prop :=
  ∀ (D : Subgroup X) (t : X),
    Odd (Nat.card D) →
    IsInvolution t →
    rightConjugate D t = D →
    (∃ x : X, x ∈ peterfalviKSet D t ∧ x ≠ 1) →
    ∀ (p : ℕ), Nat.Prime p →
      ∀ (P : Subgroup X),
      IsPGroup p P →
      P ≠ ⊥ →
      P ≤ peterfalviV D t →
      PeterfalviSubgroupCentralizerTrivial D t P →
        Nat.Coprime p
        (Nat.card (Subgroup.closure (peterfalviKSet D t)))

/-- The cyclic consequence of `[II1; 4.3(b)]` in its genuine standing
odd-order setup. -/
@[expose] public def II1Lemma43bCyclic
    {X : Type u} [Group X] [Finite X] : Prop :=
  ∀ (D : Subgroup X) (t : X),
    Odd (Nat.card D) → IsInvolution t → rightConjugate D t = D →
    (∃ x : X, x ∈ peterfalviKSet D t ∧ x ≠ 1) →
    ∀ (p : ℕ), Nat.Prime p → ∀ (U : Subgroup X),
      IsPGroup p U → U ≤ peterfalviV D t →
      PeterfalviCentralizersTrivial D t U → IsCyclic U

/-- Source notation `C_I(Y) != 1`, where `I = I_D(t)`. -/
@[expose] public def HasNontrivialPeterfalviCentralizer
    {X : Type u} [Group X]
    (D : Subgroup X) (t : X) (Y : Subgroup X) : Prop :=
  ∃ k : X,
    k ∈ peterfalviKSet D t ∧
      k ∈ Subgroup.centralizer (Y : Set X) ∧ k ≠ 1

/-- The normal-complement conclusion of Peterfalvi `[II1; 4.3(c)]`. -/
public structure II1Lemma43cConclusion
    {X : Type u} [Group X]
    (D : Subgroup X) (t : X) : Prop where
  closure_le : Subgroup.closure (peterfalviKSet D t) ≤ D
  closure_eq_set :
    (Subgroup.closure (peterfalviKSet D t) : Set X) =
      peterfalviKSet D t
  normal :
    ((Subgroup.closure (peterfalviKSet D t)).subgroupOf D).Normal
  isComplement' :
    ((Subgroup.closure (peterfalviKSet D t)).subgroupOf D).IsComplement'
      ((peterfalviV D t).subgroupOf D)

/-- The genuine implication-shaped statement of Peterfalvi `[II1; 4.3(c)]`. -/
@[expose] public def II1Lemma43cNormalComplement
    {X : Type u} [Group X] [Finite X] : Prop :=
  ∀ (D : Subgroup X) (t : X),
    Odd (Nat.card D) →
      IsInvolution t →
      rightConjugate D t = D →
      (∃ k : X, k ∈ peterfalviKSet D t ∧ k ≠ 1) →
      (∀ Y : Subgroup X,
        Y ≤ peterfalviV D t →
          Y ≠ ⊥ →
          (Y.subgroupOf (peterfalviV D t)).Normal →
          ¬ HasNontrivialPeterfalviCentralizer D t Y) →
      II1Lemma43cConclusion D t

private theorem mem_normalizer_of_rightConjugate_eq_self
    {X : Type u} [Group X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t) (hD : rightConjugate D t = D) :
    t ∈ Subgroup.normalizer (D : Set X) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro d
  change d ∈ D ↔ rightConjugateElem d t ∈ D
  constructor
  · intro hd
    have hmem := rightConjugateElem_mem_rightConjugate
      (M := D) (g := t) hd
    simpa [hD] using hmem
  · intro hdt
    have hmem := rightConjugateElem_mem_rightConjugate
      (M := D) (g := t) hdt
    have hback : rightConjugateElem (rightConjugateElem d t) t ∈ D := by
      simpa [hD] using hmem
    simpa [rightConjugateElem_rightConjugateElem ht.inv_eq_self] using hback

private theorem eq_one_of_mem_odd_subgroup_of_sq_eq_one
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} (hDodd : Odd (Nat.card D))
    {x : X} (hxD : x ∈ D) (hx2 : x ^ 2 = 1) :
    x = 1 := by
  let xD : D := ⟨x, hxD⟩
  have hxD2 : xD ^ 2 = 1 := by
    apply Subtype.ext
    simpa [xD] using hx2
  have horderTwo : orderOf xD ∣ 2 := orderOf_dvd_of_pow_eq_one hxD2
  have horderCard : orderOf xD ∣ Nat.card D := orderOf_dvd_natCard xD
  have horderOne : orderOf xD = 1 :=
    Nat.eq_one_of_dvd_coprimes hDodd.coprime_two_right horderCard horderTwo
  have hxDone : xD = 1 := orderOf_eq_one_iff.mp horderOne
  simpa [xD] using congrArg Subtype.val hxDone

private theorem commutator_le_closure_peterfalviKSet
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X} (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    ⁅D, Subgroup.zpowers t⁆ ≤
      Subgroup.closure (peterfalviKSet D t) := by
  let A : Subgroup X := Subgroup.zpowers t
  have hA_norm_D : A ≤ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hDnorm
  letI : Subgroup.Normalizes A D := ⟨hA_norm_D⟩
  have horder : orderOf t = 2 :=
    (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    simp [A, Nat.card_zpowers, horder]
  let az : A := ⟨t, Subgroup.mem_zpowers t⟩
  have hazne : az ≠ 1 := by
    intro h
    exact ht.ne_one (congrArg Subtype.val h)
  have haCases (a : A) : a = 1 ∨ a = az := by
    by_cases ha : a = 1
    · exact Or.inl ha
    · right
      obtain ⟨other, hother, huniq⟩ :=
        (Nat.card_eq_two_iff' (1 : A)).mp hAcard
      exact (huniq a ha).trans (huniq az hazne).symm
  have hmap :
      (commutatorAction (A := A) (G := D)).map D.subtype =
        ⁅D, A⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator D A hA_norm_D
  have haction : ∀ x : D,
      x ∈ commutatorAction (A := A) (G := D) →
        (x : X) ∈ Subgroup.closure (peterfalviKSet D t) := by
    intro x hx
    rw [commutatorAction_eq_closure] at hx
    refine Subgroup.closure_induction
      (p := fun q : D => fun _hq =>
        (q : X) ∈ Subgroup.closure (peterfalviKSet D t))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, g, rfl⟩
      rcases haCases a with rfl | rfl
      · simp
      · apply Subgroup.subset_closure
        change ((g : X)⁻¹ * (az • g : D) : X) ∈
          peterfalviKSet D t
        change ((g : X)⁻¹ * (t * (g : X) * t⁻¹) : X) ∈
          peterfalviKSet D t
        constructor
        · exact D.mul_mem (D.inv_mem g.property)
            ((Subgroup.mem_normalizer_iff.mp hDnorm (g : X)).1 g.property)
        · change
            t⁻¹ * ((g : X)⁻¹ * (t * (g : X) * t⁻¹)) * t =
              ((g : X)⁻¹ * (t * (g : X) * t⁻¹))⁻¹
          simp [ht.inv_eq_self, mul_assoc, show t * t = 1 by
            simpa [pow_two] using ht.sq_eq_one]
    · exact Subgroup.one_mem _
    · intro a b _ha _hb ha hb
      exact (Subgroup.closure (peterfalviKSet D t)).mul_mem ha hb
    · intro a _ha ha
      exact (Subgroup.closure (peterfalviKSet D t)).inv_mem ha
  have hcomm_le : ⁅D, A⁆ ≤
      Subgroup.closure (peterfalviKSet D t) := by
    intro x hx
    rw [← hmap] at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact haction y hy
  simpa [A] using hcomm_le

/-- Source `(8B)`: the Peterfalvi anti-fixed set generates the action
commutator with the normalizing involution. -/
public theorem closure_peterfalviKSet_eq_commutator_zpowers
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X} (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hDodd : Odd (Nat.card D)) :
    Subgroup.closure (peterfalviKSet D t) =
      ⁅D, Subgroup.zpowers t⁆ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro k hk
    exact
      IsStronglyEmbedded.mem_commutator_zpowers_of_mem_peterfalviKSet
        D hDodd ht hk
  · exact commutator_le_closure_peterfalviKSet ht hDnorm

/-- The subgroup generated by the Peterfalvi anti-fixed set is normal in
the odd-order group normalized by the involution. -/
private theorem closure_peterfalviKSet_normal_subgroupOf
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t) (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    ((Subgroup.closure (peterfalviKSet D t)).subgroupOf D).Normal := by
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  have hKD : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  let Z : Set D :=
    {x : D | rightConjugateElem (x : X) t = (x : X)⁻¹}
  let L : Subgroup D := Subgroup.closure Z
  have himage : D.subtype '' Z = peterfalviKSet D t := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hmapL : L.map D.subtype = K := by
    simp only [L, K, MonoidHom.map_closure, himage]
  have hEq : K.subgroupOf D = L := by
    apply Subgroup.map_injective D.subtype_injective
    calc
      (K.subgroupOf D).map D.subtype = K := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKD]
      _ = L.map D.subtype := hmapL.symm
  rw [show Subgroup.closure (peterfalviKSet D t) = K by rfl, hEq]
  simpa [L, Z] using PFchapter1section1.lemma_b t D ht hDodd hDnorm

/-- The Peterfalvi anti-fixed set is invariant under conjugation by the fixed
subgroup `V = C_D(t)`. -/
public theorem peterfalviKSet_conj_mem_of_mem_V
    {X : Type u} [Group X]
    {D : Subgroup X} {t v k : X}
    (hv : v ∈ peterfalviV D t)
    (hk : k ∈ peterfalviKSet D t) :
    v * k * v⁻¹ ∈ peterfalviKSet D t := by
  refine ⟨D.mul_mem (D.mul_mem hv.1 hk.1) (D.inv_mem hv.1), ?_⟩
  have hvt : Commute v t := by
    change v ∈ D ∧ v ∈ Subgroup.centralizer ({t} : Set X) at hv
    rw [Subgroup.mem_centralizer_singleton_iff] at hv
    exact hv.2
  have htv_inv : t⁻¹ * v = v * t⁻¹ := hvt.symm.inv_left.eq
  have hv_inv_t : v⁻¹ * t = t * v⁻¹ := hvt.inv_left.eq
  calc
    rightConjugateElem (v * k * v⁻¹) t =
        t⁻¹ * (v * k * v⁻¹) * t := rfl
    _ = (t⁻¹ * v) * k * (v⁻¹ * t) := by simp [mul_assoc]
    _ = (v * t⁻¹) * k * (t * v⁻¹) := by rw [htv_inv, hv_inv_t]
    _ = v * (t⁻¹ * k * t) * v⁻¹ := by group
    _ = v * k⁻¹ * v⁻¹ := by
      simpa [rightConjugateElem, mul_assoc] using congrArg
        (fun z : X => v * z * v⁻¹) hk.2
    _ = (v * k * v⁻¹)⁻¹ := by group

/-- The relative index of `V = C_D(t)` is the cardinality of the anti-fixed
set. -/
public theorem peterfalviV_index_eq_kset_card
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    ((peterfalviV D t).subgroupOf D).index =
      Nat.card {x : X // x ∈ peterfalviKSet D t} := by
  have hcard := (PFchapter1section1.lemma_a t D ht hDodd hDnorm).2.2
  have hVD : peterfalviV D t ≤ D := inf_le_left
  have hpos : 0 < Nat.card (peterfalviV D t) := Nat.card_pos
  apply Nat.mul_left_cancel hpos
  calc
    Nat.card (peterfalviV D t) *
        ((peterfalviV D t).subgroupOf D).index =
        Nat.card D := by
      rw [← natCard_subgroupOf_eq (peterfalviV D t) D hVD]
      exact ((peterfalviV D t).subgroupOf D).card_mul_index
    _ = Nat.card (peterfalviV D t) *
        Nat.card {x : X // x ∈ peterfalviKSet D t} := by
      rw [show Nat.card {x : X // x ∈ peterfalviKSet D t} =
          (peterfalviKSet D t).ncard by rfl]
      simpa [peterfalviV, peterfalviKSet] using hcard

/-- Conjugation-orbit congruence on the Peterfalvi anti-fixed set. -/
public theorem peterfalviKSet_card_modEq_centralizer
    {X : Type u} [Group X] [Finite X]
    {D R : Subgroup X} {t : X} {r : ℕ}
    (hr : r.Prime) (hRp : IsPGroup r R)
    (hRV : R ≤ peterfalviV D t) :
    Nat.card {x : X // x ∈ peterfalviKSet D t} ≡
      Nat.card {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} [MOD r] := by
  classical
  letI : Fact r.Prime := ⟨hr⟩
  let I := {x : X // x ∈ peterfalviKSet D t}
  let conjI : R → I → I := fun a x =>
    ⟨(a : X) * (x : X) * (a : X)⁻¹,
      peterfalviKSet_conj_mem_of_mem_V (hRV a.property) x.property⟩
  letI : MulAction R I :=
    { smul := conjI
      one_smul := by
        intro x
        apply Subtype.ext
        change (1 : X) * (x : X) * (1 : X)⁻¹ = (x : X)
        simp
      mul_smul := by
        intro a b x
        apply Subtype.ext
        change ((a : X) * (b : X)) * (x : X) *
            ((a : X) * (b : X))⁻¹ =
          (a : X) * ((b : X) * (x : X) * (b : X)⁻¹) * (a : X)⁻¹
        group }
  let fixedEquiv : MulAction.fixedPoints R I ≃
      {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} :=
    { toFun := fun x => ⟨(x.1 : X), x.1.property, by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        let aR : R := ⟨a, ha⟩
        have hfix := MulAction.mem_fixedPoints.mp x.2 aR
        have hval := congrArg Subtype.val hfix
        change a * (x.1 : X) * a⁻¹ = (x.1 : X) at hval
        have hmul := congrArg (fun z : X => z * a) hval
        simpa [mul_assoc] using hmul⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        rw [MulAction.mem_fixedPoints]
        intro a
        apply Subtype.ext
        change (a : X) * x.1 * (a : X)⁻¹ = x.1
        have hcomm := Subgroup.mem_centralizer_iff.mp x.2.2
          (a : X) a.property
        calc
          (a : X) * x.1 * (a : X)⁻¹ = x.1 * (a : X) * (a : X)⁻¹ := by
            rw [hcomm]
          _ = x.1 := by simp⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  calc
    Nat.card {x : X // x ∈ peterfalviKSet D t} = Nat.card I := rfl
    _ ≡ Nat.card (MulAction.fixedPoints R I) [MOD r] :=
      hRp.card_modEq_card_fixedPoints I
    _ = Nat.card {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (R : Set X)} := Nat.card_congr fixedEquiv

/-- Peterfalvi `[II1; 4.2]`. -/
public theorem ii1Lemma42PrimeTransfer
    {X : Type u} [Group X] [Finite X] :
    II1Lemma42PrimeTransfer (X := X) := by
  classical
  intro D t hDodd ht hDnorm r hr hrK
  by_contra hrI
  let V : Subgroup X := peterfalviV D t
  let VD : Subgroup D := V.subgroupOf D
  have hindex : VD.index =
      Nat.card {x : X // x ∈ peterfalviKSet D t} := by
    simpa [V, VD] using
      peterfalviV_index_eq_kset_card ht hDodd hDnorm
  have hrIndex : ¬ r ∣ VD.index := by
    rwa [hindex]
  letI : Fact r.Prime := ⟨hr⟩
  let rp : Nat.Primes := ⟨r, hr⟩
  let S : Sylow r VD := default
  let R0 : Subgroup D := (S : Subgroup VD).map VD.subtype
  have hR0p : IsPGroup r R0 := S.isPGroup'.map VD.subtype
  have hR0index : R0.index = (S : Subgroup VD).index * VD.index := by
    simpa [R0] using
      (Subgroup.index_map_subtype (H := VD) (K := (S : Subgroup VD)))
  have hrR0index : ¬ r ∣ R0.index := by
    rw [hR0index]
    exact hr.not_dvd_mul S.not_dvd_index hrIndex
  let R : Sylow r D := hR0p.toSylow hrR0index
  have hR_eq : (R : Subgroup D) = R0 := by
    simpa [R] using IsPGroup.toSylow_coe hR0p hrR0index
  have hR_le_VD : (R : Subgroup D) ≤ VD := by
    rw [hR_eq]
    exact Subgroup.map_subtype_le (S : Subgroup VD)
  let A : Subgroup X := Subgroup.zpowers t
  have hA_norm_D : A ≤ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hDnorm
  letI : Subgroup.Normalizes A D := ⟨hA_norm_D⟩
  have hRfixed : (R : Subgroup D) ≤ fixedPointSubgroup A D := by
    rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
      D A hA_norm_D]
    intro x hxR
    have hxV : (x : X) ∈ V := hR_le_VD hxR
    refine ⟨x.property, ?_⟩
    change (x : X) ∈ Subgroup.centralizer (A : Set X)
    simpa [V, A, peterfalviV, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure] using hxV.2
  have hRpi : IsPiSubgroup (G := D) ({rp} : Set Nat.Primes)
      (R : Subgroup D) := by
    simpa [rp] using isPiSubgroup_singleton_of_isPGroup R.isPGroup'
  have hRhall : IsHallSubgroup ({rp} : Set Nat.Primes)
      (R : Subgroup D) := by
    refine isHallSubgroup_of (G := D) (π := ({rp} : Set Nat.Primes))
      (H := (R : Subgroup D)) hRpi ?_
    intro q hqmem hqindex
    have hqeq : q = rp := by simpa using hqmem
    subst q
    exact R.not_dvd_index (by simpa [rp] using hqindex)
  have horder : orderOf t = 2 :=
    (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    simpa [A] using (Nat.card_zpowers t).trans horder
  have hcop : Nat.Coprime (Nat.card A) (Nat.card D) := by
    rw [hAcard]
    exact hDodd.coprime_two_left
  have hsolvD : Group.IsSolvable D := odd_order_theorem D hDodd
  let pi : Set Nat.Primes := ({rp} : Set Nat.Primes)ᶜ
  have hRhallCompl : IsHallSubgroup {q | q ∉ pi}
      (R : Subgroup D) := by
    simpa [pi] using hRhall
  have hcommCore : commutatorAction (A := A) (G := D) ≤ piCore pi D :=
    commutatorAction_le_piCore_of_hall_complement_le_fixedPointSubgroup
      (G := D) (A := A) hsolvD hcop pi (R : Subgroup D)
      hRhallCompl hRfixed
  let C : Subgroup D := commutatorAction (A := A) (G := D)
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  have hmapC : C.map D.subtype = K := by
    calc
      C.map D.subtype = ⁅D, A⁆ := by
        simpa [C] using
          commutatorAction_subgroup_conj_map_eq_commutator D A hA_norm_D
      _ = K := by
        symm
        simpa [A, K] using
          closure_peterfalviKSet_eq_commutator_zpowers ht hDnorm hDodd
  have hcardKC : Nat.card K = Nat.card C := by
    rw [← hmapC, Subgroup.card_map_of_injective D.subtype_injective]
  have hrC : r ∣ Nat.card C := by
    rw [← hcardKC]
    simpa [K] using hrK
  have hrCore : r ∣ Nat.card (piCore pi D) :=
    hrC.trans (Subgroup.card_dvd_of_le hcommCore)
  have hrMem : rp ∈ pi :=
    (piCore_isPiSubgroup (G := D) pi) rp (by simpa [rp] using hrCore)
  simpa [pi] using hrMem

/-- Peterfalvi `[II1; 4.3(a)]`. -/
public theorem ii1Lemma43aCoprime
    {X : Type u} [Group X] [Finite X] :
    II1Lemma43aCoprime (X := X) := by
  classical
  intro D t hDodd ht hDinv _hIne p hp P hPp _hPne hPV hPfixed
  refine hp.coprime_iff_not_dvd.mpr ?_
  intro hpK
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) :=
    mem_normalizer_of_rightConjugate_eq_self ht hDinv
  have hOneI : (1 : X) ∈ peterfalviKSet D t := by
    simp [peterfalviKSet, rightConjugateElem]
  have hfixedCard :
      Nat.card {x : X // x ∈ peterfalviKSet D t ∧
        x ∈ Subgroup.centralizer (P : Set X)} = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨1, ⟨hOneI, by simp⟩⟩, ?_⟩
    intro x
    apply Subtype.ext
    exact hPfixed x.1 x.2.1 x.2.2
  have hmod := peterfalviKSet_card_modEq_centralizer
    (D := D) (R := P) hp hPp hPV
  rw [hfixedCard] at hmod
  have hpI : p ∣ Nat.card {x : X // x ∈ peterfalviKSet D t} :=
    ii1Lemma42PrimeTransfer D t hDodd ht hDnorm p hp hpK
  have hpOne : p ∣ 1 := (hmod.dvd_iff (dvd_refl p)).mp hpI
  exact hp.not_dvd_one hpOne

/-- Peterfalvi `[II1; 4.3(b)]`: a `p`-subgroup of the fixed subgroup which
acts fixed-point-freely on the anti-fixed set is cyclic. -/
public theorem ii1Lemma43bCyclic
    {X : Type u} [Group X] [Finite X] :
    II1Lemma43bCyclic (X := X) := by
  classical
  intro D t hDodd ht hDinv hIne p hp U hUp hUV hcentral
  by_contra hUcyclic
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (IsPGroup p U) := ⟨hUp⟩
  letI : Nontrivial U := Nontrivial.of_not_isCyclic hUcyclic
  obtain ⟨n, hn, hUcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := U) hUp).mp inferInstance
  have hpU : p ∣ Nat.card U := by
    rw [hUcard]
    exact dvd_pow_self p (Nat.ne_of_gt hn)
  have hUD : U ≤ D := hUV.trans inf_le_left
  have hpD : p ∣ Nat.card D :=
    hpU.trans (Subgroup.card_dvd_of_le hUD)
  have hpne2 : p ≠ 2 := Odd.ne_two_of_dvd_nat hDodd hpD
  obtain ⟨A0, _hA0normal, hA0card, hA0elem⟩ :=
    lemma_4_5_a (R := U) (p := p) hpne2 hUcyclic
  letI : IsElementaryAbelian p A0 := hA0elem
  let A : Subgroup X := A0.map U.subtype
  have hA_U : A ≤ U := by
    simpa [A] using Subgroup.map_subtype_le A0
  have hA_V : A ≤ peterfalviV D t := hA_U.trans hUV
  have hA_D : A ≤ D := hA_U.trans hUD
  have hAcard : Nat.card A = p ^ 2 := by
    calc
      Nat.card A = Nat.card A0 := by
        simpa [A] using
          Subgroup.card_map_of_injective
            (K := A0) (f := U.subtype) U.subtype_injective
      _ = p ^ 2 := hA0card
  have hAelem : IsElementaryAbelian p A := by
    simpa [A] using
      (IsElementaryAbelian.map_subtype (p := p) (K := U) (H := A0))
  letI : IsElementaryAbelian p A := hAelem
  letI : CommGroup A := IsMulCommutative.instCommGroup
  letI : Fact (IsPGroup p A) := ⟨IsElementaryAbelian.isPGroup p A⟩
  have hAnoncyclic : ¬ IsCyclic A :=
    IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hAcard
  have hAne : A ≠ ⊥ := by
    intro hAbot
    apply hAnoncyclic
    rw [hAbot]
    exact isCyclic_of_subsingleton (α := (⊥ : Subgroup X))
  have hAcentral : PeterfalviCentralizersTrivial D t A := by
    intro a haA ha1 x hxI hxa
    exact hcentral a (hA_U haA) ha1 x hxI hxa
  have hAcentralSubgroup :
      PeterfalviSubgroupCentralizerTrivial D t A :=
    hAcentral.subgroup hAne
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  have hKD : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) :=
    mem_normalizer_of_rightConjugate_eq_self ht hDinv
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using
      closure_peterfalviKSet_normal_subgroupOf ht hDodd hDnorm
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).mp hKnormalD
  have hAnormK : A ≤ Subgroup.normalizer (K : Set X) :=
    hA_D.trans hDnormK
  letI : Subgroup.Normalizes A K := ⟨hAnormK⟩
  letI : MulDistribMulAction A K :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A K hAnormK
  have hcopK : Nat.Coprime p (Nat.card K) := by
    simpa [K] using
      ii1Lemma43aCoprime D t hDodd ht hDinv hIne p hp A
        (IsElementaryAbelian.isPGroup p A) hAne hA_V hAcentralSubgroup
  have hfixTop :
      (⨆ (a : A) (_ : a ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers a)) K) = ⊤ := by
    exact proposition_1_16_a (G := K) (A := A) p hcopK hAnoncyclic
  have hfixedMapLe :
      ∀ (a : A) (ha : a ≠ 1),
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype ≤
          peterfalviV D t := by
    intro a ha
    have haX : (a : X) ≠ 1 := by
      intro ha1
      exact ha (Subtype.ext ha1)
    let C : Subgroup X := elementCentralizerIn D (a : X)
    have hCD : C ≤ D := inf_le_left
    have hCodd : Odd (Nat.card C) :=
      hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hCD)
    have htCentA : t ∈ Subgroup.centralizer ({(a : X)} : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      have haCt : (a : X) ∈ Subgroup.centralizer ({t} : Set X) :=
        (hA_V a.property).2
      exact Subgroup.mem_centralizer_singleton_iff.mp haCt
    have htNormCentA :
        t ∈ Subgroup.normalizer
          (Subgroup.centralizer ({(a : X)} : Set X) : Set X) :=
      Subgroup.le_normalizer htCentA
    have htNormC : t ∈ Subgroup.normalizer (C : Set X) := by
      simpa [C, elementCentralizerIn] using
        (Subgroup.inf_normalizer_le_normalizer_inf
          (G := X) (H := D)
          (K := Subgroup.centralizer ({(a : X)} : Set X))
          ⟨hDnorm, htNormCentA⟩)
    have hC_le_V : C ≤ peterfalviV D t := by
      intro x hxC
      obtain ⟨yz, _hyz, hyzEq⟩ :=
        (PFchapter1section1.lemma_a t C ht hCodd htNormC).1.surjOn hxC
      have hzI : (yz.2 : X) ∈ peterfalviKSet D t :=
        ⟨hCD yz.2.property.1, yz.2.property.2⟩
      have hzCentA :
          (yz.2 : X) ∈ Subgroup.centralizer ({(a : X)} : Set X) :=
        (show C ≤ Subgroup.centralizer ({(a : X)} : Set X) from inf_le_right)
          yz.2.property.1
      have hza : (yz.2 : X) * (a : X) = (a : X) * (yz.2 : X) :=
        Subgroup.mem_centralizer_singleton_iff.mp hzCentA
      have hzOne : (yz.2 : X) = 1 :=
        hcentral (a : X) (hA_U a.property) haX
          (yz.2 : X) hzI hza
      have hxEq : x = (yz.1 : X) := by
        change (yz.1 : X) * (yz.2 : X) = x at hyzEq
        simpa [hzOne] using hyzEq.symm
      change x ∈ D ∧ x ∈ Subgroup.centralizer ({t} : Set X)
      refine ⟨hCD hxC, ?_⟩
      rw [hxEq]
      exact yz.1.property.2
    have hfixEq :
        fixedPointSubgroup (↥(Subgroup.zpowers a)) K =
          (elementCentralizerIn K (a : X)).subgroupOf K := by
      simpa using
        fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
          K A hAnormK a
    have hfixMap :
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype =
          elementCentralizerIn K (a : X) := by
      calc
        (fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype =
            ((elementCentralizerIn K (a : X)).subgroupOf K).map K.subtype := by
              rw [hfixEq]
        _ = elementCentralizerIn K (a : X) ⊓ K := by
              rw [Subgroup.subgroupOf_map_subtype]
        _ = elementCentralizerIn K (a : X) := inf_eq_left.2 inf_le_left
    calc
      (fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype =
          elementCentralizerIn K (a : X) := hfixMap
      _ ≤ C := by
        intro x hx
        exact ⟨hKD hx.1, hx.2⟩
      _ ≤ peterfalviV D t := hC_le_V
  have htopMapK : (⊤ : Subgroup K).map K.subtype = K := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := K))
  have hKV : K ≤ peterfalviV D t := by
    calc
      K = (⊤ : Subgroup K).map K.subtype := htopMapK.symm
      _ =
          (⨆ (a : A) (_ : a ≠ 1),
            fixedPointSubgroup (↥(Subgroup.zpowers a)) K).map K.subtype := by
              simp [hfixTop]
      _ ≤ peterfalviV D t := by
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro a
        rw [Subgroup.map_iSup]
        refine iSup_le ?_
        intro ha
        exact hfixedMapLe a ha
  obtain ⟨x, hxI, hx1⟩ := hIne
  have hxV : x ∈ peterfalviV D t := hKV (Subgroup.subset_closure hxI)
  have hxFixed : rightConjugateElem x t = x := by
    have htx : t * x = x * t :=
      Subgroup.mem_centralizer_iff.mp hxV.2 t (Set.mem_singleton t)
    calc
      rightConjugateElem x t = t * x * t := by rw [rightConjugateElem, ht.inv_eq_self]
      _ = x * (t * t) := by rw [htx, mul_assoc]
      _ = x := by simp [show t * t = 1 by simpa [pow_two] using ht.sq_eq_one]
  have hxInv : x = x⁻¹ := hxFixed.symm.trans hxI.2
  have hx2 : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := congrArg (fun y : X => y * x) hxInv
      _ = 1 := by simp
  exact hx1 (eq_one_of_mem_odd_subgroup_of_sq_eq_one hDodd hxI.1 hx2)

/-- Peterfalvi `[II1; 4.3(c)]`: if every nontrivial normal subgroup of
`V = C_D(t)` has trivial centralizer in the anti-fixed set, then that set is
the abelian normal complement generated by itself. -/
public theorem ii1Lemma43cNormalComplement
    {X : Type u} [Group X] [Finite X] :
    II1Lemma43cNormalComplement (X := X) := by
  classical
  intro D t hDodd ht hDinv hIne hNoNormal
  let V : Subgroup X := peterfalviV D t
  let K : Subgroup X := Subgroup.closure (peterfalviKSet D t)
  have hVleD : V ≤ D := by
    simpa [V, peterfalviV] using
      (inf_le_left : peterfalviV D t ≤ D)
  have hKD : K ≤ D := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) :=
    mem_normalizer_of_rightConjugate_eq_self ht hDinv
  have hKnormalD : (K.subgroupOf D).Normal := by
    simpa [K] using
      closure_peterfalviKSet_normal_subgroupOf ht hDodd hDnorm
  have hDnormK : D ≤ Subgroup.normalizer (K : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKD).mp hKnormalD
  have hVnormK : V ≤ Subgroup.normalizer (K : Set X) :=
    hVleD.trans hDnormK
  let J : Subgroup X := K ⊓ V
  have hJleV : J ≤ V := inf_le_right
  have hVnormJ : V ≤ Subgroup.normalizer (J : Set X) := by
    intro v hv
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (G := X) (H := K) (K := V)
      ⟨hVnormK hv, V.le_normalizer hv⟩
  have hJnormalV : (J.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJleV).mpr hVnormJ
  have hJbot : J = ⊥ := by
    by_contra hJne
    have hJsub_ne : J.subgroupOf V ≠ ⊥ := by
      intro hbot
      apply hJne
      have hmap : (J.subgroupOf V).map V.subtype = J := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJleV]
      rw [← hmap, hbot]
      simp
    obtain ⟨N, hNnormal, hNleJ, hNne, hNmin⟩ :=
      exists_minimal_normal_le (G := V) (J.subgroupOf V)
        hJnormalV hJsub_ne
    let : N.Normal := hNnormal
    let : IsMinimalNormal N := {
      minimal := by
        intro L hLnormal hLN
        by_cases hLbot : L = ⊥
        · exact Or.inl hLbot
        · exact Or.inr (hNmin L hLnormal hLN hLbot)
    }
    have hVodd : Odd (Nat.card V) :=
      hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hVleD)
    have hVsolv : Group.IsSolvable V := odd_order_theorem V hVodd
    let : Group.IsSolvable V := hVsolv
    have hNsolv : Group.IsSolvable N := inferInstance
    let : Group.IsSolvable N := hNsolv
    obtain ⟨q, hq, hNelem⟩ :=
      minimalNormal_solvable_exists_isElementaryAbelian N
    let : Fact q.Prime := ⟨hq⟩
    let : IsElementaryAbelian q N := hNelem
    have hNp : IsPGroup q N :=
      IsElementaryAbelian.isPGroup q N
    have hNleCore : N ≤ pCore q V := by
      exact le_sSup ⟨hNnormal, hNp⟩
    have hcore_ne : pCore q V ≠ ⊥ := by
      intro hcore
      apply hNne
      rw [eq_bot_iff]
      intro n hn
      have hncore := hNleCore hn
      rw [hcore] at hncore
      simpa using hncore
    let O : Subgroup X := (pCore q V).map V.subtype
    have hOleV : O ≤ V := by
      simpa [O] using Subgroup.map_subtype_le (pCore q V)
    have hOne : O ≠ ⊥ := by
      intro hObot
      apply hcore_ne
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := pCore q V) (f := V.subtype) V.subtype_injective).mp
        (by simpa [O] using hObot)
    have hOnormalV : (O.subgroupOf V).Normal := by
      have hOsub : O.subgroupOf V = pCore q V := by
        simpa [O] using
          (subgroupOf_map_subtype_eq (K := V) (pCore q V))
      rw [hOsub]
      infer_instance
    have hOcentral :
        PeterfalviSubgroupCentralizerTrivial D t O := by
      intro x hxI hxC
      by_contra hx1
      exact (hNoNormal O (by simpa [V] using hOleV) hOne
        (by simpa [V] using hOnormalV)) ⟨x, hxI, hxC, hx1⟩
    have hOp : IsPGroup q O := by
      simpa [O] using
        (pCore_isPGroup (G := V) (p := q)).map V.subtype
    have hqN : q ∣ Nat.card N := by
      rcases hNp.card_eq_or_dvd with hcard | hdiv
      · exact (hNne (Subgroup.card_eq_one.mp hcard)).elim
      · exact hdiv
    have hNmap_le_K : N.map V.subtype ≤ K := by
      calc
        N.map V.subtype ≤ (J.subgroupOf V).map V.subtype :=
          Subgroup.map_mono hNleJ
        _ = J := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJleV]
        _ ≤ K := inf_le_left
    have hqK : q ∣ Nat.card K := by
      have hqNmap : q ∣ Nat.card (N.map V.subtype) := by
        rw [Subgroup.card_map_of_injective V.subtype_injective]
        exact hqN
      exact hqNmap.trans (Subgroup.card_dvd_of_le hNmap_le_K)
    have hcop : Nat.Coprime q (Nat.card K) := by
      simpa [K] using
        ii1Lemma43aCoprime D t hDodd ht hDinv hIne q hq O
          hOp hOne (by simpa [V] using hOleV) hOcentral
    exact (hq.coprime_iff_not_dvd.mp hcop) hqK
  have hright :
      Set.BijOn
        (fun p : V × {x : X // x ∈ peterfalviKSet D t} =>
          (p.2 : X) * (p.1 : X))
        Set.univ (D : Set X) := by
    change Set.BijOn
      (fun p : V × {x : X // x ∈ peterfalviKSet D t} =>
        (p.2 : X) * (p.1 : X)) Set.univ (D : Set X)
    exact (PFchapter1section1.lemma_a t D ht hDodd hDnorm).2.1
  have hcardD :
      Nat.card D = Nat.card V *
        Nat.card {x : X // x ∈ peterfalviKSet D t} := by
    rw [show Nat.card {x : X // x ∈ peterfalviKSet D t} =
        (peterfalviKSet D t).ncard by rfl]
    simpa [V, peterfalviV, peterfalviKSet] using
      (PFchapter1section1.lemma_a t D ht hDodd hDnorm).2.2
  have hKset : (K : Set X) = peterfalviKSet D t := by
    ext x
    constructor
    · intro hxK
      obtain ⟨p, _hp, hp⟩ := hright.surjOn (hKD hxK)
      have hiK : (p.2 : X) ∈ K :=
        Subgroup.subset_closure p.2.property
      have hp' : (p.2 : X) * (p.1 : X) = x := hp
      have hprodK : (p.2 : X) * (p.1 : X) ∈ K := by
        rw [hp']
        exact hxK
      have hvK : (p.1 : X) ∈ K := by
        have hmul := K.mul_mem (K.inv_mem hiK) hprodK
        simpa [mul_assoc] using hmul
      have hvJ : (p.1 : X) ∈ J := ⟨hvK, p.1.property⟩
      have hv1 : (p.1 : X) = 1 := by
        rw [hJbot] at hvJ
        simpa using hvJ
      rw [← hp']
      simpa [hv1] using p.2.property
    · intro hx
      exact Subgroup.subset_closure hx
  have hdisj :
      Disjoint (K.subgroupOf D) (V.subgroupOf D) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxV
    apply Subtype.ext
    have hxJ : (x : X) ∈ J := ⟨hxK, hxV⟩
    rw [hJbot] at hxJ
    simpa using hxJ
  have hcardK :
      Nat.card K = Nat.card {x : X // x ∈ peterfalviKSet D t} :=
    Nat.card_congr (Set.equivOfEq hKset)
  have hcardComp :
      Nat.card (K.subgroupOf D) * Nat.card (V.subgroupOf D) =
        Nat.card D := by
    calc
      Nat.card (K.subgroupOf D) * Nat.card (V.subgroupOf D) =
          Nat.card K * Nat.card V := by
            rw [natCard_subgroupOf_eq K D hKD,
              natCard_subgroupOf_eq V D hVleD]
      _ = Nat.card {x : X // x ∈ peterfalviKSet D t} *
          Nat.card V := by rw [hcardK]
      _ = Nat.card V *
          Nat.card {x : X // x ∈ peterfalviKSet D t} :=
        Nat.mul_comm _ _
      _ = Nat.card D := hcardD.symm
  refine {
    closure_le := hKD
    closure_eq_set := by simpa [K] using hKset
    normal := by simpa [K] using hKnormalD
    isComplement' := by
      simpa [K, V] using
        Subgroup.isComplement'_of_card_mul_and_disjoint hcardComp hdisj
  }

end CFSG.BenderSuzuki
