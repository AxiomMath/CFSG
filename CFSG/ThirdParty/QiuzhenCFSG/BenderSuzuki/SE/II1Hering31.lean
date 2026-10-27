module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma98
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Permutation
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStabilityReduction
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.theorem
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Hering31Finite
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Hering31Abelian
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.corollary_9_2
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

namespace CFSG
end CFSG
open CFSG

/-!
# Hering's theorem `[II1; 3.1]`

This file proves the earlier-volume theorem that a finite group acting doubly
transitively by conjugation on its involutions has `2`-rank one.  The first
layer below packages the elementary opening of Hering's minimal-counterexample
argument: a four-subgroup makes all involutions commute, and the identity
together with the involutions is then a normal elementary abelian subgroup.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u v

/-- The conjugation permutation domain in Hering's theorem. -/
public abbrev II1Hering31Involutions (X : Type u) [Group X] :=
  {x : X // IsInvolution x}

/-- Left conjugation on the involutions.  The source and the ambient callback
use right conjugation; replacing an actor by its inverse identifies the two
actions. -/
@[reducible, expose] public def ii1Hering31ConjugationAction
    (X : Type u) [Group X] : MulAction X (II1Hering31Involutions X) where
  smul g x :=
    ⟨g * (x : X) * g⁻¹, by
      simpa [rightConjugateElem] using
        isInvolution_rightConjugateElem (x := (x : X)) (g := g⁻¹) x.property⟩
  one_smul x := by
    apply Subtype.ext
    change 1 * (x : X) * (1 : X)⁻¹ = (x : X)
    simp
  mul_smul g h x := by
    apply Subtype.ext
    change (g * h) * (x : X) * (g * h)⁻¹ =
      g * (h * (x : X) * h⁻¹) * g⁻¹
    simp [mul_assoc]

/-- Ambient right-conjugation double transitivity is the standard
two-pretransitivity of the conjugation action on the involution subtype. -/
public theorem ii1Hering31ConjugationAction_twoPretransitive
    {X : Type u} [Group X]
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X))) :
    letI : MulAction X (II1Hering31Involutions X) :=
      ii1Hering31ConjugationAction X
    MulAction.IsMultiplyPretransitive X (II1Hering31Involutions X) 2 := by
  letI : MulAction X (II1Hering31Involutions X) :=
    ii1Hering31ConjugationAction X
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g, hag, hbg⟩ := htwo
    ⟨Subgroup.mem_top _, a.property⟩
    ⟨Subgroup.mem_top _, b.property⟩
    ⟨Subgroup.mem_top _, c.property⟩
    ⟨Subgroup.mem_top _, d.property⟩
    (fun h => hab (Subtype.ext h))
    (fun h => hcd (Subtype.ext h))
  refine ⟨(g : X)⁻¹, ?_, ?_⟩
  · apply Subtype.ext
    change (g : X)⁻¹ * (a : X) * ((g : X)⁻¹)⁻¹ = (c : X)
    simpa [rightConjugateElem] using hag
  · apply Subtype.ext
    change (g : X)⁻¹ * (b : X) * ((g : X)⁻¹)⁻¹ = (d : X)
    simpa [rightConjugateElem] using hbg

/-- Restrict the ambient subgroup formulation to the abstract group carried by
the subgroup. -/
public theorem ii1Hering31Conjugation_top_of_subgroup
    {G : Type u} [Group G] {H : Subgroup G}
    (htwo : ConjugationTwoTransitiveOn H (involutionsInSet H)) :
    ConjugationTwoTransitiveOn (⊤ : Subgroup H)
      (involutionsInSet (⊤ : Subgroup H)) := by
  intro a b c d ha hb hc hd hab hcd
  have haG : IsInvolution (a : G) :=
    IsInvolution.map_of_injective ha.2 H.subtype H.subtype_injective
  have hbG : IsInvolution (b : G) :=
    IsInvolution.map_of_injective hb.2 H.subtype H.subtype_injective
  have hcG : IsInvolution (c : G) :=
    IsInvolution.map_of_injective hc.2 H.subtype H.subtype_injective
  have hdG : IsInvolution (d : G) :=
    IsInvolution.map_of_injective hd.2 H.subtype H.subtype_injective
  obtain ⟨g, hag, hbg⟩ := htwo
    ⟨a.property, haG⟩ ⟨b.property, hbG⟩
    ⟨c.property, hcG⟩ ⟨d.property, hdG⟩
    (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
  let gTop : (⊤ : Subgroup H) := ⟨g, Subgroup.mem_top _⟩
  refine ⟨gTop, ?_, ?_⟩
  · apply Subtype.ext
    exact hag
  · apply Subtype.ext
    exact hbg

/-- Double transitivity by conjugation descends through a normal odd-order
kernel.  Every quotient involution has an involution lift, and the quotient
map transports the two simultaneous conjugation equations. -/
public theorem ii1Hering31Conjugation_quotient_of_odd_kernel
    {X : Type u} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] (hNodd : Odd (Nat.card N))
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X))) :
    ConjugationTwoTransitiveOn (⊤ : Subgroup (X ⧸ N))
      (involutionsInSet (⊤ : Subgroup (X ⧸ N))) := by
  intro a b c d ha hb hc hd hab hcd
  obtain ⟨a0, ha0, ha0q⟩ :=
    exists_involution_lift_of_odd_kernel N hNodd ha.2
  obtain ⟨b0, hb0, hb0q⟩ :=
    exists_involution_lift_of_odd_kernel N hNodd hb.2
  obtain ⟨c0, hc0, hc0q⟩ :=
    exists_involution_lift_of_odd_kernel N hNodd hc.2
  obtain ⟨d0, hd0, hd0q⟩ :=
    exists_involution_lift_of_odd_kernel N hNodd hd.2
  have hab0 : a0 ≠ b0 := by
    intro h
    apply hab
    rw [← ha0q, ← hb0q, h]
  have hcd0 : c0 ≠ d0 := by
    intro h
    apply hcd
    rw [← hc0q, ← hd0q, h]
  obtain ⟨g, hag, hbg⟩ := htwo
    ⟨Subgroup.mem_top _, ha0⟩ ⟨Subgroup.mem_top _, hb0⟩
    ⟨Subgroup.mem_top _, hc0⟩ ⟨Subgroup.mem_top _, hd0⟩
    hab0 hcd0
  let q : X →* X ⧸ N := QuotientGroup.mk' N
  let gq : (⊤ : Subgroup (X ⧸ N)) :=
    ⟨q (g : X), Subgroup.mem_top _⟩
  refine ⟨gq, ?_, ?_⟩
  · rw [← ha0q, ← hc0q]
    simpa [q, gq, rightConjugateElem] using congrArg q hag
  · rw [← hb0q, ← hd0q]
    simpa [q, gq, rightConjugateElem] using congrArg q hbg

private theorem exists_two_distinct_nontrivial_of_card_four
    {A : Type*} [Group A] [Finite A] (hcard : Nat.card A = 4) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hcardF : Fintype.card A = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have htwo_lt : 2 < Fintype.card A := by omega
  rcases Fintype.two_lt_card_iff.mp htwo_lt with
    ⟨a, b, c, hab, hac, hbc⟩
  by_cases ha : a = 1
  · by_cases hb : b = 1
    · exact False.elim (hab (ha.trans hb.symm))
    · by_cases hc : c = 1
      · exact False.elim (hac (ha.trans hc.symm))
      · exact ⟨b, c, hb, hc, hbc⟩
  · by_cases hb : b = 1
    · by_cases hc : c = 1
      · exact False.elim (hbc (hb.trans hc.symm))
      · exact ⟨a, c, ha, hc, hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

/-- Two distinct nonidentity elements of an exponent-two group of cardinality
four generate the whole group. -/
private theorem ii1Hering31_generate_four
    {A : Type*} [Group A] [Finite A]
    (hcard : Nat.card A = 4)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (_ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    Subgroup.closure ({a, b} : Set A) = ⊤ := by
  classical
  let S : Subgroup A := Subgroup.closure ({a, b} : Set A)
  have haS : a ∈ S := Subgroup.subset_closure (Set.mem_insert a {b})
  have hbS : b ∈ S :=
    Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b))
  let f : Fin 4 → S := ![
    (1 : S), ⟨a, haS⟩, ⟨b, hbS⟩, ⟨a * b, S.mul_mem haS hbS⟩]
  have hbInv : b⁻¹ = b :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb2)
  have habOne : a * b ≠ 1 := by
    intro h
    apply hab
    exact (mul_eq_one_iff_eq_inv.mp h).trans hbInv
  have habA : a * b ≠ a := by
    intro h
    apply hb
    have h' : a * b = a * 1 := by simpa using h
    exact mul_left_cancel h'
  have habB : a * b ≠ b := by
    intro h
    apply ha
    have h' : a * b = 1 * b := by simpa using h
    exact mul_right_cancel h'
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, Subtype.ext_iff, ha, hb, hab, habOne, habA, habB,
        Ne.symm ha, Ne.symm hb, Ne.symm hab, Ne.symm habOne,
        Ne.symm habA, Ne.symm habB] at hij ⊢
  have hge : 4 ≤ Nat.card S := by
    simpa using Nat.card_le_card_of_injective f hf
  have hle : Nat.card S ≤ Nat.card A :=
    Nat.card_le_card_of_injective S.subtype S.subtype_injective
  have hScard : Nat.card S = Nat.card A := by omega
  exact Subgroup.eq_top_of_card_eq S hScard

/-- A generating ordered pair of a four-subgroup has pointwise stabilizer
equal to the centralizer of the whole four-subgroup. -/
private theorem ii1Hering31_pair_stabilizer
    {X : Type*} [Group X] [Finite X]
    (V : Subgroup X) (hcard : Nat.card V = 4)
    (a b : V) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    letI : MulAction X (II1Hering31Involutions X) :=
      ii1Hering31ConjugationAction X
    ∃ pair : Fin 2 ↪ II1Hering31Involutions X,
      MulAction.stabilizer X pair = Subgroup.centralizer (V : Set X) := by
  classical
  letI : MulAction X (II1Hering31Involutions X) :=
    ii1Hering31ConjugationAction X
  have haInvV : IsInvolution a := ⟨ha, ha2⟩
  have hbInvV : IsInvolution b := ⟨hb, hb2⟩
  have haInv : IsInvolution (a : X) :=
    IsInvolution.map_of_injective haInvV V.subtype V.subtype_injective
  have hbInv : IsInvolution (b : X) :=
    IsInvolution.map_of_injective hbInvV V.subtype V.subtype_injective
  let aI : II1Hering31Involutions X := ⟨a, haInv⟩
  let bI : II1Hering31Involutions X := ⟨b, hbInv⟩
  let pair : Fin 2 ↪ II1Hering31Involutions X :=
    { toFun := ![aI, bI]
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact False.elim (hab (Subtype.ext (by
            simpa [aI, bI] using congrArg Subtype.val hij)))
        · exact False.elim (hab (Subtype.ext (by
            simpa [aI, bI] using congrArg Subtype.val hij.symm)))
        · rfl }
  refine ⟨pair, ?_⟩
  have hgenV : Subgroup.closure ({a, b} : Set V) = ⊤ :=
    ii1Hering31_generate_four hcard a b ha hb hab ha2 hb2
  have hVclosure : V = Subgroup.closure ({(a : X), (b : X)} : Set X) := by
    calc
      V = (⊤ : Subgroup V).map V.subtype := by ext; simp
      _ = (Subgroup.closure ({a, b} : Set V)).map V.subtype := by rw [hgenV]
      _ = Subgroup.closure (V.subtype '' ({a, b} : Set V)) :=
        MonoidHom.map_closure V.subtype _
      _ = Subgroup.closure ({(a : X), (b : X)} : Set X) := by
        congr 1
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rcases hy with hy | hy
          · left
            exact congrArg Subtype.val hy
          · right
            exact congrArg Subtype.val hy
        · intro hx
          rcases hx with rfl | rfl
          · exact ⟨a, Set.mem_insert _ _, rfl⟩
          · exact ⟨b, Set.mem_insert_of_mem _ (Set.mem_singleton _), rfl⟩
  rw [hVclosure, Subgroup.centralizer_closure]
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have hfix := congrArg
        (fun f : Fin 2 ↪ II1Hering31Involutions X => f 0) hg
      have hfixX : g * (a : X) * g⁻¹ = (a : X) :=
        congrArg Subtype.val hfix
      calc
        (a : X) * g = (g * (a : X) * g⁻¹) * g := by rw [hfixX]
        _ = g * (a : X) := by simp [mul_assoc]
    · have hfix := congrArg
        (fun f : Fin 2 ↪ II1Hering31Involutions X => f 1) hg
      have hfixX : g * (b : X) * g⁻¹ = (b : X) :=
        congrArg Subtype.val hfix
      calc
        (b : X) * g = (g * (b : X) * g⁻¹) * g := by rw [hfixX]
        _ = g * (b : X) := by simp [mul_assoc]
  · intro hg
    apply Function.Embedding.ext
    intro i
    fin_cases i
    · apply Subtype.ext
      change g * (a : X) * g⁻¹ = (a : X)
      have hcomm := hg (a : X) (Set.mem_insert _ _)
      calc
        g * (a : X) * g⁻¹ = (a : X) * g * g⁻¹ := by rw [hcomm]
        _ = (a : X) := by simp
    · apply Subtype.ext
      change g * (b : X) * g⁻¹ = (b : X)
      have hcomm := hg (b : X)
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      calc
        g * (b : X) * g⁻¹ = (b : X) * g * g⁻¹ := by rw [hcomm]
        _ = (b : X) := by simp

private theorem commute_of_square_one
    {A : Type*} [Group A]
    (hsq : ∀ x : A, x ^ 2 = 1) (a b : A) : Commute a b := by
  have haInv : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq a)
  have hbInv : b⁻¹ = b :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq b)
  have habInv : (a * b)⁻¹ = a * b :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq (a * b))
  rw [mul_inv_rev, haInv, hbInv] at habInv
  exact habInv.symm

/-- The elementary opening of Hering's proof: once a four-subgroup exists,
double transitivity transports a commuting ordered pair from that subgroup to
every ordered pair of distinct involutions. -/
public theorem ii1Hering31_involutions_commute
    {X : Type u} [Group X] [Finite X]
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X) :
    ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y := by
  classical
  obtain ⟨E, hEcard, hEsq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hrank
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_two_distinct_nontrivial_of_card_four hEcard
  have haInv : IsInvolution (a : X) := by
    refine ⟨?_, ?_⟩
    · intro haOne
      exact ha (Subtype.ext haOne)
    · exact congrArg E.subtype (hEsq a)
  have hbInv : IsInvolution (b : X) := by
    refine ⟨?_, ?_⟩
    · intro hbOne
      exact hb (Subtype.ext hbOne)
    · exact congrArg E.subtype (hEsq b)
  have habX : (a : X) ≠ (b : X) := fun h => hab (Subtype.ext h)
  have habComm : Commute (a : X) (b : X) := by
    change (a : X) * (b : X) = (b : X) * (a : X)
    exact congrArg E.subtype (commute_of_square_one hEsq a b).eq
  intro x y hx hy
  by_cases hxy : x = y
  · subst y
    exact Commute.refl x
  · obtain ⟨g, hag, hbg⟩ := htwo
      (a := (a : X)) (b := (b : X)) (c := x) (d := y)
      ⟨Subgroup.mem_top _, haInv⟩ ⟨Subgroup.mem_top _, hbInv⟩
      ⟨Subgroup.mem_top _, hx⟩ ⟨Subgroup.mem_top _, hy⟩ habX hxy
    rw [← hag, ← hbg]
    change Commute (g⁻¹ * (a : X) * g) (g⁻¹ * (b : X) * g)
    let phi : X →* X := (MulAut.conj (G := X) g⁻¹).toMonoidHom
    simpa [phi, MulAut.conj_apply] using habComm.map phi

/-- The identity together with all involutions, under the hypothesis that all
involutions commute. -/
@[expose] public def ii1Hering31InvolutionSubgroup
    (X : Type u) [Group X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    Subgroup X where
  carrier := {x : X | x = 1 ∨ IsInvolution x}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | hx
    · simpa using hy
    rcases hy with rfl | hy
    · simpa using Or.inr hx
    by_cases hxy : x = y
    · left
      subst y
      simpa [pow_two] using hx.sq_eq_one
    · right
      refine ⟨?_, ?_⟩
      · intro hmul
        have hxeq : x = y⁻¹ := (mul_eq_one_iff_eq_inv).mp hmul
        exact hxy (hxeq.trans hy.inv_eq_self)
      · calc
          (x * y) ^ 2 = x * (y * x) * y := by simp [pow_two, mul_assoc]
          _ = x * (x * y) * y := by rw [(hcomm hx hy).eq.symm]
          _ = (x ^ 2) * (y ^ 2) := by simp [pow_two, mul_assoc]
          _ = 1 := by rw [hx.sq_eq_one, hy.sq_eq_one, one_mul]
  inv_mem' := by
    intro x hx
    rcases hx with rfl | hx
    · exact Or.inl (inv_one)
    · simpa [hx.inv_eq_self] using Or.inr hx

/-- The Hering involution subgroup is normal, since conjugation preserves the
identity and the property of being an involution. -/
public theorem ii1Hering31InvolutionSubgroup_normal
    {X : Type u} [Group X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    (ii1Hering31InvolutionSubgroup X hcomm).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rcases hn with rfl | hn
  · exact Or.inl (by simp)
  · exact Or.inr (by
      simpa [rightConjugateElem] using
        isInvolution_rightConjugateElem (x := n) (g := g⁻¹) hn)

/-- The nonidentity elements of the Hering involution subgroup are exactly
the involutions of the ambient group. -/
public theorem ii1Hering31InvolutionSubgroup_ne_one_iff
    {X : Type u} [Group X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (x : ii1Hering31InvolutionSubgroup X hcomm) :
    x ≠ 1 ↔ IsInvolution (x : X) := by
  constructor
  · intro hx
    rcases x.property with hxOne | hxInv
    · exact False.elim (hx (Subtype.ext hxOne))
    · exact hxInv
  · intro hxInv hxOne
    exact hxInv.ne_one (congrArg Subtype.val hxOne)

/-- Every element of the Hering involution subgroup has square one. -/
public theorem ii1Hering31InvolutionSubgroup_sq_eq_one
    {X : Type u} [Group X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (x : ii1Hering31InvolutionSubgroup X hcomm) :
    x ^ 2 = 1 := by
  apply Subtype.ext
  rcases x.property with hx | hx
  · simp [hx]
  · exact hx.sq_eq_one

/-- The Hering involution subgroup is elementary abelian. -/
public theorem ii1Hering31InvolutionSubgroup_commute
    {X : Type u} [Group X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (x y : ii1Hering31InvolutionSubgroup X hcomm) : Commute x y := by
  exact commute_of_square_one
    (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm) x y

/-- A rank-two elementary abelian subgroup embeds in the Hering involution
subgroup.  In particular that subgroup has at least four elements. -/
public theorem ii1Hering31InvolutionSubgroup_card_ge_four
    {X : Type u} [Group X] [Finite X]
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    4 ≤ Nat.card (ii1Hering31InvolutionSubgroup X hcomm) := by
  obtain ⟨E, hEcard, hEsq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hrank
  have hEN : E ≤ ii1Hering31InvolutionSubgroup X hcomm := by
    intro x hx
    by_cases hxOne : x = 1
    · exact Or.inl hxOne
    · exact Or.inr ⟨hxOne, by
        let xE : E := ⟨x, hx⟩
        simpa [xE] using congrArg Subtype.val (hEsq xE)⟩
  rw [← hEcard]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hEN)

/-- Any specified rank-two elementary abelian subgroup lies in the Hering
involution subgroup. -/
public theorem ii1Hering31_rankTwo_le_involutionSubgroup
    {X : Type u} [Group X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (E : Subgroup X) (hEsq : ∀ x : E, x ^ 2 = 1) :
    E ≤ ii1Hering31InvolutionSubgroup X hcomm := by
  intro x hx
  by_cases hxOne : x = 1
  · exact Or.inl hxOne
  · exact Or.inr ⟨hxOne, by
      let xE : E := ⟨x, hx⟩
      simpa [xE] using congrArg Subtype.val (hEsq xE)⟩

/-- The kernel of conjugation on the involution subtype is the centralizer of
the identity together with the involutions. -/
public theorem ii1Hering31_pointStabilizerCore_eq_centralizer
    {X : Type u} [Group X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    letI : MulAction X (II1Hering31Involutions X) :=
      ii1Hering31ConjugationAction X
    pointStabilizerCore X (II1Hering31Involutions X) =
      Subgroup.centralizer
        (ii1Hering31InvolutionSubgroup X hcomm : Set X) := by
  letI : MulAction X (II1Hering31Involutions X) :=
    ii1Hering31ConjugationAction X
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with rfl | hx
    · simp
    · let xI : II1Hering31Involutions X := ⟨x, hx⟩
      have hgStab : g ∈ MulAction.stabilizer X xI := by
        rw [pointStabilizerCore] at hg
        exact Subgroup.mem_iInf.mp hg xI
      have hfix : g * x * g⁻¹ = x := by
        exact congrArg Subtype.val
          (MulAction.mem_stabilizer_iff.mp hgStab)
      have hgx : g * x = x * g := by
        calc
          g * x = (g * x * g⁻¹) * g := by simp [mul_assoc]
          _ = x * g := by rw [hfix]
      exact hgx.symm
  · intro hg
    change g ∈ ⨅ z : II1Hering31Involutions X,
      MulAction.stabilizer X z
    rw [Subgroup.mem_iInf]
    intro z
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g * (z : X) * g⁻¹ = (z : X)
    have hzg : (z : X) * g = g * (z : X) :=
      (Subgroup.mem_centralizer_iff.mp hg) (z : X) (Or.inr z.property)
    calc
      g * (z : X) * g⁻¹ = (z : X) * g * g⁻¹ := by rw [hzg]
      _ = (z : X) := by simp

/-- Baer--Suzuki puts every involution into the normal `2`-core once all
involutions commute. -/
public theorem ii1Hering31_involutions_le_twoCore
    {X : Type u} [Group X] [Finite X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    ∀ x : X, IsInvolution x → x ∈ pCore 2 X := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hxP : IsPElement (p := 2) x := by
    refine ⟨1, ?_⟩
    simpa using (orderOf_eq_prime hx.sq_eq_one hx.ne_one)
  refine gorenstein_3_8_2_conjugacy_class_le_pCore hxP ?_ x ?_
  · intro y hy
    rcases hy with ⟨g, rfl⟩
    have hyInv : IsInvolution (g * x * g⁻¹) := by
      simpa [rightConjugateElem] using
        isInvolution_rightConjugateElem (x := x) (g := g⁻¹) hx
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    have hclosure : Subgroup.closure ({x, g * x * g⁻¹} : Set X) ≤ N := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Or.inr hx
      · exact Or.inr hyInv
    intro z
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val
      (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm
        ⟨(z : X), hclosure z.property⟩)
  · exact ⟨1, by simp⟩

/-- The identity and every involution lie in the normal `2`-core. -/
public theorem ii1Hering31InvolutionSubgroup_le_twoCore
    {X : Type u} [Group X] [Finite X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    ii1Hering31InvolutionSubgroup X hcomm ≤ pCore 2 X := by
  intro x hx
  rcases hx with rfl | hx
  · exact (pCore 2 X).one_mem
  · exact ii1Hering31_involutions_le_twoCore hcomm x hx

/-- In Hering's counterexample setup, the normal `2`-core centralizes the
elementary abelian involution subgroup.  A central involution of the `2`-core
exists by the center theorem for finite `p`-groups; transitivity and normality
of the image of that center then put every involution in it. -/
public theorem ii1Hering31_twoCore_le_centralizer
    {X : Type u} [Group X] [Finite X]
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    pCore 2 X ≤ Subgroup.centralizer
      (ii1Hering31InvolutionSubgroup X hcomm : Set X) := by
  classical
  let Q : Subgroup X := pCore 2 X
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  have hNcard : 4 ≤ Nat.card N :=
    ii1Hering31InvolutionSubgroup_card_ge_four hrank hcomm
  have hNne : N ≠ ⊥ := by
    intro hNbot
    have hcard : Nat.card N = 1 := by simp [hNbot]
    omega
  have hNQ : N ≤ Q := by
    simpa [N, Q] using ii1Hering31InvolutionSubgroup_le_twoCore hcomm
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    apply hNne
    rw [eq_bot_iff]
    simpa [hQbot] using hNQ
  letI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
  have hQ2 : IsPGroup 2 Q := by
    simpa [Q] using pCore_isPGroup (G := X) (p := 2)
  have hcenter_nontrivial : Nontrivial (Subgroup.center Q) :=
    hQ2.center_nontrivial
  have hcenter2 : IsPGroup 2 (Subgroup.center Q) :=
    hQ2.to_subgroup (Subgroup.center Q)
  have htwo_center : 2 ∣ Nat.card (Subgroup.center Q) := by
    rcases (IsPGroup.nontrivial_iff_card
      (p := 2) (G := Subgroup.center Q) hcenter2).mp
        hcenter_nontrivial with ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨zC, hzOrder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := Subgroup.center Q) 2 htwo_center
  let zQ : Q := (zC : Q)
  have hzQOrder : orderOf zQ = 2 := by
    simpa [zQ] using (Subgroup.orderOf_coe zC).trans hzOrder
  have hzQData := orderOf_eq_prime_iff.mp hzQOrder
  have hzQ : IsInvolution zQ := ⟨hzQData.2, hzQData.1⟩
  let z : X := (zQ : X)
  have hz : IsInvolution z :=
    IsInvolution.map_of_injective hzQ Q.subtype Q.subtype_injective
  let Z : Subgroup X := (Subgroup.center Q).map Q.subtype
  letI : (Subgroup.center Q).Characteristic := Subgroup.centerCharacteristic
  have hZnormal : Z.Normal := by
    dsimp [Z]
    exact ConjAct.normal_of_characteristic_of_normal
  have hzZ : z ∈ Z := by
    exact Subgroup.mem_map_of_mem Q.subtype zC.property
  letI : MulAction X (II1Hering31Involutions X) :=
    ii1Hering31ConjugationAction X
  haveI : MulAction.IsMultiplyPretransitive X
      (II1Hering31Involutions X) 2 :=
    ii1Hering31ConjugationAction_twoPretransitive htwo
  haveI : MulAction.IsPretransitive X (II1Hering31Involutions X) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hNZ : N ≤ Z := by
    intro n hn
    rcases hn with rfl | hn
    · exact Z.one_mem
    · let zI : II1Hering31Involutions X := ⟨z, hz⟩
      let nI : II1Hering31Involutions X := ⟨n, hn⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X zI nI
      have hconj : g * z * g⁻¹ = n := congrArg Subtype.val hg
      rw [← hconj]
      exact hZnormal.conj_mem z hzZ g
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hnZ : n ∈ Z := hNZ hn
  rcases hnZ with ⟨zC, hzC, rfl⟩
  rcases hq with hq
  have hcommQ : (zC : Q) * ⟨q, hq⟩ = ⟨q, hq⟩ * (zC : Q) :=
    (Subgroup.mem_center_iff.mp hzC ⟨q, hq⟩).symm
  have hcommX := congrArg Subtype.val hcommQ
  exact hcommX

/-- Witt's fixed-point action becomes conjugation double transitivity on the
whole normalizer.  Every normalizing involution belongs to the elementary
abelian involution subgroup `N`; its commutators with the odd subgroup `P`
belong to both `N` and `P`, hence vanish. -/
private theorem ii1Hering31_normalizer_conjugation
    {X : Type*} [Group X] [Finite X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (P : Subgroup X) (hPq : IsPGroup q P)
    (htwoF :
      letI : MulAction X (II1Hering31Involutions X) :=
        ii1Hering31ConjugationAction X
      IsTwoTransitiveOn (Subgroup.normalizer (P : Set X))
        (fixedPointsOfSubgroup X (II1Hering31Involutions X) P)) :
    ConjugationTwoTransitiveOn
      (⊤ : Subgroup (Subgroup.normalizer (P : Set X)))
      (involutionsInSet
        (⊤ : Subgroup (Subgroup.normalizer (P : Set X)))) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  letI : MulAction X (II1Hering31Involutions X) :=
    ii1Hering31ConjugationAction X
  have htwoF' : IsTwoTransitiveOn (Subgroup.normalizer (P : Set X))
      (fixedPointsOfSubgroup X (II1Hering31Involutions X) P) := htwoF
  let H : Subgroup X := Subgroup.normalizer (P : Set X)
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  have hN2 : IsPGroup 2 N := by
    rw [IsPGroup.iff_orderOf]
    intro n
    by_cases hn : n = 1
    · exact ⟨0, by simp [hn]⟩
    · refine ⟨1, ?_⟩
      simpa using orderOf_eq_prime
        (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm n) hn
  have hNP : Disjoint N P :=
    IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) N P hN2 hPq
  have hinvCentralizes : ∀ z : H, IsInvolution z →
      (z : X) ∈ Subgroup.centralizer (P : Set X) := by
    intro z hz
    have hzX : IsInvolution (z : X) :=
      IsInvolution.map_of_injective hz H.subtype H.subtype_injective
    have hzN : (z : X) ∈ N := Or.inr hzX
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hcommN : p * (z : X) * p⁻¹ * (z : X)⁻¹ ∈ N :=
      N.mul_mem ((ii1Hering31InvolutionSubgroup_normal hcomm).conj_mem
        (z : X) hzN p) (N.inv_mem hzN)
    have hzNorm : (z : X) ∈ Subgroup.normalizer (P : Set X) := z.property
    have hzConjP : (z : X) * p⁻¹ * (z : X)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hzNorm p⁻¹).mp (P.inv_mem hp)
    have hcommP : p * (z : X) * p⁻¹ * (z : X)⁻¹ ∈ P := by
      simpa [mul_assoc] using P.mul_mem hp hzConjP
    have hbot : p * (z : X) * p⁻¹ * (z : X)⁻¹ ∈
        (⊥ : Subgroup X) := by
      rw [← hNP.eq_bot]
      exact ⟨hcommN, hcommP⟩
    have hone : p * (z : X) * p⁻¹ * (z : X)⁻¹ = 1 := by
      simpa using hbot
    exact (commutatorElement_eq_one_iff_commute.mp (by
      simpa [commutatorElement_def] using hone)).eq
  intro a b c d ha hb hc hd hab hcd
  have haInv : IsInvolution a := ha.2
  have hbInv : IsInvolution b := hb.2
  have hcInv : IsInvolution c := hc.2
  have hdInv : IsInvolution d := hd.2
  have haX : IsInvolution (a : X) :=
    IsInvolution.map_of_injective haInv H.subtype H.subtype_injective
  have hbX : IsInvolution (b : X) :=
    IsInvolution.map_of_injective hbInv H.subtype H.subtype_injective
  have hcX : IsInvolution (c : X) :=
    IsInvolution.map_of_injective hcInv H.subtype H.subtype_injective
  have hdX : IsInvolution (d : X) :=
    IsInvolution.map_of_injective hdInv H.subtype H.subtype_injective
  let aX : II1Hering31Involutions X := ⟨a, haX⟩
  let bX : II1Hering31Involutions X := ⟨b, hbX⟩
  let cX : II1Hering31Involutions X := ⟨c, hcX⟩
  let dX : II1Hering31Involutions X := ⟨d, hdX⟩
  have haFix : aX ∈ fixedPointsOfSubgroup X
      (II1Hering31Involutions X) P := by
    intro p hp
    apply Subtype.ext
    change p * (a : X) * p⁻¹ = (a : X)
    have hpa := (Subgroup.mem_centralizer_iff.mp
      (hinvCentralizes a haInv)) p hp
    calc
      p * (a : X) * p⁻¹ = (a : X) * p * p⁻¹ := by rw [hpa]
      _ = (a : X) := by simp
  have hbFix : bX ∈ fixedPointsOfSubgroup X
      (II1Hering31Involutions X) P := by
    intro p hp
    apply Subtype.ext
    change p * (b : X) * p⁻¹ = (b : X)
    have hpb := (Subgroup.mem_centralizer_iff.mp
      (hinvCentralizes b hbInv)) p hp
    calc
      p * (b : X) * p⁻¹ = (b : X) * p * p⁻¹ := by rw [hpb]
      _ = (b : X) := by simp
  have hcFix : cX ∈ fixedPointsOfSubgroup X
      (II1Hering31Involutions X) P := by
    intro p hp
    apply Subtype.ext
    change p * (c : X) * p⁻¹ = (c : X)
    have hpc := (Subgroup.mem_centralizer_iff.mp
      (hinvCentralizes c hcInv)) p hp
    calc
      p * (c : X) * p⁻¹ = (c : X) * p * p⁻¹ := by rw [hpc]
      _ = (c : X) := by simp
  have hdFix : dX ∈ fixedPointsOfSubgroup X
      (II1Hering31Involutions X) P := by
    intro p hp
    apply Subtype.ext
    change p * (d : X) * p⁻¹ = (d : X)
    have hpd := (Subgroup.mem_centralizer_iff.mp
      (hinvCentralizes d hdInv)) p hp
    calc
      p * (d : X) * p⁻¹ = (d : X) * p * p⁻¹ := by rw [hpd]
      _ = (d : X) := by simp
  obtain ⟨n, hnac, hnbd⟩ := htwoF' haFix hbFix hcFix hdFix
    (fun h => hab (Subtype.ext (by
      simpa [aX, bX] using congrArg Subtype.val h)))
    (fun h => hcd (Subtype.ext (by
      simpa [cX, dX] using congrArg Subtype.val h)))
  let ntop : (⊤ : Subgroup H) := ⟨n⁻¹, Subgroup.mem_top _⟩
  refine ⟨ntop, ?_, ?_⟩
  · apply Subtype.ext
    have hnacX : (n : X) * (a : X) * (n : X)⁻¹ = (c : X) :=
      congrArg Subtype.val hnac
    simpa [rightConjugateElem, ntop] using hnacX
  · apply Subtype.ext
    have hnbdX : (n : X) * (b : X) * (n : X)⁻¹ = (d : X) :=
      congrArg Subtype.val hnbd
    simpa [rightConjugateElem, ntop] using hnbdX

/-- Hering's Lemma 3.3(a): in a cardinal-minimal counterexample, the
centralizer of every four-subgroup is a `2`-group.  An odd Sylow subgroup of
such a centralizer would, by Witt's lemma, give a smaller doubly transitive
quotient whose embedded four-subgroup contradicts minimality. -/
public theorem ii1Hering31_four_centralizer
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (V : Subgroup X) (hVcard : Nat.card V = 4)
    (hVsq : ∀ x : V, x ^ 2 = 1) :
    IsPGroup 2 (Subgroup.centralizer (V : Set X)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hCtwo
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_two_distinct_nontrivial_of_card_four hVcard
  letI : MulAction X (II1Hering31Involutions X) :=
    ii1Hering31ConjugationAction X
  obtain ⟨pair, hpair⟩ :=
    ii1Hering31_pair_stabilizer V hVcard a b ha hb hab
      (hVsq a) (hVsq b)
  let D : Subgroup X := MulAction.stabilizer X pair
  have hDtwo : ¬ IsPGroup 2 D := by
    change ¬ IsPGroup 2 (MulAction.stabilizer X pair)
    rw [hpair]
    exact hCtwo
  have hDnotPow : ∀ n : ℕ, Nat.card D ≠ 2 ^ n := by
    intro n hn
    exact hDtwo (IsPGroup.of_card hn)
  obtain ⟨q, hq, hqD, hq2⟩ :=
    External.hkt_exists_prime_dvd_ne_of_not_prime_power
      Nat.card_pos.ne' hDnotPow
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let S : Sylow q D := default
  let P : Subgroup X := (S : Subgroup D).map D.subtype
  have hSne : (S : Subgroup D) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card S hqD
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hSne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (S : Subgroup D) D.subtype_injective).mp hP
  have hPq : IsPGroup q P := by
    exact S.isPGroup'.map D.subtype
  have htwoAct : MulAction.IsMultiplyPretransitive X
      (II1Hering31Involutions X) 2 :=
    ii1Hering31ConjugationAction_twoPretransitive htwo
  have htwoFixed : IsTwoTransitiveOn (Subgroup.normalizer (P : Set X))
      (fixedPointsOfSubgroup X (II1Hering31Involutions X) P) := by
    apply witt_normalizer_twoTransitiveOn_fixedPoints hq htwoAct pair P
    exact ⟨S, rfl⟩
  have htwoNorm : ConjugationTwoTransitiveOn
      (⊤ : Subgroup (Subgroup.normalizer (P : Set X)))
      (involutionsInSet
        (⊤ : Subgroup (Subgroup.normalizer (P : Set X)))) :=
    ii1Hering31_normalizer_conjugation hcomm hq hq2 P hPq htwoFixed
  let H : Subgroup X := Subgroup.normalizer (P : Set X)
  let PH : Subgroup H := P.subgroupOf H
  letI : PH.Normal := Subgroup.normal_in_normalizer
  have hPHne : PH ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    letI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
    exact (Subgroup.subgroupOfEquivOfLe
      (Subgroup.le_normalizer : P ≤ H)).toEquiv.nontrivial
  have hPHodd : Odd (Nat.card PH) := by
    have hcardPH : Nat.card PH = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.le_normalizer : P ≤ H)).toEquiv
    rcases IsPGroup.iff_card.mp hPq with ⟨n, hn⟩
    rw [hcardPH, hn]
    exact (hq.odd_of_ne_two hq2).pow
  have htwoQuot : ConjugationTwoTransitiveOn
      (⊤ : Subgroup (H ⧸ PH))
      (involutionsInSet (⊤ : Subgroup (H ⧸ PH))) :=
    ii1Hering31Conjugation_quotient_of_odd_kernel PH hPHodd htwoNorm
  have hquotCard : Nat.card (H ⧸ PH) < Nat.card X := by
    exact (natCard_quotient_lt_natCard_of_ne_bot PH hPHne).trans_le
      (Nat.card_le_card_of_injective H.subtype H.subtype_injective)
  have hPD : P ≤ D := by
    rintro x ⟨s, hs, rfl⟩
    exact s.property
  have hPC : P ≤ Subgroup.centralizer (V : Set X) := by
    simpa [D, hpair] using hPD
  have hVC : V ≤ Subgroup.centralizer (P : Set X) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact ((Subgroup.mem_centralizer_iff.mp (hPC hp)) v hv).symm
  have hVH : V ≤ H :=
    hVC.trans (centralizer_le_normalizer P)
  have hV2 : IsPGroup 2 V := by
    rw [IsPGroup.iff_orderOf]
    intro v
    by_cases hv : v = 1
    · exact ⟨0, by simp [hv]⟩
    · refine ⟨1, ?_⟩
      simpa using orderOf_eq_prime (hVsq v) hv
  have hVP : Disjoint V P :=
    IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) V P hV2 hPq
  let f : V →* H ⧸ PH :=
    (QuotientGroup.mk' PH).comp (Subgroup.inclusion hVH)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    ext v
    constructor
    · intro hv
      change (v : X) ∈ P at hv
      have hvP : (v : X) ∈ P := hv
      have hvBot : (v : X) ∈ (⊥ : Subgroup X) := by
        rw [← hVP.eq_bot]
        exact ⟨v.property, hvP⟩
      simpa using hvBot
    · intro hv
      have hvOne : v = 1 := by simpa using hv
      subst v
      simp [PH]
  have hVrank : TwoRankAtLeastTwo V := by
    refine ⟨⊤, ?_, ?_⟩
    · simpa using hVcard
    · intro v
      apply Subtype.ext
      exact hVsq (v : V)
  have hquotRank : TwoRankAtLeastTwo (H ⧸ PH) :=
    hVrank.map_of_injective f hf
  exact (hsmall hquotCard htwoQuot) hquotRank

/-- In a cardinal-minimal rank-two counterexample, the centralizer of the
elementary abelian involution subgroup is exactly the normal `2`-core. -/
public theorem ii1Hering31_centralizer_involutionSubgroup_eq_twoCore
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    Subgroup.centralizer
        (ii1Hering31InvolutionSubgroup X hcomm : Set X) =
      pCore 2 X := by
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  have hQle : Q ≤ Subgroup.centralizer (N : Set X) := by
    simpa [N, Q] using
      ii1Hering31_twoCore_le_centralizer htwo hrank hcomm
  obtain ⟨V, hVcard, hVsq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hrank
  have hVN : V ≤ N := by
    simpa [N] using
      ii1Hering31_rankTwo_le_involutionSubgroup hcomm V hVsq
  have hCle : Subgroup.centralizer (N : Set X) ≤
      Subgroup.centralizer (V : Set X) :=
    Subgroup.centralizer_le hVN
  have hCVtwo : IsPGroup 2 (Subgroup.centralizer (V : Set X)) :=
    ii1Hering31_four_centralizer hsmall htwo hcomm V hVcard hVsq
  have hCtwo : IsPGroup 2 (Subgroup.centralizer (N : Set X)) :=
    hCVtwo.to_le hCle
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  have hCleQ : Subgroup.centralizer (N : Set X) ≤ Q := by
    exact le_sSup ⟨inferInstance, hCtwo⟩
  exact le_antisymm hCleQ hQle

/-- The nonidentity part of an elementary abelian involution subgroup. -/
public abbrev II1Hering31Nonidentity (N : Type*) [Group N] :=
  {n : N // n ≠ 1}

/-- The natural action of a subgroup of `MulAut N` on the nonidentity
elements of `N`. -/
@[reducible, expose] public def ii1Hering31NonidentityAction
    (N : Type*) [Group N] (A : Subgroup (MulAut N)) :
    MulAction A (II1Hering31Nonidentity N) where
  smul a n := ⟨(a : MulAut N) n, by
    intro h
    apply n.property
    exact (a : MulAut N).injective (by simpa using h)⟩
  one_smul n := by
    apply Subtype.ext
    change ((1 : A) : MulAut N) (n : N) = n
    simp
  mul_smul a b n := by
    apply Subtype.ext
    change (((a * b : A) : MulAut N) (n : N)) =
      (a : MulAut N) ((b : MulAut N) (n : N))
    rfl

/-- Conjugation double transitivity on ambient involutions descends to the
faithful conjugation range acting on the nonidentity elements of the Hering
involution subgroup. -/
public theorem ii1Hering31_range_twoPretransitive
    {X : Type u} [Group X] [Finite X]
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
    let phi : X →* MulAut N := MulAut.conjNormal (H := N)
    let A : Subgroup (MulAut N) := phi.range
    letI : MulAction A (II1Hering31Nonidentity N) :=
      ii1Hering31NonidentityAction N A
    MulAction.IsMultiplyPretransitive A (II1Hering31Nonidentity N) 2 := by
  dsimp only
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  have haInv : IsInvolution (a : X) :=
    (ii1Hering31InvolutionSubgroup_ne_one_iff hcomm a).mp a.property
  have hbInv : IsInvolution (b : X) :=
    (ii1Hering31InvolutionSubgroup_ne_one_iff hcomm b).mp b.property
  have hcInv : IsInvolution (c : X) :=
    (ii1Hering31InvolutionSubgroup_ne_one_iff hcomm c).mp c.property
  have hdInv : IsInvolution (d : X) :=
    (ii1Hering31InvolutionSubgroup_ne_one_iff hcomm d).mp d.property
  obtain ⟨g, hag, hbg⟩ := htwo
    ⟨Subgroup.mem_top _, haInv⟩ ⟨Subgroup.mem_top _, hbInv⟩
    ⟨Subgroup.mem_top _, hcInv⟩ ⟨Subgroup.mem_top _, hdInv⟩
    (fun h => hab (Subtype.ext (Subtype.ext h)))
    (fun h => hcd (Subtype.ext (Subtype.ext h)))
  let gA : A := ⟨phi g⁻¹, ⟨g⁻¹, rfl⟩⟩
  refine ⟨gA, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    change g⁻¹ * (a : X) * (g⁻¹)⁻¹ = (c : X)
    simpa [rightConjugateElem] using hag
  · apply Subtype.ext
    apply Subtype.ext
    change g⁻¹ * (b : X) * (g⁻¹)⁻¹ = (d : X)
    simpa [rightConjugateElem] using hbg

private theorem ii1Hering31_natCard_nonidentity
    (N : Type*) [Group N] [Finite N] :
    Nat.card (II1Hering31Nonidentity N) = Nat.card N - 1 := by
  classical
  letI : Fintype N := Fintype.ofFinite N
  unfold II1Hering31Nonidentity
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun n : N => n = 1)]
  simp

private theorem ii1Hering31_prime_card_faithful_action_regular
    {K Omega : Type*} [Group K] [Finite K] [Finite Omega]
    [MulAction K Omega] [FaithfulSMul K Omega]
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    (hKcard : Nat.card K = p) (hOmegaCard : Nat.card Omega = p) :
    ∀ x y : Omega, ∃! k : K, k • x = y := by
  have hKp : IsPGroup p K := by
    apply IsPGroup.of_card (n := 1)
    simpa using hKcard
  have hfixedEmpty : IsEmpty (MulAction.fixedPoints K Omega) := by
    rw [isEmpty_iff]
    intro fixed
    have hmod := hKp.card_modEq_card_fixedPoints Omega
    have hfixedDvd : p ∣ Nat.card (MulAction.fixedPoints K Omega) :=
      (hmod.dvd_iff (dvd_refl p)).mp (by rw [hOmegaCard])
    have hfixedPos : 0 < Nat.card (MulAction.fixedPoints K Omega) :=
      Finite.card_pos_iff.mpr ⟨fixed⟩
    have hpLeFixed : p ≤ Nat.card (MulAction.fixedPoints K Omega) :=
      Nat.le_of_dvd hfixedPos hfixedDvd
    have hfixedLe : Nat.card (MulAction.fixedPoints K Omega) ≤
        Nat.card Omega :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hfixedCard : Nat.card (MulAction.fixedPoints K Omega) = p :=
      le_antisymm (hfixedLe.trans_eq hOmegaCard) hpLeFixed
    have hfixedSurj : Function.Surjective
        (fun z : MulAction.fixedPoints K Omega => (z : Omega)) :=
      (Subtype.val_injective.bijective_of_nat_card_le (by
        rw [hfixedCard, hOmegaCard])).2
    have hallFix : ∀ k : K, ∀ x : Omega, k • x = x := by
      intro k x
      obtain ⟨z, rfl⟩ := hfixedSurj x
      exact MulAction.mem_fixedPoints.mp z.property k
    have hsubsingle : ∀ k : K, k = 1 := by
      intro k
      exact (faithfulSMul_iff.mp (inferInstance : FaithfulSMul K Omega)) k
        (hallFix k)
    have hKcardOne : Nat.card K = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hsubsingle a).trans (hsubsingle b).symm⟩, ⟨1⟩⟩
    rw [hKcard] at hKcardOne
    exact hp.out.ne_one hKcardOne
  have hstabilizer : ∀ x : Omega, MulAction.stabilizer K x = ⊥ := by
    intro x
    letI : Fact (Nat.Prime (Nat.card K)) := ⟨hKcard.symm ▸ hp.out⟩
    rcases (MulAction.stabilizer K x).eq_bot_or_eq_top_of_prime_card with
      hbot | htop
    · exact hbot
    · exfalso
      have hxFixed : x ∈ MulAction.fixedPoints K Omega := by
        rw [MulAction.mem_fixedPoints]
        intro k
        have hk : k ∈ MulAction.stabilizer K x := by
          rw [htop]
          exact Subgroup.mem_top k
        exact hk
      exact isEmpty_iff.mp hfixedEmpty ⟨x, hxFixed⟩
  intro x y
  let orbitMap : K → Omega := fun k => k • x
  have horbitInj : Function.Injective orbitMap := by
    intro k l hkl
    have hmem : l⁻¹ * k ∈ MulAction.stabilizer K x := by
      change (l⁻¹ * k) • x = x
      rw [mul_smul, inv_smul_eq_iff]
      exact hkl
    rw [hstabilizer x] at hmem
    exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem)).symm
  have horbitBij : Function.Bijective orbitMap :=
    horbitInj.bijective_of_nat_card_le (by rw [hKcard, hOmegaCard])
  obtain ⟨k, hk⟩ := horbitBij.2 y
  refine ⟨k, hk, ?_⟩
  intro l hl
  exact horbitBij.1 (hl.trans hk.symm)

/-- An order-seven subgroup of the faithful Hering action is regular on the
involutions of the order-eight elementary abelian subgroup. -/
public theorem ii1Hering31_orderSeven_actor
    {N : Type*} [Group N] [Finite N]
    (A : Subgroup (MulAut N))
    (hcard : Nat.card N = 8)
    (htwo : letI : MulAction A (II1Hering31Nonidentity N) :=
      ii1Hering31NonidentityAction N A
      MulAction.IsMultiplyPretransitive A (II1Hering31Nonidentity N) 2) :
    ∃ g : A, orderOf g = 7 ∧
      let K : Subgroup A := Subgroup.zpowers g
      letI : MulDistribMulAction A N :=
        MulDistribMulAction.compHom N A.subtype
      ActionRegularOn K N (involutions N) := by
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  letI : FaithfulSMul A (II1Hering31Nonidentity N) := by
    rw [faithfulSMul_iff]
    intro a ha
    apply Subtype.ext
    apply MulEquiv.ext
    intro n
    by_cases hn : n = 1
    · subst n
      simp
    · exact congrArg Subtype.val (ha ⟨n, hn⟩)
  letI : MulAction.IsMultiplyPretransitive A
      (II1Hering31Nonidentity N) 2 := htwo
  letI : MulAction.IsPretransitive A (II1Hering31Nonidentity N) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hOmegaCard : Nat.card (II1Hering31Nonidentity N) = 7 := by
    rw [ii1Hering31_natCard_nonidentity, hcard]
  letI : Nonempty (II1Hering31Nonidentity N) :=
    Finite.card_pos_iff.mp (by omega)
  let omega0 : II1Hering31Nonidentity N := Classical.choice inferInstance
  have hindex : (MulAction.stabilizer A omega0).index = 7 := by
    rw [MulAction.index_stabilizer_of_transitive]
    exact hOmegaCard
  have hsevenDvd : 7 ∣ Nat.card A := by
    rw [← Subgroup.index_mul_card (MulAction.stabilizer A omega0), hindex]
    exact dvd_mul_right 7 _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 hsevenDvd
  refine ⟨g, hg, ?_⟩
  let K : Subgroup A := Subgroup.zpowers g
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N A.subtype
  have hKcard : Nat.card K = 7 := by
    change Nat.card (Subgroup.zpowers g) = 7
    rw [Nat.card_zpowers, hg]
  have hregular := ii1Hering31_prime_card_faithful_action_regular
    (K := K) (Omega := II1Hering31Nonidentity N)
    hKcard hOmegaCard
  constructor
  · intro x hx k
    constructor
    · intro hkx
      apply hx.ne_one
      apply (k : MulAut N).injective
      change (k : MulAut N) x = 1 at hkx
      simpa using hkx
    · change ((k : MulAut N) x) ^ 2 = 1
      simpa using congrArg (k : MulAut N) hx.sq_eq_one
  · intro x hx y hy
    let x0 : II1Hering31Nonidentity N := ⟨x, hx.ne_one⟩
    let y0 : II1Hering31Nonidentity N := ⟨y, hy.ne_one⟩
    obtain ⟨k, hk, huniq⟩ := hregular x0 y0
    refine ⟨k, ?_, ?_⟩
    · exact (congrArg Subtype.val hk).symm
    · intro l hl
      apply huniq l
      apply Subtype.ext
      exact hl.symm

private theorem ii1Hering31_eq_of_card_three_of_ne
    {α : Type*} [Finite α] (hcard : Nat.card α = 3)
    {a b x y : α}
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b)
    (hya : y ≠ a) (hyb : y ≠ b) : x = y := by
  by_contra hxy
  let f : Fin 4 → α := ![a, b, x, y]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hab, hxa, hxb, hya, hyb, hxy,
        Ne.symm hab, Ne.symm hxa, Ne.symm hxb,
        Ne.symm hya, Ne.symm hyb, Ne.symm hxy] at hij ⊢
  have hfour : 4 ≤ Nat.card α := by
    simpa using Nat.card_le_card_of_injective f hf
  omega

private theorem ii1Hering31_closure_coe_pair_eq_four
    {N : Type*} [Group N] [Finite N]
    (V : Subgroup N) (hcard : Nat.card V = 4)
    (a b : V) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    Subgroup.closure ({(a : N), (b : N)} : Set N) = V := by
  have hgen : Subgroup.closure ({a, b} : Set V) = ⊤ :=
    ii1Hering31_generate_four hcard a b ha hb hab ha2 hb2
  symm
  calc
    V = (⊤ : Subgroup V).map V.subtype := by ext; simp
    _ = (Subgroup.closure ({a, b} : Set V)).map V.subtype := by rw [hgen]
    _ = Subgroup.closure (V.subtype '' ({a, b} : Set V)) :=
      MonoidHom.map_closure V.subtype _
    _ = Subgroup.closure ({(a : N), (b : N)} : Set N) := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        rcases hy with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨a, Set.mem_insert _ _, rfl⟩
        · exact ⟨b, Set.mem_insert_of_mem _ (Set.mem_singleton _), rfl⟩

private theorem ii1Hering31_four_stabilizer_surjective
    {N : Type*} [Group N] [Finite N]
    (hsq : ∀ n : N, n ^ 2 = 1)
    (A : Subgroup (MulAut N))
    (htwo :
      letI : MulAction A (II1Hering31Nonidentity N) :=
        ii1Hering31NonidentityAction N A
      MulAction.IsMultiplyPretransitive A (II1Hering31Nonidentity N) 2)
    (V : Subgroup N) (hVcard : Nat.card V = 4) :
    letI : MulAction A (II1Hering31Nonidentity N) :=
      ii1Hering31NonidentityAction N A
    let S : Set (II1Hering31Nonidentity N) := {n | (n : N) ∈ V}
    Function.Surjective
      (MulAction.toPermHom (MulAction.stabilizer A S) S) := by
  classical
  dsimp only
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  let S : Set (II1Hering31Nonidentity N) := {n | (n : N) ∈ V}
  have hScard : Nat.card S = 3 := by
    let e : S ≃ II1Hering31Nonidentity V :=
      { toFun := fun n =>
          ⟨⟨(n : N), (show (n : N) ∈ V from n.property)⟩, by
            intro h
            exact n.val.property (congrArg Subtype.val h)⟩
        invFun := fun v =>
          ⟨⟨(v : N), by
              intro h
              exact v.property (Subtype.ext h)⟩,
            (show (v : N) ∈ V from v.val.property)⟩
        left_inv := by
          intro n
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro v
          apply Subtype.ext
          apply Subtype.ext
          rfl }
    calc
      Nat.card S = Nat.card (II1Hering31Nonidentity V) := Nat.card_congr e
      _ = Nat.card V - 1 := ii1Hering31_natCard_nonidentity V
      _ = 3 := by omega
  have htwoS : 2 < Nat.card S := by omega
  letI : Fintype S := Fintype.ofFinite S
  have htwoSF : 2 < Fintype.card S := by
    simpa [Nat.card_eq_fintype_card] using htwoS
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    Fintype.two_lt_card_iff.mp htwoSF
  intro p
  have hab' :
      (a : II1Hering31Nonidentity N) ≠ (b : II1Hering31Nonidentity N) :=
    fun h => hab (Subtype.ext h)
  have hpab' :
      (p a : II1Hering31Nonidentity N) ≠
        (p b : II1Hering31Nonidentity N) :=
    fun h => hab (p.injective (Subtype.ext h))
  obtain ⟨g, hga, hgb⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo) hab' hpab'
  let aV : V := ⟨(a : N), a.property⟩
  let bV : V := ⟨(b : N), b.property⟩
  have haV : aV ≠ 1 := by
    intro h
    exact a.val.property (congrArg Subtype.val h)
  have hbV : bV ≠ 1 := by
    intro h
    exact b.val.property (congrArg Subtype.val h)
  have habV : aV ≠ bV := by
    intro h
    have habN : (a : N) = (b : N) :=
      congrArg (fun v : V => (v : N)) h
    have habNon :
        (a : II1Hering31Nonidentity N) =
          (b : II1Hering31Nonidentity N) := Subtype.ext habN
    exact hab (Subtype.ext habNon)
  have hVgen : Subgroup.closure ({(a : N), (b : N)} : Set N) = V := by
    apply ii1Hering31_closure_coe_pair_eq_four
      V hVcard aV bV haV hbV habV
    · apply Subtype.ext
      exact hsq (a : N)
    · apply Subtype.ext
      exact hsq (b : N)
  have hgMapLe : V.map (g : MulAut N).toMonoidHom ≤ V := by
    have hmap :
        V.map (g : MulAut N).toMonoidHom =
          Subgroup.closure
            (((g : MulAut N).toMonoidHom : N → N) ''
              ({(a : N), (b : N)} : Set N)) := by
      rw [← hVgen, MonoidHom.map_closure]
    rw [hmap, Subgroup.closure_le]
    intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hgaN := congrArg
        (fun n : II1Hering31Nonidentity N => (n : N)) hga
      change (g : MulAut N) (a : N) = (p a : N) at hgaN
      have hgaM : (g : MulAut N).toMonoidHom (a : N) = (p a : N) := hgaN
      rw [hgaM]
      exact (p a).property
    · have hgbN := congrArg
        (fun n : II1Hering31Nonidentity N => (n : N)) hgb
      change (g : MulAut N) (b : N) = (p b : N) at hgbN
      have hgbM : (g : MulAut N).toMonoidHom (b : N) = (p b : N) := hgbN
      rw [hgbM]
      exact (p b).property
  have hgMapCard : Nat.card (V.map (g : MulAut N).toMonoidHom) = Nat.card V := by
    exact Subgroup.card_map_of_injective
      (K := V) (f := (g : MulAut N).toMonoidHom) (g : MulAut N).injective
  have hgMapEq : V.map (g : MulAut N).toMonoidHom = V := by
    apply Subgroup.eq_of_le_of_card_ge hgMapLe
    rw [hgMapCard]
  have hgS : g • S = S := by
    ext n
    constructor
    · rintro ⟨m, hm, rfl⟩
      change ((g : MulAut N) (m : N)) ∈ V
      rw [← hgMapEq]
      exact Subgroup.mem_map_of_mem (g : MulAut N).toMonoidHom hm
    · intro hn
      let mN : N := (g : MulAut N)⁻¹ (n : N)
      have hmNe : mN ≠ 1 := by
        intro hm
        have := congrArg (g : MulAut N) hm
        exact n.property (by simpa [mN] using this)
      let m : II1Hering31Nonidentity N := ⟨mN, hmNe⟩
      have hmV : (m : N) ∈ V := by
        have hnMap : (n : N) ∈ V.map (g : MulAut N).toMonoidHom := by
          rw [hgMapEq]
          exact hn
        rcases hnMap with ⟨v, hv, hvn⟩
        have : (m : N) = v := by
          apply (g : MulAut N).injective
          simpa [m, mN] using hvn.symm
        rw [this]
        exact hv
      refine ⟨m, hmV, ?_⟩
      apply Subtype.ext
      change (g : MulAut N) mN = (n : N)
      simp [mN]
  let d : MulAction.stabilizer A S := ⟨g, hgS⟩
  refine ⟨d, ?_⟩
  apply Equiv.ext
  intro x
  have hdaEq : (d • a : S) = p a := Subtype.ext hga
  have hdbEq : (d • b : S) = p b := Subtype.ext hgb
  by_cases hxa : x = a
  · subst x
    exact hdaEq
  by_cases hxb : x = b
  · subst x
    exact hdbEq
  have hda : (d • x : S) ≠ p a := by
    intro h
    apply hxa
    apply (MulAction.toPerm d).injective
    exact h.trans hdaEq.symm
  have hdb : (d • x : S) ≠ p b := by
    intro h
    apply hxb
    apply (MulAction.toPerm d).injective
    exact h.trans hdbEq.symm
  have hpa : p x ≠ p a := fun h => hxa (p.injective h)
  have hpb : p x ≠ p b := fun h => hxb (p.injective h)
  exact ii1Hering31_eq_of_card_three_of_ne hScard
    (fun h => hab (p.injective h)) hda hdb hpa hpb

/-- A contrapositive Baer--Suzuki extraction: an involution outside the
normal `2`-core inverts an element of odd prime order. -/
public theorem ii1Hering31_odd_rotation
    {G : Type u} [Group G] [Finite G]
    (t : G) (ht : IsInvolution t) (htcore : t ∉ pCore 2 G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      ∃ r : G, orderOf r = q ∧ rightConjugateElem r t = r⁻¹ := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htP : IsPElement (p := 2) t := by
    refine ⟨1, ?_⟩
    simpa using orderOf_eq_prime ht.sq_eq_one ht.ne_one
  have hpair : ∃ y : G,
      (∃ g : G, y = g * t * g⁻¹) ∧
        ¬ IsPGroup 2 (Subgroup.closure ({t, y} : Set G)) := by
    by_contra hpair
    push_neg at hpair
    have htmem := gorenstein_3_8_2_conjugacy_class_le_pCore
      (G := G) (p := 2) (x := t) htP hpair t ⟨1, by simp⟩
    exact htcore htmem
  obtain ⟨y, ⟨g, rfl⟩, hnotTwo⟩ := hpair
  let y : G := g * t * g⁻¹
  have hy : IsInvolution y := by
    simpa [y, rightConjugateElem] using
      isInvolution_rightConjugateElem (x := t) (g := g⁻¹) ht
  let a : G := t * y
  have hta : rightConjugateElem a t = a⁻¹ := by
    change t⁻¹ * (t * y) * t = (t * y)⁻¹
    rw [ht.inv_eq_self, mul_inv_rev, ht.inv_eq_self, hy.inv_eq_self]
    calc
      t * (t * y) * t = (t * t) * y * t := by group
      _ = y * t := by rw [← pow_two, ht.sq_eq_one]; simp
  have hnotPow : ∀ n : ℕ, orderOf a ≠ 2 ^ n := by
    intro n haorder
    let A : Subgroup G := Subgroup.zpowers a
    let T : Subgroup G := Subgroup.zpowers t
    have hA2 : IsPGroup 2 A := by
      apply IsPGroup.of_card (p := 2) (G := A) (n := n)
      simpa [A, Nat.card_zpowers] using haorder
    have hT2 : IsPGroup 2 T := by
      simpa [T] using isPGroup_two_zpowers_of_isInvolution ht
    have htNormA : t ∈ Subgroup.normalizer (A : Set G) := by
      have hforward : ∀ z : G, z ∈ A → t * z * t⁻¹ ∈ A := by
        intro z hz
        rw [Subgroup.mem_zpowers_iff] at hz ⊢
        obtain ⟨k, rfl⟩ := hz
        refine ⟨-k, ?_⟩
        let c : MulAut G := MulAut.conj t
        have hc : c a = a⁻¹ := by
          simpa [c, MulAut.conj_apply, rightConjugateElem,
            ht.inv_eq_self] using hta
        have hpow : c (a ^ k) = (a⁻¹) ^ k := by
          rw [map_zpow, hc]
        simpa [c, MulAut.conj_apply] using hpow.symm
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · exact hforward z
      · intro hz
        have hback := hforward (t * z * t⁻¹) hz
        have heq : t * (t * z * t⁻¹) * t⁻¹ = z := by
          rw [ht.inv_eq_self]
          calc
            t * (t * z * t) * t = (t * t) * z * (t * t) := by group
            _ = z := by rw [← pow_two, ht.sq_eq_one]; simp
        rwa [heq] at hback
    have hTNormA : T ≤ Subgroup.normalizer (A : Set G) :=
      Subgroup.zpowers_le.mpr htNormA
    have hsup2 : IsPGroup 2 (A ⊔ T : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hA2 hT2 hTNormA
    have hclosure : Subgroup.closure ({t, y} : Set G) ≤ A ⊔ T := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]
        exact (show T ≤ A ⊔ T from le_sup_right) (Subgroup.mem_zpowers t)
      · rw [hz]
        have haA : a ∈ A := Subgroup.mem_zpowers a
        have htT : t ∈ T := Subgroup.mem_zpowers t
        have hyEq : y = t * a := by
          calc
            y = 1 * y := by simp
            _ = (t * t) * y := by rw [← pow_two, ht.sq_eq_one]
            _ = t * (t * y) := by simp [mul_assoc]
            _ = t * a := by rfl
        rw [hyEq]
        exact (A ⊔ T).mul_mem
          ((show T ≤ A ⊔ T from le_sup_right) htT)
          ((show A ≤ A ⊔ T from le_sup_left) haA)
    exact hnotTwo (hsup2.to_le hclosure)
  obtain ⟨q, hq, hqa, hq2⟩ :=
    External.hkt_exists_prime_dvd_ne_of_not_prime_power
      (orderOf_pos a).ne' hnotPow
  let r : G := a ^ (orderOf a / q)
  have hrorder : orderOf r = q :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne' hqa
  have hrinv : rightConjugateElem r t = r⁻¹ := by
    have hpow : ∀ n : ℕ,
        rightConjugateElem (a ^ n) t = (a⁻¹) ^ n := by
      intro n
      induction n with
      | zero => simp [rightConjugateElem]
      | succ n ih =>
          rw [pow_succ, pow_succ]
          simp only [rightConjugateElem] at ih hta ⊢
          calc
            t⁻¹ * (a ^ n * a) * t =
                (t⁻¹ * a ^ n * t) * (t⁻¹ * a * t) := by
                  simp [mul_assoc]
            _ = (a⁻¹) ^ n * a⁻¹ := by rw [ih, hta]
    simpa [r] using hpow (orderOf a / q)
  exact ⟨q, hq, hq2, r, hrorder, hrinv⟩

private theorem ii1Hering31_four_stabilizer_dihedral_three
    {N : Type*} [Group N] [Finite N]
    (hsq : ∀ n : N, n ^ 2 = 1)
    (A : Subgroup (MulAut N))
    (htwo :
      letI : MulAction A (II1Hering31Nonidentity N) :=
        ii1Hering31NonidentityAction N A
      MulAction.IsMultiplyPretransitive A (II1Hering31Nonidentity N) 2)
    (V : Subgroup N) (hVcard : Nat.card V = 4) :
    letI : MulAction A (II1Hering31Nonidentity N) :=
      ii1Hering31NonidentityAction N A
    let S : Set (II1Hering31Nonidentity N) := {n | (n : N) ∈ V}
    let D : Subgroup A := MulAction.stabilizer A S
    let rho : D →* Equiv.Perm S := MulAction.toPermHom D S
    IsPGroup 2 rho.ker →
      ∃ t r : D, IsInvolution t ∧ orderOf r = 3 ∧
        rightConjugateElem r t = r⁻¹ := by
  classical
  dsimp only
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  let S : Set (II1Hering31Nonidentity N) := {n | (n : N) ∈ V}
  let D : Subgroup A := MulAction.stabilizer A S
  let rho : D →* Equiv.Perm S := MulAction.toPermHom D S
  intro hker2
  have hsurj : Function.Surjective rho :=
    ii1Hering31_four_stabilizer_surjective hsq A htwo V hVcard
  have hScard : Nat.card S = 3 := by
    let e : S ≃ II1Hering31Nonidentity V :=
      { toFun := fun n =>
          ⟨⟨(n : N), (show (n : N) ∈ V from n.property)⟩, by
            intro h
            exact n.val.property (congrArg Subtype.val h)⟩
        invFun := fun v =>
          ⟨⟨(v : N), by
              intro h
              exact v.property (Subtype.ext h)⟩,
            (show (v : N) ∈ V from v.val.property)⟩
        left_inv := by
          intro n
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro v
          apply Subtype.ext
          apply Subtype.ext
          rfl }
    calc
      Nat.card S = Nat.card (II1Hering31Nonidentity V) := Nat.card_congr e
      _ = Nat.card V - 1 := ii1Hering31_natCard_nonidentity V
      _ = 3 := by omega
  have hrange : rho.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  have hsix : 6 ∣ Nat.card D := by
    have hdiv := Subgroup.card_range_dvd rho
    rw [hrange] at hdiv
    norm_num [Nat.card_perm, hScard, Nat.factorial] at hdiv ⊢
    exact hdiv
  have htwoD : 2 ∣ Nat.card D := dvd_trans (by norm_num) hsix
  obtain ⟨t0, ht0order⟩ :=
    exists_prime_orderOf_dvd_card' (G := D) 2 htwoD
  have ht0Data := orderOf_eq_prime_iff.mp ht0order
  have ht0 : IsInvolution t0 := ⟨ht0Data.2, ht0Data.1⟩
  let t0A : A := (t0 : A)
  have ht0Aorder : orderOf t0A = 2 := by
    simpa [t0A] using (Subgroup.orderOf_coe t0).trans ht0order
  have ht0AData := orderOf_eq_prime_iff.mp ht0Aorder
  have ht0A : IsInvolution t0A := ⟨ht0AData.2, ht0AData.1⟩
  have ht0AutNe : (t0A : MulAut N) ≠ 1 := by
    intro h
    apply ht0A.ne_one
    apply Subtype.ext
    exact h
  have hnmove : ∃ n : N, (t0A : MulAut N) n ≠ n := by
    by_contra hn
    push_neg at hn
    apply ht0AutNe
    apply MulEquiv.ext
    intro n
    simpa using hn n
  obtain ⟨n, hnmove⟩ := hnmove
  have hnNe : n ≠ 1 := by
    intro hn
    subst n
    exact hnmove (map_one (t0A : MulAut N))
  let nI : II1Hering31Nonidentity N := ⟨n, hnNe⟩
  let mI : II1Hering31Nonidentity N := t0A • nI
  have hnm : nI ≠ mI := by
    intro h
    apply hnmove
    exact congrArg Subtype.val h.symm
  letI : Fintype S := Fintype.ofFinite S
  have htwoSF : 2 < Fintype.card S := by
    have : 2 < Nat.card S := by omega
    simpa [Nat.card_eq_fintype_card] using this
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    Fintype.two_lt_card_iff.mp htwoSF
  have habNon :
      (a : II1Hering31Nonidentity N) ≠ (b : II1Hering31Nonidentity N) :=
    fun h => hab (Subtype.ext h)
  obtain ⟨g, hgn, hgm⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo) hnm habNon
  let tA : A := g * t0A * g⁻¹
  have htA : IsInvolution tA := by
    simpa [tA, rightConjugateElem] using
      isInvolution_rightConjugateElem (x := t0A) (g := g⁻¹) ht0A
  have hta :
      tA • (a : II1Hering31Nonidentity N) =
        (b : II1Hering31Nonidentity N) := by
    rw [← hgn, ← hgm]
    simp [tA, mI, mul_smul]
  have htb :
      tA • (b : II1Hering31Nonidentity N) =
        (a : II1Hering31Nonidentity N) := by
    rw [← hgm, ← hgn]
    simp only [tA, mI, mul_smul, inv_smul_smul]
    rw [← mul_smul g t0A (t0A • nI),
      ← mul_smul (g * t0A) t0A nI,
      mul_assoc, ← pow_two, ht0A.sq_eq_one, mul_one]
  let aV : V := ⟨(a : N), a.property⟩
  let bV : V := ⟨(b : N), b.property⟩
  have haV : aV ≠ 1 := by
    intro h
    exact a.val.property (congrArg Subtype.val h)
  have hbV : bV ≠ 1 := by
    intro h
    exact b.val.property (congrArg Subtype.val h)
  have habV : aV ≠ bV := by
    intro h
    have habN : (a : N) = (b : N) :=
      congrArg (fun v : V => (v : N)) h
    have habNon :
        (a : II1Hering31Nonidentity N) =
          (b : II1Hering31Nonidentity N) := Subtype.ext habN
    exact hab (Subtype.ext habNon)
  have hVgen : Subgroup.closure ({(a : N), (b : N)} : Set N) = V := by
    apply ii1Hering31_closure_coe_pair_eq_four
      V hVcard aV bV haV hbV habV
    · apply Subtype.ext
      exact hsq (a : N)
    · apply Subtype.ext
      exact hsq (b : N)
  have htMapLe : V.map (tA : MulAut N).toMonoidHom ≤ V := by
    have hmap :
        V.map (tA : MulAut N).toMonoidHom =
          Subgroup.closure
            (((tA : MulAut N).toMonoidHom : N → N) ''
              ({(a : N), (b : N)} : Set N)) := by
      rw [← hVgen, MonoidHom.map_closure]
    rw [hmap, Subgroup.closure_le]
    intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have htaN := congrArg
        (fun n : II1Hering31Nonidentity N => (n : N)) hta
      change (tA : MulAut N) (a : N) = (b : N) at htaN
      have htaM : (tA : MulAut N).toMonoidHom (a : N) = (b : N) := htaN
      rw [htaM]
      exact b.property
    · have htbN := congrArg
        (fun n : II1Hering31Nonidentity N => (n : N)) htb
      change (tA : MulAut N) (b : N) = (a : N) at htbN
      have htbM : (tA : MulAut N).toMonoidHom (b : N) = (a : N) := htbN
      rw [htbM]
      exact a.property
  have htMapCard : Nat.card (V.map (tA : MulAut N).toMonoidHom) = Nat.card V := by
    exact Subgroup.card_map_of_injective
      (K := V) (f := (tA : MulAut N).toMonoidHom) (tA : MulAut N).injective
  have htMapEq : V.map (tA : MulAut N).toMonoidHom = V := by
    apply Subgroup.eq_of_le_of_card_ge htMapLe
    rw [htMapCard]
  have htS : tA • S = S := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      change ((tA : MulAut N) (m : N)) ∈ V
      rw [← htMapEq]
      exact Subgroup.mem_map_of_mem (tA : MulAut N).toMonoidHom hm
    · intro hx
      let m : II1Hering31Nonidentity N := tA • x
      have hmV : (m : N) ∈ V := by
        change (tA : MulAut N) (x : N) ∈ V
        rw [← htMapEq]
        exact Subgroup.mem_map_of_mem (tA : MulAut N).toMonoidHom hx
      refine ⟨m, hmV, ?_⟩
      change tA • m = x
      rw [show m = tA • x by rfl, ← mul_smul, ← pow_two,
        htA.sq_eq_one, one_smul]
  let t : D := ⟨tA, htS⟩
  have ht : IsInvolution t := by
    refine ⟨?_, ?_⟩
    · intro h
      exact htA.ne_one (congrArg Subtype.val h)
    · apply Subtype.ext
      exact htA.sq_eq_one
  have hrhoTa : rho t a = b := by
    apply Subtype.ext
    exact hta
  have hrhoTb : rho t b = a := by
    apply Subtype.ext
    exact htb
  have hrhoTc : rho t c = c := by
    have hca : c ≠ a := Ne.symm hac
    have hcb : c ≠ b := Ne.symm hbc
    have htcA : rho t c ≠ a := by
      intro h
      apply hbc
      apply (rho t).injective
      exact hrhoTb.trans h.symm
    have htcB : rho t c ≠ b := by
      intro h
      apply hac
      apply (rho t).injective
      exact hrhoTa.trans h.symm
    exact ii1Hering31_eq_of_card_three_of_ne
      hScard hab htcA htcB hca hcb
  have hrhoT : rho t = Equiv.swap a b := by
    apply Equiv.ext
    intro x
    by_cases hxa : x = a
    · subst x
      simpa using hrhoTa
    by_cases hxb : x = b
    · subst x
      simpa using hrhoTb
    have hxc : x = c :=
      ii1Hering31_eq_of_card_three_of_ne hScard hab hxa hxb
        (Ne.symm hac) (Ne.symm hbc)
    subst x
    simpa [Equiv.swap_apply_def, Ne.symm hac, Ne.symm hbc] using hrhoTc
  have htNotCore : t ∉ pCore 2 D := by
    intro htCore
    obtain ⟨e, he⟩ := hsurj (Equiv.swap b c)
    let t' : D := e * t * e⁻¹
    have ht'Core : t' ∈ pCore 2 D := by
      simpa [t'] using
        (pCore_normal (G := D) (p := 2)).conj_mem t htCore e
    let u : D := t * t'
    have huCore : u ∈ pCore 2 D :=
      (pCore 2 D).mul_mem htCore ht'Core
    have hrhoUorder : orderOf (rho u) = 3 := by
      have hua : rho u a = c := by
        simp [u, t', he, hrhoT, Equiv.swap_apply_def,
          hab, hac, Ne.symm hac, Ne.symm hbc]
      have hub : rho u b = a := by
        simp [u, t', he, hrhoT, Equiv.swap_apply_def,
          Ne.symm hac, Ne.symm hbc]
      have huc : rho u c = b := by
        simp [u, t', he, hrhoT, Equiv.swap_apply_def, hab, hac]
      have huCube : (rho u) ^ 3 = 1 := by
        apply Equiv.ext
        intro x
        by_cases hxa : x = a
        · subst x
          change rho u (rho u (rho u a)) = a
          rw [hua, huc, hub]
        by_cases hxb : x = b
        · subst x
          change rho u (rho u (rho u b)) = b
          rw [hub, hua, huc]
        have hxc : x = c :=
          ii1Hering31_eq_of_card_three_of_ne hScard hab hxa hxb
            (Ne.symm hac) (Ne.symm hbc)
        subst x
        change rho u (rho u (rho u c)) = c
        rw [huc, hub, hua]
      have huNe : rho u ≠ 1 := by
        intro h
        have haFix := congrArg (fun p : Equiv.Perm S => p a) h
        simp only [hua, Equiv.Perm.one_apply] at haFix
        exact (Ne.symm hac) haFix
      letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime huCube huNe
    let uCore : pCore 2 D := ⟨u, huCore⟩
    obtain ⟨k, huk⟩ := (IsPGroup.iff_orderOf.mp
      (pCore_isPGroup (G := D) (p := 2))) uCore
    have huOrder : orderOf u = 2 ^ k := by
      simpa [uCore] using (Subgroup.orderOf_coe uCore).trans huk
    have hthreePow : 3 ∣ 2 ^ k := by
      rw [← huOrder, ← hrhoUorder]
      exact orderOf_map_dvd rho u
    have hthreeTwo : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthreePow
    norm_num at hthreeTwo
  obtain ⟨q, hq, hq2, r, hrOrder, hrInv⟩ :=
    ii1Hering31_odd_rotation t ht htNotCore
  have hrhoNe : rho r ≠ 1 := by
    intro hrho
    have hrKer : r ∈ rho.ker := by
      rw [MonoidHom.mem_ker]
      exact hrho
    let rKer : rho.ker := ⟨r, hrKer⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hker2) rKer
    have hrKerOrder : orderOf r = 2 ^ k := by
      simpa [rKer] using (Subgroup.orderOf_coe rKer).trans hk
    have hqDvdPow : q ∣ 2 ^ k := by
      rw [← hrKerOrder, hrOrder]
    have hqDvdTwo : q ∣ 2 := hq.dvd_of_dvd_pow hqDvdPow
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hqDvdTwo)
  have hrhoDvd : orderOf (rho r) ∣ q := by
    rw [← hrOrder]
    exact orderOf_map_dvd rho r
  have hrhoOrder : orderOf (rho r) = q := by
    exact ((Nat.dvd_prime hq).mp hrhoDvd).resolve_left
      (fun h => hrhoNe (orderOf_eq_one_iff.mp h))
  have hqDvdSix : q ∣ 6 := by
    have hdiv := orderOf_dvd_natCard (rho r)
    rw [hrhoOrder, Nat.card_perm, hScard] at hdiv
    norm_num [Nat.factorial] at hdiv ⊢
    exact hdiv
  have hqDvdMul : q ∣ 2 * 3 := by
    norm_num at hqDvdSix ⊢
    exact hqDvdSix
  have hqThree : q = 3 := by
    rcases hq.dvd_mul.mp hqDvdMul with hqDvdTwo | hqDvdThree
    · exact False.elim
        (hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hqDvdTwo))
    · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hqDvdThree
  exact ⟨t, r, ht, hrOrder.trans hqThree, hrInv⟩

/-- The dihedral-order-six core of Hering's Lemma 3.3(b), in the faithful
conjugation image.  The setwise stabilizer of a four-subgroup contains an
involution that inverts an element of order three. -/
public theorem ii1Hering31_four_normalizer_dihedral_three
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    ∀ (V : Subgroup N), Nat.card V = 4 →
      letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
      let phi : X →* MulAut N := MulAut.conjNormal (H := N)
      let A : Subgroup (MulAut N) := phi.range
      letI : MulAction A (II1Hering31Nonidentity N) :=
        ii1Hering31NonidentityAction N A
      let S : Set (II1Hering31Nonidentity N) := {n | (n : N) ∈ V}
      let D : Subgroup A := MulAction.stabilizer A S
      ∃ t r : D, IsInvolution t ∧ orderOf r = 3 ∧
        rightConjugateElem r t = r⁻¹ := by
  classical
  dsimp only
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  intro V hVcard
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  let S : Set (II1Hering31Nonidentity N) := {n | (n : N) ∈ V}
  let D : Subgroup A := MulAction.stabilizer A S
  let rho : D →* Equiv.Perm S := MulAction.toPermHom D S
  let VX : Subgroup X := V.map N.subtype
  have hVXcard : Nat.card VX = 4 := by
    rw [show Nat.card VX = Nat.card V by
      exact Subgroup.card_map_of_injective
        (K := V) (f := N.subtype) N.subtype_injective]
    exact hVcard
  have hVXsq : ∀ v : VX, v ^ 2 = 1 := by
    intro v
    rcases v.property with ⟨n, hn, hnv⟩
    apply Subtype.ext
    change (v : X) ^ 2 = 1
    rw [← hnv]
    exact congrArg N.subtype
      (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm n)
  have hC2 : IsPGroup 2 (Subgroup.centralizer (VX : Set X)) :=
    ii1Hering31_four_centralizer hsmall htwo hcomm VX hVXcard hVXsq
  have hker2 : IsPGroup 2 rho.ker := by
    rw [IsPGroup.iff_orderOf]
    intro k
    obtain ⟨x, hx⟩ := ((k : D) : A).property
    have hxC : x ∈ Subgroup.centralizer (VX : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rcases hv with ⟨n, hn, rfl⟩
      by_cases hnOne : n = 1
      · subst n
        simp
      let nI : II1Hering31Nonidentity N := ⟨n, hnOne⟩
      let nS : S := ⟨nI, hn⟩
      have hkPerm : rho (k : D) = 1 :=
        MonoidHom.mem_ker.mp k.property
      have hkFix : (k : D) • nS = nS := by
        have := congrArg (fun p : Equiv.Perm S => p nS) hkPerm
        change rho (k : D) nS = nS
        exact this
      have hkFixN : (((k : D) : A) : MulAut N) n = n := by
        exact congrArg
          (fun z : S => ((z : II1Hering31Nonidentity N) : N)) hkFix
      have hphiFix : phi x n = n := by
        rw [hx]
        exact hkFixN
      have hconj : x * (n : X) * x⁻¹ = (n : X) := by
        simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using
          congrArg N.subtype hphiFix
      have hmul := congrArg (fun z : X => z * x) hconj
      simpa [mul_assoc] using hmul.symm
    let xC : Subgroup.centralizer (VX : Set X) := ⟨x, hxC⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hC2) xC
    have hxOrder : orderOf x = 2 ^ m := by
      simpa [xC] using (Subgroup.orderOf_coe xC).trans hm
    have hkDvdX : orderOf k ∣ orderOf x := by
      rw [← Subgroup.orderOf_coe k, ← Subgroup.orderOf_coe (k : D)]
      simpa [hx] using orderOf_map_dvd phi x
    rw [hxOrder] at hkDvdX
    obtain ⟨j, _hj, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp hkDvdX
    exact ⟨j, hj⟩
  exact ii1Hering31_four_stabilizer_dihedral_three
    (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm) A
    (ii1Hering31_range_twoPretransitive htwo hcomm) V hVcard hker2

private theorem ii1Hering31_nonidentity_action_faithful
    {N : Type*} [Group N]
    (A : Subgroup (MulAut N)) :
    letI : MulAction A (II1Hering31Nonidentity N) :=
      ii1Hering31NonidentityAction N A
    Function.Injective
      (MulAction.toPermHom A (II1Hering31Nonidentity N)) := by
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  intro a b hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro n
  by_cases hn : n = 1
  · subst n
    simp
  let nI : II1Hering31Nonidentity N := ⟨n, hn⟩
  have hfix := congrArg
    (fun p : Equiv.Perm (II1Hering31Nonidentity N) => p nI) hab
  exact congrArg Subtype.val hfix

private theorem ii1Hering31_four_range_card_eq_six
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (hcard : Nat.card (ii1Hering31InvolutionSubgroup X hcomm) = 4) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
    let phi : X →* MulAut N := MulAut.conjNormal (H := N)
    let A : Subgroup (MulAut N) := phi.range
    Nat.card A = 6 := by
  classical
  dsimp only
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  let rho : A →* Equiv.Perm (II1Hering31Nonidentity N) :=
    MulAction.toPermHom A (II1Hering31Nonidentity N)
  have hNoncard : Nat.card (II1Hering31Nonidentity N) = 3 := by
    rw [ii1Hering31_natCard_nonidentity]
    simpa [N] using hcard
  have hUpper : Nat.card A ≤ 6 := by
    have hle := Nat.card_le_card_of_injective rho
      (ii1Hering31_nonidentity_action_faithful A)
    rw [Nat.card_perm, hNoncard] at hle
    norm_num [Nat.factorial] at hle ⊢
    exact hle
  obtain ⟨t, r, ht, hr, _htr⟩ :=
    ii1Hering31_four_normalizer_dihedral_three hsmall htwo hcomm
      (⊤ : Subgroup N) (by simpa [N] using hcard)
  have htwoD : 2 ∣ Nat.card (MulAction.stabilizer A
      ({n : II1Hering31Nonidentity N | (n : N) ∈ (⊤ : Subgroup N)} : Set _)) := by
    rw [← orderOf_eq_prime ht.sq_eq_one ht.ne_one]
    exact orderOf_dvd_natCard t
  have hthreeD : 3 ∣ Nat.card (MulAction.stabilizer A
      ({n : II1Hering31Nonidentity N | (n : N) ∈ (⊤ : Subgroup N)} : Set _)) := by
    rw [← hr]
    exact orderOf_dvd_natCard r
  have hsixD : 6 ∣ Nat.card (MulAction.stabilizer A
      ({n : II1Hering31Nonidentity N | (n : N) ∈ (⊤ : Subgroup N)} : Set _)) := by
    exact (by norm_num : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd htwoD hthreeD
  have hDvdA : Nat.card (MulAction.stabilizer A
      ({n : II1Hering31Nonidentity N | (n : N) ∈ (⊤ : Subgroup N)} : Set _)) ∣
      Nat.card A :=
    Subgroup.card_subgroup_dvd_card _
  have hLower : 6 ≤ Nat.card A :=
    Nat.le_of_dvd (Nat.card_pos) (dvd_trans hsixD hDvdA)
  exact Nat.le_antisymm hUpper hLower

private theorem ii1Hering31_normal_nontrivial_fixedPointSubgroup_eq_bot
    {N : Type*} [Group N]
    (A : Subgroup (MulAut N))
    (htwo :
      letI : MulAction A (II1Hering31Nonidentity N) :=
        ii1Hering31NonidentityAction N A
      MulAction.IsMultiplyPretransitive A
        (II1Hering31Nonidentity N) 2)
    (P : Subgroup A) [P.Normal] (hPne : P ≠ ⊥) :
    fixedPointSubgroup P N = ⊥ := by
  classical
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  letI : MulAction.IsMultiplyPretransitive A
      (II1Hering31Nonidentity N) 2 := htwo
  haveI : MulAction.IsPretransitive A (II1Hering31Nonidentity N) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  by_contra hnOne
  let nI : II1Hering31Nonidentity N := ⟨n, hnOne⟩
  letI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPne
  obtain ⟨p, hpNe⟩ := exists_ne (1 : P)
  have hpFix : ∀ x : N, (p : A) • x = x := by
    intro x
    by_cases hxOne : x = 1
    · subst x
      simp
    let xI : II1Hering31Nonidentity N := ⟨x, hxOne⟩
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A nI xI
    let p' : P := ⟨a⁻¹ * (p : A) * a,
      by
        simpa only [inv_inv] using
          (inferInstance : P.Normal).conj_mem (p : A) p.property a⁻¹⟩
    have hp'Fix : (p' : A) • n = n := by
      exact (FixedPoints.mem_subgroup P N n).mp hn p'
    have hpa : (p : A) * a = a * (p' : A) := by
      change (p : A) * a = a * (a⁻¹ * (p : A) * a)
      group
    have haN : a • n = x := congrArg Subtype.val ha
    rw [← haN, ← mul_smul, hpa, mul_smul, hp'Fix]
  apply hpNe
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  exact hpFix x

private theorem ii1Hering31_conjNormal_ker_eq_centralizer
    {G : Type*} [Group G] {H : Subgroup G} [H.Normal] :
    (MulAut.conjNormal (H := H)).ker = Subgroup.centralizer (H : Set G) := by
  let phi : G →* MulAut H := MulAut.conjNormal (H := H)
  ext x
  rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
  constructor
  · intro hx h hh
    have hxApply : phi x ⟨h, hh⟩ = ⟨h, hh⟩ := by
      change (MulAut.conjNormal (H := H) x) ⟨h, hh⟩ = ⟨h, hh⟩
      rw [hx]
      rfl
    have hconj : x * h * x⁻¹ = h := by
      simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using
        congrArg Subtype.val hxApply
    have heq := congrArg (fun y : G => y * x) hconj
    simpa [mul_assoc] using heq.symm
  · intro hx
    ext h
    have hcomm : (h : G) * x = x * h := hx h h.2
    have hconj : x * (h : G) * x⁻¹ = h := by
      calc
        x * (h : G) * x⁻¹ = ((h : G) * x) * x⁻¹ := by rw [hcomm]
        _ = h := by simp [mul_assoc]
    simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj

/-- The elementary abelian involution subgroup in Hering's minimal
counterexample cannot have cardinality four. -/
public theorem ii1Hering31_four_card_ne
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    Nat.card N ≠ 4 := by
  classical
  dsimp only
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  intro hNcard
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  let psi : X →* A := phi.rangeRestrict
  have hpsiSurj : Function.Surjective psi := MonoidHom.rangeRestrict_surjective phi
  have hAcard : Nat.card A = 6 :=
    ii1Hering31_four_range_card_eq_six hsmall htwo hcomm hNcard
  let PA : Sylow 3 A := Sylow.nonempty.some
  have hPAcard : Nat.card PA = 3 := by
    have hthreeDvd : 3 ∣ Nat.card PA := by
      apply PA.dvd_card_of_dvd_card
      rw [hAcard]
      norm_num
    have hPAdvd : Nat.card PA ∣ 6 := by
      rw [← hAcard]
      exact Subgroup.card_subgroup_dvd_card (PA : Subgroup A)
    have hPAle : Nat.card PA ≤ 6 := Nat.le_of_dvd (by norm_num) hPAdvd
    have hPAodd : Odd (Nat.card PA) := by
      rcases IsPGroup.iff_card.mp PA.isPGroup' with ⟨m, hm⟩
      rw [hm]
      have hthreeOdd : Odd 3 := ⟨1, rfl⟩
      exact hthreeOdd.pow
    rcases hthreeDvd with ⟨m, hm⟩
    rcases hPAodd with ⟨n, hn⟩
    omega
  have hPAindex : (PA : Subgroup A).index = 2 := by
    have hmul := (PA : Subgroup A).index_mul_card
    rw [hPAcard, hAcard] at hmul
    omega
  letI : (PA : Subgroup A).Normal :=
    Subgroup.normal_of_index_eq_two hPAindex
  have hPAne : (PA : Subgroup A) ≠ ⊥ := by
    intro h
    rw [h] at hPAcard
    simp at hPAcard
  obtain ⟨P, hPmap⟩ :=
    Sylow.mapSurjective_surjective hpsiSurj 3 PA
  have hPmapSub : (P : Subgroup X).map psi = (PA : Subgroup A) := by
    simpa only [Sylow.coe_mapSurjective] using
      congrArg (fun Q : Sylow 3 A => (Q : Subgroup A)) hPmap
  let M : Subgroup X := (PA : Subgroup A).comap psi
  letI : M.Normal :=
    (inferInstance : (PA : Subgroup A).Normal).comap psi
  have hP_le_M : (P : Subgroup X) ≤ M := by
    change (P : Subgroup X) ≤ (PA : Subgroup A).comap psi
    exact Subgroup.map_le_iff_le_comap.mp hPmapSub.le
  let B : Subgroup X := Subgroup.normalizer ((P : Subgroup X) : Set X)
  have hFrattini : B ⊔ M = ⊤ := by
    simpa [B] using P.normalizer_sup_eq_top' hP_le_M
  have hMmap : M.map psi = (PA : Subgroup A) := by
    simpa [M] using
      Subgroup.map_comap_eq_self_of_surjective hpsiSurj (PA : Subgroup A)
  have hPAleBmap : (PA : Subgroup A) ≤ B.map psi := by
    rw [← hPmapSub]
    exact Subgroup.map_mono (by simpa [B] using (P : Subgroup X).le_normalizer)
  have hBmapTop : B.map psi = ⊤ := by
    have hmapFrattini : B.map psi ⊔ M.map psi = ⊤ := by
      rw [← Subgroup.map_sup, hFrattini,
        Subgroup.map_top_of_surjective psi hpsiSurj]
    rw [hMmap, sup_eq_left.mpr hPAleBmap] at hmapFrattini
    exact hmapFrattini
  let psiB : B →* A := psi.comp B.subtype
  have hpsiBSurj : Function.Surjective psiB := by
    intro a
    have ha : a ∈ B.map psi := by rw [hBmapTop]; trivial
    rcases ha with ⟨x, hxB, hxa⟩
    exact ⟨⟨x, hxB⟩, hxa⟩
  have hfixedPA : fixedPointSubgroup (PA : Subgroup A) N = ⊥ := by
    exact ii1Hering31_normal_nontrivial_fixedPointSubgroup_eq_bot A
      (ii1Hering31_range_twoPretransitive htwo hcomm)
      (PA : Subgroup A) hPAne
  have hpsiKer : psi.ker = pCore 2 X := by
    rw [show psi.ker = phi.ker by
      exact MonoidHom.ker_rangeRestrict phi]
    rw [ii1Hering31_conjNormal_ker_eq_centralizer]
    exact ii1Hering31_centralizer_involutionSubgroup_eq_twoCore
      hsmall htwo hrank hcomm
  let K : Subgroup B := psiB.ker
  have hKleQ : ∀ k : K, ((k : B) : X) ∈ pCore 2 X := by
    intro k
    rw [← hpsiKer, MonoidHom.mem_ker]
    simpa [K, psiB] using MonoidHom.mem_ker.mp k.property
  let kToQ : K →* pCore 2 X :=
    (B.subtype.comp K.subtype).codRestrict (pCore 2 X) hKleQ
  have hkToQinj : Function.Injective kToQ := by
    intro x y hxy
    have hxyX : ((x : B) : X) = ((y : B) : X) :=
      congrArg (fun q : pCore 2 X => (q : X)) hxy
    exact Subtype.ext (Subtype.ext hxyX)
  have hK2 : IsPGroup 2 K :=
    IsPGroup.of_injective (pCore_isPGroup (G := X) (p := 2))
      kToQ hkToQinj
  have hN2 : IsPGroup 2 N := by
    rw [IsPGroup.iff_orderOf]
    intro n
    by_cases hn : n = 1
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨1, by
        simpa using orderOf_eq_prime
          (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm n) hn⟩
  have hNPdisjoint : Disjoint N (P : Subgroup X) :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) N (P : Subgroup X)
      hN2 P.isPGroup'
  have hKbot : K = ⊥ := by
    by_contra hKne
    letI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
    have htwoDvdK : 2 ∣ Nat.card K := by
      rcases (IsPGroup.nontrivial_iff_card hK2).mp inferInstance with
        ⟨m, hm, hmcard⟩
      rw [hmcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hm)
    obtain ⟨z, hzOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := K) 2 htwoDvdK
    have hz : IsInvolution z := by
      have hzData := orderOf_eq_prime_iff.mp hzOrder
      exact ⟨hzData.2, hzData.1⟩
    let zB : B := (z : B)
    let zX : X := (zB : X)
    have hzB : IsInvolution zB :=
      IsInvolution.map_of_injective hz K.subtype K.subtype_injective
    have hzX : IsInvolution zX :=
      IsInvolution.map_of_injective hzB B.subtype B.subtype_injective
    have hzN : zX ∈ N := by
      change zX = 1 ∨ IsInvolution zX
      exact Or.inr hzX
    have hzCentralizesP : ∀ x : P, Commute zX (x : X) := by
      intro x
      let c : X := zX * (x : X) * zX⁻¹ * (x : X)⁻¹
      have hcP : c ∈ (P : Subgroup X) := by
        have hzNorm : zX ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) := zB.property
        have hconjP : zX * (x : X) * zX⁻¹ ∈ (P : Subgroup X) :=
          (Subgroup.mem_normalizer_iff.mp hzNorm (x : X)).mp x.property
        exact (P : Subgroup X).mul_mem hconjP ((P : Subgroup X).inv_mem x.property)
      have hcN : c ∈ N := by
        have hconjN : (x : X) * zX⁻¹ * (x : X)⁻¹ ∈ N :=
          (inferInstance : N.Normal).conj_mem zX⁻¹ (N.inv_mem hzN) (x : X)
        simpa [c, mul_assoc] using N.mul_mem hzN hconjN
      have hcOne : c = 1 :=
        Subgroup.disjoint_def.mp hNPdisjoint hcN hcP
      have heq := congrArg (fun y : X => y * (x : X) * zX) hcOne
      change zX * (x : X) = (x : X) * zX
      simpa [c, mul_assoc] using heq
    let zN : N := ⟨zX, hzN⟩
    have hzFixed : zN ∈ fixedPointSubgroup (PA : Subgroup A) N := by
      rw [FixedPoints.mem_subgroup]
      intro a
      have haMap : (a : A) ∈ (P : Subgroup X).map psi := by
        rw [hPmapSub]
        exact a.property
      rcases haMap with ⟨x, hxP, hxa⟩
      let xP : P := ⟨x, hxP⟩
      have hxComm : Commute zX x := hzCentralizesP xP
      have hconj : x * zX * x⁻¹ = zX := by
        calc
          x * zX * x⁻¹ = (zX * x) * x⁻¹ := by rw [hxComm.eq.symm]
          _ = zX := by simp [mul_assoc]
      have hphi : phi x = (a : A) := by
        exact congrArg Subtype.val hxa
      change ((a : A) : MulAut N) zN = zN
      rw [← hphi]
      apply Subtype.ext
      simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj
    rw [hfixedPA] at hzFixed
    have hzNOne : zN = 1 := by simpa using hzFixed
    exact hzX.ne_one (congrArg Subtype.val hzNOne)
  have hpsiBinj : Function.Injective psiB :=
    (MonoidHom.ker_eq_bot_iff psiB).mp hKbot
  have htwoDvdA : 2 ∣ Nat.card A := by rw [hAcard]; norm_num
  obtain ⟨tA, htAOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := A) 2 htwoDvdA
  have htA : IsInvolution tA := by
    have htAData := orderOf_eq_prime_iff.mp htAOrder
    exact ⟨htAData.2, htAData.1⟩
  obtain ⟨tB, htBmap⟩ := hpsiBSurj tA
  have htBNe : tB ≠ 1 := by
    intro htB
    apply htA.ne_one
    simpa [htB] using htBmap.symm
  have htBSq : tB ^ 2 = 1 := by
    apply hpsiBinj
    rw [map_pow, htBmap, htA.sq_eq_one, map_one]
  have htB : IsInvolution tB := ⟨htBNe, htBSq⟩
  have htX : IsInvolution ((tB : B) : X) :=
    IsInvolution.map_of_injective htB B.subtype B.subtype_injective
  have htN : ((tB : B) : X) ∈ N := by
    change ((tB : B) : X) = 1 ∨ IsInvolution ((tB : B) : X)
    exact Or.inr htX
  have htKer : ((tB : B) : X) ∈ psi.ker := by
    rw [hpsiKer]
    exact ii1Hering31InvolutionSubgroup_le_twoCore hcomm htN
  have htMapOne : psiB tB = 1 := by
    change psi ((tB : B) : X) = 1
    exact MonoidHom.mem_ker.mp htKer
  exact htA.ne_one (by rw [← htBmap, htMapOne])

private theorem ii1Hering31_commutatorAction_mem_of_mem_normalizer
    {N : Type*} [Group N]
    (A : Subgroup (MulAut N)) (R : Subgroup A)
    (z : A) (hzR : z ∈ Subgroup.normalizer (R : Set A))
    {c : N} (hc : c ∈ commutatorAction (A := R) (G := N)) :
    z • c ∈ commutatorAction (A := R) (G := N) := by
  rw [commutatorAction_eq_closure] at hc ⊢
  apply Subgroup.closure_induction (p := fun c _ => z • c ∈
    Subgroup.closure {x : N | ∃ r : R, ∃ n : N, x = n⁻¹ * r • n}) _ _ _ _ hc
  · intro x hx
    obtain ⟨r, n, rfl⟩ := hx
    let r' : R := ⟨z * (r : A) * z⁻¹,
      (Subgroup.mem_normalizer_iff.mp hzR (r : A)).mp r.property⟩
    apply Subgroup.subset_closure
    refine ⟨r', z • n, ?_⟩
    simp [r', smul_mul', smul_inv', mul_smul, mul_assoc]
    change (r : A) • n = (r : A) • n
    rfl
  · simp
  · intro x y _ _ hx hy
    simpa [smul_mul'] using
      (Subgroup.closure {x : N | ∃ r : R, ∃ n : N, x = n⁻¹ * r • n}).mul_mem hx hy
  · intro x _ hx
    simpa [smul_inv'] using
      (Subgroup.closure {x : N | ∃ r : R, ∃ n : N, x = n⁻¹ * r • n}).inv_mem hx

private theorem ii1Hering31_normal_pSubgroup_acts_trivially
    {p : ℕ} [Fact (Nat.Prime p)]
    {A α : Type*} [Group A] [Finite A] [MulAction A α] [Finite α]
    (K : Subgroup A) [K.Normal] (hK : IsPGroup p K)
    (e : α) (hdiv : p ∣ Nat.card α)
    (he : ∀ a : A, a • e = e)
    (htrans : ∀ x y : α, x ≠ e → y ≠ e → ∃ a : A, a • x = y) :
    ∀ k : K, ∀ x : α, (k : A) • x = x := by
  letI : MulAction K α := MulAction.compHom α K.subtype
  obtain ⟨b, hbfix, hbne⟩ :=
    hK.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      α hdiv (a := e) (by
        intro k
        exact he k)
  intro k x
  by_cases hx : x = e
  · subst x
    exact he k
  obtain ⟨a, ha⟩ := htrans b x (fun h => hbne h.symm) hx
  rw [← ha]
  let k' : K := ⟨a⁻¹ * (k : A) * a,
    by
      simpa only [inv_inv] using
        (inferInstance : K.Normal).conj_mem (k : A) k.property a⁻¹⟩
  have hkMul : (k : A) * a = a * (k' : A) := by
    change (k : A) * a = a * (a⁻¹ * (k : A) * a)
    group
  have hbk' := hbfix k'
  change (k' : A) • b = b at hbk'
  rw [← mul_smul, hkMul, mul_smul, hbk']

/-- An odd-prime-order element of the faithful Hering conjugation image fixes
at most one involution (and the identity) in the elementary abelian normal
subgroup. -/
public theorem ii1Hering31_odd_prime_fixed_card_le_two
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
    let phi : X →* MulAut N := MulAut.conjNormal (H := N)
    let A : Subgroup (MulAut N) := phi.range
    ∀ r : A, Nat.Prime (orderOf r) → orderOf r ≠ 2 →
      Nat.card (fixedPointSubgroup (Subgroup.zpowers r) N) ≤ 2 := by
  classical
  dsimp only
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  intro r hrPrime hrTwo
  let R : Subgroup A := Subgroup.zpowers r
  let F : Subgroup N := fixedPointSubgroup R N
  have hN2 : IsPGroup 2 N := by
    rw [IsPGroup.iff_orderOf]
    intro n
    by_cases hn : n = 1
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨1, by
        simpa using (orderOf_eq_prime
          (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm n) hn)⟩
  have hF2 : IsPGroup 2 F := hN2.to_subgroup F
  change Nat.card F ≤ 2
  by_contra hcard
  have hFgt : 2 < Nat.card F := by omega
  rcases IsPGroup.iff_card.mp hF2 with ⟨k, hk⟩
  have hkge : 2 ≤ k := by
    by_contra hknot
    have hklt : k < 2 := Nat.lt_of_not_ge hknot
    interval_cases k
    · simp only [pow_zero] at hk
      omega
    · simp only [pow_one] at hk
      omega
  have hfour : 2 ^ 2 ≤ Nat.card F := by
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hkge
  obtain ⟨V0, hV0card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hF2 hfour
  let V : Subgroup N := V0.map F.subtype
  have hVcard : Nat.card V = 4 := by
    rw [show Nat.card V = Nat.card V0 by
      exact Subgroup.card_map_of_injective
        (K := V0) (f := F.subtype) F.subtype_injective]
    norm_num at hV0card ⊢
    exact hV0card
  let VX : Subgroup X := V.map N.subtype
  have hVXcard : Nat.card VX = 4 := by
    rw [show Nat.card VX = Nat.card V by
      exact Subgroup.card_map_of_injective
        (K := V) (f := N.subtype) N.subtype_injective]
    exact hVcard
  have hVXsq : ∀ v : VX, v ^ 2 = 1 := by
    intro v
    rcases v.property with ⟨n, hn, hnv⟩
    apply Subtype.ext
    change (v : X) ^ 2 = 1
    rw [← hnv]
    exact congrArg N.subtype
      (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm n)
  have hC2 : IsPGroup 2 (Subgroup.centralizer (VX : Set X)) :=
    ii1Hering31_four_centralizer hsmall htwo hcomm VX hVXcard hVXsq
  obtain ⟨x, hx⟩ := r.property
  have hxC : x ∈ Subgroup.centralizer (VX : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases hv with ⟨n, hnV, hnv⟩
    rcases hnV with ⟨f, hfV0, hfn⟩
    have hfF : (f : N) ∈ F := (f : F).property
    have hrFixF : (⟨r, Subgroup.mem_zpowers r⟩ : R) • (f : N) = f := by
      exact (FixedPoints.mem_subgroup R N (f : N)).mp hfF
        ⟨r, Subgroup.mem_zpowers r⟩
    have hrFixN : (r : MulAut N) (f : N) = f := hrFixF
    have hphiFix : phi x (f : N) = f := by
      rw [hx]
      exact hrFixN
    have hconj : x * (f : X) * x⁻¹ = (f : X) := by
      simpa [phi, MulAut.conjNormal_apply, MulAut.conj_apply] using
        congrArg N.subtype hphiFix
    have hcommX : (f : X) * x = x * (f : X) := by
      have := congrArg (fun y : X => y * x) hconj
      have htemp : x * (f : X) = (f : X) * x := by
        simpa [mul_assoc] using this
      exact htemp.symm
    rw [← hnv, ← hfn]
    exact hcommX
  let xC : Subgroup.centralizer (VX : Set X) := ⟨x, hxC⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hC2) xC
  have hxOrder : orderOf x = 2 ^ m := by
    simpa [xC] using (Subgroup.orderOf_coe xC).trans hm
  have hrDvd : orderOf r ∣ orderOf x := by
    rw [← Subgroup.orderOf_coe r]
    change orderOf (r : MulAut N) ∣ orderOf x
    rw [← hx]
    exact orderOf_map_dvd phi x
  rw [hxOrder] at hrDvd
  have hrDvdTwo : orderOf r ∣ 2 := hrPrime.dvd_of_dvd_pow hrDvd
  exact hrTwo ((Nat.prime_dvd_prime_iff_eq hrPrime Nat.prime_two).mp hrDvdTwo)

/-- In Hering's faithful elementary-abelian action, every involution is a
transvection: its fixed subgroup has index at most two. -/
public theorem ii1Hering31_involution_fixed_index_le_two
    {N : Type u} [Group N] [Finite N]
    (hsq : ∀ n : N, n ^ 2 = 1)
    (hcomm : ∀ x y : N, Commute x y)
    (A : Subgroup (MulAut N))
    (htwo :
      letI : MulAction A (II1Hering31Nonidentity N) :=
        ii1Hering31NonidentityAction N A
      MulAction.IsMultiplyPretransitive A
        (II1Hering31Nonidentity N) 2)
    (hcard : 4 ≤ Nat.card N)
    (hodd : ∀ r : A, Nat.Prime (orderOf r) → orderOf r ≠ 2 →
      Nat.card (fixedPointSubgroup (Subgroup.zpowers r) N) ≤ 2)
    (z : A) (hz : IsInvolution z) :
    (fixedPointSubgroup (Subgroup.zpowers z) N).index ≤ 2 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsMulCommutative N := ⟨⟨fun x y => (hcomm x y).eq⟩⟩
  letI : CommGroup N := IsMulCommutative.instCommGroup
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  have hN2 : IsPGroup 2 N := by
    rw [IsPGroup.iff_orderOf]
    intro n
    by_cases hn : n = 1
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨1, by simpa using orderOf_eq_prime (hsq n) hn⟩
  have hzAutNe : (z : MulAut N) ≠ 1 := by
    intro h
    exact hz.ne_one (Subtype.ext h)
  have hnmove : ∃ n : N, (z : MulAut N) n ≠ n := by
    by_contra hn
    push_neg at hn
    apply hzAutNe
    apply MulEquiv.ext
    intro n
    simpa using hn n
  obtain ⟨n, hnmove⟩ := hnmove
  let a : N := z • n * n⁻¹
  have haNe : a ≠ 1 := by
    intro ha
    apply hnmove
    have := congrArg (fun x : N => x * n) ha
    change z • n = n
    simpa [a, mul_assoc] using this
  have haSq : a ^ 2 = 1 := hsq a
  have haInv : IsInvolution a := ⟨haNe, haSq⟩
  have hza : z • a = a := by
    have hnInv : n⁻¹ = n :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq n)
    have hznInv : (z • n)⁻¹ = z • n :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq (z • n))
    dsimp [a]
    rw [smul_mul', smul_inv', ← mul_smul, show z * z = 1 by
      simpa [pow_two] using hz.sq_eq_one, one_smul,
      hnInv, hznInv]
    exact (hcomm n (z • n)).eq
  let H : Subgroup A := MulAction.stabilizer A a
  let zH : H := ⟨z, MulAction.mem_stabilizer_iff.mpr hza⟩
  have hzH : IsInvolution zH := by
    refine ⟨?_, ?_⟩
    · intro h
      exact hz.ne_one (congrArg Subtype.val h)
    · apply Subtype.ext
      exact hz.sq_eq_one
  have hzHcore : zH ∈ pCore 2 H := by
    by_contra hzCore
    obtain ⟨q, hq, hq2, rH, hrOrder, hrInv⟩ :=
      ii1Hering31_odd_rotation zH hzH hzCore
    let r : A := (rH : A)
    have hrOrderA : orderOf r = q := by
      simpa [r] using (Subgroup.orderOf_coe rH).trans hrOrder
    have hrPrime : Nat.Prime (orderOf r) := hrOrderA.symm ▸ hq
    have hrTwo : orderOf r ≠ 2 := by simpa [hrOrderA] using hq2
    let R : Subgroup A := Subgroup.zpowers r
    let F : Subgroup N := fixedPointSubgroup R N
    let C : Subgroup N := commutatorAction (A := R) (G := N)
    have hra : r • a = a := rH.property
    have haF : a ∈ F := by
      change a ∈ fixedPointSubgroup R N
      rw [FixedPoints.mem_subgroup]
      intro s
      rcases Subgroup.mem_zpowers_iff.mp s.property with ⟨k, hk⟩
      change (s : A) • a = a
      rw [← hk]
      exact MulAction.mem_fixedBy_zpow (show a ∈ MulAction.fixedBy N r from hra) k
    have hLleF : Subgroup.zpowers a ≤ F :=
      Subgroup.zpowers_le.mpr haF
    have hLcard : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime haSq haNe
    have hFcardLe : Nat.card F ≤ 2 := by
      simpa [F, R] using hodd r hrPrime hrTwo
    have hFcardGe : 2 ≤ Nat.card F := by
      rw [← hLcard]
      exact Nat.card_le_card_of_injective
        (Subgroup.inclusion hLleF) (Subgroup.inclusion_injective hLleF)
    have hFcard : Nat.card F = 2 := by omega
    have hFeq : F = Subgroup.zpowers a := by
      symm
      apply Subgroup.eq_of_le_of_card_ge hLleF
      simpa [hFcard, hLcard]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    have hcop : Nat.Coprime (Nat.card R) (Nat.card N) := by
      change Nat.Coprime (Nat.card (Subgroup.zpowers r)) (Nat.card N)
      rw [Nat.card_zpowers, hrOrderA, hk]
      exact ((Nat.coprime_primes hq Nat.prime_two).2 hq2).pow_right k
    have hcompl : IsCompl F C := by
      simpa [F, C] using
        (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
          (G := N) (A := R) (by infer_instance) hcop (by infer_instance))
    have hrInvA : z * r * z⁻¹ = r⁻¹ := by
      have h := congrArg (fun x : H => (x : A)) hrInv
      simpa [r, rightConjugateElem, hz.inv_eq_self, hzH.inv_eq_self] using h
    have hzR : z ∈ Subgroup.normalizer (R : Set A) := by
      simpa [R] using theorem4b_mem_normalizer_zpowers_of_inverts hz hrInvA
    have hnTop : n ∈ F ⊔ C := by rw [hcompl.sup_eq_top]; trivial
    rcases (Subgroup.mem_sup_of_normal_left (s := F) (t := C)).mp hnTop with
      ⟨f, hfF, c, hcC, hfc⟩
    have hzf : z • f = f := by
      rw [hFeq] at hfF
      rcases Subgroup.mem_zpowers_iff.mp hfF with ⟨m, rfl⟩
      rw [smul_zpow', hza]
    have hzcC : z • c ∈ C := by
      exact ii1Hering31_commutatorAction_mem_of_mem_normalizer A R z hzR hcC
    have haC : a ∈ C := by
      have haEq : a = (z • c) * c⁻¹ := by
        dsimp [a]
        rw [← hfc]
        simp only [smul_mul', mul_inv_rev, hzf]
        change (f * (z • c)) * (c⁻¹ * f⁻¹) = (z • c) * c⁻¹
        calc
          (f * (z • c)) * (c⁻¹ * f⁻¹) =
              (f * f⁻¹) * ((z • c) * c⁻¹) := by ac_rfl
          _ = (z • c) * c⁻¹ := by simp
      rw [haEq]
      exact C.mul_mem hzcC (C.inv_mem hcC)
    have haInf : a ∈ F ⊓ C := ⟨haF, haC⟩
    rw [hcompl.inf_eq_bot] at haInf
    exact haNe (by simpa using haInf)
  let L : Subgroup N := Subgroup.zpowers a
  have hLcard : Nat.card L = 2 := by
    change Nat.card (Subgroup.zpowers a) = 2
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime haSq haNe
  have hfixL : ∀ h : H, ∀ {y : N}, y ∈ L → h • y = y := by
    intro h y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨m, hm⟩
    have haFix : h • a = a := h.property
    rw [← hm, smul_zpow', haFix]
  let hLinv : IsInvariant H N L := by
    refine ⟨?_⟩
    intro h x
    constructor
    · intro hx
      rw [hfixL h hx]
      exact hx
    · intro hx
      have heq : x = h • x := by
        simpa using hfixL h⁻¹ hx
      rwa [heq]
  letI : IsInvariant H N L := hLinv
  letI : L.Normal := by infer_instance
  letI : MulAction.QuotientAction H L :=
    quotientAction_of_isInvariant (A := H) L hLinv
  letI : MulDistribMulAction H (N ⧸ L) :=
    quotientMulDistribMulAction (A := H) (G := N) L hLinv
  have hLneTop : L ≠ ⊤ := by
    intro htop
    have hNcard : Nat.card N = 2 := by simpa [htop] using hLcard
    omega
  letI : Nontrivial (N ⧸ L) := QuotientGroup.nontrivial_iff.mpr hLneTop
  have hQ2 : IsPGroup 2 (N ⧸ L) := hN2.to_quotient L
  have htwoDvdQ : 2 ∣ Nat.card (N ⧸ L) := by
    rcases (IsPGroup.nontrivial_iff_card hQ2).mp inferInstance with
      ⟨m, hm, hmcard⟩
    rw [hmcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hm)
  let K : Subgroup H := pCore 2 H
  letI : K.Normal := by simpa [K] using pCore_normal (G := H) (p := 2)
  have hK2 : IsPGroup 2 K := by
    simpa [K] using pCore_isPGroup (G := H) (p := 2)
  have htrans : ∀ b c : N ⧸ L, b ≠ 1 → c ≠ 1 →
      ∃ h : H, h • b = c := by
    intro bbar cbar hbbar hcbar
    obtain ⟨b0, rfl⟩ := QuotientGroup.mk'_surjective L bbar
    obtain ⟨c0, rfl⟩ := QuotientGroup.mk'_surjective L cbar
    have hb0L : b0 ∉ L := by
      intro hb0
      apply hbbar
      exact (QuotientGroup.eq_one_iff (N := L) b0).mpr hb0
    have hc0L : c0 ∉ L := by
      intro hc0
      apply hcbar
      exact (QuotientGroup.eq_one_iff (N := L) c0).mpr hc0
    have hb0Ne : b0 ≠ 1 := fun h => hb0L (h.symm ▸ L.one_mem)
    have hc0Ne : c0 ≠ 1 := fun h => hc0L (h.symm ▸ L.one_mem)
    have hb0a : b0 ≠ a := by
      intro h
      apply hb0L
      rw [h]
      exact Subgroup.mem_zpowers a
    have hc0a : c0 ≠ a := by
      intro h
      apply hc0L
      rw [h]
      exact Subgroup.mem_zpowers a
    let aI : II1Hering31Nonidentity N := ⟨a, haNe⟩
    let bI : II1Hering31Nonidentity N := ⟨b0, hb0Ne⟩
    let cI : II1Hering31Nonidentity N := ⟨c0, hc0Ne⟩
    have htwo' : ∀ {aa bb cc dd : II1Hering31Nonidentity N},
        aa ≠ bb → cc ≠ dd →
          ∃ g : A, g • aa = cc ∧ g • bb = dd :=
      MulAction.is_two_pretransitive_iff.mp htwo
    obtain ⟨g, hga, hgb⟩ :=
      htwo' (aa := aI) (bb := bI) (cc := aI) (dd := cI)
        (fun h => hb0a (congrArg Subtype.val h).symm)
        (fun h => hc0a (congrArg Subtype.val h).symm)
    have hgaN : g • a = a := congrArg Subtype.val hga
    let gH : H := ⟨g, MulAction.mem_stabilizer_iff.mpr hgaN⟩
    refine ⟨gH, ?_⟩
    change QuotientGroup.mk' L (g • b0) = QuotientGroup.mk' L c0
    exact congrArg (QuotientGroup.mk' L) (congrArg Subtype.val hgb)
  have hKtriv : ∀ k : K, ∀ x : N ⧸ L, (k : H) • x = x :=
    ii1Hering31_normal_pSubgroup_acts_trivially K hK2 (1 : N ⧸ L)
      htwoDvdQ (fun a => smul_one a) htrans
  let zK : K := ⟨zH, hzHcore⟩
  have hzQuot : ∀ x : N, QuotientGroup.mk' L (z • x) =
      QuotientGroup.mk' L x := by
    intro x
    have hzfix := hKtriv zK (QuotientGroup.mk' L x)
    simpa [zK, zH] using hzfix
  let delta : N →* N :=
    { toFun := fun x => z • x * x⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [smul_mul', mul_inv_rev]
        ac_rfl }
  have hdeltaRange : delta.range ≤ L := by
    rintro d ⟨x, rfl⟩
    have hq := hzQuot x
    simpa [delta, div_eq_mul_inv] using
      (QuotientGroup.eq_iff_div_mem (N := L) (x := z • x) (y := x)).mp hq
  have hdeltaKer : delta.ker = fixedPointSubgroup (Subgroup.zpowers z) N := by
    ext x
    constructor
    · intro hx
      have hzx : z • x = x := by
        rw [MonoidHom.mem_ker] at hx
        have := congrArg (fun y : N => y * x) hx
        simpa [delta, mul_assoc] using this
      rw [FixedPoints.mem_subgroup]
      intro s
      rcases Subgroup.mem_zpowers_iff.mp s.property with ⟨m, hm⟩
      change (s : A) • x = x
      rw [← hm]
      exact MulAction.mem_fixedBy_zpow
        (show x ∈ MulAction.fixedBy N z from hzx) m
    · intro hx
      rw [FixedPoints.mem_subgroup] at hx
      have hzx := hx ⟨z, Subgroup.mem_zpowers z⟩
      change z • x = x at hzx
      rw [MonoidHom.mem_ker]
      simpa [delta, hzx]
  rw [← hdeltaKer, Subgroup.index_ker]
  rw [← hLcard]
  exact Nat.card_le_card_of_injective
    (Subgroup.inclusion hdeltaRange)
    (Subgroup.inclusion_injective hdeltaRange)

/-- Hering's Lemma 3.4: in a cardinal-minimal rank-two counterexample, the
elementary abelian subgroup consisting of the identity and all involutions has
cardinality eight. -/
public theorem ii1Hering31_involution_subgroup_card
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    Nat.card (ii1Hering31InvolutionSubgroup X hcomm) = 8 := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  have hNcardGe : 4 ≤ Nat.card N :=
    ii1Hering31InvolutionSubgroup_card_ge_four hrank hcomm
  have hNcardNe : Nat.card N ≠ 4 :=
    ii1Hering31_four_card_ne hsmall htwo hrank hcomm
  have hN2 : IsPGroup 2 N := by
    rw [IsPGroup.iff_orderOf]
    intro n
    by_cases hn : n = 1
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨1, by
        simpa using orderOf_eq_prime
          (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm n) hn⟩
  have hfourPow : 2 ^ 2 ≤ Nat.card N := by
    norm_num at hNcardGe ⊢
    exact hNcardGe
  obtain ⟨V, hVcardPow⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hN2 hfourPow
  have hVcard : Nat.card V = 4 := by
    norm_num at hVcardPow ⊢
    exact hVcardPow
  obtain ⟨t, r, ht, hrOrder, htr⟩ :=
    ii1Hering31_four_normalizer_dihedral_three hsmall htwo hcomm V hVcard
  let tA : A := (t : A)
  let rA : A := (r : A)
  have htA : IsInvolution tA := by
    refine ⟨?_, ?_⟩
    · intro h
      apply ht.ne_one
      apply Subtype.ext
      exact h
    · simpa [tA] using congrArg Subtype.val ht.sq_eq_one
  have hrOrderA : orderOf rA = 3 := by
    simpa [rA] using (Subgroup.orderOf_coe r).trans hrOrder
  have htrA : tA⁻¹ * rA * tA = rA⁻¹ := by
    change t⁻¹ * r * t = r⁻¹ at htr
    apply Subtype.ext
    have h0 := congrArg Subtype.val htr
    have h := congrArg
      (Subgroup.subtype (MulAut.conjNormal (H := N)).range) h0
    simpa [tA, rA, A, phi, N] using h
  have htrA' : tA * rA * tA = rA⁻¹ := by
    simpa [htA.inv_eq_self] using htrA
  let uA : A := tA * rA
  have huSq : uA ^ 2 = 1 := by
    calc
      uA ^ 2 = (tA * rA * tA) * rA := by
        simp [uA, pow_two, mul_assoc]
      _ = rA⁻¹ * rA := by rw [htrA']
      _ = 1 := inv_mul_cancel rA
  have huNe : uA ≠ 1 := by
    intro hu
    have hEq : tA = rA⁻¹ := (mul_eq_one_iff_eq_inv).mp hu
    have horders := congrArg orderOf hEq
    rw [orderOf_inv, orderOf_eq_prime htA.sq_eq_one htA.ne_one,
      hrOrderA] at horders
    omega
  have hu : IsInvolution uA := ⟨huNe, huSq⟩
  have hodd : ∀ q : A, Nat.Prime (orderOf q) → orderOf q ≠ 2 →
      Nat.card (fixedPointSubgroup (Subgroup.zpowers q) N) ≤ 2 :=
    ii1Hering31_odd_prime_fixed_card_le_two hsmall htwo hcomm
  have htwoA : MulAction.IsMultiplyPretransitive A
      (II1Hering31Nonidentity N) 2 :=
    ii1Hering31_range_twoPretransitive htwo hcomm
  let T : Subgroup N := fixedPointSubgroup (Subgroup.zpowers tA) N
  let U : Subgroup N := fixedPointSubgroup (Subgroup.zpowers uA) N
  let R : Subgroup N := fixedPointSubgroup (Subgroup.zpowers rA) N
  have hTindex : T.index ≤ 2 := by
    simpa [T] using ii1Hering31_involution_fixed_index_le_two
      (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm)
      (ii1Hering31InvolutionSubgroup_commute hcomm) A htwoA hNcardGe hodd tA htA
  have hUindex : U.index ≤ 2 := by
    simpa [U] using ii1Hering31_involution_fixed_index_le_two
      (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm)
      (ii1Hering31InvolutionSubgroup_commute hcomm) A htwoA hNcardGe hodd uA hu
  have hRcard : Nat.card R ≤ 2 := by
    simpa [R] using hodd rA (hrOrderA.symm ▸ Nat.prime_three) (by omega)
  have hrEq : rA = tA * uA := by
    symm
    calc
      tA * uA = (tA * tA) * rA := by simp [uA, mul_assoc]
      _ = tA ^ 2 * rA := by rw [pow_two]
      _ = rA := by rw [htA.sq_eq_one, one_mul]
  have hInfLe : T ⊓ U ≤ R := by
    intro n hn
    have htFix : tA • (n : N) = n := by
      exact (FixedPoints.mem_subgroup (Subgroup.zpowers tA) N n).mp hn.1
        ⟨tA, Subgroup.mem_zpowers tA⟩
    have huFix : uA • (n : N) = n := by
      exact (FixedPoints.mem_subgroup (Subgroup.zpowers uA) N n).mp hn.2
        ⟨uA, Subgroup.mem_zpowers uA⟩
    have hrFix : rA • (n : N) = n := by
      rw [hrEq, mul_smul, huFix, htFix]
    rw [FixedPoints.mem_subgroup]
    intro s
    rcases Subgroup.mem_zpowers_iff.mp s.property with ⟨k, hk⟩
    change (s : A) • (n : N) = n
    rw [← hk]
    exact MulAction.mem_fixedBy_zpow
      (show (n : N) ∈ MulAction.fixedBy N rA from hrFix) k
  have hInfIndex : (T ⊓ U).index ≤ 4 := by
    calc
      (T ⊓ U).index ≤ T.index * U.index := Subgroup.index_inf_le
      _ ≤ 2 * 2 := Nat.mul_le_mul hTindex hUindex
      _ = 4 := by norm_num
  have hInfCard : Nat.card (T ⊓ U : Subgroup N) ≤ Nat.card R :=
    Nat.card_le_card_of_injective
      (Subgroup.inclusion hInfLe) (Subgroup.inclusion_injective hInfLe)
  have hNcardLe : Nat.card N ≤ 8 := by
    calc
      Nat.card N = (T ⊓ U).index * Nat.card (T ⊓ U : Subgroup N) :=
        (T ⊓ U).index_mul_card.symm
      _ ≤ 4 * 2 := Nat.mul_le_mul hInfIndex (hInfCard.trans hRcard)
      _ = 8 := by norm_num
  have hfourDvd : 4 ∣ Nat.card N := by
    rw [← hVcard]
    exact Subgroup.card_subgroup_dvd_card V
  rcases hfourDvd with ⟨k, hk⟩
  change Nat.card N = 8
  rw [hk] at hNcardGe hNcardNe hNcardLe ⊢
  omega

/-! ## Hering's Lemma 3.5: recognition of the faithful quotient -/

/-- The automorphism group of an elementary abelian group of order eight has
order `168`. -/
private theorem ii1Hering31_mulAut_card_eq_168
    {N : Type*} [Group N] [Finite N]
    [IsElementaryAbelian 2 N]
    (hcard : Nat.card N = 8) :
    Nat.card (MulAut N) = 168 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsMulCommutative N :=
    (inferInstance : IsElementaryAbelian 2 N).toIsMulCommutative
  letI : CommGroup N := IsMulCommutative.instCommGroup
  let Q := Additive N
  letI : AddCommGroup Q := Additive.addCommGroup
  letI : Module (ZMod 2) Q := inferInstance
  letI : Finite Q := inferInstance
  letI : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  let eAdd : MulAut N ≃* Multiplicative (AddAut Q) :=
    (AddAutAdditive N).toMultiplicative.symm
  let eAddLin : Multiplicative (AddAut Q) ≃* (Q ≃ₗ[ZMod 2] Q) :=
    { toFun := fun a =>
        (a : AddAut Q).toLinearEquiv (fun c x => by
          change (a : AddAut Q) (c • x) = c • (a : AddAut Q) x
          exact ZMod.map_smul (a : AddAut Q).toAddMonoidHom c x)
      invFun := fun a => Multiplicative.ofAdd a.toAddEquiv
      left_inv := by
        intro a
        apply Multiplicative.toAdd.injective
        ext x
        rfl
      right_inv := by
        intro a
        ext x
        rfl
      map_mul' := by
        intro a b
        ext x
        rfl }
  let eLin : Multiplicative (AddAut Q) ≃*
      LinearMap.GeneralLinearGroup (ZMod 2) Q :=
    eAddLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Q).symm
  let n := Module.finrank (ZMod 2) Q
  let basis : Module.Basis (Fin n) (ZMod 2) Q :=
    Module.finBasis (ZMod 2) Q
  let eMatrix : MulAut N ≃* GL (Fin n) (ZMod 2) :=
    (eAdd.trans eLin).trans (Matrix.GeneralLinearGroup.toLin' basis).symm
  have hcardQ : Nat.card Q = 2 ^ n := by
    simpa [Q, n, ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Q))
  have hn : n = 3 := by
    have hpow : 2 ^ n = 8 := hcardQ.symm.trans (by
      simpa [Q] using
        (Nat.card_congr (Additive.ofMul (α := N))).symm.trans hcard)
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    norm_num [Nat.choose]
    exact hpow
  rw [Nat.card_congr eMatrix.toEquiv, hn, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- The automorphism group of an elementary abelian group of order eight is
`GL(3,2)`. -/
private theorem ii1Hering31_mulAut_equiv_GL3
    {N : Type*} [Group N] [Finite N]
    [IsElementaryAbelian 2 N]
    (hcard : Nat.card N = 8) :
    Nonempty (MulAut N ≃* GL (Fin 3) (ZMod 2)) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsMulCommutative N :=
    (inferInstance : IsElementaryAbelian 2 N).toIsMulCommutative
  letI : CommGroup N := IsMulCommutative.instCommGroup
  let Q := Additive N
  letI : AddCommGroup Q := Additive.addCommGroup
  letI : Module (ZMod 2) Q := inferInstance
  letI : Finite Q := inferInstance
  letI : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  let eAdd : MulAut N ≃* Multiplicative (AddAut Q) :=
    (AddAutAdditive N).toMultiplicative.symm
  let eAddLin : Multiplicative (AddAut Q) ≃* (Q ≃ₗ[ZMod 2] Q) :=
    { toFun := fun a =>
        (a : AddAut Q).toLinearEquiv (fun c x => by
          change (a : AddAut Q) (c • x) = c • (a : AddAut Q) x
          exact ZMod.map_smul (a : AddAut Q).toAddMonoidHom c x)
      invFun := fun a => Multiplicative.ofAdd a.toAddEquiv
      left_inv := by
        intro a
        apply Multiplicative.toAdd.injective
        ext x
        rfl
      right_inv := by
        intro a
        ext x
        rfl
      map_mul' := by
        intro a b
        ext x
        rfl }
  let eLin : MulAut N ≃*
      LinearMap.GeneralLinearGroup (ZMod 2) Q :=
    (eAdd.trans eAddLin).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Q).symm
  let n := Module.finrank (ZMod 2) Q
  let basis : Module.Basis (Fin n) (ZMod 2) Q :=
    Module.finBasis (ZMod 2) Q
  let eMatrix : MulAut N ≃* GL (Fin n) (ZMod 2) :=
    eLin.trans (Matrix.GeneralLinearGroup.toLin' basis).symm
  have hcardQ : Nat.card Q = 2 ^ n := by
    simpa [Q, n, ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Q))
  have hn : n = 3 := by
    have hpow : 2 ^ n = 8 := hcardQ.symm.trans (by
      simpa [Q] using
        (Nat.card_congr (Additive.ofMul (α := N))).symm.trans hcard)
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    norm_num
    exact hpow
  exact ⟨hn ▸ eMatrix⟩

/-- Coordinates on an elementary abelian group of order eight. -/
private theorem ii1Hering31_orderEight_equiv_abelianV
    {N : Type*} [Group N] [Finite N]
    [IsElementaryAbelian 2 N] (hcard : Nat.card N = 8) :
    Nonempty (N ≃* II1Hering31AbelianV) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsMulCommutative N :=
    (inferInstance : IsElementaryAbelian 2 N).toIsMulCommutative
  letI : CommGroup N := IsMulCommutative.instCommGroup
  let Q := Additive N
  letI : AddCommGroup Q := Additive.addCommGroup
  letI : Module (ZMod 2) Q := inferInstance
  letI : Finite Q := inferInstance
  letI : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  let n := Module.finrank (ZMod 2) Q
  let basis : Module.Basis (Fin n) (ZMod 2) Q :=
    Module.finBasis (ZMod 2) Q
  have hcardQ : Nat.card Q = 2 ^ n := by
    simpa [Q, n, ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Q))
  have hn : n = 3 := by
    have hpow : 2 ^ n = 8 :=
      hcardQ.symm.trans (by
        simpa [Q] using
          (Nat.card_congr (Additive.ofMul (α := N))).symm.trans hcard)
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    norm_num
    exact hpow
  let basis3 : Module.Basis (Fin 3) (ZMod 2) Q := hn ▸ basis
  exact ⟨AddEquiv.toMultiplicativeRight basis3.equivFun.toAddEquiv⟩

/-! ### The involution class of `GL(3,2)` -/

private abbrev II1Hering31RawV := Fin 3 → ZMod 2

private abbrev II1Hering31RawM := Matrix (Fin 3) (Fin 3) (ZMod 2)

private def ii1Hering31RawVectors : List II1Hering31RawV :=
  [![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
    ![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

private def ii1Hering31RawApply
    (A : II1Hering31RawM) (x : II1Hering31RawV) : II1Hering31RawV :=
  fun i => A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2

private def ii1Hering31RawMul
    (A B : II1Hering31RawM) : II1Hering31RawM :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

private def ii1Hering31RawDet (A : II1Hering31RawM) : ZMod 2 :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
    - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
    + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

private def ii1Hering31RawN
    (A : II1Hering31RawM) (x : II1Hering31RawV) : II1Hering31RawV :=
  ii1Hering31RawApply A x + x

private def ii1Hering31RawW (A : II1Hering31RawM) : II1Hering31RawV :=
  (ii1Hering31RawVectors.find? fun w =>
    decide (ii1Hering31RawN A w ≠ 0)).getD 0

private def ii1Hering31RawU (A : II1Hering31RawM) : II1Hering31RawV :=
  ii1Hering31RawN A (ii1Hering31RawW A)

private def ii1Hering31RawFixedVector
    (A : II1Hering31RawM) : II1Hering31RawV :=
  (ii1Hering31RawVectors.find? fun v =>
    decide (ii1Hering31RawApply A v = v ∧ v ≠ 0 ∧
      v ≠ ii1Hering31RawU A)).getD 0

/-- The columns are an image vector, one of its preimages under `A - 1`,
and an independent fixed vector. -/
private def ii1Hering31RawConjugator
    (A : II1Hering31RawM) : II1Hering31RawM :=
  fun i j =>
    ![ii1Hering31RawU A, ii1Hering31RawW A,
      ii1Hering31RawFixedVector A] j i

private def ii1Hering31RawTransvection : II1Hering31RawM :=
  !![(1 : ZMod 2), 1, 0; 0, 1, 0; 0, 0, 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A pruned finite check: every nonidentity involutory invertible matrix over
`F₂` admits the explicit basis change selected above.  This uses ordinary
kernel reduction, never native evaluation. -/
private theorem ii1Hering31_raw_involution_conjugacy_check :
    ∀ A : II1Hering31RawM,
      A = 1 ∨ ii1Hering31RawMul A A ≠ 1 ∨
        ii1Hering31RawDet A = 0 ∨
          ii1Hering31RawDet (ii1Hering31RawConjugator A) ≠ 0 ∧
            ii1Hering31RawMul A (ii1Hering31RawConjugator A) =
              ii1Hering31RawMul (ii1Hering31RawConjugator A)
                ii1Hering31RawTransvection := by
  let P := fun A : II1Hering31RawM =>
    A = 1 ∨ ii1Hering31RawMul A A ≠ 1 ∨
      ii1Hering31RawDet A = 0 ∨
        ii1Hering31RawDet (ii1Hering31RawConjugator A) ≠ 0 ∧
          ii1Hering31RawMul A (ii1Hering31RawConjugator A) =
            ii1Hering31RawMul (ii1Hering31RawConjugator A)
              ii1Hering31RawTransvection
  change ∀ A, P A
  let decPoint : ∀ A, Decidable (P A) := fun _ => inferInstance
  let decAll : Decidable (∀ A, P A) :=
    @Fintype.decidableForallFintype _ P decPoint inferInstance
  exact @of_decide_eq_true (∀ A, P A) decAll rfl

private theorem ii1Hering31RawMul_eq
    (A B : II1Hering31RawM) : ii1Hering31RawMul A B = A * B := by
  ext i j
  simp [ii1Hering31RawMul, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem ii1Hering31RawDet_eq
    (A : II1Hering31RawM) : ii1Hering31RawDet A = Matrix.det A := by
  rw [Matrix.det_fin_three]
  rfl

private def ii1Hering31GL3Transvection : GL (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ii1Hering31RawTransvection
    (by decide)

private theorem ii1Hering31_GL3_involution_conjugate_transvection
    (a : GL (Fin 3) (ZMod 2)) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    ∃ c : GL (Fin 3) (ZMod 2),
      c⁻¹ * a * c = ii1Hering31GL3Transvection := by
  let A : II1Hering31RawM := a
  have hA1 : A ≠ 1 := by
    intro h
    apply ha1
    apply Units.ext
    exact h
  have hA2 : ii1Hering31RawMul A A = 1 := by
    rw [ii1Hering31RawMul_eq]
    simpa [A, pow_two] using congrArg Units.val ha2
  have hAdet : ii1Hering31RawDet A ≠ 0 := by
    rw [ii1Hering31RawDet_eq]
    exact Matrix.GeneralLinearGroup.det_ne_zero a
  rcases ii1Hering31_raw_involution_conjugacy_check A with
    h | h | h | ⟨hdetC, hAC⟩
  · exact (hA1 h).elim
  · exact (h hA2).elim
  · exact (hAdet h).elim
  let c : GL (Fin 3) (ZMod 2) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (ii1Hering31RawConjugator A) (by
        simpa [← ii1Hering31RawDet_eq] using hdetC)
  refine ⟨c, ?_⟩
  apply Units.ext
  change (↑(c⁻¹) : II1Hering31RawM) * A *
      ii1Hering31RawConjugator A = ii1Hering31RawTransvection
  rw [mul_assoc]
  rw [← ii1Hering31RawMul_eq A (ii1Hering31RawConjugator A), hAC,
    ii1Hering31RawMul_eq]
  change (↑(c⁻¹) : II1Hering31RawM) *
      (ii1Hering31RawConjugator A * ii1Hering31RawTransvection) =
        ii1Hering31RawTransvection
  rw [← mul_assoc]
  change (↑(c⁻¹) : II1Hering31RawM) * (c : II1Hering31RawM) *
      ii1Hering31RawTransvection = ii1Hering31RawTransvection
  rw [Units.inv_mul]
  simp

/-- All involutions of `GL(3,2)` are conjugate. -/
private theorem ii1Hering31_GL3_involutions_conjugate
    (a b : GL (Fin 3) (ZMod 2))
    (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) :
    ∃ c : GL (Fin 3) (ZMod 2), c⁻¹ * a * c = b := by
  obtain ⟨ca, hca⟩ :=
    ii1Hering31_GL3_involution_conjugate_transvection a ha1 ha2
  obtain ⟨cb, hcb⟩ :=
    ii1Hering31_GL3_involution_conjugate_transvection b hb1 hb2
  refine ⟨ca * cb⁻¹, ?_⟩
  calc
    (ca * cb⁻¹)⁻¹ * a * (ca * cb⁻¹) =
        cb * (ca⁻¹ * a * ca) * cb⁻¹ := by group
    _ = cb * ii1Hering31GL3Transvection * cb⁻¹ := by rw [hca]
    _ = cb * (cb⁻¹ * b * cb) * cb⁻¹ := by rw [hcb]
    _ = b := by group

/-- In the fixed order-eight coordinate group, all automorphism involutions
are conjugate. -/
private theorem ii1Hering31AbelianV_mulAut_involutions_conjugate
    (a b : MulAut II1Hering31AbelianV)
    (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) :
    ∃ c : MulAut II1Hering31AbelianV, c⁻¹ * a * c = b := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsMulCommutative II1Hering31AbelianV :=
    ⟨⟨fun x y => by
      ext i
      exact add_comm (x.toAdd i) (y.toAdd i)⟩⟩
  letI : IsElementaryAbelian 2 II1Hering31AbelianV :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (by
          intro x
          rw [pow_two]
          ext i
          change x.toAdd i + x.toAdd i = 0
          have htwo : (2 : ZMod 2) = 0 := by decide
          calc
            x.toAdd i + x.toAdd i = 2 * x.toAdd i := (two_mul _).symm
            _ = 0 := by rw [htwo, zero_mul]) }
  obtain ⟨e⟩ := ii1Hering31_mulAut_equiv_GL3
    (N := II1Hering31AbelianV) (by
      rw [Nat.card_eq_fintype_card]
      norm_num [II1Hering31AbelianV, ZMod.card])
  have hea1 : e a ≠ 1 := by simpa using ha1
  have hea2 : (e a) ^ 2 = 1 := by simpa using congrArg e ha2
  have heb1 : e b ≠ 1 := by simpa using hb1
  have heb2 : (e b) ^ 2 = 1 := by simpa using congrArg e hb2
  obtain ⟨c, hc⟩ :=
    ii1Hering31_GL3_involutions_conjugate (e a) (e b)
      hea1 hea2 heb1 heb2
  refine ⟨e.symm c, ?_⟩
  apply e.injective
  simpa using hc

/-- The automorphism group of an elementary abelian group of order eight is
simple. -/
private theorem ii1Hering31_mulAut_isSimple
    {N : Type*} [Group N] [Finite N]
    [IsElementaryAbelian 2 N]
    (hcard : Nat.card N = 8) :
    IsSimpleGroup (MulAut N) := by
  let SL3 := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  let PSL3 := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
  let eGLSL : GL (Fin 3) (ZMod 2) ≃* SL3 :=
    { toFun := fun A =>
        ⟨(A : Matrix (Fin 3) (Fin 3) (ZMod 2)), by
          have hdet : Matrix.GeneralLinearGroup.det A = 1 :=
            Subsingleton.elim _ _
          exact congrArg Units.val hdet⟩
      invFun := fun A => Matrix.SpecialLinearGroup.toGL A
      left_inv := by
        intro A
        apply Units.ext
        rfl
      right_inv := by
        intro A
        apply Subtype.ext
        rfl
      map_mul' := by
        intro A B
        apply Subtype.ext
        rfl }
  have hcenter : Subgroup.center SL3 = ⊥ := by
    apply le_antisymm
    · intro A hA
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
      rcases hA with ⟨r, _hr, hscalar⟩
      have hrOne : r = 1 := by
        fin_cases r
        · contradiction
        · rfl
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      rw [← hscalar, hrOne]
      simp
    · exact bot_le
  let ePSLSL : PSL3 ≃* SL3 :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      QuotientGroup.quotientBot
  obtain ⟨eAutGL⟩ := ii1Hering31_mulAut_equiv_GL3 hcard
  let e : MulAut N ≃* PSL3 :=
    (eAutGL.trans eGLSL).trans ePSLSL.symm
  letI : IsSimpleGroup PSL3 :=
    External.huppert_II_6_13 3 (by omega) (Or.inl (by omega))
      (Or.inl (by omega))
  exact e.isSimpleGroup

/-- A doubly transitive subgroup of `Aut(N)` satisfying Hering's transvection
bound is the full automorphism group when `N` is elementary abelian of order
eight. -/
private theorem ii1Hering31_range_eq_top
    {N : Type*} [Group N] [Finite N]
    [IsElementaryAbelian 2 N]
    (A : Subgroup (MulAut N))
    (hcard : Nat.card N = 8)
    (htwo : letI : MulAction A (II1Hering31Nonidentity N) :=
      ii1Hering31NonidentityAction N A
      MulAction.IsMultiplyPretransitive A (II1Hering31Nonidentity N) 2)
    (hfixed : letI : MulDistribMulAction A N :=
      MulDistribMulAction.compHom N A.subtype
      ∀ t : A, IsInvolution t →
        (fixedPointSubgroup (Subgroup.zpowers t) N).index ≤ 2) :
    A = ⊤ := by
  classical
  let Omega := II1Hering31Nonidentity N
  letI : MulAction A Omega := ii1Hering31NonidentityAction N A
  letI : MulAction.IsMultiplyPretransitive A Omega 2 := htwo
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N A.subtype
  have hOmegaCard : Nat.card Omega = 7 := by
    letI : Fintype N := Fintype.ofFinite N
    unfold Omega II1Hering31Nonidentity
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl (fun n : N => n = 1)]
    have hcardF : Fintype.card N = 8 := by
      simpa [Nat.card_eq_fintype_card] using hcard
    rw [hcardF]
    norm_num
  letI : Fintype Omega := Fintype.ofFinite Omega
  have hOmegaCardF : Fintype.card Omega = 7 := by
    simpa [Nat.card_eq_fintype_card] using hOmegaCard
  have htwoOmega : 2 < Fintype.card Omega := by omega
  obtain ⟨a, b, _c, hab, _hac, _hbc⟩ :=
    Fintype.two_lt_card_iff.mp htwoOmega
  let s : Set Omega := {a, b}
  have hsCard : s.ncard = 2 := by simp [s, hab]
  have hindexFix : (fixingSubgroup A s).index = 42 := by
    rw [MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq s
      (by simpa [hsCard] using htwo)]
    rw [hsCard, hOmegaCard]
    norm_num [Nat.choose]
  have h42dvd : 42 ∣ Nat.card A := by
    rw [← Subgroup.index_mul_card (fixingSubgroup A s), hindexFix]
    exact dvd_mul_right 42 _
  obtain ⟨k, hk⟩ := h42dvd
  have hA_le : Nat.card A ≤ Nat.card (MulAut N) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hAutCard : Nat.card (MulAut N) = 168 :=
    ii1Hering31_mulAut_card_eq_168 hcard
  have hkpos : 0 < k := by
    have hApos : 0 < Nat.card A := Nat.card_pos
    rw [hk] at hApos
    omega
  have hkle : k ≤ 4 := by
    rw [hk, hAutCard] at hA_le
    omega
  have hAdiv : Nat.card A ∣ 168 := by
    simpa [hAutCard] using Subgroup.card_subgroup_dvd_card A
  haveI : IsSimpleGroup (MulAut N) := ii1Hering31_mulAut_isSimple hcard
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl
  · have hAcard : Nat.card A = 42 := by omega
    obtain ⟨t, htOrder⟩ :=
      exists_prime_orderOf_dvd_card' 2 (by rw [hAcard]; norm_num)
    have ht : IsInvolution t := (orderOf_eq_prime_iff.mp htOrder).symm
    let F : Subgroup N := fixedPointSubgroup (Subgroup.zpowers t) N
    have hFindex : F.index ≤ 2 := by simpa [F] using hfixed t ht
    have hFindexNe : F.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hFcardFormula : F.index * Nat.card F = 8 := by
      rw [Subgroup.index_mul_card, hcard]
    have hFcard : 4 ≤ Nat.card F := by
      have hi : F.index = 1 ∨ F.index = 2 := by omega
      rcases hi with hi | hi
      · rw [hi] at hFcardFormula
        omega
      · rw [hi] at hFcardFormula
        omega
    letI : Fintype F := Fintype.ofFinite F
    have htwoF : 2 < Fintype.card F := by
      simpa [Nat.card_eq_fintype_card] using
        lt_of_lt_of_le (by omega : 2 < 4) hFcard
    obtain ⟨x0, y0, z0, hxy0, hxz0, hyz0⟩ :=
      Fintype.two_lt_card_iff.mp htwoF
    obtain ⟨x, y, hx, hy, hxy⟩ :
        ∃ x y : F, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
      by_cases hx0 : x0 = 1
      · by_cases hy0 : y0 = 1
        · exact False.elim (hxy0 (hx0.trans hy0.symm))
        · by_cases hz0 : z0 = 1
          · exact False.elim (hxz0 (hx0.trans hz0.symm))
          · exact ⟨y0, z0, hy0, hz0, hyz0⟩
      · by_cases hy0 : y0 = 1
        · by_cases hz0 : z0 = 1
          · exact False.elim (hyz0 (hy0.trans hz0.symm))
          · exact ⟨x0, z0, hx0, hz0, hxz0⟩
        · exact ⟨x0, y0, hx0, hy0, hxy0⟩
    let xO : Omega := ⟨(x : N), by
      intro h
      exact hx (Subtype.ext h)⟩
    let yO : Omega := ⟨(y : N), by
      intro h
      exact hy (Subtype.ext h)⟩
    have hxyO : xO ≠ yO := by
      intro h
      apply hxy
      apply Subtype.ext
      exact congrArg (fun z : Omega => (z : N)) h
    let st : Set Omega := {xO, yO}
    have hstCard : st.ncard = 2 := by simp [st, hxyO]
    have hstIndex : (fixingSubgroup A st).index = 42 := by
      rw [MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq st
        (by simpa [hstCard] using htwo)]
      rw [hstCard, hOmegaCard]
      norm_num [Nat.choose]
    have hstCardOne : Nat.card (fixingSubgroup A st) = 1 := by
      have hformula := Subgroup.index_mul_card (fixingSubgroup A st)
      rw [hstIndex, hAcard] at hformula
      omega
    have htFixX : t • xO = xO := by
      apply Subtype.ext
      exact (FixedPoints.mem_subgroup (Subgroup.zpowers t) N x).mp x.property
        ⟨t, Subgroup.mem_zpowers t⟩
    have htFixY : t • yO = yO := by
      apply Subtype.ext
      exact (FixedPoints.mem_subgroup (Subgroup.zpowers t) N y).mp y.property
        ⟨t, Subgroup.mem_zpowers t⟩
    have htMem : t ∈ fixingSubgroup A st := by
      rw [mem_fixingSubgroup_iff]
      intro z hz
      simp only [st, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact htFixX
      · exact htFixY
    have hstBot : fixingSubgroup A st = ⊥ := by
      rw [Subgroup.eq_bot_iff_card]
      exact hstCardOne
    have htOne : t = 1 := by
      exact Subgroup.mem_bot.mp (hstBot ▸ htMem)
    exact False.elim (ht.ne_one htOne)
  · have hAcard : Nat.card A = 84 := by omega
    have hAindex : A.index = 2 := by
      have hformula := Subgroup.index_mul_card A
      rw [hAcard, hAutCard] at hformula
      omega
    have hAnormal : A.Normal := Subgroup.normal_of_index_eq_two hAindex
    rcases hAnormal.eq_bot_or_eq_top with hbot | htop
    · have hcardBot : Nat.card A = 1 := by rw [hbot]; simp
      omega
    · exact htop
  · have hAcard : Nat.card A = 126 := by omega
    rw [hAcard] at hAdiv
    norm_num at hAdiv
  · apply Subgroup.eq_top_of_card_eq
    rw [hAutCard]
    omega

/-- In a cardinal-minimal rank-two counterexample, every automorphism of the
elementary abelian involution subgroup is induced by ambient conjugation. -/
public theorem ii1Hering31_conjNormal_surjective
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
    Function.Surjective (MulAut.conjNormal (H := N)) := by
  classical
  dsimp only
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  letI : IsMulCommutative N :=
    ⟨⟨fun x y => (ii1Hering31InvolutionSubgroup_commute hcomm x y).eq⟩⟩
  letI : IsElementaryAbelian 2 N :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.2
          (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm) }
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N A.subtype
  have hNcard : Nat.card N = 8 :=
    ii1Hering31_involution_subgroup_card hsmall htwo hrank hcomm
  have hNcardGe : 4 ≤ Nat.card N := by
    rw [hNcard]
    norm_num
  have htwoA : MulAction.IsMultiplyPretransitive A
      (II1Hering31Nonidentity N) 2 :=
    ii1Hering31_range_twoPretransitive htwo hcomm
  have hodd : ∀ q : A, Nat.Prime (orderOf q) → orderOf q ≠ 2 →
      Nat.card (fixedPointSubgroup (Subgroup.zpowers q) N) ≤ 2 :=
    ii1Hering31_odd_prime_fixed_card_le_two hsmall htwo hcomm
  have hfixed : ∀ t : A, IsInvolution t →
      (fixedPointSubgroup (Subgroup.zpowers t) N).index ≤ 2 := by
    intro t ht
    exact ii1Hering31_involution_fixed_index_le_two
      (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm)
      (ii1Hering31InvolutionSubgroup_commute hcomm) A htwoA
      hNcardGe hodd t ht
  exact MonoidHom.range_eq_top.mp
    (ii1Hering31_range_eq_top A hNcard htwoA hfixed)

/-- Hering's Lemma 3.5 quotient recognition: in a cardinal-minimal rank-two
counterexample, conjugation identifies `X / O₂(X)` with the full automorphism
group of its elementary abelian involution subgroup of order eight. -/
public theorem ii1Hering31_twoCore_quotient
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    Nonempty (X ⧸ pCore 2 X ≃* MulAut N) := by
  classical
  dsimp only
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  letI : IsMulCommutative N :=
    ⟨⟨fun x y => (ii1Hering31InvolutionSubgroup_commute hcomm x y).eq⟩⟩
  letI : IsElementaryAbelian 2 N :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.2
          (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm) }
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N A.subtype
  have hNcard : Nat.card N = 8 :=
    ii1Hering31_involution_subgroup_card hsmall htwo hrank hcomm
  have hNcardGe : 4 ≤ Nat.card N := by
    rw [hNcard]
    norm_num
  have htwoA : MulAction.IsMultiplyPretransitive A
      (II1Hering31Nonidentity N) 2 :=
    ii1Hering31_range_twoPretransitive htwo hcomm
  have hodd : ∀ q : A, Nat.Prime (orderOf q) → orderOf q ≠ 2 →
      Nat.card (fixedPointSubgroup (Subgroup.zpowers q) N) ≤ 2 :=
    ii1Hering31_odd_prime_fixed_card_le_two hsmall htwo hcomm
  have hfixed : ∀ t : A, IsInvolution t →
      (fixedPointSubgroup (Subgroup.zpowers t) N).index ≤ 2 := by
    intro t ht
    exact ii1Hering31_involution_fixed_index_le_two
      (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm)
      (ii1Hering31InvolutionSubgroup_commute hcomm) A htwoA
      hNcardGe hodd t ht
  have hRangeTop : A = ⊤ :=
    ii1Hering31_range_eq_top A hNcard htwoA hfixed
  have hker : phi.ker = pCore 2 X := by
    rw [ii1Hering31_conjNormal_ker_eq_centralizer]
    exact ii1Hering31_centralizer_involutionSubgroup_eq_twoCore
      hsmall htwo hrank hcomm
  let eQuot : X ⧸ pCore 2 X ≃* X ⧸ phi.ker :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  let eRange : X ⧸ phi.ker ≃* A :=
    QuotientGroup.quotientKerEquivRange phi
  let eTop : A ≃* (⊤ : Subgroup (MulAut N)) :=
    MulEquiv.subgroupCongr hRangeTop
  exact ⟨eQuot.trans (eRange.trans (eTop.trans Subgroup.topEquiv))⟩

/-! ## Automorphisms of the center and central quotient -/

/-- Restrict an automorphism to the characteristic center. -/
private noncomputable def ii1Hering31CenterAction
    (P : Type*) [Group P] : MulAut P →* MulAut (Subgroup.center P) where
  toFun alpha :=
    { toFun := fun z =>
        ⟨alpha z, by
          rw [Subgroup.mem_center_iff]
          intro x
          have hz := Subgroup.mem_center_iff.mp z.property (alpha.symm x)
          have h := congrArg alpha hz
          simpa using h⟩
      invFun := fun z =>
        ⟨alpha.symm z, by
          rw [Subgroup.mem_center_iff]
          intro x
          have hz := Subgroup.mem_center_iff.mp z.property (alpha x)
          have h := congrArg alpha.symm hz
          simpa using h⟩
      left_inv := fun z => Subtype.ext (alpha.symm_apply_apply z)
      right_inv := fun z => Subtype.ext (alpha.apply_symm_apply z)
      map_mul' := by
        intro z w
        apply Subtype.ext
        exact map_mul alpha (z : P) (w : P) }
  map_one' := by
    apply DFunLike.ext _ _
    intro z
    apply Subtype.ext
    rfl
  map_mul' := by
    intro alpha beta
    apply DFunLike.ext _ _
    intro z
    apply Subtype.ext
    rfl

private theorem ii1Hering31CenterAction_apply
    {P : Type*} [Group P] (alpha : MulAut P) (z : Subgroup.center P) :
    (((ii1Hering31CenterAction P alpha) z : Subgroup.center P) : P) =
      alpha (z : P) :=
  rfl

/-- Descend an automorphism to the quotient by the characteristic center. -/
private noncomputable def ii1Hering31CenterQuotientAction
    (P : Type*) [Group P] :
    MulAut P →* MulAut
      (HasQuotient.Quotient P (Subgroup.center P)) := by
  classical
  have hpreserve (alpha : MulAut P) :
      Subgroup.center P ≤ (Subgroup.center P).comap alpha.toMonoidHom := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro x
    have hzComm := Subgroup.mem_center_iff.mp hz (alpha.symm x)
    have h := congrArg alpha hzComm
    simpa using h
  let descend (alpha : MulAut P) :
      HasQuotient.Quotient P (Subgroup.center P) →*
        HasQuotient.Quotient P (Subgroup.center P) :=
    QuotientGroup.map (N := Subgroup.center P) (Subgroup.center P)
      alpha.toMonoidHom (hpreserve alpha)
  have hleft (alpha : MulAut P) :
      Function.LeftInverse (descend alpha.symm) (descend alpha) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change QuotientGroup.mk' (Subgroup.center P) (alpha.symm (alpha x)) =
      QuotientGroup.mk' (Subgroup.center P) x
    rw [alpha.symm_apply_apply]
  have hright (alpha : MulAut P) :
      Function.RightInverse (descend alpha.symm) (descend alpha) := by
    exact (hleft alpha.symm).rightInverse
  let descendAut (alpha : MulAut P) :
      MulAut (HasQuotient.Quotient P (Subgroup.center P)) :=
    { toFun := descend alpha
      invFun := descend alpha.symm
      left_inv := hleft alpha
      right_inv := hright alpha
      map_mul' := (descend alpha).map_mul }
  exact
    { toFun := descendAut
      map_one' := by
        apply DFunLike.ext _ _
        intro q
        refine QuotientGroup.induction_on q ?_
        intro x
        rfl
      map_mul' := by
        intro alpha beta
        apply DFunLike.ext _ _
        intro q
        refine QuotientGroup.induction_on q ?_
        intro x
        rfl }

private theorem ii1Hering31CenterQuotientAction_mk
    {P : Type*} [Group P] (alpha : MulAut P) (x : P) :
    ii1Hering31CenterQuotientAction P alpha
        (QuotientGroup.mk' (Subgroup.center P) x) =
      QuotientGroup.mk' (Subgroup.center P) (alpha x) :=
  rfl

/-- The restricted center action and the descended quotient action preserve
the square map from the central quotient into the center. -/
private theorem ii1Hering31CenterActions_square
    {P : Type*} [Group P] (alpha : MulAut P) (x : P)
    (hx : x ^ 2 ∈ Subgroup.center P) :
    ii1Hering31CenterAction P alpha ⟨x ^ 2, hx⟩ =
      ⟨(alpha x) ^ 2, by
        have hcenter :=
          (ii1Hering31CenterAction P alpha ⟨x ^ 2, hx⟩).property
        change alpha (x ^ 2) ∈ Subgroup.center P at hcenter
        simpa only [map_pow] using hcenter⟩ := by
  apply Subtype.ext
  exact map_pow alpha x 2

/-! ## Coprime lifts of the order-seven actor -/

/-- Schur--Zassenhaus supplies a section of a surjective homomorphism when its
kernel is a `p`-group and the target has order prime to `p`. -/
private theorem ii1Hering31_exists_rightInverse_of_surjective_isPGroup_ker
    {E Q : Type u} [Group E] [Group Q] [Finite E] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (phi : E →* Q) (hphi : Function.Surjective phi)
    (hker : IsPGroup p phi.ker) (hcop : Nat.Coprime p (Nat.card Q)) :
    ∃ sigma : Q →* E, Function.RightInverse sigma phi := by
  classical
  haveI : phi.ker.Normal := inferInstance
  have hkerCard : Nat.Coprime (Nat.card phi.ker) phi.ker.index := by
    rcases (IsPGroup.iff_card (p := p) (G := phi.ker)).1 hker with
      ⟨n, hcard⟩
    have hindex : phi.ker.index = Nat.card Q := by
      rw [Subgroup.index_ker]
      calc
        Nat.card phi.range = Nat.card (⊤ : Subgroup Q) := by
          rw [phi.range_eq_top_of_surjective hphi]
        _ = Nat.card Q := Subgroup.card_top
    rw [hcard, hindex]
    exact hcop.pow_left n
  rcases Subgroup.exists_right_complement'_of_coprime
      (N := phi.ker) hkerCard with
    ⟨K, hcomp⟩
  have hcomp' : K.IsComplement' phi.ker := hcomp.symm
  let e : E ⧸ phi.ker ≃* K := hcomp'.QuotientMulEquiv
  let qIso : E ⧸ phi.ker ≃* Q :=
    QuotientGroup.quotientKerEquivOfSurjective phi hphi
  let sigma : Q →* E :=
    K.subtype.comp (e.toMonoidHom.comp qIso.symm.toMonoidHom)
  refine ⟨sigma, ?_⟩
  intro q
  rcases hphi q with ⟨x, rfl⟩
  dsimp [sigma, qIso, e]
  have hq :
      QuotientGroup.mk' phi.ker
          (hcomp'.QuotientMulEquiv
            ((QuotientGroup.quotientKerEquivOfSurjective phi hphi).symm
              (phi x)) : E) =
        (QuotientGroup.quotientKerEquivOfSurjective phi hphi).symm
          (phi x) :=
    Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hcomp' _
  have hq' :
      (QuotientGroup.quotientKerEquivOfSurjective phi hphi)
          (QuotientGroup.mk' phi.ker
            (hcomp'.QuotientMulEquiv
              ((QuotientGroup.quotientKerEquivOfSurjective phi hphi).symm
                (phi x)) : E)) =
        phi x := by
    rw [hq, MulEquiv.apply_symm_apply]
  simpa [QuotientGroup.quotientKerEquivOfSurjective] using hq'

/-- A coprime group action in the target of a surjective map with `p`-group
kernel lifts to a genuine homomorphism into the source. -/
private theorem ii1Hering31_exists_lift_of_surjective_isPGroup_ker_of_coprime
    {E Q K : Type u} [Group E] [Group Q] [Group K]
    [Finite E] [Finite Q] [Finite K]
    {p : ℕ} [Fact p.Prime]
    (phi : E →* Q) (hphi : Function.Surjective phi)
    (hker : IsPGroup p phi.ker) (hcop : Nat.Coprime p (Nat.card K))
    (rho : K →* Q) :
    ∃ lift : K →* E, phi.comp lift = rho := by
  classical
  let P : Subgroup E := rho.range.comap phi
  let phiP : P →* rho.range :=
    { toFun := fun x => ⟨phi x, x.2⟩
      map_one' := by
        ext
        exact map_one phi
      map_mul' := by
        intro x y
        ext
        exact map_mul phi (x : E) (y : E) }
  have hphiP : Function.Surjective phiP := by
    rintro ⟨q, hq⟩
    rcases hphi q with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change phi x ∈ rho.range
      simpa [hx] using hq
    · ext
      exact hx
  have hkerP : IsPGroup p phiP.ker := by
    intro x
    have hxker : (x : P) ∈ phiP.ker := x.2
    have hxphi : (x : E) ∈ phi.ker := by
      change phi ((x : P) : E) = 1
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hxker)
    rcases hker ⟨(x : E), hxphi⟩ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hn
  have hcopRange : Nat.Coprime p (Nat.card rho.range) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_range_dvd rho) hcop
  rcases ii1Hering31_exists_rightInverse_of_surjective_isPGroup_ker
      (p := p) phiP hphiP hkerP hcopRange with
    ⟨sigma, hsigma⟩
  let lift : K →* E := P.subtype.comp (sigma.comp rho.rangeRestrict)
  refine ⟨lift, ?_⟩
  ext k
  change phi (lift k) = rho k
  exact congrArg Subtype.val (hsigma (rho.rangeRestrict k))

/-- The order-seven subgroup of the full action on the involution subgroup
lifts coherently and acts faithfully and regularly on the involutions of the
ambient two-core. -/
private theorem ii1Hering31_twoCore_actor
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let Q : Subgroup X := pCore 2 X
    ∃ (K : Type u) (_ : Group K) (_ : MulDistribMulAction K Q),
      IsCyclic K ∧ FaithfulSMul K Q ∧
        ActionRegularOn K Q (involutions Q) := by
  classical
  dsimp only
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  let Q : Subgroup X := pCore 2 X
  letI : Q.Normal := pCore_normal
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let A : Subgroup (MulAut N) := phi.range
  letI : MulAction A (II1Hering31Nonidentity N) :=
    ii1Hering31NonidentityAction N A
  letI : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N A.subtype
  have hNcard : Nat.card N = 8 :=
    ii1Hering31_involution_subgroup_card hsmall htwo hrank hcomm
  have htwoA : MulAction.IsMultiplyPretransitive A
      (II1Hering31Nonidentity N) 2 :=
    ii1Hering31_range_twoPretransitive htwo hcomm
  obtain ⟨g, hg, hregular⟩ :=
    ii1Hering31_orderSeven_actor A hNcard htwoA
  let K : Subgroup A := Subgroup.zpowers g
  change ActionRegularOn K N (involutions N) at hregular
  have hKcard : Nat.card K = 7 := by
    change Nat.card (Subgroup.zpowers g) = 7
    rw [Nat.card_zpowers, hg]
  let rho : K →* MulAut N := A.subtype.comp K.subtype
  have hphiSurj : Function.Surjective phi :=
    ii1Hering31_conjNormal_surjective hsmall htwo hrank hcomm
  have hkerEq : phi.ker = Q := by
    rw [ii1Hering31_conjNormal_ker_eq_centralizer]
    exact ii1Hering31_centralizer_involutionSubgroup_eq_twoCore
      hsmall htwo hrank hcomm
  have hkerTwo : IsPGroup 2 phi.ker := by
    rw [hkerEq]
    exact pCore_isPGroup
  have hcop : Nat.Coprime 2 (Nat.card K) := by
    rw [hKcard]
    norm_num
  obtain ⟨lift, hlift⟩ :=
    ii1Hering31_exists_lift_of_surjective_isPGroup_ker_of_coprime
      phi hphiSurj hkerTwo hcop rho
  let psi : K →* MulAut Q := (MulAut.conjNormal (H := Q)).comp lift
  letI : MulDistribMulAction K Q :=
    MulDistribMulAction.compHom Q psi
  have hNleQ : N ≤ Q :=
    ii1Hering31InvolutionSubgroup_le_twoCore hcomm
  have haction (k : K) (n : N) :
      (((psi k) ⟨(n : X), hNleQ n.property⟩ : Q) : X) =
        (((rho k) n : N) : X) := by
    have hk : phi (lift k) = rho k :=
      congrArg (fun f : K →* MulAut N => f k) hlift
    have hkn := congrArg (fun alpha : MulAut N => ((alpha n : N) : X)) hk
    simpa [phi, psi, MulAut.conjNormal_apply, MulAut.conj_apply] using hkn
  refine ⟨K, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · infer_instance
  · rw [faithfulSMul_iff]
    intro k hk
    apply (A.subtype_injective.comp K.subtype_injective)
    change rho k = rho 1
    rw [map_one]
    have hphiOne : phi (lift k) = 1 := by
      apply MulEquiv.ext
      intro n
      apply Subtype.ext
      let nQ : Q := ⟨(n : X), hNleQ n.property⟩
      have hfix := hk nQ
      have hfixX := congrArg Q.subtype hfix
      have hact := haction k n
      change (((phi (lift k)) n : N) : X) = (n : X)
      calc
        (((phi (lift k)) n : N) : X) =
            (((rho k) n : N) : X) := by
              exact congrArg (fun alpha : MulAut N => ((alpha n : N) : X))
                (congrArg (fun f : K →* MulAut N => f k) hlift)
        _ = (((psi k) nQ : Q) : X) := hact.symm
        _ = (nQ : X) := hfixX
        _ = (n : X) := rfl
    calc
      rho k = phi (lift k) :=
        (congrArg (fun f : K →* MulAut N => f k) hlift).symm
      _ = 1 := hphiOne
  · constructor
    · intro x hx k
      exact IsInvolution.map_of_injective hx (psi k).toMonoidHom
        (psi k).injective
    · intro x hx y hy
      have hxX : IsInvolution (x : X) :=
        IsInvolution.map_of_injective hx Q.subtype Q.subtype_injective
      have hyX : IsInvolution (y : X) :=
        IsInvolution.map_of_injective hy Q.subtype Q.subtype_injective
      let xN : N := ⟨(x : X), Or.inr hxX⟩
      let yN : N := ⟨(y : X), Or.inr hyX⟩
      have hxN : IsInvolution xN := by
        refine ⟨?_, ?_⟩
        · intro h
          exact hxX.ne_one (by
            simpa [xN] using congrArg N.subtype h)
        · apply Subtype.ext
          exact hxX.sq_eq_one
      have hyN : IsInvolution yN := by
        refine ⟨?_, ?_⟩
        · intro h
          exact hyX.ne_one (by
            simpa [yN] using congrArg N.subtype h)
        · apply Subtype.ext
          exact hyX.sq_eq_one
      obtain ⟨k, hk, huniq⟩ := hregular.2 xN hxN yN hyN
      refine ⟨k, ?_, ?_⟩
      · apply Subtype.ext
        calc
          (y : X) = (yN : X) := rfl
          _ = (((rho k) xN : N) : X) := by
            have hk' := congrArg N.subtype hk
            have hsmul : k • xN = (rho k) xN := by
              change ((k : A) : MulAut N) xN = (rho k) xN
              rfl
            rw [hsmul] at hk'
            exact hk'
          _ = (((psi k) x : Q) : X) := (haction k xN).symm
      · intro l hl
        apply huniq l
        apply Subtype.ext
        calc
          (yN : X) = (y : X) := rfl
          _ = (((psi l) x : Q) : X) := congrArg Q.subtype hl
          _ = (((rho l) xN : N) : X) := haction l xN

/-- The two-core in a cardinal-minimal rank-two counterexample is either
abelian or is a Suzuki two-group for the lifted order-seven action. -/
public theorem ii1Hering31_twoCore_commutative_or_suzuki
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let Q : Subgroup X := pCore 2 X
    IsMulCommutative Q ∨ IsSuzukiTwoGroup Q := by
  classical
  dsimp only
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  by_cases hQcomm : IsMulCommutative Q
  · exact Or.inl hQcomm
  · right
    have hQcard : ∃ n : ℕ, Nat.card (⊤ : Subgroup Q) = 2 ^ n := by
      rcases (IsPGroup.iff_card (p := 2) (G := Q)).mp pCore_isPGroup with
        ⟨n, hn⟩
      exact ⟨n, by simpa using hn⟩
    obtain ⟨E, hEcard, hEsq⟩ :=
      TwoRankAtLeastTwo.exists_subgroup hrank
    obtain ⟨a, b, ha, hb, hab⟩ :=
      exists_two_distinct_nontrivial_of_card_four hEcard
    have hEleN : E ≤ N :=
      ii1Hering31_rankTwo_le_involutionSubgroup hcomm E hEsq
    have hNleQ : N ≤ Q :=
      ii1Hering31InvolutionSubgroup_le_twoCore hcomm
    let aQ : Q := ⟨(a : X), hNleQ (hEleN a.property)⟩
    let bQ : Q := ⟨(b : X), hNleQ (hEleN b.property)⟩
    have haQ : IsInvolution aQ := by
      refine ⟨?_, ?_⟩
      · intro h
        exact ha (Subtype.ext (congrArg Q.subtype h))
      · apply Subtype.ext
        exact congrArg E.subtype (hEsq a)
    have hbQ : IsInvolution bQ := by
      refine ⟨?_, ?_⟩
      · intro h
        exact hb (Subtype.ext (congrArg Q.subtype h))
      · apply Subtype.ext
        exact congrArg E.subtype (hEsq b)
    have habQ : aQ ≠ bQ := by
      intro h
      exact hab (Subtype.ext (congrArg Q.subtype h))
    obtain ⟨K, hKGroup, hKAction, hKcyclic, hKfaithful, hKregular⟩ :=
      ii1Hering31_twoCore_actor hsmall htwo hrank hcomm
    exact ⟨hQcard, hQcomm, ⟨aQ, bQ, haQ, hbQ, habQ⟩,
      K, hKGroup, hKAction, hKcyclic, hKfaithful, hKregular⟩

/-- The abelian two-core branch supplies exactly the abstract extension data
used by Peterfalvi's direct contradiction. -/
private noncomputable def ii1Hering31_abelianExtensionData
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (hQcomm : IsMulCommutative (pCore 2 X)) :
    II1Hering31AbelianExtensionData X := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  have hNnormal : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  have hQnormal : Q.Normal := pCore_normal
  letI : N.Normal := hNnormal
  letI : Q.Normal := hQnormal
  letI : IsMulCommutative Q := hQcomm
  letI : IsMulCommutative N :=
    ⟨⟨fun x y => (ii1Hering31InvolutionSubgroup_commute hcomm x y).eq⟩⟩
  letI : IsElementaryAbelian 2 N :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.2
          (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm) }
  have hNcard : Nat.card N = 8 :=
    ii1Hering31_involution_subgroup_card hsmall htwo hrank hcomm
  let coord : N ≃* II1Hering31AbelianV :=
    Classical.choice (ii1Hering31_orderEight_equiv_abelianV hNcard)
  let transport : MulAut N →* MulAut II1Hering31AbelianV :=
    ii1Hering31AbelianTransportAut coord
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  let action : X →* MulAut II1Hering31AbelianV :=
    ii1Hering31AbelianCoordinateAction N hNnormal coord
  have htransportInjective : Function.Injective transport := by
    intro alpha beta hab
    apply MulEquiv.ext
    intro n
    apply coord.injective
    have hn := DFunLike.congr_fun hab (coord n)
    simpa [transport, ii1Hering31AbelianTransportAut] using hn
  have htransportSurjective : Function.Surjective transport := by
    intro alpha
    let beta : MulAut N := coord.trans (alpha.trans coord.symm)
    refine ⟨beta, ?_⟩
    apply MulEquiv.ext
    intro v
    simp [transport, beta, ii1Hering31AbelianTransportAut]
  have hphiSurjective : Function.Surjective phi :=
    ii1Hering31_conjNormal_surjective hsmall htwo hrank hcomm
  have hactionSurjective : Function.Surjective action := by
    intro alpha
    obtain ⟨beta, hbeta⟩ := htransportSurjective alpha
    obtain ⟨x, hx⟩ := hphiSurjective beta
    refine ⟨x, ?_⟩
    calc
      action x = transport (phi x) := rfl
      _ = transport beta := congrArg transport hx
      _ = alpha := hbeta
  have hphiKer : phi.ker = Q := by
    rw [ii1Hering31_conjNormal_ker_eq_centralizer]
    exact ii1Hering31_centralizer_involutionSubgroup_eq_twoCore
      hsmall htwo hrank hcomm
  have hactionKer : action.ker = Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change transport (phi x) = 1 ↔ x ∈ Q
    rw [← map_one transport, htransportInjective.eq_iff]
    change x ∈ phi.ker ↔ x ∈ Q
    rw [hphiKer]
  have htwoTorsion : ∀ q : Q, (q : X) ∈ N ↔ q ^ 2 = 1 := by
    intro q
    constructor
    · intro hq
      let n : N := ⟨(q : X), hq⟩
      apply Q.subtype_injective
      simpa [n] using congrArg N.subtype
        (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm n)
    · intro hq
      by_cases hqOne : q = 1
      · left
        simpa using congrArg Q.subtype hqOne
      · right
        refine ⟨?_, ?_⟩
        · intro h
          apply hqOne
          apply Q.subtype_injective
          simpa using h
        · simpa using congrArg Q.subtype hq
  have hVtransitive : ∀ v w : N, v ≠ 1 → w ≠ 1 →
      ∃ x : X, x * (v : X) * x⁻¹ = (w : X) := by
    letI : MulAction X (II1Hering31Involutions X) :=
      ii1Hering31ConjugationAction X
    haveI : MulAction.IsMultiplyPretransitive X
        (II1Hering31Involutions X) 2 :=
      ii1Hering31ConjugationAction_twoPretransitive htwo
    haveI : MulAction.IsPretransitive X (II1Hering31Involutions X) :=
      MulAction.isPretransitive_of_is_two_pretransitive
    intro v w hv hw
    let vI : II1Hering31Involutions X :=
      ⟨(v : X), (ii1Hering31InvolutionSubgroup_ne_one_iff hcomm v).mp hv⟩
    let wI : II1Hering31Involutions X :=
      ⟨(w : X), (ii1Hering31InvolutionSubgroup_ne_one_iff hcomm w).mp hw⟩
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X vI wI
    exact ⟨x, congrArg Subtype.val hx⟩
  have hquotientInvolutions :
      ∀ {x y : X}, x ∉ Q → x ^ 2 ∈ Q → y ∉ Q → y ^ 2 ∈ Q →
        ∃ g : X, g⁻¹ * x * g * y⁻¹ ∈ Q := by
    intro x y hxQ hx2 hyQ hy2
    have hax1 : action x ≠ 1 := by
      intro hx
      apply hxQ
      rw [← hactionKer]
      exact MonoidHom.mem_ker.mpr hx
    have hax2 : (action x) ^ 2 = 1 := by
      rw [← map_pow]
      apply MonoidHom.mem_ker.mp
      rw [hactionKer]
      exact hx2
    have hay1 : action y ≠ 1 := by
      intro hy
      apply hyQ
      rw [← hactionKer]
      exact MonoidHom.mem_ker.mpr hy
    have hay2 : (action y) ^ 2 = 1 := by
      rw [← map_pow]
      apply MonoidHom.mem_ker.mp
      rw [hactionKer]
      exact hy2
    obtain ⟨c, hc⟩ :=
      ii1Hering31AbelianV_mulAut_involutions_conjugate
        (action x) (action y) hax1 hax2 hay1 hay2
    obtain ⟨g, hg⟩ := hactionSurjective c
    refine ⟨g, ?_⟩
    rw [← hactionKer]
    apply MonoidHom.mem_ker.mpr
    simp only [map_mul, map_inv, hg]
    rw [hc]
    simp
  exact
    { Q := Q
      V := N
      Q_normal := hQnormal
      V_normal := hNnormal
      Q_commutative := hQcomm
      Q_isPGroup := pCore_isPGroup
      V_le_Q := ii1Hering31InvolutionSubgroup_le_twoCore hcomm
      V_twoTorsion := htwoTorsion
      V_coord := coord
      V_action_transitive := hVtransitive
      action := action
      action_on_V := by
        intro x v
        exact ii1Hering31AbelianCoordinateAction_apply N hNnormal coord x v
      action_surjective := hactionSurjective
      action_ker := hactionKer
      quotient_involutions_conjugate := hquotientInvolutions }

/-- The first omega subgroup of the ambient two-core is exactly the subgroup
consisting of the identity and all ambient involutions. -/
private theorem ii1Hering31_twoCore_omegaOne_eq_involutionSubgroup
    {X : Type u} [Group X] [Finite X]
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    let Q : Subgroup X := pCore 2 X
    omega₁ (G := Q) (p := 2) = N.subgroupOf Q := by
  classical
  dsimp only
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  apply le_antisymm
  · dsimp [omega₁]
    rw [omega, Subgroup.closure_le]
    intro q hq
    change (q : X) ∈ N
    by_cases hqOne : q = 1
    · left
      simpa using congrArg Q.subtype hqOne
    · right
      have hqSq : q ^ 2 = 1 := by simpa using hq
      exact IsInvolution.map_of_injective ⟨hqOne, hqSq⟩
        Q.subtype Q.subtype_injective
  · intro q hq
    dsimp [omega₁]
    rw [omega]
    apply Subgroup.subset_closure
    change q ^ (2 ^ 1) = 1
    apply Q.subtype_injective
    simpa using congrArg N.subtype
      (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm ⟨(q : X), hq⟩)

/-- The two-torsion of the ambient two-core consists of the identity and the
seven ambient involutions, so it has cardinality eight. -/
private theorem ii1Hering31_twoCore_twoTorsion_card
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y) :
    Nat.card {q : pCore 2 X // q ^ 2 = 1} = 8 := by
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  have hNleQ : N ≤ Q :=
    ii1Hering31InvolutionSubgroup_le_twoCore hcomm
  let e : {q : Q // q ^ 2 = 1} ≃ N :=
    { toFun := fun q => ⟨(q.1 : X), by
        by_cases hq : q.1 = 1
        · left
          simpa using congrArg Q.subtype hq
        · right
          exact IsInvolution.map_of_injective ⟨hq, q.2⟩
            Q.subtype Q.subtype_injective⟩
      invFun := fun n => ⟨⟨(n : X), hNleQ n.property⟩, by
        apply Q.subtype_injective
        simpa using congrArg N.subtype
          (ii1Hering31InvolutionSubgroup_sq_eq_one hcomm n)⟩
      left_inv := by intro q; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro n; apply Subtype.ext; rfl }
  calc
    Nat.card {q : pCore 2 X // q ^ 2 = 1} = Nat.card N :=
      Nat.card_congr e
    _ = 8 :=
      ii1Hering31_involution_subgroup_card hsmall htwo hrank hcomm

/-- In the abelian branch the ambient two-core is a rank-three homocyclic
`2`-group. -/
private theorem ii1Hering31_abelian_twoCore_homocyclic
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (hQcomm : IsMulCommutative (pCore 2 X)) :
    ∃ e : ℕ, 0 < e ∧ Nonempty
      ((pCore 2 X) ≃* Multiplicative (Fin 3 → ZMod (2 ^ e))) := by
  let Q : Subgroup X := pCore 2 X
  obtain ⟨K, hKGroup, hKAction, _hKcyclic, _hKfaithful, hKregular⟩ :=
    ii1Hering31_twoCore_actor hsmall htwo hrank hcomm
  letI : Group K := hKGroup
  letI : MulDistribMulAction K Q := hKAction
  obtain ⟨e, r, he, ⟨f⟩⟩ :=
    External.Higman.homocyclic_of_abelian_twoGroup_of_involutions_transitive
      (P := Q) (X := K) pCore_isPGroup hQcomm
      (fun x hx y hy => (hKregular.2 x hx y hy).exists)
  have hpow : 2 ^ r = 8 := by
    rw [← External.Higman.lemma1_twoTorsion_card_of_homocyclic he f]
    exact ii1Hering31_twoCore_twoTorsion_card hsmall htwo hrank hcomm
  have hr : r = 3 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    calc
      2 ^ r = 8 := hpow
      _ = 2 ^ 3 := by norm_num
  subst r
  exact ⟨e, he, ⟨f⟩⟩

/-- In the abelian branch, the Frattini quotient of the two-core has order
eight. -/
private theorem ii1Hering31_abelian_twoCore_frattini_quotient_card
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (hQcomm : IsMulCommutative (pCore 2 X)) :
    let Q : Subgroup X := pCore 2 X
    Nat.card (Q ⧸ frattini Q) = 8 := by
  classical
  dsimp only
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsMulCommutative Q := hQcomm
  letI : Fact (IsPGroup 2 Q) := ⟨pCore_isPGroup⟩
  have hOmega : omega₁ (G := Q) (p := 2) = N.subgroupOf Q :=
    ii1Hering31_twoCore_omegaOne_eq_involutionSubgroup hcomm
  have hNcard : Nat.card N = 8 :=
    ii1Hering31_involution_subgroup_card hsmall htwo hrank hcomm
  calc
    Nat.card (Q ⧸ frattini Q) = Nat.card (omega₁ (G := Q) (p := 2)) :=
      (section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative
        (p := 2) Q).symm
    _ = Nat.card (N.subgroupOf Q) := by rw [hOmega]
    _ = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (ii1Hering31InvolutionSubgroup_le_twoCore hcomm)).toEquiv
    _ = 8 := hNcard

/-- If the ambient two-core is larger than the involution subgroup, then the
latter lies in the Frattini subgroup of the two-core. -/
private theorem ii1Hering31_involutionSubgroup_le_frattini_of_twoCore_ne
    {X : Type u} [Group X] [Finite X]
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (hNcard : Nat.card (ii1Hering31InvolutionSubgroup X hcomm) = 8)
    (hquotCard : Nat.card
      ((pCore 2 X) ⧸ frattini (pCore 2 X)) = 8)
    (hQneN : pCore 2 X ≠ ii1Hering31InvolutionSubgroup X hcomm) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    let Q : Subgroup X := pCore 2 X
    N.subgroupOf Q ≤ frattini Q := by
  classical
  dsimp only
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  let Phi : Subgroup Q := frattini Q
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Q.Normal := pCore_normal
  have hNleQ : N ≤ Q := ii1Hering31InvolutionSubgroup_le_twoCore hcomm
  have hPhiNeBot : Phi ≠ ⊥ := by
    intro hPhiBot
    have hQcard : Nat.card Q = 8 := by
      calc
        Nat.card Q = Nat.card (Q ⧸ (⊥ : Subgroup Q)) :=
          (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm
        _ = Nat.card (Q ⧸ Phi) := by rw [hPhiBot]
        _ = 8 := by simpa [Q, Phi] using hquotCard
    have hNQ : N = Q :=
      Subgroup.eq_of_le_of_card_ge hNleQ (by rw [hNcard, hQcard])
    exact hQneN hNQ.symm
  letI : Nontrivial Phi := (Subgroup.nontrivial_iff_ne_bot Phi).mpr hPhiNeBot
  have hPhiP : IsPGroup 2 Phi := pCore_isPGroup.to_subgroup Phi
  have htwoDvdPhi : 2 ∣ Nat.card Phi := by
    rcases (IsPGroup.nontrivial_iff_card hPhiP).mp inferInstance with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨z, hzOrder⟩ := exists_prime_orderOf_dvd_card' 2 htwoDvdPhi
  have hzPhi : IsInvolution z :=
    let hz := orderOf_eq_prime_iff.mp hzOrder
    ⟨hz.2, hz.1⟩
  let zQ : Q := (z : Q)
  have hzQ : IsInvolution zQ :=
    IsInvolution.map_of_injective hzPhi Phi.subtype Phi.subtype_injective
  let zX : X := (zQ : X)
  have hzX : IsInvolution zX :=
    IsInvolution.map_of_injective hzQ Q.subtype Q.subtype_injective
  let PhiX : Subgroup X := Phi.map Q.subtype
  letI : Phi.Characteristic := by
    simpa [Phi] using (frattini_characteristic (G := Q))
  have hPhiXNormal : PhiX.Normal := by
    dsimp [PhiX]
    exact ConjAct.normal_of_characteristic_of_normal
  have hzPhiX : zX ∈ PhiX := by
    exact Subgroup.mem_map_of_mem Q.subtype z.property
  letI : MulAction X (II1Hering31Involutions X) :=
    ii1Hering31ConjugationAction X
  haveI : MulAction.IsMultiplyPretransitive X
      (II1Hering31Involutions X) 2 :=
    ii1Hering31ConjugationAction_twoPretransitive htwo
  haveI : MulAction.IsPretransitive X (II1Hering31Involutions X) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hNlePhiX : N ≤ PhiX := by
    intro n hn
    rcases hn with rfl | hn
    · exact PhiX.one_mem
    · let zI : II1Hering31Involutions X := ⟨zX, hzX⟩
      let nI : II1Hering31Involutions X := ⟨n, hn⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X zI nI
      have hconj : g * zX * g⁻¹ = n := congrArg Subtype.val hg
      rw [← hconj]
      exact hPhiXNormal.conj_mem zX hzPhiX g
  intro n hn
  have hnPhiX : (n : X) ∈ PhiX := hNlePhiX hn
  rcases hnPhiX with ⟨q, hq, hqn⟩
  have hqeq : q = n := Q.subtype_injective hqn
  simpa [hqeq] using hq

/-- In the nonabelian branch, Higman's center theorem identifies the center of
the two-core with the ambient subgroup consisting of the identity and all
involutions. -/
private theorem ii1Hering31_twoCore_center_eq_involutionSubgroup
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (hSuzuki : IsSuzukiTwoGroup (pCore 2 X)) :
    let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
    let Q : Subgroup X := pCore 2 X
    N.subgroupOf Q = Subgroup.center Q := by
  classical
  dsimp only
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  have hNleQ : N ≤ Q :=
    ii1Hering31InvolutionSubgroup_le_twoCore hcomm
  have hQcentralizer : Subgroup.centralizer (N : Set X) = Q :=
    ii1Hering31_centralizer_involutionSubgroup_eq_twoCore
      hsmall htwo hrank hcomm
  have hHigman := (External.Higman.theorem1_involutions_center hSuzuki).1
  ext q
  constructor
  · intro hqN
    rw [Subgroup.mem_center_iff]
    intro r
    apply Q.subtype_injective
    have hrCentralizes : (r : X) ∈ Subgroup.centralizer (N : Set X) := by
      rw [hQcentralizer]
      exact r.property
    simpa using (hrCentralizes (q : X) hqN).symm
  · intro hqCenter
    by_cases hqOne : q = 1
    · change (q : X) = 1 ∨ IsInvolution (q : X)
      exact Or.inl (congrArg Q.subtype hqOne)
    · have hqInvQ : IsInvolution q := by
        have hqSet : q ∈ {z : Q | z ∈ Subgroup.center Q ∧ z ≠ 1} :=
          ⟨hqCenter, hqOne⟩
        rw [← hHigman] at hqSet
        exact hqSet
      have hqInvX : IsInvolution (q : X) :=
        IsInvolution.map_of_injective hqInvQ Q.subtype Q.subtype_injective
      exact Or.inr hqInvX

/-- Coordinate-free transport of the square-map obstruction.  Once the square
map from the central quotient is represented by `quad`, an automorphism of the
group extending `tau` on the center would induce an additive equivalence `L`
satisfying `quad (L v) = tau (quad v)`. -/
private theorem ii1Hering31_no_center_lift_of_quadratic_coordinates
    {P : Type u} {V F : Type v} [Group P] [AddCommGroup V] [AddCommGroup F]
    (hsquare : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (eQ : (P ⧸ Subgroup.center P) ≃* Multiplicative V)
    (eZ : Subgroup.center P ≃* Multiplicative F)
    (quad : V → F)
    (hsquareCoord : ∀ x : P,
      (eZ ⟨x ^ 2, hsquare x⟩).toAdd =
        quad (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd)
    (tau : F ≃+ F)
    (hNoLift : ∀ L : V ≃+ V,
      (∀ v : V, quad (L v) = tau (quad v)) → False) :
    ∃ tauZ : MulAut (Subgroup.center P),
      ∀ alpha : MulAut P, ii1Hering31CenterAction P alpha ≠ tauZ := by
  classical
  let tauMul : MulAut (Multiplicative F) := tau.toMultiplicative
  let tauZ : MulAut (Subgroup.center P) :=
    eZ.trans (tauMul.trans eZ.symm)
  refine ⟨tauZ, ?_⟩
  intro alpha halpha
  let alphaBar : MulAut (P ⧸ Subgroup.center P) :=
    ii1Hering31CenterQuotientAction P alpha
  let Lmul : MulAut (Multiplicative V) :=
    eQ.symm.trans (alphaBar.trans eQ)
  let L : V ≃+ V := MulAutMultiplicative V Lmul
  apply hNoLift L
  intro v
  let q : P ⧸ Subgroup.center P := eQ.symm (Multiplicative.ofAdd v)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) q
  have hxCoord :
      (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd = v := by
    rw [hx]
    simp [q]
  have hLCoord :
      (eQ (QuotientGroup.mk' (Subgroup.center P) (alpha x))).toAdd =
        L v := by
    calc
      (eQ (QuotientGroup.mk' (Subgroup.center P) (alpha x))).toAdd =
          (eQ (alphaBar
            (QuotientGroup.mk' (Subgroup.center P) x))).toAdd := by
              rw [ii1Hering31CenterQuotientAction_mk]
      _ = L
          (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd := by
            simp [L, Lmul, MulAutMultiplicative_apply_apply]
      _ = L v := by rw [hxCoord]
  have hcenterCoord :
      (eZ ⟨(alpha x) ^ 2, hsquare (alpha x)⟩).toAdd =
        tau (eZ ⟨x ^ 2, hsquare x⟩).toAdd := by
    let z : Subgroup.center P := ⟨x ^ 2, hsquare x⟩
    have hcompat := ii1Hering31CenterActions_square alpha x (hsquare x)
    have heval : ii1Hering31CenterAction P alpha z = tauZ z :=
      congrArg (fun f : MulAut (Subgroup.center P) => f z) halpha
    calc
      (eZ ⟨(alpha x) ^ 2, hsquare (alpha x)⟩).toAdd =
          (eZ (ii1Hering31CenterAction P alpha z)).toAdd := by
            exact congrArg (fun w : Subgroup.center P => (eZ w).toAdd)
              hcompat.symm
      _ = (eZ (tauZ z)).toAdd := by rw [heval]
      _ = tau (eZ z).toAdd := by
        simp [tauZ, tauMul]
      _ = tau (eZ ⟨x ^ 2, hsquare x⟩).toAdd := rfl
  calc
    quad (L v) =
        (eZ ⟨(alpha x) ^ 2, hsquare (alpha x)⟩).toAdd := by
          rw [hsquareCoord, hLCoord]
    _ = tau (eZ ⟨x ^ 2, hsquare x⟩).toAdd := hcenterCoord
    _ = tau (quad
        (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd) := by
          rw [hsquareCoord]
    _ = tau (quad v) := by rw [hxCoord]

/-! The three-coordinate branches share the same quotient bookkeeping.  The
following helper isolates that bookkeeping; the branch-specific input is only
the first-coordinate cocycle and the resulting quadratic square map. -/

private theorem ii1Hering31_triple_forbidden_center_aut
    {P : Type u} {F : Type v} [Group P] [AddCommGroup F]
    [Finite P] [Finite F]
    (tripleLift : F → F → F → P)
    (cocycle : F → F → F → F → F)
    (hone : tripleLift 0 0 0 = 1)
    (hzeroLeft : ∀ a b : F, cocycle 0 0 a b = 0)
    (hzeroRight : ∀ a b : F, cocycle a b 0 0 = 0)
    (hsurj : ∀ x : P, ∃ c a b : F, x = tripleLift c a b)
    (hinj : ∀ c a b d e f : F,
      tripleLift c a b = tripleLift d e f → c = d ∧ a = e ∧ b = f)
    (hmul : ∀ c a b d e f : F,
      tripleLift c a b * tripleLift d e f =
        tripleLift (c + d + cocycle a b e f) (a + e) (b + f))
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3)
    (quad : F × F → F)
    (hsquareRaw : ∀ c a b : F,
      (tripleLift c a b) ^ 2 = tripleLift (quad (a, b)) 0 0)
    (tau : F ≃+ F)
    (hNoLift : ∀ L : (F × F) ≃+ (F × F),
      (∀ v : F × F, quad (L v) = tau (quad v)) → False) :
    ∃ tauZ : MulAut (Subgroup.center P),
      ∀ alpha : MulAut P, ii1Hering31CenterAction P alpha ≠ tauZ := by
  classical
  have htripleBijective : Function.Bijective
      (fun cab : F × F × F => tripleLift cab.1 cab.2.1 cab.2.2) := by
    constructor
    · intro cab dbf hEq
      rcases hinj cab.1 cab.2.1 cab.2.2
          dbf.1 dbf.2.1 dbf.2.2 hEq with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x with ⟨c, a, b, hx⟩
      exact ⟨(c, a, b), hx.symm⟩
  let tripleEquiv : F × F × F ≃ P :=
    Equiv.ofBijective (fun cab : F × F × F =>
      tripleLift cab.1 cab.2.1 cab.2.2) htripleBijective
  have htripleEquiv_apply (c a b : F) :
      tripleEquiv (c, a, b) = tripleLift c a b := rfl
  have hPraw : Nat.card P = (Nat.card F) ^ 3 := by
    calc
      Nat.card P = Nat.card (F × F × F) :=
        (Nat.card_congr tripleEquiv).symm
      _ = Nat.card F * (Nat.card F * Nat.card F) := by
        rw [Nat.card_prod, Nat.card_prod]
      _ = (Nat.card F) ^ 3 := by ring
  have hcenterCard : Nat.card (Subgroup.center P) = Nat.card F := by
    apply Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)
    calc
      Nat.card (Subgroup.center P) ^ 3 = Nat.card P := hcard.symm
      _ = (Nat.card F) ^ 3 := hPraw
  let centerMap : Multiplicative F →* Subgroup.center P :=
    { toFun := fun c =>
        ⟨tripleLift c.toAdd 0 0, by
          rw [Subgroup.mem_center_iff]
          intro x
          rcases hsurj x with ⟨d, a, b, hx⟩
          change x * tripleLift c.toAdd 0 0 =
            tripleLift c.toAdd 0 0 * x
          rw [hx, hmul, hmul, hzeroLeft, hzeroRight]
          simp [add_comm]⟩
      map_one' := by
        apply Subtype.ext
        simpa using hone
      map_mul' := by
        intro c d
        apply Subtype.ext
        change tripleLift (c.toAdd + d.toAdd) 0 0 =
          tripleLift c.toAdd 0 0 * tripleLift d.toAdd 0 0
        rw [hmul, hzeroRight]
        simp }
  have hcenterMapInjective : Function.Injective centerMap := by
    intro c d hEq
    apply Multiplicative.toAdd.injective
    have hval := congrArg
      (fun x : Subgroup.center P => (x : P)) hEq
    exact (hinj c.toAdd 0 0 d.toAdd 0 0 hval).1
  have hcenterMapBijective : Function.Bijective centerMap :=
    hcenterMapInjective.bijective_of_nat_card_le (by
      rw [hcenterCard]
      rfl)
  let eZ : Subgroup.center P ≃* Multiplicative F :=
    (MulEquiv.ofBijective centerMap hcenterMapBijective).symm
  let piNat : P →* Multiplicative (F × F) :=
    { toFun := fun p => Multiplicative.ofAdd (tripleEquiv.symm p).2
      map_one' := by
        apply Multiplicative.ofAdd.injective
        have hcoords : tripleEquiv.symm (1 : P) = (0, 0, 0) := by
          apply tripleEquiv.injective
          rw [tripleEquiv.apply_symm_apply, htripleEquiv_apply, hone]
        rw [hcoords]
        rfl
      map_mul' := by
        intro x y
        obtain ⟨⟨c, a, b⟩, rfl⟩ := tripleEquiv.surjective x
        obtain ⟨⟨d, e, f⟩, rfl⟩ := tripleEquiv.surjective y
        simp only [tripleEquiv.symm_apply_apply]
        rw [htripleEquiv_apply, htripleEquiv_apply]
        change Multiplicative.ofAdd
            (tripleEquiv.symm
              (tripleLift c a b * tripleLift d e f)).2 =
          Multiplicative.ofAdd ((a, b) + (e, f))
        apply Multiplicative.ofAdd.injective
        rw [hmul]
        have hcoords : tripleEquiv.symm
            (tripleLift (c + d + cocycle a b e f) (a + e) (b + f)) =
              (c + d + cocycle a b e f, a + e, b + f) := by
          apply tripleEquiv.injective
          rw [tripleEquiv.apply_symm_apply, htripleEquiv_apply]
        rw [hcoords]
        rfl }
  have hpiNat_surj : Function.Surjective piNat := by
    intro ab
    let p := tripleLift 0 ab.toAdd.1 ab.toAdd.2
    refine ⟨p, ?_⟩
    apply Multiplicative.ofAdd.injective
    change (tripleEquiv.symm p).2 = ab.toAdd
    have hcoords : tripleEquiv.symm p =
        (0, ab.toAdd.1, ab.toAdd.2) := by
      apply tripleEquiv.injective
      rw [tripleEquiv.apply_symm_apply, htripleEquiv_apply]
    rw [hcoords]
  have hpiNat_ker_le : piNat.ker ≤ Subgroup.center P := by
    intro p hp
    have hpOne : piNat p = 1 := MonoidHom.mem_ker.mp hp
    let cab := tripleEquiv.symm p
    have ha : cab.2.1 = 0 := by
      have h := congrArg
        (fun q : Multiplicative (F × F) => (q.toAdd).1) hpOne
      simpa [piNat, cab] using h
    have hb : cab.2.2 = 0 := by
      have h := congrArg
        (fun q : Multiplicative (F × F) => (q.toAdd).2) hpOne
      simpa [piNat, cab] using h
    have hpCoord : p = tripleLift cab.1 cab.2.1 cab.2.2 :=
      (tripleEquiv.apply_symm_apply p).symm
    rw [hpCoord, ha, hb]
    exact (centerMap (Multiplicative.ofAdd cab.1)).property
  have hquotCard : Nat.card (P ⧸ piNat.ker) = Nat.card (F × F) := by
    exact Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective piNat hpiNat_surj).toEquiv
  have hkerCard : Nat.card piNat.ker = Nat.card F := by
    have hcardMul := Subgroup.card_eq_card_quotient_mul_card_subgroup
      piNat.ker
    have hmulCard : Nat.card F * Nat.card F * Nat.card piNat.ker =
        Nat.card F * Nat.card F * Nat.card F := by
      calc
        Nat.card F * Nat.card F * Nat.card piNat.ker =
            Nat.card (P ⧸ piNat.ker) * Nat.card piNat.ker := by
              rw [hquotCard, Nat.card_prod]
        _ = Nat.card P := hcardMul.symm
        _ = (Nat.card F) ^ 3 := hPraw
        _ = Nat.card F * Nat.card F * Nat.card F := by ring
    exact Nat.mul_left_cancel
      (Nat.mul_pos Nat.card_pos Nat.card_pos) hmulCard
  have hkerEqCenter : piNat.ker = Subgroup.center P :=
    Subgroup.eq_of_le_of_card_ge hpiNat_ker_le (by
      rw [hkerCard, hcenterCard])
  let eQ : (P ⧸ Subgroup.center P) ≃*
      Multiplicative (F × F) :=
    (QuotientGroup.quotientMulEquivOfEq hkerEqCenter.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective piNat hpiNat_surj)
  have heQ_mk (p : P) :
      eQ (QuotientGroup.mk' (Subgroup.center P) p) = piNat p := by
    change QuotientGroup.kerLift piNat
        (QuotientGroup.quotientMulEquivOfEq hkerEqCenter.symm
          (QuotientGroup.mk' (Subgroup.center P) p)) = piNat p
    calc
      QuotientGroup.kerLift piNat
          (QuotientGroup.quotientMulEquivOfEq hkerEqCenter.symm
            (QuotientGroup.mk' (Subgroup.center P) p)) =
        QuotientGroup.kerLift piNat (QuotientGroup.mk' piNat.ker p) := by
          exact congrArg (QuotientGroup.kerLift piNat)
            (QuotientGroup.quotientMulEquivOfEq_mk hkerEqCenter.symm p)
      _ = piNat p := QuotientGroup.kerLift_mk piNat p
  have hsquare : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    intro x
    rcases hsurj x with ⟨c, a, b, hx⟩
    rw [hx, hsquareRaw]
    exact (centerMap (Multiplicative.ofAdd (quad (a, b)))).property
  have hsquareCoord : ∀ x : P,
      (eZ ⟨x ^ 2, hsquare x⟩).toAdd =
        quad (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd := by
    intro x
    rcases hsurj x with ⟨c, a, b, hx⟩
    have hcoord :
        (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd = (a, b) := by
      rw [hx, heQ_mk]
      have hcoords : tripleEquiv.symm (tripleLift c a b) =
          (c, a, b) := by
        apply tripleEquiv.injective
        rw [tripleEquiv.apply_symm_apply, htripleEquiv_apply]
      simp [piNat, hcoords]
    have hsq : x ^ 2 =
        (centerMap (Multiplicative.ofAdd (quad (a, b))) : Subgroup.center P) := by
      rw [hx, hsquareRaw]
      rfl
    have hcenterEq :
        (⟨x ^ 2, hsquare x⟩ : Subgroup.center P) =
          centerMap (Multiplicative.ofAdd (quad (a, b))) := by
      apply Subtype.ext
      exact hsq
    calc
      (eZ ⟨x ^ 2, hsquare x⟩).toAdd =
          (eZ (centerMap (Multiplicative.ofAdd (quad (a, b))))).toAdd := by
            rw [hcenterEq]
      _ = quad (a, b) := by
        change ((MulEquiv.ofBijective centerMap hcenterMapBijective).symm
          (centerMap (Multiplicative.ofAdd (quad (a, b))))).toAdd = _
        exact congrArg Multiplicative.toAdd
          ((MulEquiv.ofBijective centerMap hcenterMapBijective).symm_apply_apply
            (Multiplicative.ofAdd (quad (a, b))))
      _ = quad (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd := by
        rw [hcoord]
  exact ii1Hering31_no_center_lift_of_quadratic_coordinates
    (P := P) (V := F × F) (F := F)
    hsquare eQ eZ (fun v => quad v) hsquareCoord tau hNoLift

/-- In Higman type A with center of order eight, the fixed `F₈`
transvection does not extend to an automorphism of the Suzuki two-group. -/
private theorem ii1Hering31_typeA_forbidden_center_aut
    {P : Type u} [Group P]
    (hP : IsSuzukiTwoGroup P)
    (hcenterCard : Nat.card (Subgroup.center P) = 8)
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 2) :
    ∃ tauZ : MulAut (Subgroup.center P),
      ∀ alpha : MulAut P, ii1Hering31CenterAction P alpha ≠ tauZ := by
  classical
  rcases hP.2.2.2 with
    ⟨K, hKGroup, hKAction, hKcyclic, hKfaithful, hKregular⟩
  letI : Group K := hKGroup
  letI : MulDistribMulAction K P := hKAction
  obtain ⟨n, hn, theta, pairLift, cocycle, _eK, eQ, eZ,
      _hperiod, htheta, _haddLeft, _haddRight, hdiag, _hmem,
      _hone, hsurj, _hinj, hmul, hcenterCardN, _hKQ, _hKZ,
      hpairQ, hpairZ⟩ :=
    PFAppendixIII.higmanTheorem_order_center_sq_typeA
      hP hKcyclic hKfaithful hKregular hcard
  have hnThree : n = 3 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    calc
      2 ^ n = Nat.card (Subgroup.center P) := hcenterCardN.symm
      _ = 8 := hcenterCard
      _ = 2 ^ 3 := by norm_num
  subst n
  let quad : BinaryGaloisField 3 → BinaryGaloisField 3 :=
    fun a => a * theta a
  have hsquare : ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
    intro x
    rcases hsurj x with ⟨a, z, hx⟩
    have hsq : x ^ 2 = pairLift 0 (quad a) := by
      rw [hx, pow_two, hmul, hdiag]
      simp only [CharTwo.add_self_eq_zero, zero_add]
      rfl
    rw [hsq, hpairZ]
    exact (eZ.symm (Multiplicative.ofAdd (quad a))).property
  have hsquareCoord : ∀ x : P,
      (eZ ⟨x ^ 2, hsquare x⟩).toAdd =
        quad (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd := by
    intro x
    rcases hsurj x with ⟨a, z, hx⟩
    have hsq : x ^ 2 = pairLift 0 (quad a) := by
      rw [hx, pow_two, hmul, hdiag]
      simp only [CharTwo.add_self_eq_zero, zero_add]
      rfl
    have hcenterEq :
        (⟨x ^ 2, hsquare x⟩ : Subgroup.center P) =
          eZ.symm (Multiplicative.ofAdd (quad a)) := by
      apply Subtype.ext
      calc
        x ^ 2 = pairLift 0 (quad a) := hsq
        _ = (eZ.symm (Multiplicative.ofAdd (quad a)) :
            Subgroup.center P) := hpairZ (quad a)
    calc
      (eZ ⟨x ^ 2, hsquare x⟩).toAdd = quad a := by
        rw [hcenterEq, eZ.apply_symm_apply]
        rfl
      _ = quad
          (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd := by
            rw [hx, hpairQ]
  exact ii1Hering31_no_center_lift_of_quadratic_coordinates
    (P := P) (V := BinaryGaloisField 3) (F := BinaryGaloisField 3)
    hsquare eQ eZ quad hsquareCoord ii1Hering31F8Transvection
    (fun (L : BinaryGaloisField 3 ≃+ BinaryGaloisField 3) hL =>
      ii1Hering31F8_typeA_no_lift theta htheta L (by
        intro a
        simpa [quad] using hL a))

/-- The fixed `F₈` transvection also cannot lift through a type-B Higman
coordinate system. -/
private theorem ii1Hering31_typeB_forbidden_center_aut
    {P : Type u} [Group P]
    (hB : IsSuzukiTwoTypeB (⊤ : Subgroup P))
    (hcenterCard : Nat.card (Subgroup.center P) = 8)
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3) :
    ∃ tauZ : MulAut (Subgroup.center P),
      ∀ alpha : MulAut P, ii1Hering31CenterAction P alpha ≠ tauZ := by
  classical
  rcases hB with
    ⟨n, hn, theta, epsilon, tripleLift, cocycle, hepsilon,
      hperiod, hanisotropic, haddLeft, haddRight, hdiag,
      _hmem, hone, hsurj, hinj, hmul⟩
  let F := BinaryGaloisField n
  have hzeroLeft : ∀ a b : F, cocycle 0 0 a b = 0 := by
    intro a b
    simpa only [zero_add, CharTwo.add_self_eq_zero] using
      haddLeft 0 0 0 0 a b
  have hzeroRight : ∀ a b : F, cocycle a b 0 0 = 0 := by
    intro a b
    simpa only [zero_add, CharTwo.add_self_eq_zero] using
      haddRight a b 0 0 0 0
  have htripleBijective : Function.Bijective
      (fun cab : F × F × F => tripleLift cab.1 cab.2.1 cab.2.2) := by
    constructor
    · intro cab dbf hEq
      rcases hinj cab.1 cab.2.1 cab.2.2
          dbf.1 dbf.2.1 dbf.2.2 hEq with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨c, a, b, hx⟩
      exact ⟨(c, a, b), hx.symm⟩
  letI : Finite P := Finite.of_surjective
    (fun cab : F × F × F => tripleLift cab.1 cab.2.1 cab.2.2)
    htripleBijective.2
  let tripleEquiv : F × F × F ≃ P :=
    Equiv.ofBijective (fun cab : F × F × F =>
      tripleLift cab.1 cab.2.1 cab.2.2) htripleBijective
  have hPraw : Nat.card P = (Nat.card F) ^ 3 := by
    calc
      Nat.card P = Nat.card (F × F × F) :=
        (Nat.card_congr tripleEquiv).symm
      _ = Nat.card F * (Nat.card F * Nat.card F) := by
        rw [Nat.card_prod, Nat.card_prod]
      _ = (Nat.card F) ^ 3 := by ring
  have hcenterCardF : Nat.card (Subgroup.center P) = Nat.card F := by
    apply Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)
    calc
      Nat.card (Subgroup.center P) ^ 3 = Nat.card P := hcard.symm
      _ = (Nat.card F) ^ 3 := hPraw
  have hFcard : Nat.card F = 2 ^ n := by
    simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
  have hnThree : n = 3 := by
    apply Nat.pow_right_injective (by norm_num : (2 : ℕ) ≤ 2)
    calc
      2 ^ n = Nat.card F := hFcard.symm
      _ = Nat.card (Subgroup.center P) := hcenterCardF.symm
      _ = 8 := hcenterCard
      _ = 2 ^ 3 := by norm_num
  subst n
  let quad : BinaryGaloisField 3 × BinaryGaloisField 3 →
      BinaryGaloisField 3 := fun ab =>
    ab.1 * theta ab.1 + epsilon * ab.1 * theta ab.2 +
      ab.2 * theta ab.2
  have hsquareRaw : ∀ c a b : BinaryGaloisField 3,
      (tripleLift c a b) ^ 2 = tripleLift (quad (a, b)) 0 0 := by
    intro c a b
    rw [pow_two, hmul, hdiag]
    simp only [CharTwo.add_self_eq_zero, zero_add]
    rfl
  exact ii1Hering31_triple_forbidden_center_aut
    tripleLift cocycle hone hzeroLeft hzeroRight
    (fun x => by simpa using hsurj x (Subgroup.mem_top x))
    hinj hmul hcard quad hsquareRaw ii1Hering31F8Transvection
    (fun (L : (BinaryGaloisField 3 × BinaryGaloisField 3) ≃+
        (BinaryGaloisField 3 × BinaryGaloisField 3)) hL =>
      ii1Hering31F8_typeB_no_lift theta epsilon hepsilon
        (by simpa using hanisotropic) L (by
          intro v
          simpa [quad] using hL v))

/-- The fixed `F₈` transvection cannot lift through a type-C Higman
coordinate system. -/
private theorem ii1Hering31_typeC_forbidden_center_aut
    {P : Type u} [Group P]
    (hC : External.Higman.IsSuzukiTwoTypeC (⊤ : Subgroup P))
    (hcenterCard : Nat.card (Subgroup.center P) = 8)
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3) :
    ∃ tauZ : MulAut (Subgroup.center P),
      ∀ alpha : MulAut P, ii1Hering31CenterAction P alpha ≠ tauZ := by
  classical
  rcases hC with
    ⟨n, hn, theta, epsilon, tripleLift, hepsilon, _hperiod,
      hthetaSquare, havoid, _hmem, hone, hsurj, hinj, hmul⟩
  let F := BinaryGaloisField n
  let cocycle : F → F → F → F → F := fun a b e f =>
    a * theta e + epsilon * a ^ (2 ^ (n - 1)) * theta (f ^ 2) + b * f
  have hpowPos : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
  have hzeroLeft : ∀ a b : F, cocycle 0 0 a b = 0 := by
    intro a b
    simp [cocycle, hpowPos.ne']
  have hzeroRight : ∀ a b : F, cocycle a b 0 0 = 0 := by
    intro a b
    simp [cocycle]
  have hmul' : ∀ c a b d e f : F,
      tripleLift c a b * tripleLift d e f =
        tripleLift (c + d + cocycle a b e f) (a + e) (b + f) := by
    intro c a b d e f
    rw [hmul]
    congr 1
    dsimp [cocycle]
    abel
  have htripleBijective : Function.Bijective
      (fun cab : F × F × F => tripleLift cab.1 cab.2.1 cab.2.2) := by
    constructor
    · intro cab dbf hEq
      rcases hinj cab.1 cab.2.1 cab.2.2
          dbf.1 dbf.2.1 dbf.2.2 hEq with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨c, a, b, hx⟩
      exact ⟨(c, a, b), hx.symm⟩
  letI : Finite P := Finite.of_surjective
    (fun cab : F × F × F => tripleLift cab.1 cab.2.1 cab.2.2)
    htripleBijective.2
  let tripleEquiv : F × F × F ≃ P :=
    Equiv.ofBijective (fun cab : F × F × F =>
      tripleLift cab.1 cab.2.1 cab.2.2) htripleBijective
  have hPraw : Nat.card P = (Nat.card F) ^ 3 := by
    calc
      Nat.card P = Nat.card (F × F × F) :=
        (Nat.card_congr tripleEquiv).symm
      _ = Nat.card F * (Nat.card F * Nat.card F) := by
        rw [Nat.card_prod, Nat.card_prod]
      _ = (Nat.card F) ^ 3 := by ring
  have hcenterCardF : Nat.card (Subgroup.center P) = Nat.card F := by
    apply Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)
    calc
      Nat.card (Subgroup.center P) ^ 3 = Nat.card P := hcard.symm
      _ = (Nat.card F) ^ 3 := hPraw
  have hFcard : Nat.card F = 2 ^ n := by
    simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
  have hnThree : n = 3 := by
    apply Nat.pow_right_injective (by norm_num : (2 : ℕ) ≤ 2)
    calc
      2 ^ n = Nat.card F := hFcard.symm
      _ = Nat.card (Subgroup.center P) := hcenterCardF.symm
      _ = 8 := hcenterCard
      _ = 2 ^ 3 := by norm_num
  subst n
  let quad : BinaryGaloisField 3 × BinaryGaloisField 3 →
      BinaryGaloisField 3 := fun ab =>
    ab.1 * theta ab.1 + epsilon * ab.1 ^ 4 * theta (ab.2 ^ 2) +
      ab.2 ^ 2
  have hsquareRaw : ∀ c a b : BinaryGaloisField 3,
      (tripleLift c a b) ^ 2 = tripleLift (quad (a, b)) 0 0 := by
    intro c a b
    rw [pow_two, hmul']
    simp only [CharTwo.add_self_eq_zero, zero_add]
    congr 1
    simp [cocycle, quad, pow_two]
  exact ii1Hering31_triple_forbidden_center_aut
    tripleLift cocycle hone hzeroLeft hzeroRight
    (fun x => by simpa using hsurj x (Subgroup.mem_top x))
    hinj hmul' hcard quad hsquareRaw ii1Hering31F8Transvection
    (fun (L : (BinaryGaloisField 3 × BinaryGaloisField 3) ≃+
        (BinaryGaloisField 3 × BinaryGaloisField 3)) hL =>
      ii1Hering31F8_typeC_no_lift theta epsilon hepsilon
        (by simpa using hthetaSquare) (by simpa using havoid) L (by
          intro v
          simpa [quad] using hL v))

/-- Type D is impossible when the center has order eight: its required
nontrivial field automorphism would have period five on `F₈`. -/
private theorem ii1Hering31_typeD_false
    {P : Type u} [Group P]
    (hD : External.Higman.IsSuzukiTwoTypeD (⊤ : Subgroup P))
    (hcenterCard : Nat.card (Subgroup.center P) = 8)
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3) : False := by
  classical
  rcases hD with
    ⟨n, hn, theta, _epsilon, tripleLift, _hepsilon, hperiod,
      hthetaNontrivial, _havoid, _hmem, _hone, hsurj, hinj, _hmul⟩
  let F := BinaryGaloisField n
  have htripleBijective : Function.Bijective
      (fun cab : F × F × F => tripleLift cab.1 cab.2.1 cab.2.2) := by
    constructor
    · intro cab dbf hEq
      rcases hinj cab.1 cab.2.1 cab.2.2
          dbf.1 dbf.2.1 dbf.2.2 hEq with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨c, a, b, hx⟩
      exact ⟨(c, a, b), hx.symm⟩
  let tripleEquiv : F × F × F ≃ P :=
    Equiv.ofBijective (fun cab : F × F × F =>
      tripleLift cab.1 cab.2.1 cab.2.2) htripleBijective
  have hPraw : Nat.card P = (Nat.card F) ^ 3 := by
    calc
      Nat.card P = Nat.card (F × F × F) :=
        (Nat.card_congr tripleEquiv).symm
      _ = Nat.card F * (Nat.card F * Nat.card F) := by
        rw [Nat.card_prod, Nat.card_prod]
      _ = (Nat.card F) ^ 3 := by ring
  have hcenterCardF : Nat.card (Subgroup.center P) = Nat.card F := by
    apply Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)
    calc
      Nat.card (Subgroup.center P) ^ 3 = Nat.card P := hcard.symm
      _ = (Nat.card F) ^ 3 := hPraw
  have hFcard : Nat.card F = 2 ^ n := by
    simpa [F, BinaryGaloisField] using GaloisField.card 2 n hn
  have hnThree : n = 3 := by
    apply Nat.pow_right_injective (by norm_num : (2 : ℕ) ≤ 2)
    calc
      2 ^ n = Nat.card F := hFcard.symm
      _ = Nat.card (Subgroup.center P) := hcenterCardF.symm
      _ = 8 := hcenterCard
      _ = 2 ^ 3 := by norm_num
  subst n
  exact ii1Hering31F8_typeD_false theta hperiod hthetaNontrivial

/-- Every Suzuki two-group with center of order eight has a center
automorphism which is not induced by an automorphism of the whole group. -/
private theorem ii1Hering31_suzuki_forbidden_center_aut
    {P : Type u} [Group P]
    (hP : IsSuzukiTwoGroup P)
    (hcenterCard : Nat.card (Subgroup.center P) = 8) :
    ∃ tauZ : MulAut (Subgroup.center P),
      ∀ alpha : MulAut P, ii1Hering31CenterAction P alpha ≠ tauZ := by
  rcases External.Higman.theorem1b_abcdAlternatives hP with
    hA | hB | hC | hD
  · exact ii1Hering31_typeA_forbidden_center_aut hP hcenterCard
      (External.Higman.theorem1b_typeA_data hA).1
  · exact ii1Hering31_typeB_forbidden_center_aut hB hcenterCard
      (External.Higman.theorem1b_typeB_data hB).1
  · exact ii1Hering31_typeC_forbidden_center_aut hC hcenterCard
      (External.Higman.theorem1b_typeC_data hC).1
  · exact (ii1Hering31_typeD_false hD hcenterCard
      (External.Higman.theorem1b_typeD_data hD).1).elim

/-- The nonabelian two-core alternative is incompatible with the full ambient
conjugation action on the order-eight involution subgroup. -/
private theorem ii1Hering31_suzuki_twoCore_false
    {X : Type u} [Group X] [Finite X]
    (hsmall : ∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y)
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X)))
    (hrank : TwoRankAtLeastTwo X)
    (hcomm : ∀ {x y : X}, IsInvolution x → IsInvolution y → Commute x y)
    (hSuzuki : IsSuzukiTwoGroup (pCore 2 X)) : False := by
  classical
  let N : Subgroup X := ii1Hering31InvolutionSubgroup X hcomm
  let Q : Subgroup X := pCore 2 X
  letI : N.Normal := ii1Hering31InvolutionSubgroup_normal hcomm
  letI : Q.Normal := pCore_normal
  have hNleQ : N ≤ Q :=
    ii1Hering31InvolutionSubgroup_le_twoCore hcomm
  have hcenterEq : N.subgroupOf Q = Subgroup.center Q :=
    ii1Hering31_twoCore_center_eq_involutionSubgroup
      hsmall htwo hrank hcomm hSuzuki
  have hNcard : Nat.card N = 8 :=
    ii1Hering31_involution_subgroup_card hsmall htwo hrank hcomm
  have hcenterCard : Nat.card (Subgroup.center Q) = 8 := by
    calc
      Nat.card (Subgroup.center Q) = Nat.card (N.subgroupOf Q) := by
        rw [hcenterEq]
      _ = Nat.card N :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNleQ).toEquiv
      _ = 8 := hNcard
  obtain ⟨tauZ, hNoLift⟩ :=
    ii1Hering31_suzuki_forbidden_center_aut hSuzuki hcenterCard
  let eNQ : N ≃* Subgroup.center Q :=
    { toFun := fun n =>
        ⟨⟨(n : X), hNleQ n.property⟩, by
          rw [← hcenterEq]
          exact n.property⟩
      invFun := fun z =>
        ⟨((z : Subgroup.center Q) : Q), by
          have hz : (z : Q) ∈ N.subgroupOf Q := by
            rw [hcenterEq]
            exact z.property
          exact hz⟩
      left_inv := by intro n; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl
      map_mul' := by intro n m; apply Subtype.ext; apply Subtype.ext; rfl }
  let tauN : MulAut N := eNQ.trans (tauZ.trans eNQ.symm)
  let phi : X →* MulAut N := MulAut.conjNormal (H := N)
  obtain ⟨x, hx⟩ :=
    (ii1Hering31_conjNormal_surjective hsmall htwo hrank hcomm) tauN
  let alphaQ : MulAut Q := MulAut.conjNormal (H := Q) x
  apply hNoLift alphaQ
  apply MulEquiv.ext
  intro z
  apply Subtype.ext
  apply Q.subtype_injective
  let n : N := eNQ.symm z
  have hxApply : phi x n = tauN n :=
    congrArg (fun alpha : MulAut N => alpha n) hx
  have hxApplyX := congrArg N.subtype hxApply
  simpa [phi, alphaQ, tauN, n, eNQ,
    ii1Hering31CenterAction_apply, MulAut.conjNormal_apply,
    MulAut.conj_apply] using hxApplyX

/-- Hering's theorem for a finite group acting doubly transitively on all of
its involutions.  The proof is the cardinal-minimal core used by the ambient
subgroup statement. -/
private theorem ii1Hering31_top
    {X : Type u} [Group X] [Finite X]
    (htwo : ConjugationTwoTransitiveOn (⊤ : Subgroup X)
      (involutionsInSet (⊤ : Subgroup X))) :
    ¬ TwoRankAtLeastTwo X := by
  let P : ℕ → Prop := fun n ↦
    ∀ {Y : Type u} [Group Y] [Finite Y], Nat.card Y = n →
      ConjugationTwoTransitiveOn (⊤ : Subgroup Y)
        (involutionsInSet (⊤ : Subgroup Y)) →
      ¬ TwoRankAtLeastTwo Y
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Y _ _ hcard htwoY hrankY
        have hsmall : ∀ {Z : Type u} [Group Z] [Finite Z],
            Nat.card Z < Nat.card Y →
            ConjugationTwoTransitiveOn (⊤ : Subgroup Z)
              (involutionsInSet (⊤ : Subgroup Z)) →
            ¬ TwoRankAtLeastTwo Z := by
          intro Z _ _ hZY htwoZ
          apply ih (Nat.card Z)
          · simpa [hcard] using hZY
          · exact rfl
          · exact htwoZ
        have hcomm : ∀ {x y : Y}, IsInvolution x → IsInvolution y →
            Commute x y :=
          ii1Hering31_involutions_commute htwoY hrankY
        rcases ii1Hering31_twoCore_commutative_or_suzuki
            hsmall htwoY hrankY hcomm with hQcomm | hSuzuki
        · let d : II1Hering31AbelianExtensionData Y :=
            ii1Hering31_abelianExtensionData
              hsmall htwoY hrankY hcomm hQcomm
          obtain ⟨y, hy, hyQ⟩ := d.exists_involution_not_mem
          exact hyQ (ii1Hering31_involutions_le_twoCore hcomm y hy)
        · exact ii1Hering31_suzuki_twoCore_false
            hsmall htwoY hrankY hcomm hSuzuki
  exact hP (Nat.card X) rfl htwo

/-- Hering `[II1; 3.1]`: double transitivity by conjugation on the
involutions of any finite subgroup forces that subgroup to have `2`-rank one. -/
public theorem ii1Hering31Ambient
    {G : Type u} [Group G] [Finite G] : II1Hering31Ambient (G := G) := by
  intro H htwo
  apply ii1Hering31_top
  intro a b c d ha hb hc hd hab hcd
  have haG : (a : G) ∈ involutionsInSet H :=
    ⟨a.property, IsInvolution.map_of_injective ha.2
      H.subtype H.subtype_injective⟩
  have hbG : (b : G) ∈ involutionsInSet H :=
    ⟨b.property, IsInvolution.map_of_injective hb.2
      H.subtype H.subtype_injective⟩
  have hcG : (c : G) ∈ involutionsInSet H :=
    ⟨c.property, IsInvolution.map_of_injective hc.2
      H.subtype H.subtype_injective⟩
  have hdG : (d : G) ∈ involutionsInSet H :=
    ⟨d.property, IsInvolution.map_of_injective hd.2
      H.subtype H.subtype_injective⟩
  have habG : (a : G) ≠ (b : G) := fun h ↦ hab (Subtype.ext h)
  have hcdG : (c : G) ≠ (d : G) := fun h ↦ hcd (Subtype.ext h)
  obtain ⟨h, hac, hbd⟩ := htwo haG hbG hcG hdG habG hcdG
  let htop : (⊤ : Subgroup H) := ⟨h, Subgroup.mem_top h⟩
  refine ⟨htop, ?_, ?_⟩
  · apply Subtype.ext
    simpa [htop, rightConjugateElem] using hac
  · apply Subtype.ext
    simpa [htop, rightConjugateElem] using hbd

end CFSG.BenderSuzuki
