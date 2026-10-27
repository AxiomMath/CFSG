module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore

namespace CFSG
end CFSG
open CFSG

/-!
# The outer reduction for Theorem SE

This file contains only checked assembly.  It derives the full strongly
embedded conclusion from the minimal-counterexample step by induction on the
order of the ambient group, and derives the simple-group classification from
that conclusion.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u v

namespace IsSimpleBenderGroup

/-- Membership in the three Bender families transports across a group
isomorphism. -/
public theorem of_mulEquiv
    {G : Type u} {H : Type v}
    [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (hG : IsSimpleBenderGroup G) :
    IsSimpleBenderGroup H := by
  rcases hG with ⟨⟨n, hn, hmodel⟩⟩ | ⟨⟨n, hn, hmodel⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard,
        hmodel⟩⟩
  · apply isPSL2
    exact ⟨n, hn, ⟨e.symm.trans hmodel.some⟩⟩
  · apply isSuzuki
    exact ⟨n, hn, ⟨e.symm.trans hmodel.some⟩⟩
  · apply isPSU3
    exact ⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard,
      ⟨e.symm.trans hmodel.some⟩⟩

/-- Being one of the three simple Bender groups is invariant under group
isomorphism. -/
public theorem mulEquiv_iff
    {G : Type u} {H : Type v}
    [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) :
    IsSimpleBenderGroup G ↔ IsSimpleBenderGroup H :=
  ⟨of_mulEquiv e, of_mulEquiv e.symm⟩

end IsSimpleBenderGroup

public theorem twoRankAtLeastTwo_of_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) (hG : TwoRankAtLeastTwo G) :
    TwoRankAtLeastTwo H := by
  rcases hG with ⟨E, hEcard, hEsq⟩
  let EH : Subgroup H := E.map e.toMonoidHom
  have hEHcard : Nat.card EH = 4 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hEcard
  refine ⟨EH, hEHcard, ?_⟩
  rintro ⟨x, hx⟩
  rcases hx with ⟨y, hy, rfl⟩
  apply Subtype.ext
  have hy_sq : y ^ 2 = (1 : G) :=
    congrArg (fun z : E => (z : G)) (hEsq ⟨y, hy⟩)
  simpa using congrArg e hy_sq

/-- The minimal-counterexample step implies Theorem SE for every finite group
with a strongly embedded subgroup.  The recursive calls are made only for
proper subgroups, whose cardinalities are strictly smaller. -/
public theorem theoremSEConclusion_of_minimalStep
    (hstep : TheoremSEMinimalStep.{u})
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (hM : IsStronglyEmbedded M) :
    TheoremSEConclusion M := by
  let P : ℕ → Prop := fun n =>
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n →
      ∀ (N : Subgroup G), IsStronglyEmbedded N →
        TheoremSEConclusion N
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro G _ _ hcard N hN
        by_cases hrank : TwoRankAtLeastTwo (involutionCore G)
        · right
          apply hstep N hN
          · intro Y _ _ hlt K hK
            apply ih (Nat.card Y)
            · simpa [hcard] using hlt
            · exact rfl
            · exact hK
          · exact hrank
        · exact Or.inl hrank
  exact hP (Nat.card X) X rfl M hM

/-- In the simple-group case, the two-rank exclusion is impossible, so the
minimal-counterexample step identifies the ambient group with one of the
three simple Bender families. -/
public theorem isSimpleBenderGroup_of_minimalStep
    (hstep : TheoremSEMinimalStep.{u})
    (hrankTwo : SimpleStronglyEmbeddedRankTwo.{u})
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (hM : IsStronglyEmbedded M)
    (hX : IsSimpleGroup X) :
    IsSimpleBenderGroup X := by
  let L : Subgroup X := involutionCore X
  have hL : L = ⊤ := hM.involutionCore_eq_top_of_isSimple hX
  let eL : L ≃* X :=
    (MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv
  have hrankL : TwoRankAtLeastTwo L :=
    twoRankAtLeastTwo_of_mulEquiv eL.symm (hrankTwo M hX hM)
  have hBender : TheoremSEBenderConclusion M :=
    hstep M hM
      (fun {_Y} _ _ _hlt N hN =>
        theoremSEConclusion_of_minimalStep hstep N hN)
      hrankL
  have hsimpleL : IsSimpleGroup L := eL.isSimpleGroup_congr.mpr hX
  have hcore : twoPrimeCore L = ⊥ := by
    rcases (hsimpleL.eq_bot_or_eq_top_of_normal (twoPrimeCore L)) with
      hbot | htop
    · exact hbot
    · obtain ⟨x, _hxM, hx⟩ := hM.exists_involution
      have hxL : x ∈ L := by
        change x ∈ involutionCore X
        rw [involutionCore_eq_closure]
        exact Subgroup.subset_closure hx
      let xL : L := ⟨x, hxL⟩
      have hxLinv : IsInvolution xL := by
        constructor
        · intro h
          exact hx.ne_one (congrArg (fun z : L => (z : X)) h)
        · apply Subtype.ext
          exact hx.sq_eq_one
      let xc : twoPrimeCore L := ⟨xL, by simp [htop]⟩
      have hxc : IsInvolution xc := by
        constructor
        · intro h
          exact hxLinv.ne_one
            (congrArg (fun z : twoPrimeCore L => (z : L)) h)
        · apply Subtype.ext
          exact hxLinv.sq_eq_one
      have horder : orderOf xc = 2 :=
        orderOf_eq_prime hxc.sq_eq_one hxc.ne_one
      have hdvd : 2 ∣ Nat.card (twoPrimeCore L) := by
        rw [← horder]
        exact orderOf_dvd_natCard xc
      exact ((Nat.prime_two.coprime_iff_not_dvd.mp
        (by simpa [twoPrimeCore] using
          (pPrimeCore_coprime_card (G := L) (p := 2)))) hdvd).elim
  let eCore : (L ⧸ twoPrimeCore L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientBot (G := L))
  exact IsSimpleBenderGroup.of_mulEquiv (eCore.trans eL) hBender.1

end CFSG.BenderSuzuki
