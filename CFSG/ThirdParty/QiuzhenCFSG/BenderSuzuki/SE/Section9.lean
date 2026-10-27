module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84
public import Mathlib.Algebra.Group.Subgroup.Ker
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9: minimal normal supplements

The source fixes a subgroup `W` minimal subject to `W ◁ M` and
`W D = M`, then sets `E = W ∩ D`.  This file begins the Sections 9--11
argument by proving the structural facts that follow directly from that
choice.  The focal-subgroup and local-normalizer analysis of Lemmas 9.2--9.9
is layered on top of these facts.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

namespace IsMinimalNormalSupplement

/-- Source `(9B)`: if `W` is normal in `M` and `D ≤ M`, then
`E = W ∩ D` is normal in `D`. -/
public theorem inf_normal_in_right
    {X : Type u} [Group X]
    {M D W : Subgroup X}
    (hW : IsMinimalNormalSupplement M D W)
    (hDle : D ≤ M) :
    ((W ⊓ D).subgroupOf D).Normal := by
  rw [Subgroup.normal_subgroupOf_iff inf_le_right]
  intro w d hw hd
  have hWprop : IsNormalSupplement M D W := hW.prop
  refine ⟨?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff hWprop.le_M).mp
      hWprop.normal_in_M w d hw.1 (hDle hd)
  · exact D.mul_mem (D.mul_mem hd hw.2) (D.inv_mem hd)

/-- Minimality eliminates any smaller normal supplement of the same `D`. -/
public theorem eq_of_normalSupplement_le
    {X : Type u} [Group X]
    {M D W Q : Subgroup X}
    (hW : IsMinimalNormalSupplement M D W)
    (hQ : IsNormalSupplement M D Q)
    (hQW : Q ≤ W) :
    Q = W :=
  hW.eq_of_le hQ hQW

/-- A minimal normal supplement disjoint from `D` is already a normal
complement inside `M`. -/
public theorem isNormalComplementIn_of_disjoint
    {X : Type u} [Group X]
    {M D W : Subgroup X}
    (hW : IsMinimalNormalSupplement M D W)
    (hdisjoint : Disjoint W D) :
    IsNormalComplementIn M D W :=
  { le_M := hW.prop.le_M
    normal_in_M := hW.prop.normal_in_M
    sup_eq := hW.prop.sup_eq
    disjoint_D := hdisjoint }

end IsMinimalNormalSupplement

namespace IsNormalSupplement

/-- If `M = W D`, `D` has odd order, and `S` is a `2`-subgroup of `M`,
then `S` lies in the normal supplement `W`.  The proof passes to the
quotient by `W`: the factorization makes that quotient an odd divisor of
`D`, while the image of `S` is both odd and a `2`-group. -/
public theorem two_subgroup_le_of_odd
    {X : Type u} [Group X] [Finite X]
    {M D W S : Subgroup X}
    (hDle : D ≤ M) (hDodd : Odd (Nat.card D))
    (hW : IsNormalSupplement M D W)
    (hSle : S ≤ M) (hS2 : IsPGroup 2 S) :
    S ≤ W := by
  let WM : Subgroup M := W.subgroupOf M
  let DM : Subgroup M := D.subgroupOf M
  haveI : WM.Normal := by
    simpa [WM] using hW.normal_in_M
  let q : M →* M ⧸ WM := QuotientGroup.mk' WM
  have hsupM : WM ⊔ DM = ⊤ := by
    calc
      WM ⊔ DM = (W ⊔ D).subgroupOf M := by
        simpa [WM, DM] using
          (Subgroup.subgroupOf_sup (A := W) (A' := D) (B := M)
            hW.le_M hDle).symm
      _ = M.subgroupOf M := by
        simpa using congrArg (Subgroup.subgroupOf · M) hW.sup_eq
      _ = ⊤ := Subgroup.subgroupOf_self M
  have hWMmap : WM.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (H := WM) (f := q)).2
    simpa [q] using (show WM ≤ WM from le_rfl)
  have hDMmap : DM.map q = ⊤ := by
    have htopmap : (⊤ : Subgroup M).map q = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective WM)
    calc
      DM.map q = ⊥ ⊔ DM.map q := (bot_sup_eq _).symm
      _ = WM.map q ⊔ DM.map q := by rw [hWMmap]
      _ = (WM ⊔ DM).map q := (Subgroup.map_sup _ _ _).symm
      _ = (⊤ : Subgroup M).map q := by rw [hsupM]
      _ = ⊤ := htopmap
  have hdiv : Nat.card (M ⧸ WM) ∣ Nat.card DM := by
    have hmapdiv : Nat.card (DM.map q) ∣ Nat.card DM :=
      Subgroup.card_map_dvd (H := DM) q
    simpa [hDMmap] using hmapdiv
  have hquotOdd : Odd (Nat.card (M ⧸ WM)) := by
    apply Odd.of_dvd_nat hDodd
    simpa [DM, natCard_subgroupOf_eq D M hDle] using hdiv
  let SM : Subgroup M := S.subgroupOf M
  have hSM2 : IsPGroup 2 SM :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSle).symm
  let Sbar : Subgroup (M ⧸ WM) := SM.map q
  have hSbar2 : IsPGroup 2 Sbar := by
    simpa [Sbar] using hSM2.map q
  have hSbarOdd : Odd (Nat.card Sbar) := by
    apply hquotOdd.of_dvd_nat
    simpa only [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le (H := Sbar)
        (K := (⊤ : Subgroup (M ⧸ WM))) le_top)
  have hSbarCard : Nat.card Sbar = 1 := by
    rcases hSbar2.card_eq_or_dvd with hcard | htwo
    · exact hcard
    · exact False.elim (hSbarOdd.not_two_dvd_nat htwo)
  have hSbarBot : Sbar = ⊥ := Subgroup.card_eq_one.mp hSbarCard
  intro s hs
  have hsM : (⟨s, hSle hs⟩ : M) ∈ SM := hs
  have hqone : q ⟨s, hSle hs⟩ = 1 := by
    have : q ⟨s, hSle hs⟩ ∈ Sbar := Subgroup.mem_map_of_mem q hsM
    simpa [hSbarBot] using this
  have hsWM : (⟨s, hSle hs⟩ : M) ∈ WM :=
    (QuotientGroup.eq_one_iff (N := WM) (x := ⟨s, hSle hs⟩)).1 hqone
  exact hsWM

end IsNormalSupplement

namespace Proposition84NormalizerFactor

/-- Restrict the Proposition 8.4 normalizer factorization from `M` to a
normal supplement `W`.  Once the `2`-factor `S` lies in `W`, intersecting
the factorization with `W` replaces `N_D(Y)` by `N_{W \cap D}(Y)`. -/
public theorem normalizerIn_normalSupplement_eq_mul
    {X : Type u} [Group X] [Finite X]
    {M D W Y S : Subgroup X}
    (hS : Proposition84NormalizerFactor M D Y S)
    (hDle : D ≤ M) (hDodd : Odd (Nat.card D))
    (hW : IsNormalSupplement M D W) :
    (normalizerIn W Y : Set X) =
      (S : Set X) * (normalizerIn (W ⊓ D) Y : Set X) := by
  have hSW : S ≤ W :=
    hW.two_subgroup_le_of_odd hDle hDodd hS.le_M hS.isPGroup_two
  apply Set.Subset.antisymm
  · intro x hx
    have hxNM : x ∈ normalizerIn M Y := ⟨hW.le_M hx.1, hx.2⟩
    have hxprod : x ∈
        (S : Set X) * (normalizerIn D Y : Set X) := by
      change x ∈ (S : Set X) *
        ((D ⊓ Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X)
      rw [← hS.normalizerIn_eq_mul]
      exact hxNM
    rw [Set.mem_mul] at hxprod ⊢
    rcases hxprod with ⟨s, hsS, d, hdD, hsd⟩
    have hdW : d ∈ W := by
      have hprodW : s * d ∈ W := by
        rw [hsd]
        exact hx.1
      have := W.mul_mem (W.inv_mem (hSW hsS)) hprodW
      simpa [mul_assoc] using this
    exact ⟨s, hsS, d, ⟨⟨hdW, hdD.1⟩, hdD.2⟩, hsd⟩
  · intro x hx
    rw [Set.mem_mul] at hx
    rcases hx with ⟨s, hsS, d, hdE, hsd⟩
    refine ⟨?_, ?_⟩
    · rw [← hsd]
      exact W.mul_mem (hSW hsS) hdE.1.1
    · rw [← hsd]
      exact (Subgroup.normalizer (Y : Set X)).mul_mem
        (hS.le_normalizerIn hsS).2 hdE.2

/-- For an odd prime `p`, the Proposition 8.4 `2`-factor belongs to the
`p'`-core of its normalizer inside a normal supplement. -/
public theorem le_pPrimeCore_normalizerIn_of_odd
    {X : Type u} [Group X] [Finite X]
    {M D W Y S : Subgroup X} {p : ℕ} [Fact p.Prime]
    (hS : Proposition84NormalizerFactor M D Y S)
    (hDle : D ≤ M) (hDodd : Odd (Nat.card D))
    (hW : IsNormalSupplement M D W) (hpOdd : Odd p) :
    S ≤ (pPrimeCore p (normalizerIn W Y)).map
      (normalizerIn W Y).subtype := by
  let NM : Subgroup X := normalizerIn M Y
  let NW : Subgroup X := normalizerIn W Y
  have hSW : S ≤ W :=
    hW.two_subgroup_le_of_odd hDle hDodd hS.le_M hS.isPGroup_two
  have hSNW : S ≤ NW := by
    intro s hs
    exact ⟨hSW hs, (hS.le_normalizerIn hs).2⟩
  have hNWNM : NW ≤ NM := by
    intro n hn
    exact ⟨hW.le_M hn.1, hn.2⟩
  let SNW : Subgroup NW := S.subgroupOf NW
  have hSNWnormal : SNW.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hSNW).2
    intro s n hs hn
    exact (Subgroup.normal_subgroupOf_iff hS.le_normalizerIn).1
      hS.normal_in_normalizerIn s n hs (hNWNM hn)
  have hpne2 : p ≠ 2 := by
    intro h
    subst p
    exact (by decide : ¬ Odd 2) hpOdd
  obtain ⟨n, hn⟩ := hS.isPGroup_two.exists_card_eq
  have hpcop : Nat.Coprime p (Nat.card S) := by
    rw [hn]
    exact ((Nat.coprime_primes (Fact.out : Nat.Prime p)
      Nat.prime_two).2 hpne2).pow_right n
  have hSNWcop : Nat.Coprime p (Nat.card SNW) := by
    simpa [SNW, natCard_subgroupOf_eq S NW hSNW] using hpcop
  have hcore : SNW ≤ pPrimeCore p NW :=
    le_sSup ⟨hSNWnormal, hSNWcop⟩
  intro s hs
  exact Subgroup.mem_map.mpr
    ⟨⟨s, hSNW hs⟩, hcore hs, rfl⟩

/-- The exact contradiction to source `(9E)` supplied by Proposition 8.4:
inside a normal supplement, the normalizer is the product of its `p'`-core
and the normalizer inside `W \cap D`. -/
public theorem normalizerIn_normalSupplement_eq_pPrimeCore_mul
    {X : Type u} [Group X] [Finite X]
    {M D W Y S : Subgroup X} {p : ℕ} [Fact p.Prime]
    (hS : Proposition84NormalizerFactor M D Y S)
    (hDle : D ≤ M) (hDodd : Odd (Nat.card D))
    (hW : IsNormalSupplement M D W) (hpOdd : Odd p) :
    (normalizerIn W Y : Set X) =
      (((pPrimeCore p (normalizerIn W Y)).map
        (normalizerIn W Y).subtype : Subgroup X) : Set X) *
        (normalizerIn (W ⊓ D) Y : Set X) := by
  let O : Subgroup X :=
    (pPrimeCore p (normalizerIn W Y)).map
      (normalizerIn W Y).subtype
  have hSO : S ≤ O := by
    simpa [O] using hS.le_pPrimeCore_normalizerIn_of_odd
      hDle hDodd hW hpOdd
  have hfactor := hS.normalizerIn_normalSupplement_eq_mul
    hDle hDodd hW
  apply Set.Subset.antisymm
  · intro x hx
    have hxprod : x ∈
        (S : Set X) * (normalizerIn (W ⊓ D) Y : Set X) := by
      rw [← hfactor]
      exact hx
    rw [Set.mem_mul] at hxprod ⊢
    rcases hxprod with ⟨s, hsS, e, he, hse⟩
    exact ⟨s, hSO hsS, e, he, hse⟩
  · intro x hx
    rw [Set.mem_mul] at hx
    rcases hx with ⟨o, ho, e, he, hoe⟩
    refine ⟨?_, ?_⟩
    · rw [← hoe]
      exact W.mul_mem
        ((Subgroup.map_subtype_le (pPrimeCore p
          (normalizerIn W Y)) ho).1) he.1.1
    · rw [← hoe]
      exact (Subgroup.normalizer (Y : Set X)).mul_mem
        ((Subgroup.map_subtype_le (pPrimeCore p
          (normalizerIn W Y)) ho).2) he.2

end Proposition84NormalizerFactor

namespace IsStronglyEmbedded

/-- Proposition 8.4 rules out source `(9E)` for any subgroup `Y` that has
a nontrivial subnormal subgroup with nontrivial Peterfalvi normalizer.  This
is the checked normalizer calculation used in Lemma 9.4. -/
public theorem proposition84_normalizerIn_eq_pPrimeCore_mul
    {X : Type u} [Group X] [Finite X]
    {M W Y Y₁ : Subgroup X} {t : X} {p : ℕ} [Fact p.Prime]
    (hM : IsStronglyEmbedded M) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hYV :
      Y ≤ (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({t} : Set X))
    (hY₁ : Y₁ ≠ ⊥) (hY₁Y : Y₁ ≤ Y)
    (hsubnormal : (Y₁.subgroupOf Y).IsSubnormal)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y₁)
    (hW : IsNormalSupplement M (M ⊓ rightConjugate M t) W)
    (hpOdd : Odd p) :
    (normalizerIn W Y : Set X) =
      (((pPrimeCore p (normalizerIn W Y)).map
        (normalizerIn W Y).subtype : Subgroup X) : Set X) *
        (normalizerIn (W ⊓ (M ⊓ rightConjugate M t)) Y : Set X) := by
  obtain ⟨S, hS⟩ := h84.exists_factor d83 hYV hY₁ hY₁Y
    hsubnormal hI
  exact hS.normalizerIn_normalSupplement_eq_pPrimeCore_mul
    inf_le_left (hM.inf_rightConjugate_card_odd htM) hW hpOdd

/-- In the Section 9 setup, `E = W ∩ D` has odd order because it is a
subgroup of the distinct-conjugate intersection `D = M ∩ M^t`. -/
public theorem minimalNormalSupplement_inf_right_card_odd
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M) (htM : t ∉ M) :
    Odd (Nat.card
      (W ⊓ (M ⊓ rightConjugate M t) : Subgroup X)) := by
  apply Odd.of_dvd_nat (hM.inf_rightConjugate_card_odd htM)
  exact Subgroup.card_dvd_of_le inf_le_right

/-- The Odd Order Theorem gives the solvability assertion following source
`(9B)`. -/
public theorem minimalNormalSupplement_inf_right_solvable
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M) (htM : t ∉ M) :
    IsSolvable
      (W ⊓ (M ⊓ rightConjugate M t) : Subgroup X) := by
  exact odd_order_theorem _
    (hM.minimalNormalSupplement_inf_right_card_odd htM)

end IsStronglyEmbedded

end CFSG.BenderSuzuki
