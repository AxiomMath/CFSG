module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Corollary96
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma91
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Lemma 9.7

This file proves the centralizer identification at the start of Lemma 9.7.
The remaining conclusions are layered on top of this equality: first the
minimal-supplement contradiction, then the Sylow--Frattini argument forcing
the common centralizer to be trivial.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The source set `\mathcal Z_M` of involutions lying in `M`. -/
@[expose] public def involutionsInSet
    {X : Type u} [Group X] (M : Subgroup X) : Set X :=
  {z : X | z ∈ M ∧ IsInvolution z}

/-- The first equality in Lemma 9.7(b): the elements of the two-point
stabilizer centralizing every involution of `M` are exactly the elements of
`V = C_D(t)` centralizing the Peterfalvi subgroup `I`.

The forward implication uses the parametrization of the involutions of `M`
by conjugates of the selected involution `u`.  In the reverse implication,
oddness of `D` makes squaring bijective, so centralizing the corresponding
squares forces centralization of each Peterfalvi anti-fixed element. -/
public theorem lemma97_centralizer_eq
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    let V : Subgroup X := peterfalviV D t
    D ⊓ Subgroup.centralizer (involutionsInSet M) =
      V ⊓ Subgroup.centralizer (peterfalviKSet D t) := by
  classical
  dsimp only
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  ext x
  constructor
  · intro hx
    have hxu : x ∈ Subgroup.centralizer ({d83.u} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hx.2 d83.u
        ⟨d83.u_mem_M, d83.u_involution⟩).symm
    have hxV : x ∈ V := by
      change x ∈ D ⊓ Subgroup.centralizer ({t} : Set X)
      rw [d83.centralizer_eq]
      exact ⟨hx.1, hxu⟩
    refine ⟨hxV, ?_⟩
    change ∀ k ∈ peterfalviKSet D t, k * x = x * k
    intro k hk
    let uk : X := rightConjugateElem d83.u k
    have hkD : k ∈ D := hk.1
    have hukM : uk ∈ M := by
      dsimp [uk, rightConjugateElem]
      exact M.mul_mem (M.mul_mem (M.inv_mem (show k ∈ M from hkD.1))
        d83.u_mem_M) (show k ∈ M from hkD.1)
    have hukInv : IsInvolution uk := by
      simpa [uk] using isInvolution_rightConjugateElem d83.u_involution
    have hxuk : Commute x uk := by
      exact (show uk * x = x * uk from
        Subgroup.mem_centralizer_iff.mp hx.2 uk ⟨hukM, hukInv⟩).symm
    let xk : X := rightConjugateElem x k⁻¹
    have hxkD : xk ∈ D := by
      simpa [xk, rightConjugateElem] using
        D.mul_mem (D.mul_mem hkD hx.1) (D.inv_mem hkD)
    have hxkCu : xk ∈ Subgroup.centralizer ({d83.u} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun z : X => k * z * k⁻¹) hxuk.eq
      simpa [xk, uk, rightConjugateElem, mul_assoc] using h
    have hxkCt : xk ∈ Subgroup.centralizer ({t} : Set X) := by
      have hxkV : xk ∈ D ⊓ Subgroup.centralizer ({t} : Set X) := by
        rw [d83.centralizer_eq]
        exact ⟨hxkD, hxkCu⟩
      exact hxkV.2
    let tk : X := rightConjugateElem t k
    have hxtk : Commute x tk := by
      have h := congrArg (fun z : X => k⁻¹ * z * k)
        (Subgroup.mem_centralizer_singleton_iff.mp hxkCt)
      exact (show x * tk = tk * x by
        simpa [xk, tk, rightConjugateElem, mul_assoc] using h)
    have hxt : Commute x t := by
      exact Subgroup.mem_centralizer_singleton_iff.mp hxV.2
    have hxprod : Commute x (t * tk) := hxt.mul_right hxtk
    have htk_sq : t * tk = k ^ 2 := by
      have hInv := congrArg Inv.inv hk.2
      have htkInv : t * k⁻¹ * t = k := by
        simpa [rightConjugateElem, ht.inv_eq_self, mul_assoc] using hInv
      dsimp [tk, rightConjugateElem]
      calc
        t * (k⁻¹ * t * k) = (t * k⁻¹ * t) * k := by group
        _ = k * k := by rw [htkInv]
        _ = k ^ 2 := by rw [pow_two]
    have hxksq : Commute x (k ^ 2) := by simpa [htk_sq] using hxprod
    let a : D := ⟨x * k * x⁻¹,
      D.mul_mem (D.mul_mem hx.1 hkD) (D.inv_mem hx.1)⟩
    let b : D := ⟨k, hkD⟩
    have habsq : a ^ 2 = b ^ 2 := by
      apply Subtype.ext
      change (x * k * x⁻¹) ^ 2 = k ^ 2
      calc
        (x * k * x⁻¹) ^ 2 = x * k ^ 2 * x⁻¹ := by
          simp only [pow_two]
          group
        _ = k ^ 2 := by
          rw [show x * k ^ 2 = k ^ 2 * x from hxksq.eq]
          simp
    have hab : a = b :=
      hDodd.coprime_two_right.pow_left_bijective.injective habsq
    have habX : x * k * x⁻¹ = k := congrArg Subtype.val hab
    have hcomm : x * k = k * x := by
      have h := congrArg (fun z : X => z * x) habX
      simpa [mul_assoc] using h
    exact hcomm.symm
  · intro hx
    have hxuD : x ∈ D ⊓ Subgroup.centralizer ({d83.u} : Set X) := by
      rw [← d83.centralizer_eq]
      exact hx.1
    refine ⟨hxuD.1, ?_⟩
    change ∀ y ∈ involutionsInSet M, y * x = x * y
    intro y hy
    obtain ⟨k, hkI, huk⟩ :=
      hM.exists_mem_peterfalviKSet_of_involution_mem
        d83.u_mem_M d83.u_involution ht htM hy.1 hy.2
    have hxk : Commute x k := by
      exact (show k * x = x * k from
        Subgroup.mem_centralizer_iff.mp hx.2 k hkI).symm
    have hxu : Commute x d83.u :=
      Subgroup.mem_centralizer_singleton_iff.mp hxuD.2
    rw [← huk]
    exact (hxk.inv_right.mul_right hxu |>.mul_right hxk).symm.eq

/-- The centralizer in `M` of the involutions of `M` is normal in `M`.
Conjugation by an element of `M` merely permutes those involutions. -/
public theorem centralizerIn_involutionsInSet_normal
    {X : Type u} [Group X] (M : Subgroup X) :
    ((M ⊓ Subgroup.centralizer (involutionsInSet M)).subgroupOf M).Normal := by
  apply (Subgroup.normal_subgroupOf_iff inf_le_left).2
  intro c m hc hm
  refine ⟨M.mul_mem (M.mul_mem hm hc.1) (M.inv_mem hm), ?_⟩
  change ∀ z ∈ involutionsInSet M,
    z * (m * c * m⁻¹) = (m * c * m⁻¹) * z
  intro z hz
  let zm : X := m⁻¹ * z * m
  have hzmM : zm ∈ M := by
    exact M.mul_mem (M.mul_mem (M.inv_mem hm) hz.1) hm
  have hzmInv : IsInvolution zm := by
    simpa [zm, rightConjugateElem, mul_assoc] using
      isInvolution_rightConjugateElem (g := m) hz.2
  have hcomm :=
    Subgroup.mem_centralizer_iff.mp hc.2 zm ⟨hzmM, hzmInv⟩
  have h := congrArg (fun q : X => m * q * m⁻¹) hcomm
  simpa [zm, mul_assoc] using h

/-- Lemma 9.7(a).  Under the standing contradiction assumption that `D` has
no nilpotent normal complement in `M`, the point stabilizer cannot be generated
by `D` and the centralizer in `M` of all involutions of `M`.

The proof follows the source's change-of-choice argument: if this join were
all of `M`, choose a minimal normal supplement `Q` below the centralizer.  Its
intersection with `D` is nontrivial (otherwise Lemma 9.1 already supplies the
forbidden complement), and Corollary 9.5 then gives a nontrivial element whose
Peterfalvi centralizer is trivial.  The equality `lemma97_centralizer_eq`
forces that same element to centralize the nontrivial Peterfalvi subgroup. -/
public theorem lemma97_ne_centralizer_sup
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (htrans : IsTransitiveOn M
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)})
    (hfail : ¬ ∃ Q : Subgroup X,
      IsNormalComplementIn M (M ⊓ rightConjugate M t) Q ∧
        Group.IsNilpotent Q)
    (h43 : II1Lemma43bCyclic (X := X)) :
    M ≠
      (M ⊓ Subgroup.centralizer (involutionsInSet M)) ⊔
        (M ⊓ rightConjugate M t) := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let C0 : Subgroup X := M ⊓ Subgroup.centralizer (involutionsInSet M)
  intro hMC0D
  have hC0supp : IsNormalSupplement M D C0 := by
    refine ⟨inf_le_left, ?_, ?_⟩
    · simpa [C0] using centralizerIn_involutionsInSet_normal M
    · simpa [C0, D] using hMC0D.symm
  obtain ⟨Q, hQC0, hQ⟩ :=
    exists_isMinimalNormalSupplement_le hC0supp
  have hEne : Q ⊓ D ≠ ⊥ := by
    intro hEbot
    have hdisjoint : Disjoint Q D := by
      rw [disjoint_iff]
      exact hEbot
    obtain ⟨hcomp, hnil, _hreg⟩ :=
      lemma_9_1 ht htM d83 hQ hdisjoint
        (by simpa [D] using hIne) htrans
    exact hfail ⟨Q, by simpa [D] using hcomp, hnil⟩
  let E : Subgroup X := Q ⊓ D
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hEodd : Odd (Nat.card E) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hEsolv : Group.IsSolvable E := odd_order_theorem E hEodd
  letI : Group.IsSolvable E := hEsolv
  haveI : Nontrivial E :=
    (Subgroup.nontrivial_iff_ne_bot E).2 (by simpa [E] using hEne)
  have hcommLt : derivedSubgroup E < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := E)
  have hAbOneLt : 1 < Nat.card (E ⧸ derivedSubgroup E) := by
    have hindex : 1 < (derivedSubgroup E).index :=
      Subgroup.one_lt_index_of_ne_top hcommLt.ne
    simpa [Subgroup.index_eq_card] using hindex
  obtain ⟨p, hp, hpAb⟩ := Nat.exists_prime_and_dvd hAbOneLt.ne'
  letI : Fact p.Prime := ⟨hp⟩
  have hB : Lemma94AlternativeB D E t p := by
    simpa [D, E] using
      (corollary_9_5_ambient_abelianization hM ht htM d83 h84 hQ
        (by simpa [E] using hpAb) (by simpa [D] using hIne)
        h43)
  obtain ⟨P, _hPcyclic, _hPV, hPcentral⟩ := hB
  have hpE : p ∣ Nat.card E :=
    hpAb.trans (Subgroup.card_quotient_dvd_card
      (s := derivedSubgroup E))
  have hPne : (P : Subgroup E) ≠ ⊥ := P.ne_bot_of_dvd_card hpE
  obtain ⟨g, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  let gx : X := E.subtype g
  have hgP : gx ∈ (P : Subgroup E).map E.subtype := by
    exact Subgroup.mem_map.mpr ⟨g, g.property, rfl⟩
  have hgxne : gx ≠ 1 := by
    intro hgx
    apply hgne
    apply Subtype.ext
    apply Subtype.ext
    simpa [gx] using hgx
  have hgE : gx ∈ E := Subgroup.map_subtype_le (P : Subgroup E) hgP
  have hgQD : gx ∈ Q ⊓ D := by simpa [E] using hgE
  have hgC0 : gx ∈ C0 := by
    apply hQC0
    exact hgQD.1
  have hgD : gx ∈ D := hgQD.2
  have hcentEq :
      D ⊓ Subgroup.centralizer (involutionsInSet M) =
        peterfalviV D t ⊓
          Subgroup.centralizer (peterfalviKSet D t) := by
    simpa [D] using lemma97_centralizer_eq hM ht htM d83
  have hgCI : gx ∈ Subgroup.centralizer (peterfalviKSet D t) := by
    have hgleft : gx ∈ D ⊓
        Subgroup.centralizer (involutionsInSet M) := ⟨hgD, hgC0.2⟩
    rw [hcentEq] at hgleft
    exact hgleft.2
  obtain ⟨k, hkI, hkne⟩ := hIne
  have hkg : k * gx = gx * k :=
    Subgroup.mem_centralizer_iff.mp hgCI k (by simpa [D] using hkI)
  exact hkne (hPcentral gx hgP hgxne k (by simpa [D] using hkI) hkg)

private theorem involution_mem_factor_of_odd
    {X : Type u} [Group X] [Finite X]
    {M D Y S : Subgroup X}
    (hS : Proposition84NormalizerFactor M D Y S)
    (hDle : D ≤ M) (hDodd : Odd (Nat.card D))
    {z : X} (hzM : z ∈ M) (hzInv : IsInvolution z)
    (hzC : z ∈ Subgroup.centralizer (Y : Set X)) :
    z ∈ S := by
  let NM : Subgroup X := normalizerIn M Y
  let ND : Subgroup X := normalizerIn D Y
  have hNDNM : ND ≤ NM := by
    intro n hn
    exact ⟨hDle hn.1, hn.2⟩
  have hNDodd : Odd (Nat.card ND) := by
    apply hDodd.of_dvd_nat
    exact Subgroup.card_dvd_of_le inf_le_left
  have hlocal : IsNormalSupplement NM ND S := by
    refine ⟨hS.le_normalizerIn, ?_, ?_⟩
    · change (S.subgroupOf
        (M ⊓ Subgroup.normalizer (Y : Set X))).Normal
      exact hS.normal_in_normalizerIn
    · apply le_antisymm
      · exact sup_le hS.le_normalizerIn hNDNM
      · intro x hx
        have hxprod : x ∈ (S : Set X) * (ND : Set X) := by
          simpa [NM, ND, normalizerIn] using
            (show x ∈ (S : Set X) *
                ((D ⊓ Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) by
              rw [← hS.normalizerIn_eq_mul]
              exact hx)
        rcases hxprod with ⟨s, hs, d, hd, hsd⟩
        rw [← hsd]
        exact Subgroup.mul_mem_sup hs hd
  have hzNorm : z ∈ Subgroup.normalizer (Y : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : y * z = z * y :=
        (Subgroup.mem_centralizer_iff.mp hzC) y hy
      have hconj : z * y * z⁻¹ = y := by
        calc
          z * y * z⁻¹ = y * z * z⁻¹ := by rw [hcomm]
          _ = y := by simp
      simpa [hconj] using hy
    · intro hconjY
      let q : X := z * y * z⁻¹
      have hqY : q ∈ Y := by simpa [q] using hconjY
      have hqcomm : q * z = z * q :=
        (Subgroup.mem_centralizer_iff.mp hzC) q hqY
      have hzy : z * y = q * z := by simp [q, mul_assoc]
      have hyq : y = q := by
        calc
          y = z⁻¹ * (z * y) := by simp
          _ = z⁻¹ * (q * z) := by rw [hzy]
          _ = z⁻¹ * (z * q) := by rw [hqcomm]
          _ = q := by simp [mul_assoc]
      rw [hyq]
      exact hqY
  have hzNM : z ∈ NM := ⟨hzM, hzNorm⟩
  have hzpowNM : Subgroup.zpowers z ≤ NM :=
    Subgroup.zpowers_le.mpr hzNM
  have hzpow2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_two_zpowers_of_isInvolution hzInv
  have hzpowS : Subgroup.zpowers z ≤ S :=
    hlocal.two_subgroup_le_of_odd hNDNM hNDodd hzpowNM hzpow2
  exact hzpowS (Subgroup.mem_zpowers z)

/-- Lemma 9.7(b), isolated from the change-of-choice proof of part (a).
If `M` is not generated by `D` and the centralizer of its involutions, then
the common centralizer `C_V(I) = C_D(𝒵_M)` is trivial.

The proof follows the source normalizer argument.  A nontrivial odd Sylow
subgroup `Y` of the common centralizer activates Proposition 8.4.  Every
involution of `M` belongs to its normal `2`-factor `S`; a central involution
of `S`, transported through the Peterfalvi parametrization, then puts all
involutions of `M` in `Z(S)`, so `S ≤ C_M(𝒵_M)`.  Sylow transfer and
Frattini's argument force the forbidden generation equality. -/
public theorem lemma97_centralizer_eq_bot_of_ne_sup
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (hne : M ≠
      (M ⊓ Subgroup.centralizer (involutionsInSet M)) ⊔
        (M ⊓ rightConjugate M t)) :
    peterfalviV (M ⊓ rightConjugate M t) t ⊓
        Subgroup.centralizer
          (peterfalviKSet (M ⊓ rightConjugate M t) t) = ⊥ := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  let C0 : Subgroup X :=
    M ⊓ Subgroup.centralizer (involutionsInSet M)
  let E : Subgroup X := C0 ⊓ D
  let CI : Subgroup X :=
    V ⊓ Subgroup.centralizer (peterfalviKSet D t)
  have hEleft :
      E = D ⊓ Subgroup.centralizer (involutionsInSet M) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, hx.1.2⟩
    · intro hx
      exact ⟨⟨hx.1.1, hx.2⟩, hx.1⟩
  have hcentEq :
      D ⊓ Subgroup.centralizer (involutionsInSet M) = CI := by
    simpa [D, V, CI] using lemma97_centralizer_eq hM ht htM d83
  have hECI : E = CI := hEleft.trans hcentEq
  change CI = ⊥
  rw [← hECI]
  by_contra hEne
  letI : Nontrivial E :=
    (Subgroup.nontrivial_iff_ne_bot E).2 hEne
  have hEcard : 1 < Nat.card E :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨p, hp, hpE⟩ := Nat.exists_prime_and_dvd hEcard.ne'
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p E := default
  let Y : Subgroup X := (P : Subgroup E).map E.subtype
  have hYE : Y ≤ E := by
    simpa [Y] using Subgroup.map_subtype_le (P : Subgroup E)
  have hYC0 : Y ≤ C0 := hYE.trans inf_le_left
  have hYCI : Y ≤ CI := by
    rw [← hECI]
    exact hYE
  have hYV : Y ≤ V := hYCI.trans inf_le_left
  have hYne : Y ≠ ⊥ := by
    have hPne : (P : Subgroup E) ≠ ⊥ := P.ne_bot_of_dvd_card hpE
    intro hYbot
    apply hPne
    apply Subgroup.map_injective E.subtype_injective
    simpa [Y] using hYbot
  have hYnormal : (Y.subgroupOf Y).Normal := by
    simpa using (inferInstance : (⊤ : Subgroup Y).Normal)
  have hPeterfalviNormalizer :
      HasNontrivialPeterfalviNormalizer D t Y := by
    obtain ⟨k, hkI, hkne⟩ := hIne
    refine ⟨k, by simpa [D] using hkI, ?_, hkne⟩
    apply centralizer_le_normalizer Y
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyCI : y ∈ CI := hYCI hy
    exact (Subgroup.mem_centralizer_iff.mp hyCI.2 k
      (by simpa [D] using hkI)).symm
  have hYVsource :
      Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    change Y ≤ V
    exact hYV
  obtain ⟨S, hS⟩ := h84.exists_factor_of_normal d83
    (by simpa [D] using hYVsource) hYne le_rfl hYnormal
    (by simpa [D] using hPeterfalviNormalizer)
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hEodd : Odd (Nat.card E) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hpOdd : Odd p := hEodd.of_dvd_nat hpE
  have hInvolutionsLeS :
      ∀ z : X, z ∈ M → IsInvolution z → z ∈ S := by
    intro z hzM hzInv
    apply involution_mem_factor_of_odd hS inf_le_left hDodd hzM hzInv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyC0 : y ∈ C0 := hYC0 hy
    exact (Subgroup.mem_centralizer_iff.mp hyC0.2 z
      ⟨hzM, hzInv⟩).symm
  have huS : d83.u ∈ S :=
    hInvolutionsLeS d83.u d83.u_mem_M d83.u_involution
  have hSne : S ≠ ⊥ := by
    exact Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨d83.u, huS⟩, by
        intro huOne
        exact d83.u_involution.ne_one (congrArg Subtype.val huOne)⟩
  letI : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot S).2 hSne
  have hCenterNontrivial : Nontrivial (Subgroup.center S) :=
    hS.isPGroup_two.center_nontrivial
  have hCenterTwo : IsPGroup 2 (Subgroup.center S) :=
    hS.isPGroup_two.to_subgroup (Subgroup.center S)
  have htwoCenter : 2 ∣ Nat.card (Subgroup.center S) := by
    rcases (IsPGroup.nontrivial_iff_card
      (p := 2) (G := Subgroup.center S) hCenterTwo).mp
        hCenterNontrivial with ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨zC, hzOrder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := Subgroup.center S) 2 htwoCenter
  let zS : S := (zC : S)
  let z : X := (zS : X)
  have hzOrderS : orderOf zS = 2 := by
    simpa [zS] using (Subgroup.orderOf_coe zC).trans hzOrder
  have hzData := orderOf_eq_prime_iff.mp hzOrderS
  have hzInvS : IsInvolution zS := ⟨hzData.2, hzData.1⟩
  have hzInv : IsInvolution z :=
    IsInvolution.map_of_injective hzInvS S.subtype
      S.subtype_injective
  have hzM : z ∈ M := hS.le_M zS.property
  let ZS : Subgroup X := (Subgroup.center S).map S.subtype
  have hzZS : z ∈ ZS := by
    exact Subgroup.mem_map.mpr ⟨zS, zC.property, rfl⟩
  have hZSleS : ZS ≤ S := by
    simpa [ZS] using Subgroup.map_subtype_le (Subgroup.center S)
  let NM : Subgroup X := normalizerIn M Y
  have hZSNM : ZS ≤ NM := hZSleS.trans hS.le_normalizerIn
  have hZSnormal : (ZS.subgroupOf NM).Normal := by
    apply normal_subgroupOf_map_of_characteristic_of_normal
      S ZS NM hS.le_normalizerIn hS.normal_in_normalizerIn
      (Subgroup.center S) Subgroup.centerCharacteristic
    · rfl
    · exact hZSNM
  have hInvolutionsLeZS :
      ∀ y : X, y ∈ M → IsInvolution y → y ∈ ZS := by
    intro y hyM hyInv
    obtain ⟨k, hkI, hzk⟩ :=
      hM.exists_mem_peterfalviKSet_of_involution_mem
        hzM hzInv ht htM hyM hyInv
    have hkCentralY : k ∈ Subgroup.centralizer (Y : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haCI : a ∈ CI := hYCI ha
      exact (Subgroup.mem_centralizer_iff.mp haCI.2 k hkI).symm
    have hkNM : k ∈ NM := by
      refine ⟨?_, centralizer_le_normalizer Y hkCentralY⟩
      exact hkI.1.1
    have hconj : k⁻¹ * z * (k⁻¹)⁻¹ ∈ ZS :=
      (Subgroup.normal_subgroupOf_iff hZSNM).mp hZSnormal
        z k⁻¹ hzZS (NM.inv_mem hkNM)
    have hright : rightConjugateElem z k ∈ ZS := by
      simpa [rightConjugateElem] using hconj
    rwa [hzk] at hright
  have hSC0 : S ≤ C0 := by
    intro s hs
    refine ⟨hS.le_M hs, ?_⟩
    change ∀ y ∈ involutionsInSet M, y * s = s * y
    intro y hy
    have hyZS := hInvolutionsLeZS y hy.1 hy.2
    rcases hyZS with ⟨yS, hyCenter, hyval⟩
    let sS : S := ⟨s, hs⟩
    have hcommS := (Subgroup.mem_center_iff.mp hyCenter) sS
    have hcommX := congrArg Subtype.val hcommS.symm
    change (yS : X) * s = s * (yS : X) at hcommX
    have hyval' : (yS : X) = y := hyval
    calc
      y * s = (yS : X) * s := by rw [hyval']
      _ = s * (yS : X) := hcommX
      _ = s * y := by rw [hyval']
  let NC0 : Subgroup X := normalizerIn C0 Y
  let NE : Subgroup X := normalizerIn E Y
  have hSNC0 : S ≤ NC0 := by
    intro s hs
    exact ⟨hSC0 hs, hS.le_normalizer hs⟩
  have hNC0NM : NC0 ≤ NM := by
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  have hSnormalNC0 : (S.subgroupOf NC0).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hSNC0).2
    intro s n hs hn
    exact (Subgroup.normal_subgroupOf_iff hS.le_normalizerIn).1
      hS.normal_in_normalizerIn s n hs (hNC0NM hn)
  have hfactorNC0 :
      (NC0 : Set X) = (S : Set X) * (NE : Set X) := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxNM : x ∈ normalizerIn M Y := ⟨hx.1.1, hx.2⟩
      have hxprod : x ∈
          (S : Set X) * (normalizerIn D Y : Set X) := by
        change x ∈ (S : Set X) *
          ((D ⊓ Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X)
        rw [← hS.normalizerIn_eq_mul]
        exact hxNM
      rcases hxprod with ⟨s, hsS, d, hdD, hsd⟩
      change s * d = x at hsd
      have hdC0 : d ∈ C0 := by
        have hprodC0 : s * d ∈ C0 := by
          rw [hsd]
          exact hx.1
        have := C0.mul_mem (C0.inv_mem (hSC0 hsS)) hprodC0
        simpa [mul_assoc] using this
      exact ⟨s, hsS, d, ⟨⟨hdC0, hdD.1⟩, hdD.2⟩, hsd⟩
    · intro x hx
      rcases hx with ⟨s, hsS, e, heE, hse⟩
      refine ⟨?_, ?_⟩
      · rw [← hse]
        exact C0.mul_mem (hSC0 hsS) heE.1.1
      · rw [← hse]
        exact (Subgroup.normalizer (Y : Set X)).mul_mem
          (hS.le_normalizer hsS) heE.2
  obtain ⟨P0, hP0map⟩ := exists_sylow_of_two_factor
    hpOdd inf_le_left hYE hEodd hSNC0 hS.isPGroup_two
      hSnormalNC0 (by simpa [NC0, NE] using hfactorNC0)
      P (by rfl)
  have hFrattini : C0 ⊔ normalizerIn M Y = M :=
    normal_sup_normalizerIn_eq_of_sylow inf_le_left
      (by simpa [C0] using centralizerIn_involutionsInSet_normal M)
      P0 hP0map
  have hNMle : normalizerIn M Y ≤ C0 ⊔ D := by
    intro x hx
    have hxprod : x ∈ (S : Set X) * (normalizerIn D Y : Set X) := by
      change x ∈ (S : Set X) *
        ((D ⊓ Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X)
      rw [← hS.normalizerIn_eq_mul]
      exact hx
    rcases hxprod with ⟨s, hsS, d, hdD, hsd⟩
    change s * d = x at hsd
    rw [← hsd]
    exact Subgroup.mul_mem_sup (hSC0 hsS) hdD.1
  have hMC0D : M = C0 ⊔ D := by
    apply le_antisymm
    · rw [← hFrattini]
      exact sup_le le_sup_left (hNMle.trans le_rfl)
    · exact sup_le inf_le_left inf_le_left
  exact hne (by simpa [C0, D] using hMC0D)

/-- The two conclusions of source Lemma 9.7. -/
public structure Lemma97Conclusion
    {X : Type u} [Group X]
    (M : Subgroup X) (t : X) : Prop where
  ne_centralizer_sup :
    M ≠
      (M ⊓ Subgroup.centralizer (involutionsInSet M)) ⊔
        (M ⊓ rightConjugate M t)
  centralizer_involutions_eq_bot :
    (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer (involutionsInSet M) = ⊥
  peterfalvi_centralizer_eq_bot :
    peterfalviV (M ⊓ rightConjugate M t) t ⊓
        Subgroup.centralizer
          (peterfalviKSet (M ⊓ rightConjugate M t) t) = ⊥

/-- Source Lemma 9.7.  Part (a) is the minimal-supplement
change-of-choice argument, and part (b) is the Proposition 8.4
Sylow--Frattini contradiction. -/
public theorem lemma_9_7
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (htrans : IsTransitiveOn M
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)})
    (hfail : ¬ ∃ Q : Subgroup X,
      IsNormalComplementIn M (M ⊓ rightConjugate M t) Q ∧
        Group.IsNilpotent Q)
    (h43 : II1Lemma43bCyclic (X := X)) :
    Lemma97Conclusion M t := by
  have hne := lemma97_ne_centralizer_sup hM ht htM d83 h84 hIne
    htrans hfail h43
  have hright :=
    lemma97_centralizer_eq_bot_of_ne_sup hM ht htM d83 h84 hIne hne
  have hleft :
      (M ⊓ rightConjugate M t) ⊓
          Subgroup.centralizer (involutionsInSet M) = ⊥ := by
    calc
      (M ⊓ rightConjugate M t) ⊓
          Subgroup.centralizer (involutionsInSet M) =
          peterfalviV (M ⊓ rightConjugate M t) t ⊓
            Subgroup.centralizer
              (peterfalviKSet (M ⊓ rightConjugate M t) t) :=
        lemma97_centralizer_eq hM ht htM d83
      _ = ⊥ := hright
  exact ⟨hne, hleft, hright⟩

end CFSG.BenderSuzuki
