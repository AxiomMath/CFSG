module

import Mathlib.GroupTheory.IndexNormal
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.theorem_7_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.theorem_6_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.theorem_6_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_6

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise IsMulCommutative commutatorElement

/-! # Proposition 7.5 from BG Section 7 -/

open scoped Pointwise

section

variable {G : Type*} [Group G] [Finite G]

private theorem CFSG.subgroupPrimeSet_eq_singleton_of_isPGroup_nonbot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hAp : IsPGroup p A) (hA_ne_bot : A ≠ ⊥) :
    subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes) := by
  ext q
  constructor
  · intro hq
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    have hqpow : q.val ∣ p ^ n := by
      simpa [subgroupPrimeSet, hn] using hq
    have hqdvdp : q.val ∣ p := q.2.dvd_of_dvd_pow hqpow
    have hqeq : q.val = p :=
      (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hqdvdp |>.resolve_left q.2.ne_one
    exact Subtype.ext hqeq
  · intro hq
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      apply hA_ne_bot
      apply Subgroup.card_eq_one.mp
      simp [hn, hn0]
    rcases Nat.exists_eq_succ_of_ne_zero hn_ne_zero with ⟨m, rfl⟩
    subst q
    simp [subgroupPrimeSet, hn, Nat.pow_succ]
    exact Nat.dvd_mul_left p (p ^ m)

private theorem CFSG.isPiSubgroup_singleton_compl_of_coprime_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hcop : Nat.Coprime p (Nat.card H)) :
    IsPiSubgroup (G := G) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H := by
  intro q hq
  simp only [Set.mem_compl_iff]
  intro hqeq
  subst q
  exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hcop) hq

private theorem CFSG.coprime_card_of_isPiSubgroup_singleton_compl
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G}
    (hH : IsPiSubgroup (G := G) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H) :
    Nat.Coprime p (Nat.card H) := by
  refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 ?_
  intro hpH
  have hpmem : (⟨p, Fact.out⟩ : Nat.Primes) ∈ (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) :=
    hH ⟨p, Fact.out⟩ hpH
  have hpmem' :
      ¬ (⟨p, Fact.out⟩ : Nat.Primes) ∈ ({⟨p, Fact.out⟩} : Set Nat.Primes) := hpmem
  exact hpmem' (Set.mem_singleton _)

private theorem CFSG.piCoreIn_singleton_compl_eq_pPrimeCore_map
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G) :
    piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H =
      (pPrimeCore p ↥H).map H.subtype := by
  let Sπ : Set (Subgroup ↥H) :=
    {K | K.Normal ∧ IsPiSubgroup (G := ↥H) (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) K}
  let Sp : Set (Subgroup ↥H) := {K | K.Normal ∧ Nat.Coprime p (Nat.card K)}
  have hsets : Sπ = Sp := by
    ext K
    constructor
    · rintro ⟨hKnorm, hKπ⟩
      exact ⟨hKnorm, coprime_card_of_isPiSubgroup_singleton_compl (p := p) hKπ⟩
    · rintro ⟨hKnorm, hKcop⟩
      exact ⟨hKnorm, isPiSubgroup_singleton_compl_of_coprime_card (p := p) hKcop⟩
  calc
    piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) H
        = (piCore (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) ↥H).map H.subtype := rfl
    _ = (sSup Sπ).map H.subtype := rfl
    _ = (sSup Sp).map H.subtype := by rw [hsets]
    _ = (pPrimeCore p ↥H).map H.subtype := rfl

private theorem CFSG.maximalElementaryAbelianSubgroups_subgroupOf_of_set_eq
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A X : Subgroup G} (hAX : A ≤ X)
    (hAeq :
      (A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1})
    [IsMulCommutative A] :
    A.subgroupOf X ∈ maximalElementaryAbelianSubgroups p ↥X := by
  have hApow : ∀ a : A, a ^ p = 1 := by
    intro a
    have ha : (a : G) ∈ (A : Set G) := a.property
    rw [hAeq] at ha
    apply Subtype.ext
    simpa using ha.2
  have hAsub_elem : IsElementaryAbelian p (A.subgroupOf X) := by
    let hAelem : IsElementaryAbelian p A := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hApow
    }
    let : IsElementaryAbelian p A := hAelem
    exact IsElementaryAbelian.subgroupOf (p := p) hAX
  refine ⟨hAsub_elem, ?_⟩
  intro B hAB hBelem
  let Bmap : Subgroup G := B.map X.subtype
  have hBmap_elem : IsElementaryAbelian p Bmap := by
    let : IsElementaryAbelian p B := hBelem
    simpa [Bmap] using IsElementaryAbelian.map_subtype (p := p) (K := X) (H := B)
  have hBmap_le_A : Bmap ≤ A := by
    intro b hb
    rcases Subgroup.mem_map.mp hb with ⟨b', hb'B, rfl⟩
    have hb_cent : (b' : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      let aX : X := ⟨a, hAX ha⟩
      have haB : aX ∈ B := hAB ha
      exact congrArg Subtype.val
        (setLike_mul_comm (s := B) haB hb'B)
    have hb_pow : (b' : G) ^ p = 1 := by
      let : IsElementaryAbelian p Bmap := hBmap_elem
      simpa using congrArg (fun z : Bmap => ((z : Bmap) : G))
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p Bmap) ⟨(b' : G), hb⟩)
    have hbA : (b' : G) ∈ A := by
      have hbAset :
          (b' : G) ∈ {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1} :=
        ⟨hb_cent, hb_pow⟩
      change (b' : G) ∈ (A : Set G)
      rw [hAeq]
      exact hbAset
    exact hbA
  have hB_le : B ≤ A.subgroupOf X := by
    intro b hb
    exact hBmap_le_A (Subgroup.mem_map_of_mem X.subtype hb)
  exact le_antisymm hAB hB_le


private theorem CFSG.piCoreIn_mem_section7HFamily_of_le_normalizer
    {G : Type*} [Group G] [Finite G] {π : Set Nat.Primes} {H P : Subgroup G}
    (hPH : P ≤ Subgroup.normalizer (H : Set G)) :
    piCoreIn π H ∈ section7HFamily H P π := by
  refine ⟨piCoreIn_le _ _, piCoreIn_isPiSubgroup _ _, ?_⟩
  exact le_normalizer_piCoreIn_of_le_normalizer (G := G) (π := π) (H := H) (P := P) hPH

private theorem CFSG.le_section7Generated_of_mem
    {G : Type*} [Group G] {H A Q : Subgroup G} {π : Set Nat.Primes}
    (hQ : Q ∈ section7HFamily H A π) :
    Q ≤ section7Generated H A π := by
  change Q ≤ sSup (section7HFamily H A π)
  exact le_sSup hQ


private theorem CFSG.inf_eq_bot_of_isPGroup_and_coprime_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H K : Subgroup G} (hHp : IsPGroup p H) (hKcop : Nat.Coprime p (Nat.card K)) :
    H ⊓ K = ⊥ := by
  have hHKsub_p : IsPGroup p ↥((H ⊓ K).subgroupOf H) :=
    IsPGroup.to_subgroup (H := (H ⊓ K).subgroupOf H) hHp
  have hHKp : IsPGroup p ↥(H ⊓ K) := by
    exact hHKsub_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := H) inf_le_left)
  have hHKcard_dvd : Nat.card ↥(H ⊓ K) ∣ Nat.card K := by
    have hsub_dvd : Nat.card ↥((H ⊓ K).subgroupOf K) ∣ Nat.card K :=
      Subgroup.card_subgroup_dvd_card ((H ⊓ K).subgroupOf K)
    have hcard_eq : Nat.card ↥((H ⊓ K).subgroupOf K) = Nat.card ↥(H ⊓ K) := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := K) inf_le_right).toEquiv
    rwa [hcard_eq] at hsub_dvd
  have hHKcop : Nat.Coprime p (Nat.card ↥(H ⊓ K)) :=
    Nat.Coprime.of_dvd_right hHKcard_dvd hKcop
  have hcard_one : Nat.card ↥(H ⊓ K) = 1 := by
    rcases hHKp.card_eq_or_dvd with h1 | hpdiv
    · exact h1
    · exfalso
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hHKcop) hpdiv
  exact Subgroup.card_eq_one.mp hcard_one


private theorem CFSG.subgroupCentralizerIn_le_of_selfCentralizing_subgroupOf
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {A : Subgroup G} (_hAP : A ≤ (P : Subgroup G))
    (hAcent :
      Subgroup.centralizer ((A.subgroupOf (P : Subgroup G)) : Set P) =
        A.subgroupOf (P : Subgroup G)) :
    subgroupCentralizerIn (P : Subgroup G) A ≤ A := by
  intro x hx
  have hxP : x ∈ (P : Subgroup G) := hx.1
  have hxA0cent :
      (⟨x, hxP⟩ : P) ∈ Subgroup.centralizer ((A.subgroupOf (P : Subgroup G)) : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hx.2) ((a : P) : G) (Subgroup.mem_subgroupOf.mp ha)
  have hxA0 : (⟨x, hxP⟩ : P) ∈ A.subgroupOf (P : Subgroup G) := by
    simpa [hAcent] using hxA0cent
  change x ∈ A at hxA0
  exact hxA0

private theorem CFSG.centralizer_zpowers_eq_centralizer_singleton
    {G : Type*} [Group G] (z : G) :
    Subgroup.centralizer (Subgroup.zpowers z : Set G) = Subgroup.centralizer ({z} : Set G) := by
  ext x
  constructor
  · intro hx
    have hsubset : ({z} : Set G) ⊆ (Subgroup.zpowers z : Set G) := by
      intro y hy
      simp at hy
      subst y
      exact Subgroup.mem_zpowers z
    exact Subgroup.centralizer_le hsubset hx
  · intro hx
    have hxz : z * x = x * z := (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have hcomm : Commute z x := hxz
    simpa using (hcomm.zpow_left n).eq

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.natCard_pSubgroup_mulAut_le_p_of_elementaryAbelian_card_le_p_sq_local
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p A] {P : Subgroup (MulAut A)} (hPp : IsPGroup p P)
    (hAcard : Nat.card A ≤ p ^ 2) :
    Nat.card P ≤ p := by
  let hp_prime : Nat.Prime p := Fact.out
  let Q := Additive A
  let : AddCommGroup Q := Additive.addCommGroup
  let : Module (ZMod p) Q := inferInstance
  let : Finite Q := inferInstance
  let : FiniteDimensional (ZMod p) Q := Module.Finite.of_finite
  have hp_one_lt : 1 < p := hp_prime.one_lt
  have hcardQ : Nat.card A = p ^ Module.finrank (ZMod p) Q := by
    calc
      Nat.card A = Nat.card Q := Nat.card_congr Additive.ofMul
      _ = p ^ Module.finrank (ZMod p) Q :=
        by simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Q))
  have hdim_le_two : Module.finrank (ZMod p) Q ≤ 2 := by
    have hpow_le : p ^ Module.finrank (ZMod p) Q ≤ p ^ 2 := by
      simpa [hcardQ] using hAcard
    exact (Nat.pow_le_pow_iff_right hp_one_lt).1 hpow_le
  let ψfun : P → LinearMap.GeneralLinearGroup (ZMod p) Q := fun a =>
    let eAdd : Q ≃+ Q := MulEquiv.toAdditive (a : MulAut A)
    let eLin : Q ≃ₗ[ZMod p] Q :=
      eAdd.toLinearEquiv (fun c x => by
        simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
    LinearMap.GeneralLinearGroup.ofLinearEquiv eLin
  let ψ : P →* LinearMap.GeneralLinearGroup (ZMod p) Q := {
    toFun := ψfun
    map_one' := by
      ext x
      rfl
    map_mul' := by
      intro a b
      ext x
      rfl
  }
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    ext x
    have hx :=
      congrArg
        (fun f : LinearMap.GeneralLinearGroup (ZMod p) Q => (f : Q → Q) (Additive.ofMul x))
        hab
    simpa [ψ, ψfun, Q] using hx
  let n := Module.finrank (ZMod p) Q
  let b : Module.Basis (Fin n) (ZMod p) Q := Module.finBasis (ZMod p) Q
  let χ : P →* GL (Fin n) (ZMod p) := ((Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom).comp ψ
  have hχ_inj : Function.Injective χ := by
    exact (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hψ_inj
  have hcard_dvd_GL : Nat.card P ∣ Nat.card (GL (Fin n) (ZMod p)) :=
    Subgroup.card_dvd_of_injective χ hχ_inj
  have hp_not_dvd_pred : ¬ p ∣ p - 1 := by
    intro h
    have hdiv1 : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) h
    have hsub : p - (p - 1) = 1 := by
      have hp_eq : p = (p - 1) + 1 := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hp_prime.pos).symm
      rw [hp_eq]
      exact Nat.add_sub_cancel_left (p - 1) 1
    rw [hsub] at hdiv1
    exact hp_prime.not_dvd_one hdiv1
  have hp_not_dvd_sq_sub_one : ¬ p ∣ p ^ 2 - 1 := by
    intro h
    have hp_dvd_sq : p ∣ p ^ 2 := by
      simp [pow_two]
    have hdiv1 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub hp_dvd_sq h
    have hsub : p ^ 2 - (p ^ 2 - 1) = 1 := by
      have hp2_eq : p ^ 2 = (p ^ 2 - 1) + 1 := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos (pow_pos hp_prime.pos 2)).symm
      rw [hp2_eq]
      exact Nat.add_sub_cancel_left (p ^ 2 - 1) 1
    rw [hsub] at hdiv1
    exact hp_prime.not_dvd_one hdiv1
  have hp_sq_not_dvd_GL : ¬ p ^ 2 ∣ Nat.card (GL (Fin n) (ZMod p)) := by
    have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by
      omega
    rcases hn_cases with hn | hn | hn
    · intro hdiv
      have hcard_GL0 : Nat.card (GL (Fin 0) (ZMod p)) = 1 := by
        simp
      rw [hn] at hdiv
      rw [hcard_GL0] at hdiv
      have hp_dvd_one : p ∣ 1 := dvd_trans (by simp [pow_two]) hdiv
      exact hp_prime.not_dvd_one hp_dvd_one
    · intro hdiv
      have hcard_GL1 : Nat.card (GL (Fin 1) (ZMod p)) = p - 1 := by
        simpa [pow_one] using (Matrix.card_GL_field (𝔽 := ZMod p) 1)
      rw [hn] at hdiv
      rw [hcard_GL1] at hdiv
      have hp_dvd_pred : p ∣ p - 1 := dvd_trans (by simp [pow_two]) hdiv
      exact hp_not_dvd_pred hp_dvd_pred
    · intro hdiv
      have hcard_GL2 : Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
        simpa [Fin.prod_univ_two] using (Matrix.card_GL_field (𝔽 := ZMod p) 2)
      rw [hn] at hdiv
      rw [hcard_GL2] at hdiv
      have hsq_sub : p ^ 2 - p = p * (p - 1) := by
        calc
          p ^ 2 - p = p * p - p * 1 := by rw [pow_two, Nat.mul_one]
          _ = p * (p - 1) := by rw [Nat.mul_sub_left_distrib]
      have hrewrite : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
        calc
          (p ^ 2 - 1) * (p ^ 2 - p) = (p ^ 2 - 1) * (p * (p - 1)) := by rw [hsq_sub]
          _ = ((p ^ 2 - 1) * p) * (p - 1) := by rw [Nat.mul_assoc]
          _ = (p * (p ^ 2 - 1)) * (p - 1) := by rw [Nat.mul_comm (p ^ 2 - 1) p]
          _ = p * ((p ^ 2 - 1) * (p - 1)) := by rw [← Nat.mul_assoc]
      have hdiv' : p * p ∣ p * ((p ^ 2 - 1) * (p - 1)) := by
        rw [pow_two] at hdiv ⊢
        convert hdiv using 1
        simpa [pow_two] using hrewrite.symm
      have hcancel : p ∣ (p ^ 2 - 1) * (p - 1) :=
        Nat.dvd_of_mul_dvd_mul_left hp_prime.pos hdiv'
      exact (hp_prime.dvd_mul.mp hcancel).elim hp_not_dvd_sq_sub_one hp_not_dvd_pred
  obtain ⟨m, hm⟩ := hPp.exists_card_eq
  have hm_le_one : m ≤ 1 := by
    by_contra hm_gt
    have htwo_le_m : 2 ≤ m := by omega
    have hp_sq_dvd_cardP : p ^ 2 ∣ Nat.card P := by
      rw [hm]
      exact (Nat.pow_dvd_pow_iff_le_right hp_one_lt).2 htwo_le_m
    exact hp_sq_not_dvd_GL (dvd_trans hp_sq_dvd_cardP hcard_dvd_GL)
  calc
    Nat.card P = p ^ m := hm
    _ ≤ p ^ 1 := (Nat.pow_le_pow_iff_right hp_one_lt).2 hm_le_one
    _ = p := by simp

private theorem CFSG.pCore_le_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) :
    pCore p G ≤ (S : Subgroup G) := by
  have hsup_p : IsPGroup p (((S : Subgroup G) ⊔ pCore p G : Subgroup G)) := by
    exact IsPGroup.to_sup_of_normal_right (p := p) (H := (S : Subgroup G)) (K := pCore p G)
      S.isPGroup' (pCore_isPGroup (G := G) (p := p))
  have hEq : (((S : Subgroup G) ⊔ pCore p G : Subgroup G)) = (S : Subgroup G) :=
    S.3 hsup_p le_sup_left
  exact sup_eq_left.mp hEq

private theorem CFSG.le_pPrimeCore_of_contains_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {A : Subgroup G} [IsMulCommutative A]
    (hAP : A ≤ (P : Subgroup G))
    (hAnorm : (A.subgroupOf (P : Subgroup G)).Normal)
    (hCPA : subgroupCentralizerIn (P : Subgroup G) A ≤ A)
    {X : Subgroup G} (hPX : (P : Subgroup G) ≤ X)
    [Group.IsSolvable X] (hXodd : Odd (Nat.card X))
    {Y : Subgroup G} (hYX : Y ≤ X)
    (hYcop : Nat.Coprime p (Nat.card Y))
    (hAYnorm : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y.subgroupOf X ≤ pPrimeCore p X := by
  classical
  let AX : Subgroup X := A.subgroupOf X
  let YX : Subgroup X := Y.subgroupOf X
  let PX : Sylow p X := P.subtype hPX
  let ePX : ↥(PX : Subgroup X) ≃* ↥(P : Subgroup G) := {
    toFun x := ⟨((x : X) : G), by
      have hx := x.property
      change (x : X) ∈ (P : Subgroup G).subgroupOf X at hx
      exact hx⟩
    invFun x := ⟨⟨(x : G), hPX x.property⟩, by
      change (x : G) ∈ (P : Subgroup G)
      exact x.property⟩
    left_inv x := by
      apply Subtype.ext
      rfl
    right_inv x := by
      apply Subtype.ext
      rfl
    map_mul' x y := by
      apply Subtype.ext
      rfl
  }
  let A0 : Subgroup P := A.subgroupOf (P : Subgroup G)
  let AXP : Subgroup (PX : Subgroup X) := A0.map ePX.symm.toMonoidHom
  have hAXPnorm : AXP.Normal := by
    dsimp [AXP]
    exact hAnorm.map ePX.symm.toMonoidHom ePX.symm.surjective
  let : AXP.Normal := hAXPnorm
  have hAXPcomm : IsMulCommutative AXP := by
    dsimp [AXP]
    simpa using (Subgroup.map_isMulCommutative (f := ePX.symm.toMonoidHom) (H := A0))
  let : IsMulCommutative AXP := hAXPcomm
  have hAX_le_PX : AX ≤ (PX : Subgroup X) := by
    intro a ha
    have haG : (a : G) ∈ A := by
      simpa [AX, Subgroup.mem_subgroupOf] using ha
    simpa [PX, Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hAP haG
  have hAX_le_Op : AX ≤ Op_p'p p X := by
    have h6 : AXP.map PX.toSubgroup.subtype ≤ Op_p'p p X := theorem_6_1 (G := X) (p := p) hXodd PX AXP
    intro a ha
    have haG : (a : G) ∈ A := by
      simpa [AX, Subgroup.mem_subgroupOf] using ha
    let aP : P := ⟨(a : G), hAP haG⟩
    have haA0 : aP ∈ A0 := by
      change (a : G) ∈ A
      exact haG
    have haAXP : ePX.symm aP ∈ AXP := by
      exact Subgroup.mem_map.mpr ⟨aP, haA0, rfl⟩
    have haOpX : (((ePX.symm aP : PX) : X)) ∈ Op_p'p p X :=
      h6 (Subgroup.mem_map_of_mem PX.toSubgroup.subtype haAXP)
    have hea : ((ePX.symm aP : PX) : X) = a := by
      rfl
    simpa [hea] using haOpX
  let M : Subgroup X := pPrimeCore p X
  let : M.Normal := by
    dsimp [M]
    infer_instance
  let q : X →* X ⧸ M := QuotientGroup.mk' M
  let Abar : Subgroup (X ⧸ M) := AX.map q
  let Ybar : Subgroup (X ⧸ M) := YX.map q
  have hmap_op : (Op_p'p p X).map q = pCore p (X ⧸ M) := by
    dsimp [Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p X))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p X))
        (H := pCore p (X ⧸ pPrimeCore p X)))
  have hAbar_le_pCore : Abar ≤ pCore p (X ⧸ M) := by
    dsimp [Abar]
    calc
      AX.map q ≤ (Op_p'p p X).map q := Subgroup.map_mono hAX_le_Op
      _ = pCore p (X ⧸ M) := hmap_op
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := X) (p := p))
  have hPX_inf_M : (PX : Subgroup X) ⊓ M = ⊥ := by
    simpa [M] using
      inf_eq_bot_of_isPGroup_and_coprime_card (G := X) (p := p) PX.isPGroup' hMcop
  have hYX_card : Nat.card YX = Nat.card Y := by
    simpa [YX] using
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Y) (K := X) hYX).toEquiv)
  have hYbar_cop : Nat.Coprime p (Nat.card Ybar) := by
    dsimp [Ybar]
    have hYXcop : Nat.Coprime p (Nat.card YX) := by
      rw [hYX_card]
      exact hYcop
    exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := YX) q) hYXcop
  have hAX_norm_YX : AX ≤ Subgroup.normalizer (YX : Set X) := by
    intro a ha
    have haG : (a : G) ∈ A := by
      simpa [AX, Subgroup.mem_subgroupOf] using ha
    have hnorm_eq :
        Subgroup.normalizer (YX : Set X) =
          (Subgroup.normalizer (Y : Set G)).subgroupOf X := by
      exact (Subgroup.subgroupOf_normalizer_eq (H := Y) (N := X) hYX).symm
    rw [hnorm_eq]
    change (a : G) ∈ Subgroup.normalizer (Y : Set G)
    exact hAYnorm haG
  have hAbar_norm_Ybar : Abar ≤ Subgroup.normalizer (Ybar : Set (X ⧸ M)) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hy
    rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, rfl⟩
    have hyconj : a0 * y0 * a0⁻¹ ∈ YX :=
      (Subgroup.mem_normalizer_iff.mp (hAX_norm_YX ha0) y0).1 hy0
    exact Subgroup.mem_map.mpr ⟨a0 * y0 * a0⁻¹, hyconj, by simp [map_mul, mul_assoc]⟩
  have hpCore_inf_Ybar : pCore p (X ⧸ M) ⊓ Ybar = ⊥ := by
    exact inf_eq_bot_of_isPGroup_and_coprime_card
      (G := X ⧸ M) (p := p) (pCore_isPGroup (G := X ⧸ M) (p := p)) hYbar_cop
  have hAbar_fix : Abar ≤ subgroupCentralizerIn (pCore p (X ⧸ M)) Ybar := by
    intro a ha
    refine ⟨hAbar_le_pCore ha, ?_⟩
    change a ∈ Subgroup.centralizer (Ybar : Set (X ⧸ M))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcomm_pcore : ⁅a, y⁆ ∈ pCore p (X ⧸ M) := by
      exact
        (Subgroup.commutator_le_left (H₁ := pCore p (X ⧸ M)) (H₂ := Ybar))
          (Subgroup.commutator_mem_commutator (hAbar_le_pCore ha) hy)
    have hcomm_Ybar : ⁅a, y⁆ ∈ Ybar := by
      have hyconj : a * y * a⁻¹ ∈ Ybar :=
        (Subgroup.mem_normalizer_iff.mp (hAbar_norm_Ybar ha) y).1 hy
      change a * y * a⁻¹ * y⁻¹ ∈ Ybar
      exact Ybar.mul_mem hyconj (Ybar.inv_mem hy)
    have hcomm_bot : ⁅a, y⁆ ∈ (⊥ : Subgroup (X ⧸ M)) := by
      rw [← hpCore_inf_Ybar]
      exact ⟨hcomm_pcore, hcomm_Ybar⟩
    exact
      ((commutatorElement_eq_one_iff_mul_comm).1 <|
        by simpa using hcomm_bot).symm
  let Pbar : Sylow p (X ⧸ M) := PX.mapSurjective (QuotientGroup.mk'_surjective M)
  have hpCore_le_Pbar : pCore p (X ⧸ M) ≤ (Pbar : Subgroup (X ⧸ M)) := pCore_le_sylow Pbar
  have hcent_Abar : subgroupCentralizerIn (pCore p (X ⧸ M)) Abar ≤ Abar := by
    intro x hx
    have hxPbar : x ∈ (Pbar : Subgroup (X ⧸ M)) := hpCore_le_Pbar hx.1
    rcases Subgroup.mem_map.mp hxPbar with ⟨xp, hxpP, rfl⟩
    have hxp_mem_P : ((xp : X) : G) ∈ (P : Subgroup G) := by
      simpa [PX, Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hxpP
    have hxp_centAX : xp ∈ Subgroup.centralizer (AX : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haAbar : q a ∈ Abar := Subgroup.mem_map_of_mem q ha
      have hq_comm : q a * q xp = q xp * q a :=
        (Subgroup.mem_centralizer_iff.mp hx.2) (q a) haAbar
      have hqcomm : q ⁅xp, a⁆ = 1 := by
        simpa [map_commutatorElement] using
          (commutatorElement_eq_one_iff_mul_comm).2 hq_comm.symm
      have hcomm_M : ⁅xp, a⁆ ∈ M := by
        exact (QuotientGroup.eq_one_iff (N := M) (x := ⁅xp, a⁆)).1 hqcomm
      have haPX : a ∈ (PX : Subgroup X) := hAX_le_PX ha
      have hcomm_PX : ⁅xp, a⁆ ∈ (PX : Subgroup X) := by
        change xp * a * xp⁻¹ * a⁻¹ ∈ (PX : Subgroup X)
        exact
          (PX : Subgroup X).mul_mem
            ((PX : Subgroup X).mul_mem ((PX : Subgroup X).mul_mem hxpP haPX)
              ((PX : Subgroup X).inv_mem hxpP))
            ((PX : Subgroup X).inv_mem haPX)
      have hcomm_bot : ⁅xp, a⁆ ∈ (⊥ : Subgroup X) := by
        rw [← hPX_inf_M]
        exact ⟨hcomm_PX, hcomm_M⟩
      exact
        ((commutatorElement_eq_one_iff_mul_comm).1 <|
          by simpa using hcomm_bot).symm
    have hxp_centA : ((xp : X) : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a haA
      let aX : X := ⟨a, hPX (hAP haA)⟩
      have haAX : aX ∈ AX := by
        simpa [AX, aX, Subgroup.mem_subgroupOf] using haA
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hxp_centAX) aX haAX)
    have hxp_cent_in : ((xp : X) : G) ∈ subgroupCentralizerIn (P : Subgroup G) A := by
      exact ⟨hxp_mem_P, hxp_centA⟩
    have hxpA : ((xp : X) : G) ∈ A := hCPA hxp_cent_in
    have hxpAX : xp ∈ AX := by
      simpa [AX, Subgroup.mem_subgroupOf] using hxpA
    exact Subgroup.mem_map.mpr ⟨xp, hxpAX, rfl⟩
  have : Subgroup.Normalizes Ybar (pCore p (X ⧸ M)) :=
    ⟨Subgroup.le_normalizer_of_normal (H := pCore p (X ⧸ M))⟩
  have hfix_eq :
      fixedPointSubgroup (↥Ybar) (↥(pCore p (X ⧸ M))) =
        (subgroupCentralizerIn (pCore p (X ⧸ M)) Ybar).subgroupOf (pCore p (X ⧸ M)) := by
    simpa using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
        (pCore p (X ⧸ M)) Ybar (Subgroup.le_normalizer_of_normal (H := pCore p (X ⧸ M)))
  let AbarCore : Subgroup (pCore p (X ⧸ M)) := Abar.subgroupOf (pCore p (X ⧸ M))
  have hAbarCore_le_fix :
      AbarCore ≤ fixedPointSubgroup (↥Ybar) (↥(pCore p (X ⧸ M))) := by
    rw [hfix_eq]
    intro a ha
    exact hAbar_fix ha
  have hcent_AbarCore :
      Subgroup.centralizer (AbarCore : Set (pCore p (X ⧸ M))) ≤ AbarCore := by
    intro x hx
    have hxbar : ((x : pCore p (X ⧸ M)) : X ⧸ M) ∈ subgroupCentralizerIn (pCore p (X ⧸ M)) Abar := by
      refine ⟨x.2, ?_⟩
      change ((x : pCore p (X ⧸ M)) : X ⧸ M) ∈
        Subgroup.centralizer (Abar : Set (X ⧸ M))
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      let aCore : AbarCore := ⟨⟨a, hAbar_le_pCore ha⟩, ha⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) aCore aCore.2)
    exact hcent_Abar hxbar
  have hcent_fix_le_fix :
      Subgroup.centralizer
          (fixedPointSubgroup (↥Ybar) (↥(pCore p (X ⧸ M))) : Set (pCore p (X ⧸ M))) ≤
        fixedPointSubgroup (↥Ybar) (↥(pCore p (X ⧸ M))) := by
    have hsubset :
        (AbarCore : Set (pCore p (X ⧸ M))) ⊆
          fixedPointSubgroup (↥Ybar) (↥(pCore p (X ⧸ M))) := by
      intro a ha
      exact hAbarCore_le_fix ha
    exact
      (Subgroup.centralizer_le hsubset).trans
        (hcent_AbarCore.trans hAbarCore_le_fix)
  have hYbar_pcore_cop :
      Nat.Coprime (Nat.card Ybar) (Nat.card (pCore p (X ⧸ M))) := by
    rcases (pCore_isPGroup (G := X ⧸ M) (p := p)).exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (hYbar_cop.symm.pow_right n)
  have htriv :
      ActsTrivially (A := ↥Ybar) (G := ↥(pCore p (X ⧸ M))) := by
    exact
      proposition_1_10
        (G := ↥(pCore p (X ⧸ M))) (A := ↥Ybar)
        (pCore_isPGroup (G := X ⧸ M) (p := p)).isNilpotent
        hYbar_pcore_cop hcent_fix_le_fix
  have hYbar_le_cent_pCore :
      Ybar ≤ Subgroup.centralizer (pCore p (X ⧸ M) : Set (X ⧸ M)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
    intro k hk
    have hkfix : (⟨y, hy⟩ : Ybar) • (⟨k, hk⟩ : pCore p (X ⧸ M)) = ⟨k, hk⟩ :=
      htriv ⟨y, hy⟩ ⟨k, hk⟩
    have hconj : y * k * y⁻¹ = k := by
      simpa using congrArg Subtype.val hkfix
    exact (commutatorElement_eq_one_iff_mul_comm).2 <| by
      have := congrArg (fun t : X ⧸ M => t * y) hconj
      simpa [mul_assoc] using this.symm
  have hsolvQ : Group.IsSolvable (X ⧸ M) := by infer_instance
  have hcore_bot : pPrimeCore p (X ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := X) (p := p))
  have hcent_pCore_le : Subgroup.centralizer (pCore p (X ⧸ M) : Set (X ⧸ M)) ≤ pCore p (X ⧸ M) := by
    have hOp_eq : Op_p'p p (X ⧸ M) = pCore p (X ⧸ M) :=
      Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := X ⧸ M) (p := p) hcore_bot
    let T : Sylow p (↥(Op_p'p p (X ⧸ M))) := by
      have htop_p : IsPGroup p (⊤ : Subgroup (Op_p'p p (X ⧸ M))) := by
        rw [hOp_eq]
        simpa using
          (pCore_isPGroup (G := X ⧸ M) (p := p)).to_subgroup
            (⊤ : Subgroup (pCore p (X ⧸ M)))
      exact IsPGroup.toSylow (p := p) htop_p (by
        simpa using (Fact.out : Nat.Prime p).not_dvd_one)
    have htop_p : IsPGroup p (⊤ : Subgroup (Op_p'p p (X ⧸ M))) := by
      rw [hOp_eq]
      simpa using
        (pCore_isPGroup (G := X ⧸ M) (p := p)).to_subgroup
          (⊤ : Subgroup (pCore p (X ⧸ M)))
    have hcent :
        Subgroup.centralizer ((T.1.map (Op_p'p p (X ⧸ M)).subtype : Subgroup (X ⧸ M)) :
            Set (X ⧸ M)) ≤
          Op_p'p p (X ⧸ M) :=
      proposition_1_15_a (G := X ⧸ M) (p := p) hsolvQ T
    have hTtop : (T : Subgroup (Op_p'p p (X ⧸ M))) = ⊤ := by
      exact T.3 htop_p le_top
    have hTmap_eq :
        (T.1.map (Op_p'p p (X ⧸ M)).subtype : Subgroup (X ⧸ M)) =
          Op_p'p p (X ⧸ M) := by
      rw [hTtop]
      ext x
      constructor
      · rintro ⟨x', hx', rfl⟩
        exact x'.2
      · intro hx
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
    calc
      Subgroup.centralizer (pCore p (X ⧸ M) : Set (X ⧸ M))
          = Subgroup.centralizer
              ((T.1.map (Op_p'p p (X ⧸ M)).subtype : Subgroup (X ⧸ M)) :
                Set (X ⧸ M)) := by
            rw [hTmap_eq, hOp_eq]
      _ ≤ Op_p'p p (X ⧸ M) := hcent
      _ = pCore p (X ⧸ M) := hOp_eq
  have hYbar_le_pCore : Ybar ≤ pCore p (X ⧸ M) := hYbar_le_cent_pCore.trans hcent_pCore_le
  have hYbar_bot : Ybar = ⊥ := by
    calc
      Ybar = Ybar ⊓ pCore p (X ⧸ M) := (inf_eq_left.2 hYbar_le_pCore).symm
      _ = ⊥ := by simpa [inf_comm] using hpCore_inf_Ybar
  have hYX_le_ker : YX ≤ q.ker := by
    have hmap_bot : YX.map q = ⊥ := by
      simpa [Ybar] using hYbar_bot
    exact (Subgroup.map_eq_bot_iff (H := YX) (f := q)).1 hmap_bot
  simpa [YX, q, M] using hYX_le_ker


private theorem CFSG.le_pPrimeCore_map_of_contains_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {A X Y : Subgroup G} [IsMulCommutative A]
    (hAP : A ≤ (P : Subgroup G))
    (hAnorm : (A.subgroupOf (P : Subgroup G)).Normal)
    (hCPA : subgroupCentralizerIn (P : Subgroup G) A ≤ A)
    (hPX : (P : Subgroup G) ≤ X) [Group.IsSolvable X] (hXodd : Odd (Nat.card X))
    (hYX : Y ≤ X) (hYcop : Nat.Coprime p (Nat.card Y))
    (hAYnorm : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ (pPrimeCore p ↥X).map X.subtype := by
  have hYsub_le : Y.subgroupOf X ≤ pPrimeCore p ↥X :=
    le_pPrimeCore_of_contains_sylow
      (P := P) (A := A) hAP hAnorm hCPA hPX hXodd hYX hYcop hAYnorm
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hYX] using
    (Subgroup.map_mono (f := X.subtype) hYsub_le)

private theorem CFSG.le_pPrimeCore_map_of_centralizer_singleton_contains_sylow
    {G : Type*} [Group G] [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {A Y : Subgroup G} [IsMulCommutative A]
    (hAP : A ≤ (P : Subgroup G))
    (hAnorm : (A.subgroupOf (P : Subgroup G)).Normal)
    (hCPA : subgroupCentralizerIn (P : Subgroup G) A ≤ A)
    (z : G) (hz_ne : z ≠ 1) (hPz : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    (hYz : Y ≤ Subgroup.centralizer ({z} : Set G))
    (hYcop : Nat.Coprime p (Nat.card Y))
    (hAYnorm : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤
      (pPrimeCore p ↥(Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype := by
  let X : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hX_ne_top : X ≠ ⊤ := by
    simpa [X] using centralizer_singleton_ne_top_of_ne_one (G := G) (z := z) hz_ne
  have : Group.IsSolvable X := solvable_of_proper_subgroup (G := G) hX_ne_top
  have hXodd : Odd (Nat.card X) := by
    exact odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card X)
  simpa [X] using
    le_pPrimeCore_map_of_contains_sylow
      (P := P) (A := A) hAP hAnorm hCPA hPz hXodd hYz hYcop hAYnorm

private theorem CFSG.le_pPrimeCore_map_of_inf_centralizer_singleton_contains_sylow
    {G : Type*} [Group G] [Finite G] [IsMinCE G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {A Y : Subgroup G} [IsMulCommutative A]
    (hAP : A ≤ (P : Subgroup G))
    (hAnorm : (A.subgroupOf (P : Subgroup G)).Normal)
    (hCPA : subgroupCentralizerIn (P : Subgroup G) A ≤ A)
    (z : G) (hz_ne : z ≠ 1) (hzA : z ∈ A)
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G))
    (hYcop : Nat.Coprime p (Nat.card Y))
    (hAYnorm : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y ⊓ Subgroup.centralizer ({z} : Set G) ≤
      (pPrimeCore p ↥(Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype := by
  let Yz : Subgroup G := Y ⊓ Subgroup.centralizer ({z} : Set G)
  have hYz_cop : Nat.Coprime p (Nat.card Yz) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hYcop
  have hA_normCz : A ≤ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G) := by
    have hA_le_Cz : A ≤ Subgroup.centralizer ({z} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact setLike_mul_comm (s := A) ha hzA
    exact hA_le_Cz.trans Subgroup.le_normalizer
  have hA_normYz : A ≤ Subgroup.normalizer (Yz : Set G) := by
    have hA_normY :
        A ≤ Subgroup.normalizer ((Y : Subgroup G) : Set G) := by
      simpa using hAYnorm
    have hA_normInf :
        A ≤
          Subgroup.normalizer ((Y : Subgroup G) : Set G) ⊓
            Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G) := by
      exact le_inf hA_normY hA_normCz
    exact hA_normInf.trans <| by
      simpa [Yz] using
        (Subgroup.inf_normalizer_le_normalizer_inf
          (H := (Y : Subgroup G)) (K := Subgroup.centralizer ({z} : Set G)))
  exact
    le_pPrimeCore_map_of_centralizer_singleton_contains_sylow
      (P := P) (A := A) hAP hAnorm hCPA z hz_ne hPz inf_le_right hYz_cop hA_normYz

private theorem CFSG.not_isCyclic_of_isElementaryAbelian_card_eq_p_sq
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p A] (hcard : Nat.card A = p ^ 2) :
    ¬ IsCyclic A := by
  intro hcyc
  have hdiv : p ^ 2 ∣ p ^ 1 := by
    simpa [hcard] using (show Nat.card A ∣ p from by
      rw [← hcyc.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p p A)
  have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have : 2 ≤ 1 :=
    (Nat.pow_le_pow_iff_right hp_one_lt).mp (Nat.le_of_dvd (by positivity) hdiv)
  omega

private theorem CFSG.map_pPrimeCore_subgroupOf_eq
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X H : Subgroup G} (hHX : H ≤ X) :
    ((pPrimeCore p ↥(H.subgroupOf X)).map (H.subgroupOf X).subtype).map X.subtype =
      (pPrimeCore p ↥H).map H.subtype := by
  classical
  let e : ↥(H.subgroupOf X) ≃* ↥H := Subgroup.subgroupOfEquivOfLe (H := H) (K := X) hHX
  have hcore :
      (pPrimeCore p ↥(H.subgroupOf X)).map e.toMonoidHom = pPrimeCore p ↥H :=
    pPrimeCore_map_iso (p := p) (G := ↥(H.subgroupOf X)) (G' := ↥H) e
  ext g
  constructor
  · intro hg
    rcases Subgroup.mem_map.mp hg with ⟨x, hx, hxg⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    subst hyx hxg
    refine Subgroup.mem_map.mpr ?_
    refine ⟨e y, ?_, rfl⟩
    rw [← hcore]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  · intro hg
    rcases Subgroup.mem_map.mp hg with ⟨x, hx, rfl⟩
    have hx' : x ∈ (pPrimeCore p ↥(H.subgroupOf X)).map e.toMonoidHom := by
      rw [hcore]
      exact hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(H.subgroupOf X).subtype y, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem (H.subgroupOf X).subtype hy
    · simpa [e] using congrArg Subtype.val hyx

private theorem CFSG.subgroupOf_inf_centralizer_singleton_eq
    {G : Type*} [Group G] (X : Subgroup G) (z : G) (hzX : z ∈ X) :
    let zX : X := ⟨z, hzX⟩
    let H : Subgroup G := X ⊓ Subgroup.centralizer ({z} : Set G)
    (H.subgroupOf X) = Subgroup.centralizer (Subgroup.zpowers zX : Set X) := by
  classical
  intro zX H
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with ⟨hxX, hxCz⟩
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have hxcomm : Commute z x := (Subgroup.mem_centralizer_singleton_iff.mp hxCz).symm
    apply Subtype.ext
    simpa using (hxcomm.zpow_left n).eq
  · intro hx
    refine ⟨x.2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr <| by
      have hxfix : zX * x = x * zX := by
        rw [Subgroup.mem_centralizer_iff] at hx
        exact hx zX (Subgroup.mem_zpowers zX)
      simpa using (congrArg Subtype.val hxfix).symm

private theorem CFSG.card_le_card_sylow_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G} (hQp : IsPGroup p Q) (P : Sylow p G) :
    Nat.card Q ≤ Nat.card P := by
  rcases IsPGroup.exists_le_sylow hQp with ⟨P', hQP'⟩
  calc
    Nat.card Q ≤ Nat.card (P' : Subgroup G) := Subgroup.card_le_of_le hQP'
    _ = Nat.card P := by
      rw [Sylow.card_eq_multiplicity P', Sylow.card_eq_multiplicity P]

private theorem CFSG.normal_of_index_le_prime_of_isPGroup
    {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q] {p : ℕ} [Fact p.Prime]
    (H : Subgroup Q) (hQp : IsPGroup p Q) (hidx_le : H.index ≤ p) :
    H.Normal := by
  by_cases hHtop : H = ⊤
  · simp [hHtop]
  have hidx_ne_one : H.index ≠ 1 := by
    intro hidx_one
    exact hHtop (Subgroup.index_eq_one.mp hidx_one)
  have hidx_ne_zero : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite (H := H)
  rcases hQp.exists_card_eq with ⟨n, hnQ⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have hcard_one : Nat.card Q = 1 := by simpa [hn0] using hnQ
    exact (Nat.ne_of_gt Finite.one_lt_card) hcard_one
  have hidx_dvd_pow : H.index ∣ p ^ n := by
    simpa [hnQ] using (Subgroup.index_dvd_card (H := H))
  have hmin_dvd_idx : H.index.minFac ∣ H.index := Nat.minFac_dvd H.index
  have hmin_dvd_pow : H.index.minFac ∣ p ^ n := dvd_trans hmin_dvd_idx hidx_dvd_pow
  rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hmin_dvd_pow with ⟨m, hmle, hm⟩
  have hmin_le_p : H.index.minFac ≤ p :=
    le_trans (Nat.minFac_le (Nat.pos_of_ne_zero hidx_ne_zero)) hidx_le
  have hm_le_one : m ≤ 1 := by
    have : p ^ m ≤ p ^ 1 := by simpa [hm] using hmin_le_p
    exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp this
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    have hmin_eq_one : H.index.minFac = 1 := by simpa [hm0] using hm
    exact (Nat.minFac_prime hidx_ne_one).ne_one hmin_eq_one
  have hm_one : m = 1 := by omega
  have hp_dvd_idx : p ∣ H.index := by
    have hmin_eq_p : H.index.minFac = p := by simpa [hm_one] using hm
    exact hmin_eq_p ▸ hmin_dvd_idx
  have hidx_eq_p : H.index = p := by
    rcases hp_dvd_idx with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hk0
      have hk_eq_zero : k = 0 := by omega
      have : H.index = 0 := by simpa [hk_eq_zero] using hk
      exact hidx_ne_zero this
    have hk_le_one : k ≤ 1 := by
      have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
      have : p * k ≤ p * 1 := by simpa [hk] using hidx_le
      exact Nat.le_of_mul_le_mul_left this hp_pos
    have hk_one : k = 1 := by omega
    simpa [hk_one] using hk
  refine Subgroup.normal_of_index_eq_minFac_card ?_
  rw [hidx_eq_p, hnQ]
  simpa using ((Fact.out : Nat.Prime p).pow_minFac hn_ne_zero).symm

private theorem CFSG.isPGroup_zpowers_of_pow_eq_one
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {g : G} (hgpow : g ^ p = 1) :
    IsPGroup p (↥(Subgroup.zpowers g)) := by
  have hcard_dvd : Nat.card (Subgroup.zpowers g) ∣ p ^ 1 := by
    simpa [show p ^ 1 = p by simp, Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hgpow
  rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hcard_dvd with ⟨n, hnle, hncard⟩
  exact IsPGroup.of_card hncard

private theorem CFSG.pPrimeCore_map_subtype_subgroupOf_local
    {G : Type*} [Group G] {p : ℕ} (H : Subgroup G) :
    (((pPrimeCore p ↥H).map H.subtype).subgroupOf H) = pPrimeCore p ↥H := by
  change ((pPrimeCore p ↥H).map H.subtype).comap H.subtype = pPrimeCore p ↥H
  exact
    Subgroup.comap_map_eq_self_of_injective
      (H := pPrimeCore p ↥H) (f := H.subtype) H.subtype_injective

private theorem CFSG.subgroupOf_le_pPrimeCore_map_local
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K H : Subgroup G} (hKH : K ≤ H) [hKN : (K.subgroupOf H).Normal]
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p ↥H).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact hcop
  have hsub : K.subgroupOf H ≤ pPrimeCore p ↥H := le_sSup ⟨hKN, hcop'⟩
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKH] using
    (Subgroup.map_mono (f := H.subtype) hsub)

private theorem CFSG.transport_pPrimeCore_from_global_singleton_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X Y : Subgroup G} [Group.IsSolvable X]
    {z : G} (hzX : z ∈ X) (hzpow : z ^ p = 1)
    (hYX : Y ≤ X)
    (hYglob :
      Y ≤
        (pPrimeCore p ↥(Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype) :
    Y ≤ (pPrimeCore p ↥X).map X.subtype := by
  classical
  let Cz : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let H : Subgroup G := X ⊓ Cz
  let Q0 : Subgroup G := (pPrimeCore p ↥Cz).map Cz.subtype
  let Q : Subgroup G := Q0 ⊓ X
  have hYQ : Y ≤ Q := le_inf hYglob hYX
  have hQ0_le_Cz : Q0 ≤ Cz := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.2
  have hQ_le_H : Q ≤ H := by
    intro q hq
    exact ⟨hq.2, hQ0_le_Cz hq.1⟩
  have : (Q0.subgroupOf Cz).Normal := by
    simpa [Q0, pPrimeCore_map_subtype_subgroupOf_local (p := p) Cz] using
      (inferInstance : (pPrimeCore p ↥Cz).Normal)
  have hCz_le_normQ0 : Cz ≤ Subgroup.normalizer (Q0 : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (H := Q0) (K := Cz) hQ0_le_Cz
  have hH_le_normQ : H ≤ Subgroup.normalizer (Q : Set G) := by
    exact
      (le_inf
        (show H ≤ Subgroup.normalizer (Q0 : Set G) from inf_le_right.trans hCz_le_normQ0)
        (show H ≤ Subgroup.normalizer (X : Set G) from inf_le_left.trans X.le_normalizer)).trans <| by
          simpa [Q, inf_comm, inf_left_comm, inf_assoc] using
            (Subgroup.inf_normalizer_le_normalizer_inf (H := Q0) (K := X))
  have : (Q.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hH_le_normQ
  have hQcop : Nat.Coprime p (Nat.card Q) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left) <| by
      have hcardQ0 : Nat.card Q0 = Nat.card (pPrimeCore p ↥Cz) := by
        simpa [Q0] using
          (Subgroup.card_map_of_injective (K := pPrimeCore p ↥Cz) (f := Cz.subtype) Cz.subtype_injective)
      rw [hcardQ0]
      exact pPrimeCore_coprime_card (G := ↥Cz) (p := p)
  have hQcoreH : Q ≤ (pPrimeCore p ↥H).map H.subtype :=
    subgroupOf_le_pPrimeCore_map_local (p := p) hQ_le_H hQcop
  let zX : X := ⟨z, hzX⟩
  have hHsub_eq : H.subgroupOf X = Subgroup.centralizer (Subgroup.zpowers zX : Set X) := by
    simpa [H] using subgroupOf_inf_centralizer_singleton_eq (X := X) (z := z) hzX
  have hzXp : IsPGroup p (↥(Subgroup.zpowers zX)) := by
    exact isPGroup_zpowers_of_pow_eq_one (p := p) (g := zX) <| by
      apply Subtype.ext
      simpa [zX] using hzpow
  have hHC_le_Xcore : (pPrimeCore p ↥H).map H.subtype ≤ (pPrimeCore p ↥X).map X.subtype := by
    calc
      (pPrimeCore p ↥H).map H.subtype
          = ((pPrimeCore p ↥(H.subgroupOf X)).map (H.subgroupOf X).subtype).map X.subtype := by
              symm
              exact map_pPrimeCore_subgroupOf_eq (p := p) (X := X) (H := H) inf_le_left
      _ = ((pPrimeCore p ↥(Subgroup.centralizer (Subgroup.zpowers zX : Set X))).map
            (Subgroup.centralizer (Subgroup.zpowers zX : Set X)).subtype).map X.subtype := by
              rw [hHsub_eq]
      _ ≤ (pPrimeCore p ↥X).map X.subtype := by
              exact Subgroup.map_mono (f := X.subtype)
                (proposition_1_15_b (G := ↥X) (hsolv := inferInstance) (p := p)
                  (Subgroup.zpowers zX) hzXp)
  exact (hYQ.trans hQcoreH).trans hHC_le_Xcore

set_option maxHeartbeats 1000000 in
private theorem CFSG.proposition_7_5_case_eq
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G)
    {A : Subgroup G} (hAp : IsPGroup p A) [IsMulCommutative A]
    (hAeq :
      (A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1})
    (hplen : ∀ X : Subgroup G, X ≠ ⊤ → HasPLengthOne (p := p) ↥X) :
    Hypothesis7_1 A := by
  classical
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := G) p hpG
  have hgpow : g ^ p = 1 := by
    simpa [hgord] using pow_orderOf_eq_one g
  have hg_ne_one : g ≠ 1 := by
    intro hg1
    have : orderOf g = 1 := by simp [hg1]
    exact (Fact.out : Nat.Prime p).ne_one (hgord.symm.trans this)
  have hA_ne_bot : A ≠ ⊥ := by
    intro hAbot
    have hgAset :
        g ∈ {x : G | x ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ∧ x ^ p = 1} := by
      refine ⟨?_, hgpow⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      subst x
      simp
    have hgA : g ∈ A := by
      have hgAset' :
          g ∈ {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1} := by
        simpa [hAbot] using hgAset
      change g ∈ (A : Set G)
      rw [hAeq]
      exact hgAset'
    exact hg_ne_one (by simpa [hAbot] using hgA)
  have hA_ne_top : A ≠ ⊤ := by
    intro hAtop
    have hgcenter : g ∈ Subgroup.center G := by
      have hgA : g ∈ (A : Set G) := by simp [hAtop]
      rw [hAeq] at hgA
      have hgcent_univ : g ∈ Subgroup.centralizer (Set.univ : Set G) := by
        simpa [hAtop] using hgA.1
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subgroup.mem_centralizer_iff.mp hgcent_univ x (by simp)
    exact hg_ne_one (by simpa [center_eq_bot_of_min_ce (G := G)] using hgcenter)
  have hAπ :
      subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes) :=
    subgroupPrimeSet_eq_singleton_of_isPGroup_nonbot (p := p) hAp hA_ne_bot
  refine ⟨hA_ne_bot, hA_ne_top, ?_⟩
  intro X hAX hX_ne_top
  have : Group.IsSolvable X := solvable_of_proper_subgroup (G := G) hX_ne_top
  have hXplen : HasPLengthOne (p := p) ↥X := hplen X hX_ne_top
  have hAmaxX :
      A.subgroupOf X ∈ maximalElementaryAbelianSubgroups p ↥X :=
    maximalElementaryAbelianSubgroups_subgroupOf_of_set_eq (p := p) hAX hAeq
  have hleft_singleton :
      section7Generated X A (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) ≤
        piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) X := by
    refine sSup_le ?_
    intro Y hY
    rcases hY with ⟨hYX, hYπ, hAYnorm⟩
    have hYπ_singleton : IsPiSubgroup (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) Y := by
      simpa [hAπ] using hYπ
    have hYcop : Nat.Coprime p (Nat.card Y) := by
      exact coprime_card_of_isPiSubgroup_singleton_compl (p := p) hYπ_singleton
    have hAYsub :
        A.subgroupOf X ≤ Subgroup.normalizer ((Y.subgroupOf X : Subgroup X) : Set X) := by
      have hnorm_eq :
          Subgroup.normalizer ((Y.subgroupOf X : Subgroup X) : Set X) =
            (Subgroup.normalizer (Y : Set G)).subgroupOf X := by
        exact (Subgroup.subgroupOf_normalizer_eq (H := Y) (N := X) hYX).symm
      intro a ha
      rw [hnorm_eq]
      change (a : G) ∈ Subgroup.normalizer (Y : Set G)
      exact hAYnorm ha
    have hYsub_cop : Nat.Coprime p (Nat.card (Y.subgroupOf X)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Y) (K := X) hYX).toEquiv]
      exact hYcop
    have hYsub_le : Y.subgroupOf X ≤ pPrimeCore p ↥X :=
      theorem_6_7 (G := ↥X) (p := p) hpodd hXplen hAmaxX hYsub_cop hAYsub
    have hY_le :
        Y ≤ (pPrimeCore p ↥X).map X.subtype := by
      simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hYX] using
        (Subgroup.map_mono (f := X.subtype) hYsub_le)
    calc
      Y ≤ (pPrimeCore p ↥X).map X.subtype := hY_le
      _ = piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) X := by
        symm
        exact piCoreIn_singleton_compl_eq_pPrimeCore_map (p := p) X
  have hright :
      piCoreIn (subgroupPrimeSet A)ᶜ X ≤
        section7Generated X A (subgroupPrimeSet A)ᶜ := by
    exact le_section7Generated_of_mem (piCoreIn_mem_section7HFamily_of_le_normalizer
      (G := G) (π := (subgroupPrimeSet A)ᶜ)
      (H := X) (P := A) (hAX.trans Subgroup.le_normalizer))
  have hleft :
      section7Generated X A (subgroupPrimeSet A)ᶜ ≤
        piCoreIn (subgroupPrimeSet A)ᶜ X := by
    simpa [hAπ] using hleft_singleton
  exact le_antisymm hleft hright

set_option maxHeartbeats 1000000 in
private theorem CFSG.proposition_7_5_case_scn
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G)
    {A : Subgroup G} (hAp : IsPGroup p A) [IsMulCommutative A]
    (hAscn : A ∈ scnPrimeSubgroups 2 p G) :
    Hypothesis7_1 A := by
  classical
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  have hG_nontrivial : Nontrivial G := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    let : Subsingleton G := hsub
    have hp_one : p ∣ 1 := by simpa using hpG
    exact (Fact.out : Nat.Prime p).not_dvd_one hp_one
  let : Nontrivial G := hG_nontrivial
  obtain ⟨P, hAP, hAscnP⟩ := hAscn
  let A0 : Subgroup P := A.subgroupOf (P : Subgroup G)
  have hA0' : A0 ∈ scnSubgroups 2 ↥(P : Subgroup G) := by
    simpa [A0] using hAscnP
  have hA0norm : A0.Normal := hA0'.1
  have hA0cent_eq : Subgroup.centralizer (A0 : Set P) = A0 := hA0'.2.1
  have hA0groupRank : 2 ≤ groupRank A0 := hA0'.2.2
  let : A0.Normal := hA0norm
  let : Fact (IsPGroup p P) := ⟨P.isPGroup'⟩
  have hA0_noncyc : ¬ IsCyclic A0 := by
    intro hcyc
    let : IsCyclic A0 := hcyc
    have hA0_le_one : groupRank A0 ≤ 1 := groupRank_le_one_of_isCyclic A0
    exact (by decide : ¬ 2 ≤ (1 : ℕ)) (le_trans hA0groupRank hA0_le_one)
  have hA_ne_bot : A ≠ ⊥ := by
    intro hAbot
    have hA0_bot : A0 = ⊥ := by
      ext x
      simp [A0, hAbot]
    apply hA0_noncyc
    rw [hA0_bot]
    infer_instance
  have hA_ne_top : A ≠ ⊤ := by
    intro hAtop
    have hcenter_top : Subgroup.center G = ⊤ := by
      apply top_unique
      intro g hg
      rw [Subgroup.mem_center_iff]
      intro x
      exact
        setLike_mul_comm (s := A)
          (by simp [hAtop])
          (by simp [hAtop])
    exact top_ne_bot (hcenter_top.symm.trans (center_eq_bot_of_min_ce (G := G)))
  have hAπ :
      subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes) :=
    subgroupPrimeSet_eq_singleton_of_isPGroup_nonbot (p := p) hAp hA_ne_bot
  have hCPA : subgroupCentralizerIn (P : Subgroup G) A ≤ A :=
    subgroupCentralizerIn_le_of_selfCentralizing_subgroupOf (p := p) hAP hA0cent_eq
  obtain ⟨B0, hB0norm, hB0_le_A0, hB0_card, hB0_elem⟩ :=
    proposition_4_6 (R := ↥P) (p := p) hpodd (S := A0) hA0_noncyc
  let : B0.Normal := hB0norm
  let : IsElementaryAbelian p B0 := hB0_elem
  have hB0_ne_bot : B0 ≠ ⊥ := by
    intro hB0bot
    have hp_dvd_card : p ∣ Nat.card B0 := by
      rw [hB0_card]
      exact dvd_pow_self p (by decide : 2 ≠ 0)
    have hp_dvd_one : p ∣ 1 := by
      simpa [hB0bot] using hp_dvd_card
    exact (Fact.out : Nat.Prime p).not_dvd_one hp_dvd_one
  have hB0_noncyc : ¬ IsCyclic B0 :=
    not_isCyclic_of_isElementaryAbelian_card_eq_p_sq (p := p) hB0_card
  let : Nontrivial B0 := B0.nontrivial_iff_ne_bot.mpr hB0_ne_bot
  obtain ⟨z0, hz0_ne, hz0_center⟩ :=
    exists_nontrivial_center_mem_normal (G := P) (p := p) (N := B0)
  let zP : P := z0
  let z : G := (zP : P)
  have hz_ne : z ≠ 1 := by
    intro hz_eq
    apply hz0_ne
    apply Subtype.ext
    simpa [z, zP] using hz_eq
  have hzpow : z ^ p = 1 := by
    have hz0pow : z0 ^ p = 1 := by
      exact
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p B0) z0
    have hzPpow : (zP : P) ^ p = 1 := by
      simpa [zP] using congrArg Subtype.val hz0pow
    simpa [z, zP] using congrArg Subtype.val hzPpow
  have hzA : z ∈ A := by
    exact hB0_le_A0 z0.2
  have hP_le_Cz : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommP : (⟨x, hx⟩ : P) * z0 = z0 * ⟨x, hx⟩ :=
      (Subgroup.mem_center_iff.mp hz0_center) ⟨x, hx⟩
    simpa [z, zP] using congrArg Subtype.val hcommP
  let B : Subgroup G := B0.map (P : Subgroup G).subtype
  have hB_le_A : B ≤ A := by
    rintro _ ⟨b0, hb0, rfl⟩
    exact hB0_le_A0 hb0
  have hB_card : Nat.card B = p ^ 2 := by
    calc
      Nat.card B = Nat.card (B0.map (P : Subgroup G).subtype) := by rfl
      _ = Nat.card B0 := by
        exact
          Subgroup.card_map_of_injective
            (K := B0) (f := (P : Subgroup G).subtype) (P : Subgroup G).subtype_injective
      _ = p ^ 2 := hB0_card
  have hB_elem : IsElementaryAbelian p B := by
    let : IsElementaryAbelian p B0 := hB0_elem
    simpa [B] using IsElementaryAbelian.map_subtype (p := p) (K := (P : Subgroup G)) (H := B0)
  let : IsElementaryAbelian p B := hB_elem
  have hB_noncyc : ¬ IsCyclic B :=
    not_isCyclic_of_isElementaryAbelian_card_eq_p_sq (p := p) hB_card
  refine ⟨hA_ne_bot, hA_ne_top, ?_⟩
  intro X hAX hX_ne_top
  have : Group.IsSolvable X := solvable_of_proper_subgroup (G := G) hX_ne_top
  have hXodd : Odd (Nat.card X) := odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card X)
  apply le_antisymm
  · simpa [hAπ] using (show
        section7Generated X A (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) ≤
          piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) X by
        refine sSup_le ?_
        intro Y hY
        rcases hY with ⟨hYX, hYπ, hAYnorm⟩
        have hYπ_singleton : IsPiSubgroup (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) Y := by
          simpa [hAπ] using hYπ
        have hYcop : Nat.Coprime p (Nat.card Y) :=
          coprime_card_of_isPiSubgroup_singleton_compl (p := p) hYπ_singleton
        have hcentralizer_case :
            ∀ {b0 : B0} (hb0_ne : b0 ≠ 1) {T : Subgroup G},
              T ≤ Subgroup.centralizer ({((b0 : P) : G)} : Set G) →
              Nat.Coprime p (Nat.card T) →
              A ≤ Subgroup.normalizer (T : Set G) →
              T ≤
                (pPrimeCore p ↥(Subgroup.centralizer ({((b0 : P) : G)} : Set G))).map
                  (Subgroup.centralizer ({((b0 : P) : G)} : Set G)).subtype := by
          intro b0 hb0_ne T hTXb hTcop hATnorm
          let bP : P := b0
          let b : G := (bP : P)
          let Xb : Subgroup G := Subgroup.centralizer ({b} : Set G)
          change T ≤ Xb at hTXb
          change T ≤ (pPrimeCore p ↥Xb).map Xb.subtype
          have hb_ne : b ≠ 1 := by
            intro hb_eq
            apply hb0_ne
            apply Subtype.ext
            simpa [b, bP] using hb_eq
          by_cases hP_le_Cb : (P : Subgroup G) ≤ Xb
          · simpa [Xb] using
              le_pPrimeCore_map_of_centralizer_singleton_contains_sylow
                (P := P) (A := A) (Y := T) hAP hA0norm hCPA b hb_ne hP_le_Cb hTXb hTcop hATnorm
          · have hXb_ne_top : Xb ≠ ⊤ := by
              simpa [Xb] using centralizer_singleton_ne_top_of_ne_one (G := G) (z := b) hb_ne
            have : Group.IsSolvable Xb := solvable_of_proper_subgroup (G := G) hXb_ne_top
            have hXbodd : Odd (Nat.card Xb) := by
              exact odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card Xb)
            have hzXb : z ∈ Xb := by
              rw [Subgroup.mem_centralizer_singleton_iff]
              have hcommB0 : (b0 : P) * z0 = z0 * (b0 : P) :=
                setLike_mul_comm (s := B0) b0.2 z0.2
              simpa [b, bP, z, zP] using (congrArg Subtype.val hcommB0).symm
            let P1 : Subgroup G := (P : Subgroup G) ⊓ Xb
            have hP1_le_P : P1 ≤ (P : Subgroup G) := inf_le_left
            have hP1_le_Xb : P1 ≤ Xb := inf_le_right
            let P1subP : Subgroup P := P1.subgroupOf (P : Subgroup G)
            have hP1subP_eq : P1subP = Subgroup.centralizer ({bP} : Set P) := by
              calc
                P1.subgroupOf (P : Subgroup G)
                    = Subgroup.centralizer (Subgroup.zpowers bP : Set P) := by
                        simpa [P1, Xb, b] using
                          subgroupOf_inf_centralizer_singleton_eq
                            (X := (P : Subgroup G)) (z := b) bP.2
                _ = Subgroup.centralizer ({bP} : Set P) := by
                      simpa using centralizer_zpowers_eq_centralizer_singleton (G := P) bP
            let φ : P →* MulAut B0 := MulAut.conjNormal (H := B0)
            have hφ_range_p : IsPGroup p φ.range := by
              have hPtop : IsPGroup p (⊤ : Subgroup P) := by
                simpa using P.isPGroup'.to_subgroup (⊤ : Subgroup P)
              rw [MonoidHom.range_eq_map]
              exact IsPGroup.map (p := p) (H := (⊤ : Subgroup P)) hPtop φ
            have hφcard : Nat.card φ.range ≤ p :=
              natCard_pSubgroup_mulAut_le_p_of_elementaryAbelian_card_le_p_sq_local
                (A := B0) (p := p) hφ_range_p (by exact le_of_eq hB0_card)
            have hker_le_P1subP : φ.ker ≤ P1subP := by
              rw [hP1subP_eq]
              intro x hx
              rw [Subgroup.mem_centralizer_singleton_iff]
              have hx_apply : (φ x) b0 = b0 := by simpa [MonoidHom.mem_ker] using congrArg (fun e : MulAut B0 => e b0) hx
              have hx_conj : (x : P) * b0 * (x : P)⁻¹ = b0 := by
                simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hx_apply
              have hx_comm : (bP : P) * x = x * bP := by
                have := congrArg (fun t : P => t * x) hx_conj
                simpa [bP, mul_assoc] using this.symm
              simpa [bP] using hx_comm.symm
            have hker_index_eq : φ.ker.index = Nat.card φ.range := by
              simpa [Subgroup.index_eq_card] using (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv)
            have hP1idx_dvd : P1subP.index ∣ Nat.card φ.range := by
              exact dvd_trans (Subgroup.index_dvd_of_le hker_le_P1subP) (dvd_of_eq hker_index_eq)
            have hP1idx_le_p : P1subP.index ≤ p := by
              exact le_trans (Nat.le_of_dvd Nat.card_pos hP1idx_dvd) hφcard
            have hP1subP_card : Nat.card P1subP = Nat.card P1 := by
              exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P1) (K := (P : Subgroup G)) hP1_le_P).toEquiv
            have hP_card_bound : Nat.card P ≤ p * Nat.card P1 := by
              calc
                Nat.card P = P1subP.index * Nat.card P1subP := by
                  simpa using (Subgroup.index_mul_card (H := P1subP)).symm
                _ ≤ p * Nat.card P1subP := Nat.mul_le_mul hP1idx_le_p le_rfl
                _ = p * Nat.card P1 := by rw [hP1subP_card]
            have hP1p : IsPGroup p P1 := P.isPGroup'.to_inf_left
            have hP1Xp : IsPGroup p (P1.subgroupOf Xb) := by
              exact hP1p.of_equiv (Subgroup.subgroupOfEquivOfLe (H := P1) (K := Xb) hP1_le_Xb).symm
            obtain ⟨P2, hP1XP2⟩ := IsPGroup.exists_le_sylow hP1Xp
            let P1P2 : Subgroup P2 := (P1.subgroupOf Xb).subgroupOf (P2 : Subgroup Xb)
            let P2G : Subgroup G := (P2 : Subgroup Xb).map Xb.subtype
            have hP2G_card : Nat.card P2G = Nat.card P2 := by
              simpa [P2G] using
                (Subgroup.card_map_of_injective (K := (P2 : Subgroup Xb)) (f := Xb.subtype) Xb.subtype_injective)
            have hP2Gp : IsPGroup p P2G := by
              exact IsPGroup.map (p := p) (H := (P2 : Subgroup Xb)) P2.isPGroup' Xb.subtype
            have hP2card_le_P : Nat.card P2 ≤ Nat.card P := by
              rw [← hP2G_card]
              exact card_le_card_sylow_of_isPGroup hP2Gp P
            have hP1P2_card : Nat.card P1P2 = Nat.card P1 := by
              calc
                Nat.card P1P2 = Nat.card (P1.subgroupOf Xb) := by
                  exact Nat.card_congr
                    (Subgroup.subgroupOfEquivOfLe (H := P1.subgroupOf Xb) (K := (P2 : Subgroup Xb)) hP1XP2).toEquiv
                _ = Nat.card P1 := by
                  exact Nat.card_congr
                    (Subgroup.subgroupOfEquivOfLe (H := P1) (K := Xb) hP1_le_Xb).toEquiv
            have hP1P2_idx_le_p : P1P2.index ≤ p := by
              have hmul_le : P1P2.index * Nat.card P1 ≤ p * Nat.card P1 := by
                calc
                  P1P2.index * Nat.card P1 = P1P2.index * Nat.card P1P2 := by rw [hP1P2_card]
                  _ = Nat.card P2 := by simpa using (Subgroup.index_mul_card (H := P1P2))
                  _ ≤ Nat.card P := hP2card_le_P
                  _ ≤ p * Nat.card P1 := hP_card_bound
              exact Nat.le_of_mul_le_mul_right hmul_le Nat.card_pos
            have hbXb : b ∈ Xb := by
              simp [Xb, Subgroup.mem_centralizer_singleton_iff]
            have hbP1 : b ∈ P1 := ⟨bP.2, hbXb⟩
            have hbP1X : (⟨b, hbXb⟩ : Xb) ∈ P1.subgroupOf Xb := by
              simpa [Subgroup.mem_subgroupOf] using hbP1
            have hbP2 : (⟨b, hbXb⟩ : Xb) ∈ (P2 : Subgroup Xb) := hP1XP2 hbP1X
            have hP2_ne_bot : (P2 : Subgroup Xb) ≠ ⊥ := by
              intro hP2bot
              have hb_one : (⟨b, hbXb⟩ : Xb) = 1 := by simpa [hP2bot] using hbP2
              exact hb_ne (congrArg Subtype.val hb_one)
            let : Nontrivial P2 := P2.nontrivial_iff_ne_bot.mpr hP2_ne_bot
            let : P1P2.Normal :=
              normal_of_index_le_prime_of_isPGroup (H := P1P2) P2.isPGroup' hP1P2_idx_le_p
            have hzP1 : z ∈ P1 := ⟨zP.2, hzXb⟩
            have hzP1X : (⟨z, hzXb⟩ : Xb) ∈ P1.subgroupOf Xb := by
              simpa [Subgroup.mem_subgroupOf] using hzP1
            have hzP2_mem : (⟨z, hzXb⟩ : Xb) ∈ (P2 : Subgroup Xb) := hP1XP2 hzP1X
            let zP2 : P2 := ⟨⟨z, hzXb⟩, hzP2_mem⟩
            have hzP1P2_mem : zP2 ∈ P1P2 := by
              change (⟨z, hzXb⟩ : Xb) ∈ P1.subgroupOf Xb
              exact hzP1X
            let zP1P2 : P1P2 := ⟨zP2, hzP1P2_mem⟩
            have hzP1P2_center : zP1P2 ∈ Subgroup.center P1P2 := by
              rw [Subgroup.mem_center_iff]
              intro x
              apply Subtype.ext
              apply Subtype.ext
              have hxP1X : (((x : P1P2) : P2) : Xb) ∈ P1.subgroupOf Xb := by
                exact x.2
              have hxP1 : ((((x : P1P2) : P2) : Xb) : G) ∈ P1 := by
                simpa [Subgroup.mem_subgroupOf] using hxP1X
              have hcommP :
                  ⟨(((x : P2) : Xb) : G), hP1_le_P hxP1⟩ * zP =
                    zP * ⟨(((x : P2) : Xb) : G), hP1_le_P hxP1⟩ :=
                (Subgroup.mem_center_iff.mp hz0_center) ⟨(((x : P2) : Xb) : G), hP1_le_P hxP1⟩
              have hcommXb :
                  ((x : P2) : Xb) * (⟨z, hzXb⟩ : Xb) =
                    (⟨z, hzXb⟩ : Xb) * ((x : P2) : Xb) := by
                apply Subtype.ext
                simpa [zP] using congrArg Subtype.val hcommP
              simpa [zP1P2, zP2] using hcommXb
            let ZP2 : Subgroup P2 := (Subgroup.center P1P2).map P1P2.subtype
            have hZP2_normal : ZP2.Normal := by
              let : (Subgroup.center P1P2).Characteristic := Subgroup.centerCharacteristic
              dsimp [ZP2]
              exact ConjAct.normal_of_characteristic_of_normal
            have hZP2_comm : IsMulCommutative ZP2 := by
              dsimp [ZP2]
              simpa using
                (Subgroup.map_isMulCommutative (f := P1P2.subtype) (H := Subgroup.center P1P2))
            let : ZP2.Normal := hZP2_normal
            let : IsMulCommutative ZP2 := hZP2_comm
            have hcenter_op :
                ZP2.map P2.toSubgroup.subtype ≤ Op_p'p p Xb :=
              theorem_6_1 (G := Xb) (p := p) hXbodd P2 ZP2
            have hzZP2 : zP2 ∈ ZP2 := by
              exact Subgroup.mem_map_of_mem P1P2.subtype hzP1P2_center
            have hzOp : (⟨z, hzXb⟩ : Xb) ∈ Op_p'p p Xb := by
              exact hcenter_op (Subgroup.mem_map_of_mem P2.toSubgroup.subtype hzZP2)
            have hZXb_le_Op : Subgroup.zpowers (⟨z, hzXb⟩ : Xb) ≤ Op_p'p p Xb :=
              Subgroup.zpowers_le.mpr hzOp
            have hfix_global :
                elementCentralizerIn T z ≤
                  (pPrimeCore p ↥(Subgroup.centralizer ({z} : Set G))).map
                    (Subgroup.centralizer ({z} : Set G)).subtype := by
              simpa [elementCentralizerIn] using
                le_pPrimeCore_map_of_inf_centralizer_singleton_contains_sylow
                  (P := P) (A := A) hAP hA0norm hCPA z hz_ne hzA hP_le_Cz hTcop hATnorm
            have hfix_le_Xb : elementCentralizerIn T z ≤ (pPrimeCore p ↥Xb).map Xb.subtype := by
              have hTz_le_Xb : elementCentralizerIn T z ≤ Xb := inf_le_left.trans hTXb
              exact
                transport_pPrimeCore_from_global_singleton_centralizer
                  (p := p) (X := Xb) (Y := elementCentralizerIn T z)
                  hzXb hzpow hTz_le_Xb hfix_global
            have hZnormT : Subgroup.zpowers z ≤ Subgroup.normalizer (T : Set G) := by
              exact (Subgroup.zpowers_le.mpr hzA).trans hATnorm
            have : Subgroup.Normalizes (Subgroup.zpowers z) T := ⟨hZnormT⟩
            have hfix_eq :
                fixedPointSubgroup (↥(Subgroup.zpowers z)) (↥T) =
                  (elementCentralizerIn T z).subgroupOf T := by
              calc
                fixedPointSubgroup (↥(Subgroup.zpowers z)) (↥T) =
                    (subgroupCentralizerIn T (Subgroup.zpowers z)).subgroupOf T := by
                      simpa using
                        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
                          T (Subgroup.zpowers z) hZnormT
                _ = (elementCentralizerIn T z).subgroupOf T := by
                      ext x
                      simp [subgroupCentralizerIn, elementCentralizerIn,
                        centralizer_zpowers_eq_centralizer_singleton]
            have hfix_map :
                (fixedPointSubgroup (↥(Subgroup.zpowers z)) (↥T)).map T.subtype =
                  elementCentralizerIn T z := by
              calc
                (fixedPointSubgroup (↥(Subgroup.zpowers z)) (↥T)).map T.subtype =
                    ((elementCentralizerIn T z).subgroupOf T).map T.subtype := by
                      rw [hfix_eq]
                _ = elementCentralizerIn T z ⊓ T := by
                      rw [Subgroup.subgroupOf_map_subtype]
                _ = elementCentralizerIn T z := inf_eq_left.2 inf_le_left
            have hcomm_map :
                (commutatorAction (A := ↥(Subgroup.zpowers z)) (G := ↥T)).map T.subtype =
                  ⁅T, Subgroup.zpowers z⁆ := by
              simpa using
                commutatorAction_subgroup_conj_map_eq_commutator T (Subgroup.zpowers z) hZnormT
            have hcomm_sub_le_Op :
                ⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆ ≤ Op_p'p p Xb := by
              exact
                (Subgroup.commutator_mono le_rfl hZXb_le_Op).trans
                  (Subgroup.commutator_le_right
                    (H₁ := T.subgroupOf Xb) (H₂ := Op_p'p p Xb))
            have hcomm_le_T : ⁅T, Subgroup.zpowers z⁆ ≤ T := by
              rw [← hcomm_map]
              rintro _ ⟨x, hx, rfl⟩
              exact x.2
            have hcomm_cop :
                Nat.Coprime p (Nat.card ((⁅T, Subgroup.zpowers z⁆ : Subgroup G))) := by
              exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hcomm_le_T) hTcop
            have hzp_sub_eq :
                (Subgroup.zpowers z).subgroupOf Xb =
                  Subgroup.zpowers (⟨z, hzXb⟩ : Xb) := by
              ext x
              constructor
              · intro hx
                have hxz : ((x : Xb) : G) ∈ Subgroup.zpowers z := by
                  simpa [Subgroup.mem_subgroupOf] using hx
                rcases Subgroup.mem_zpowers_iff.mp hxz with ⟨n, hn⟩
                exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
                  apply Subtype.ext
                  simpa using hn⟩
              · intro hx
                rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, hn⟩
                have hxz : ((x : Xb) : G) ∈ Subgroup.zpowers z := by
                  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
                simpa [Subgroup.mem_subgroupOf] using hxz
            have hcomm_eq_map :
                ⁅T, Subgroup.zpowers z⁆ =
                  (⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆).map Xb.subtype := by
              calc
                ⁅T, Subgroup.zpowers z⁆ =
                    (⁅T.subgroupOf Xb, (Subgroup.zpowers z).subgroupOf Xb⁆).map Xb.subtype := by
                      symm
                      exact
                        commutator_subgroupOf_map_eq
                          (S := Xb) (H := Subgroup.zpowers z) (R := T)
                          (Subgroup.zpowers_le.mpr hzXb) hTXb
                _ =
                    (⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆).map Xb.subtype := by
                      rw [hzp_sub_eq]
            have hcomm_sub_card :
                Nat.card
                    ((⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆).map Xb.subtype) =
                  Nat.card ((⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆ : Subgroup Xb)) := by
              simpa using
                (Subgroup.card_map_of_injective
                  (K := ⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆)
                  (f := Xb.subtype) Xb.subtype_injective)
            have hcomm_sub_cop :
                Nat.Coprime p
                  (Nat.card
                    ((⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆ : Subgroup Xb))) := by
              rw [← hcomm_sub_card, ← hcomm_eq_map]
              exact hcomm_cop
            have hcomm_sub_core :
                ⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆ ≤ pPrimeCore p Xb :=
              le_pPrimeCore_of_le_Op_p'p_of_coprime (G := Xb) (p := p) hcomm_sub_le_Op hcomm_sub_cop
            have hcomm_le_Xb : ⁅T, Subgroup.zpowers z⁆ ≤ (pPrimeCore p Xb).map Xb.subtype := by
              calc
                ⁅T, Subgroup.zpowers z⁆ =
                    (⁅T.subgroupOf Xb, Subgroup.zpowers (⟨z, hzXb⟩ : Xb)⁆).map Xb.subtype := hcomm_eq_map
                _ ≤ (pPrimeCore p Xb).map Xb.subtype := Subgroup.map_mono hcomm_sub_core
            have hTsolv : Group.IsSolvable T := by
              let e : T.subgroupOf Xb ≃* T := Subgroup.subgroupOfEquivOfLe (H := T) (K := Xb) hTXb
              exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
            have hzpow_cop : Nat.Coprime (Nat.card (Subgroup.zpowers z)) (Nat.card T) := by
              have hzpow_dvd : Nat.card (Subgroup.zpowers z) ∣ p := by
                simpa [Nat.card_zpowers] using orderOf_dvd_of_pow_eq_one hzpow
              exact Nat.Coprime.of_dvd_left hzpow_dvd hTcop
            have hsup :
                fixedPointSubgroup (↥(Subgroup.zpowers z)) (↥T) ⊔
                    commutatorAction (A := ↥(Subgroup.zpowers z)) (G := ↥T) =
                  ⊤ :=
              fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
                (G := ↥T) (A := ↥(Subgroup.zpowers z)) hTsolv hzpow_cop
            have htop_map_T : (⊤ : Subgroup T).map T.subtype = T := by
              simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := T))
            calc
              T = (⊤ : Subgroup T).map T.subtype := htop_map_T.symm
              _ =
                  (fixedPointSubgroup (↥(Subgroup.zpowers z)) (↥T) ⊔
                      commutatorAction (A := ↥(Subgroup.zpowers z)) (G := ↥T)).map T.subtype := by
                    simp [hsup]
              _ =
                  (fixedPointSubgroup (↥(Subgroup.zpowers z)) (↥T)).map T.subtype ⊔
                    (commutatorAction (A := ↥(Subgroup.zpowers z)) (G := ↥T)).map T.subtype := by
                    rw [Subgroup.map_sup]
              _ = elementCentralizerIn T z ⊔ ⁅T, Subgroup.zpowers z⁆ := by rw [hfix_map, hcomm_map]
              _ ≤ (pPrimeCore p Xb).map Xb.subtype := by
                    exact sup_le hfix_le_Xb hcomm_le_Xb
        have hBnormY : B ≤ Subgroup.normalizer (Y : Set G) := hB_le_A.trans hAYnorm
        let : CommGroup B := IsMulCommutative.instCommGroup
        have : Subgroup.Normalizes B Y := ⟨hBnormY⟩
        let : Fact (IsPGroup p B) := ⟨IsElementaryAbelian.isPGroup p B⟩
        have hBfix_top :
            (⨆ (b : B) (_ : b ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers b)) ↥Y) = ⊤ := by
          simpa using proposition_1_16_a (G := ↥Y) (A := B) p hYcop hB_noncyc
        have hfixed_map_le :
            ∀ b : B, ∀ hb_ne : b ≠ 1,
              (fixedPointSubgroup (↥(Subgroup.zpowers b)) ↥Y).map Y.subtype ≤
                (pPrimeCore p ↥X).map X.subtype := by
          intro b hb_ne
          have hbA : (b : G) ∈ A := hB_le_A b.2
          have hbX : (b : G) ∈ X := hAX hbA
          have hbpow : (b : G) ^ p = 1 := by
            have hbpowB : b ^ p = 1 := by
              exact
                Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                  (IsElementaryAbelian.exponent_dvd_p p B) b
            simpa using congrArg Subtype.val hbpowB
          have hfix_eq :
              fixedPointSubgroup (↥(Subgroup.zpowers b)) (↥Y) =
                (elementCentralizerIn Y (b : G)).subgroupOf Y := by
            simpa using
              fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
                Y B hBnormY b
          have hfix_map :
              (fixedPointSubgroup (↥(Subgroup.zpowers b)) (↥Y)).map Y.subtype =
                elementCentralizerIn Y (b : G) := by
            calc
              (fixedPointSubgroup (↥(Subgroup.zpowers b)) (↥Y)).map Y.subtype =
                  ((elementCentralizerIn Y (b : G)).subgroupOf Y).map Y.subtype := by
                    rw [hfix_eq]
              _ = elementCentralizerIn Y (b : G) ⊓ Y := by
                    rw [Subgroup.subgroupOf_map_subtype]
              _ = elementCentralizerIn Y (b : G) := inf_eq_left.2 inf_le_left
          have hfix_le_X : elementCentralizerIn Y (b : G) ≤ X := inf_le_left.trans hYX
          rcases Subgroup.mem_map.mp b.2 with ⟨b0, hb0, hb_eq⟩
          let b0B : B0 := ⟨b0, hb0⟩
          have hb0_eq_b : ((b0B : P) : G) = (b : G) := by
            simpa [b0B] using hb_eq
          have hb0B_ne : b0B ≠ 1 := by
            intro hb0B_eq
            have hb0B_eq_one : ((b0B : P) : G) = 1 := by
              exact congrArg Subtype.val (congrArg Subtype.val hb0B_eq)
            apply hb_ne
            apply Subtype.ext
            exact hb0_eq_b.symm.trans hb0B_eq_one
          have hfix_le_Cb : elementCentralizerIn Y (b : G) ≤ Subgroup.centralizer ({(b : G)} : Set G) :=
            inf_le_right
          have hfix_cop : Nat.Coprime p (Nat.card (elementCentralizerIn Y (b : G))) := by
            exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hYcop
          have hA_normCb : A ≤ Subgroup.normalizer (Subgroup.centralizer ({(b : G)} : Set G) : Set G) := by
            have hA_le_Cb : A ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
              intro a ha
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact setLike_mul_comm (s := A) ha hbA
            exact hA_le_Cb.trans Subgroup.le_normalizer
          have hfix_norm : A ≤ Subgroup.normalizer (elementCentralizerIn Y (b : G) : Set G) := by
            exact
              (le_inf hAYnorm hA_normCb).trans <| by
                simpa [elementCentralizerIn] using
                  (Subgroup.inf_normalizer_le_normalizer_inf
                    (H := Y) (K := Subgroup.centralizer ({(b : G)} : Set G)))
          have hfix_le_Cb0 :
              elementCentralizerIn Y (b : G) ≤
                Subgroup.centralizer ({((b0B : P) : G)} : Set G) := by
            simpa [hb0_eq_b] using hfix_le_Cb
          have hfix_global0 :
              elementCentralizerIn Y (b : G) ≤
                (pPrimeCore p ↥(Subgroup.centralizer ({((b0B : P) : G)} : Set G))).map
                  (Subgroup.centralizer ({((b0B : P) : G)} : Set G)).subtype :=
            hcentralizer_case (b0 := b0B) hb0B_ne
              (T := elementCentralizerIn Y (b : G)) hfix_le_Cb0 hfix_cop hfix_norm
          have hb0B_X : ((b0B : P) : G) ∈ X := by
            simpa [hb0_eq_b] using hbX
          have hb0B_pow : ((b0B : P) : G) ^ p = 1 := by
            simpa [hb0_eq_b] using hbpow
          calc
            (fixedPointSubgroup (↥(Subgroup.zpowers b)) (↥Y)).map Y.subtype =
                elementCentralizerIn Y (b : G) := hfix_map
            _ ≤ (pPrimeCore p ↥X).map X.subtype := by
                  exact
                    transport_pPrimeCore_from_global_singleton_centralizer
                      (p := p) (X := X) (Y := elementCentralizerIn Y (b : G))
                      hb0B_X hb0B_pow hfix_le_X hfix_global0
        have htop_map_Y : (⊤ : Subgroup Y).map Y.subtype = Y := by
          simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := Y))
        calc
          Y = (⊤ : Subgroup Y).map Y.subtype := htop_map_Y.symm
          _ = (⨆ (b : B) (_ : b ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers b)) ↥Y).map Y.subtype := by
                simp [hBfix_top]
          _ ≤ (pPrimeCore p ↥X).map X.subtype := by
                rw [Subgroup.map_iSup]
                refine iSup_le ?_
                intro b
                rw [Subgroup.map_iSup]
                refine iSup_le ?_
                intro hb_ne
                exact hfixed_map_le b hb_ne
          _ = piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) X := by
                exact (piCoreIn_singleton_compl_eq_pPrimeCore_map (p := p) X).symm)
  · exact le_section7Generated_of_mem (piCoreIn_mem_section7HFamily_of_le_normalizer
      (G := G) (π := (subgroupPrimeSet A)ᶜ)
      (H := X) (P := A) (hAX.trans Subgroup.le_normalizer))

public theorem CFSG.proposition_7_5_core
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G)
    {A : Subgroup G} (hAp : IsPGroup p A) [IsMulCommutative A]
    (hAcase :
      ((A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1} ∧
        ∀ X : Subgroup G, X ≠ ⊤ → HasPLengthOne (p := p) ↥X) ∨
      A ∈ scnPrimeSubgroups 2 p G) :
    Hypothesis7_1 A := by
  rcases hAcase with ⟨hAeq, hplen⟩ | hAscn
  · exact proposition_7_5_case_eq (G := G) (p := p) hpG hAp hAeq hplen
  · exact proposition_7_5_case_scn (G := G) (p := p) hpG hAp hAscn

end

/-! # Proposition 7.5 from BG Section 7 -/

open scoped Pointwise

section

variable {G : Type*} [Group G] [Finite G]

public theorem CFSG.proposition_7_5
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G)
    {A : Subgroup G} (hAp : IsPGroup p A) [IsMulCommutative A]
    (hAcase :
      ((A : Set G) = {x : G | x ∈ Subgroup.centralizer (A : Set G) ∧ x ^ p = 1} ∧
        ∀ X : Subgroup G, X ≠ ⊤ → HasPLengthOne (p := p) ↥X) ∨
      A ∈ scnPrimeSubgroups 2 p G) :
    Hypothesis7_1 A := by
  simpa using
    (proposition_7_5_core (G := G) (p := p) hpG hAp hAcase)

end
