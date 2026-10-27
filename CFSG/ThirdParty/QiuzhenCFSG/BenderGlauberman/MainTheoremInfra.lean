module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Hyp12OfHyp11
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Lemma25
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Lemma34
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Theorem43

namespace CFSG
end CFSG
open CFSG

/-!
# Shared infrastructure for the main Bender--Glauberman theorems

This module contains the small structural and Section-4 interfaces used by
both Theorem A and Theorem C.  Keeping these facts below the theorem modules
avoids importing one main theorem merely to recover a reusable index or
component lemma.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

variable {G : Type u} [Group G] [Finite G]

section Structural

/-- The multiplication bijection `U × S0 ≃ H0`. -/
public noncomputable def main_H0_equiv_U_prod_S0 (c : Hyp11 G) (h12 : Hyp12 c) :
    ↥c.U × ↥(c.S0 : Subgroup G) ≃ ↥c.H0 := by
  classical
  refine Equiv.ofBijective (fun p : ↥c.U × ↥(c.S0 : Subgroup G) =>
    ⟨(p.1 : G) * (p.2 : G),
      c.H0.mul_mem ((h12.U_normal_in_H0).1 p.1.2) (S0_le_H0 c p.2.2)⟩) ⟨?_, ?_⟩
  · rintro ⟨u1, r1⟩ ⟨u2, r2⟩ h
    have hval : (u1 : G) * (r1 : G) = (u2 : G) * (r2 : G) :=
      congrArg Subtype.val h
    have hcross : (u2 : G)⁻¹ * (u1 : G) = (r2 : G) * (r1 : G)⁻¹ := by
      calc
        (u2 : G)⁻¹ * (u1 : G) =
            (u2 : G)⁻¹ * ((u1 : G) * (r1 : G)) * (r1 : G)⁻¹ := by group
        _ = (u2 : G)⁻¹ * ((u2 : G) * (r2 : G)) * (r1 : G)⁻¹ := by rw [hval]
        _ = (r2 : G) * (r1 : G)⁻¹ := by group
    have hcrossU : (u2 : G)⁻¹ * (u1 : G) ∈ c.U :=
      c.U.mul_mem (c.U.inv_mem u2.2) u1.2
    have hcrossS0 : (u2 : G)⁻¹ * (u1 : G) ∈ (c.S0 : Subgroup G) := by
      rw [hcross]
      exact c.S0.mul_mem r2.2 (c.S0.inv_mem r1.2)
    have hcrossOne : (u2 : G)⁻¹ * (u1 : G) = 1 :=
      U_inter_S0_eq_bot c hcrossU hcrossS0
    have huval : (u1 : G) = (u2 : G) := by
      calc
        (u1 : G) = (u2 : G) * ((u2 : G)⁻¹ * (u1 : G)) := by group
        _ = (u2 : G) := by rw [hcrossOne]; simp
    have hrval : (r1 : G) = (r2 : G) := by
      calc
        (r1 : G) = (u1 : G)⁻¹ * ((u1 : G) * (r1 : G)) := by group
        _ = (u1 : G)⁻¹ * ((u2 : G) * (r2 : G)) := by rw [hval]
        _ = (r2 : G) := by rw [huval]; group
    congr
    · exact Subtype.ext huval
    · exact Subtype.ext hrval
  · intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
    refine ⟨(u, r), ?_⟩
    exact Subtype.ext hx.symm

/-- The index of `U` in `H0` is the order of `S0`. -/
public lemma main_H0_index_eq_S0_card (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (↥(c.S0 : Subgroup G)) := by
  have hUcard : Nat.card ↥(c.U.subgroupOf c.H0) = Nat.card ↥c.U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := c.U) (K := c.H0)
      (h12.U_normal_in_H0).1).toEquiv
  have hH0card : Nat.card (↥c.H0) =
      Nat.card ↥c.U * Nat.card (↥(c.S0 : Subgroup G)) := by
    simpa [Nat.card_prod] using
      (Nat.card_congr (main_H0_equiv_U_prod_S0 c h12).symm)
  have hindex := Subgroup.index_mul_card (c.U.subgroupOf c.H0)
  have hEq : (c.U.subgroupOf c.H0).index * Nat.card ↥c.U =
      Nat.card (↥(c.S0 : Subgroup G)) * Nat.card ↥c.U := by
    calc
      (c.U.subgroupOf c.H0).index * Nat.card ↥c.U =
          (c.U.subgroupOf c.H0).index * Nat.card ↥(c.U.subgroupOf c.H0) := by rw [hUcard]
      _ = Nat.card (↥c.H0) := hindex
      _ = Nat.card ↥c.U * Nat.card (↥(c.S0 : Subgroup G)) := hH0card
      _ = Nat.card (↥(c.S0 : Subgroup G)) * Nat.card ↥c.U := by ac_rfl
  exact Nat.mul_right_cancel (Nat.card_pos (α := ↥c.U)) hEq

/-- In the non-Section-4 case, `[H0 : U]` is at least four. -/
public lemma main_H0_index_ge_four_of_S_ne_four (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Nat.card (↥(c.S : Subgroup G)) ≠ 4) :
    4 ≤ (c.U.subgroupOf c.H0).index := by
  have hU := main_H0_index_eq_S0_card c h12
  have hS0 := S0_nat_card c
  have hS := S_nat_card c
  have hm2 : 2 ≤ c.m := by
    by_contra hm
    have hmle : c.m ≤ 1 := by omega
    have hpow : 2 ^ c.m ≤ 2 := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hmle
    have hcard : Nat.card (↥(c.S : Subgroup G)) ≤ 4 := by
      rw [hS]
      nlinarith
    have hge : 4 ≤ Nat.card (↥(c.S : Subgroup G)) := by
      have hpow1 : 2 ≤ 2 ^ c.m := by
        have h1 : 2 ^ 1 ≤ 2 ^ c.m :=
          pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) c.one_le_m
        simpa using h1
      rw [hS]
      nlinarith
    exact hS4 (le_antisymm hcard hge)
  have h4 : 4 ≤ 2 ^ c.m := by
    have hpow : 2 ^ 2 ≤ 2 ^ c.m :=
      pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hm2
    norm_num at hpow ⊢
    exact hpow
  rw [hU, hS0]
  exact h4

/-- There is a Lambda character whose square is nontrivial once the Lambda
group has cardinality at least four. -/
public lemma main_exists_lambda_sq_ne_one (c : Hyp11 G) (h12 : Hyp12 c)
    (hm : 4 ≤ (c.U.subgroupOf c.H0).index) :
    ∃ l : LambdaHom c.H0 c.U, l ^ 2 ≠ 1 := by
  classical
  have hcard : 4 ≤ Fintype.card (LambdaHom c.H0 c.U) := by
    rw [← Nat.card_eq_fintype_card, lambda_card_eq_index c h12]
    exact hm
  by_contra hnone
  push Not at hnone
  have hall : ∀ l : LambdaHom c.H0 c.U, l ^ 2 = 1 := hnone
  have hsub : (Finset.univ : Finset (LambdaHom c.H0 c.U)) ⊆
      {1, lambdaTwo c h12} := by
    intro l _hl
    simpa using lambda_eq_one_or_two_of_sq_one c h12 l (hall l)
  have hle : Fintype.card (LambdaHom c.H0 c.U) ≤ 2 := by
    rw [← Finset.card_univ]
    calc
      (Finset.univ : Finset (LambdaHom c.H0 c.U)).card ≤
          ({1, lambdaTwo c h12} : Finset (LambdaHom c.H0 c.U)).card :=
        Finset.card_le_card hsub
      _ = 2 := Finset.card_pair (lambdaTwo_ne_one c h12).symm
  omega

/-- A nontrivial-square Lambda character is not fixed by `s`. -/
public lemma main_lambda_not_fixed_by_s (c : Hyp11 G) (h12 : Hyp12 c)
    {l : LambdaHom c.H0 c.U} (hl : l ^ 2 ≠ 1) :
    conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) ≠ LambdaChar l.1 := by
  intro hfix
  rcases (lambda_fixed_by_s_iff c h12 l).1 hfix with h1 | h2
  · exact hl (by rw [h1]; simp)
  · exact hl (by rw [h2]; exact lambdaTwo_sq_eq_one c h12)

/-- The Lambda orbit of a linear character has full cardinality. -/
public lemma main_linear_orbit_card (c : Hyp11 G) (h12 : Hyp12 c)
    {κ : ClassFunction (↥c.H0)} (hκ : IsLinearCharacter κ) :
    (orbit c.H0 c.U κ).card = (c.U.subgroupOf c.H0).index := by
  classical
  have hstab : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
      LambdaChar l.1 * κ = κ)).card = 1 := by
    have hle : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
        LambdaChar l.1 * κ = κ)) ≤ ({1} : Finset (LambdaHom c.H0 c.U)) := by
      intro l hl
      simp
      apply Subtype.ext
      apply MonoidHom.ext
      intro x
      apply Units.ext
      have hx := congrArg (fun f : ClassFunction (↥c.H0) => f x)
        (Finset.mem_filter.mp hl).2
      have hκnz : κ x ≠ 0 := linearChar_ne_zero hκ x
      apply mul_right_cancel₀ hκnz
      simpa [LambdaChar] using hx
    have hge : 1 ≤ (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
        LambdaChar l.1 * κ = κ)).card := by
      exact Finset.card_pos.mpr ⟨1, by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ 1, ?_⟩
        ext x
        simp [LambdaChar]⟩
    have hlecard : (Finset.univ.filter (fun l : LambdaHom c.H0 c.U =>
        LambdaChar l.1 * κ = κ)).card ≤ 1 := by
      simpa using Finset.card_le_card hle
    omega
  have h := orbit_card_mul_stab c.H0 c.U κ
  rw [hstab, mul_one] at h
  rw [← Nat.card_eq_fintype_card, lambda_card_eq_index c h12] at h
  exact h

/-- `S'` centralizes `U` in the Section-4 case, since it is trivial. -/
public lemma main_section3Hyp_of_section4 (c : Hyp11 G) (hS4 : Section4Hyp c) :
    Section3Hyp c := by
  rw [Section3Hyp, SPrime_eq_bot_of_section4 c hS4]
  intro x hx y hy
  have hx1 : x = 1 := by simpa using hx
  subst x
  simp

/-- The exceptional index-four Lambda case is also in Section 3: here
`|S| = 8`, so `S'` has order two and is generated by the central involution
`t`, which centralizes `U`. -/
public lemma main_section3Hyp_of_H0_index_four (c : Hyp11 G) (h12 : Hyp12 c)
    (hindex : (c.U.subgroupOf c.H0).index = 4) : Section3Hyp c := by
  have hS0card : Nat.card (↥(c.S0 : Subgroup G)) = 4 := by
    rw [← main_H0_index_eq_S0_card c h12, hindex]
  have hSPcard : Nat.card (SPrime c : Subgroup G) = 2 := by
    have hEqCard : Nat.card ↥((SPrime c).subgroupOf (c.S0 : Subgroup G)) =
        Nat.card (SPrime c : Subgroup G) := by
      exact Nat.card_congr {
        toFun := fun x : ↥((SPrime c).subgroupOf (c.S0 : Subgroup G)) =>
          ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun y : ↥(SPrime c : Subgroup G) =>
          ⟨⟨(y : G), SPrime_le_S0 c y.2⟩,
            Subgroup.mem_subgroupOf.mpr y.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro y; apply Subtype.ext; rfl }
    have hcm := Subgroup.card_mul_index ((SPrime c).subgroupOf (c.S0 : Subgroup G))
    rw [hEqCard, SPrime_index c, hS0card] at hcm
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) hcm
  rw [Section3Hyp]
  intro x hx u hu
  have hxsq : (⟨x, hx⟩ : ↥(SPrime c : Subgroup G)) ^ 2 = 1 :=
    sq_eq_one_of_card_two hSPcard _
  have hxsqG : x ^ 2 = 1 := by
    simpa [Subgroup.coe_pow] using congrArg Subtype.val hxsq
  have hxS0 : x ∈ (c.S0 : Subgroup G) := SPrime_le_S0 c hx
  rcases (S0_sq_eq_one_iff c (x := ⟨x, hxS0⟩)).1 (by
      simpa [Subgroup.coe_pow] using hxsq) with h1 | ht
  · have : x = 1 := by simpa using congrArg Subtype.val h1
    subst x
    simp
  · have : x = c.t := by simpa using congrArg Subtype.val ht
    subst x
    have huH : u ∈ c.H := by
      simpa [Hyp11.U] using (Subgroup.map_subtype_le (pPrimeCore 2 c.H) hu)
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff] at huH
    exact (huH c.t (by simp)).symm

/-- In the Section-4 case the generator `t1 * t2` of `S0` is its unique
nontrivial element `t`. -/
public lemma main_t1_mul_t2_eq_t_of_section4 (c : Hyp11 G)
    (hS4 : Section4Hyp c) : c.t1 * c.t2 = c.t := by
  have hS0card : Nat.card (↥(c.S0 : Subgroup G)) = 2 :=
    S0_card_eq_two_of_section4 c hS4
  have hmem : c.t1 * c.t2 ∈ c.S0 := by
    rw [c.S0_eq_zpowers]
    exact Subgroup.mem_zpowers (c.t1 * c.t2)
  let x : ↥(c.S0 : Subgroup G) := ⟨c.t1 * c.t2, hmem⟩
  have hx2 : x ^ 2 = 1 := by
    apply (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).mp
    have hdvd : orderOf x ∣ Fintype.card ↥(c.S0 : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S0 : Subgroup G)) (x := x)
    rwa [← Nat.card_eq_fintype_card, hS0card] at hdvd
  have hxne1 : x ≠ 1 := by
    intro hx1
    have hprod : c.t1 * c.t2 = 1 := by
      change (x : ↥(c.S0 : Subgroup G)) = (1 : ↥(c.S0 : Subgroup G)) at hx1
      exact congrArg Subtype.val hx1
    have hS0bot : c.S0 = ⊥ := by
      rw [c.S0_eq_zpowers, hprod]
      simp
    have hcardBot : Nat.card (↥(⊥ : Subgroup G)) = 1 := by simp
    rw [hS0bot, hcardBot] at hS0card
    norm_num at hS0card
  rcases (S0_sq_eq_one_iff c (x := x)).mp hx2 with hx1 | hxt
  · exact False.elim (hxne1 hx1)
  · exact congrArg Subtype.val hxt

/-- In Section 4 the central involution `t` is a commutator: a conjugator
sending `t2` to `t1` has commutator `t1 * t2 = t` with `t2`. -/
public lemma main_t_mem_commutator_of_section4 (c : Hyp11 G)
    (hS4 : Section4Hyp c) : c.t ∈ commutator G := by
  rcases c.one_involution_class c.t2 c.t1 c.t2_involution c.t1_involution with
    ⟨g, hg⟩
  have ht2inv : c.t2⁻¹ = c.t2 := by
    exact inv_eq_of_mul_eq_one_right (by
      simpa [pow_two] using c.t2_involution.2)
  have hcomm : ⁅g, c.t2⁆ = c.t := by
    rw [commutatorElement_def, hg, ht2inv,
      main_t1_mul_t2_eq_t_of_section4 c hS4]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
    (Subgroup.mem_top c.t2)

/-- The two reflection-centralizer indices agree in Section 4.  Inside
`H = C_G(t)`, centralizing `t1` is equivalent to centralizing `t2` because
`t = t1 * t2`. -/
public lemma main_k1_eq_k2_of_section4 (c : Hyp11 G)
    (hS4 : Section4Hyp c) : c.k1 = c.k2 := by
  have htprod : c.t1 * c.t2 = c.t :=
    main_t1_mul_t2_eq_t_of_section4 c hS4
  have ht1sq : c.t1 * c.t1 = 1 := by
    simpa [pow_two] using c.t1_involution.2
  have ht2sq : c.t2 * c.t2 = 1 := by
    simpa [pow_two] using c.t2_involution.2
  have ht2eq : c.t2 = c.t1 * c.t := by
    calc
      c.t2 = c.t1 * (c.t1 * c.t2) := by rw [← mul_assoc, ht1sq, one_mul]
      _ = c.t1 * c.t := by rw [htprod]
  have ht1eq : c.t1 = c.t * c.t2 := by
    calc
      c.t1 = (c.t1 * c.t2) * c.t2 := by rw [mul_assoc, ht2sq, mul_one]
      _ = c.t * c.t2 := by rw [htprod]
  have hcent : centralizerIn c.H c.t1 = centralizerIn c.H c.t2 := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxH, hxC1⟩
      refine Subgroup.mem_inf.mpr ⟨hxH, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hxC1 ⊢
      have hxt : c.t * x = x * c.t := by
        rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff] at hxH
        exact hxH c.t (by simp)
      have hxt1 : c.t1 * x = x * c.t1 := hxC1 c.t1 (by simp)
      intro y hy
      have hy2 : y = c.t2 := by simpa using hy
      subst y
      rw [ht2eq]
      calc
        (c.t1 * c.t) * x = c.t1 * (c.t * x) := by group
        _ = c.t1 * (x * c.t) := by rw [hxt]
        _ = (c.t1 * x) * c.t := by group
        _ = (x * c.t1) * c.t := by rw [hxt1]
        _ = x * (c.t1 * c.t) := by group
    · intro hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxH, hxC2⟩
      refine Subgroup.mem_inf.mpr ⟨hxH, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hxC2 ⊢
      have hxt : c.t * x = x * c.t := by
        rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff] at hxH
        exact hxH c.t (by simp)
      have hxt2 : c.t2 * x = x * c.t2 := hxC2 c.t2 (by simp)
      intro y hy
      have hy1 : y = c.t1 := by simpa using hy
      subst y
      rw [ht1eq]
      calc
        (c.t * c.t2) * x = c.t * (c.t2 * x) := by group
        _ = c.t * (x * c.t2) := by rw [hxt2]
        _ = (c.t * x) * c.t2 := by group
        _ = (x * c.t) * c.t2 := by rw [hxt]
        _ = x * (c.t * c.t2) := by group
  unfold Hyp11.k1 Hyp11.k2
  rw [hcent]

end Structural

section PrincipalSection4Component

/-- The principal irreducible character of `H0`. -/
public noncomputable def main_principalIrr (c : Hyp11 G) : Irr (↥c.H0) :=
  ⟨(1 : ClassFunction (↥c.H0)), isIrreducibleCharacter_one (↥c.H0)⟩

private lemma main_B_coprime_two (c : Hyp11 G) :
    Nat.Coprime 2 (Nat.card (↥c.B)) := by
  have hEq : Nat.card (↥c.B) =
      Nat.card (↥(fixedSubgroup (c.S : Subgroup G) c.U)) :=
    Nat.card_congr (B_fixedSubgroup_equiv c)
  have hdiv : Nat.card (↥(fixedSubgroup (c.S : Subgroup G) c.U)) ∣
      Nat.card (↥c.U) :=
    Subgroup.card_subgroup_dvd_card (fixedSubgroup (c.S : Subgroup G) c.U)
  rw [hEq]
  exact Nat.Coprime.of_dvd_right hdiv (U_coprime_two c)

private lemma main_nuHat_principal_eq_principal (c : Hyp11 G)
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c) :
    nuHat c h12 (main_principalIrr c) =
      ⟨(1 : ClassFunction (↥c.B)), isIrreducibleCharacter_one (↥c.B)⟩ := by
  let oneIrr : Irr (↥c.H0) := main_principalIrr c
  let oneB : Irr (↥c.B) :=
    ⟨(1 : ClassFunction (↥c.B)), isIrreducibleCharacter_one (↥c.B)⟩
  have hones : conjChar c.H0 (s_normalizes_H0 c h12) oneIrr.1 = oneIrr.1 := by
    ext x
    simp [oneIrr, main_principalIrr, conjChar]
  have honet : oneIrr.1 (tH0 c) = oneIrr.1 1 := by
    simp [oneIrr, main_principalIrr]
  have hcong : ∀ b : ↥c.B,
      CongruentModTwo ((nuHat c h12 oneIrr).1 b) (oneB.1 b) := by
    intro b
    have h := nuHat_congruence c h12 hSC hS4 hones honet b
      (U_le_H0 c (mem_U_of_mem_B_s4 c b.2))
    simpa [oneIrr, oneB, main_principalIrr] using h
  simpa [oneIrr, oneB] using
    eq_of_congruent_irr (main_B_coprime_two c) hcong

private noncomputable def main_deltaComponent (c : Hyp11 G) (h12 : Hyp12 c)
    (delta0 : ClassFunction G) : Set (ClassFunction G) :=
  {delta | delta ∈ Delta c h12 ∧
    Relation.ReflTransGen (deltaAdjacent c h12) delta0 delta}

private lemma main_deltaAdjacent_symm (c : Hyp11 G) (h12 : Hyp12 c)
    {delta epsilon : ClassFunction G} (h : deltaAdjacent c h12 delta epsilon) :
    deltaAdjacent c h12 epsilon delta := by
  unfold deltaAdjacent at h ⊢
  rcases h with ⟨hdelta, hepsilon, hne, hdis⟩
  exact ⟨hepsilon, hdelta, hne.symm, by
    intro h'
    apply hdis
    unfold Theory.Character.Disjoint at h' ⊢
    intro chi hchi hchidelta
    by_contra hchiepsilon
    exact hchidelta (h' chi hchi hchiepsilon)⟩

private lemma main_reflTransGen_symm {alpha : Type*} {r : alpha → alpha → Prop}
    (hr : ∀ {a b}, r a b → r b a) {a b : alpha}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h1 h2 ih =>
      exact (Relation.ReflTransGen.single (hr h2)).trans ih

private lemma main_deltaComponent_isConnected (c : Hyp11 G) (h12 : Hyp12 c)
    {delta0 : ClassFunction G} (hdelta0 : delta0 ∈ Delta c h12) :
    IsConnectedComponent c h12 (main_deltaComponent c h12 delta0) := by
  let Delta0 := main_deltaComponent c h12 delta0
  have hmem0 : delta0 ∈ Delta0 := ⟨hdelta0, Relation.ReflTransGen.refl⟩
  have hsub : Delta0 ⊆ Delta c h12 := fun _ hdelta => hdelta.1
  have hpath (delta : ClassFunction G) (hdelta : delta ∈ Delta0) :
      Relation.ReflTransGen (deltaAdjacent c h12) delta0 delta := hdelta.2
  unfold IsConnectedComponent
  refine ⟨⟨delta0, hmem0⟩, hsub, ?_, ?_⟩
  · intro delta delta' hdelta hdelta'
    exact (main_reflTransGen_symm (fun {a b} h =>
      main_deltaAdjacent_symm c h12 h) (hpath delta hdelta)).trans
        (hpath delta' hdelta')
  · intro delta hdeltaNot delta' hdelta' hadj
    apply hdeltaNot
    have hadj' := main_deltaAdjacent_symm c h12 hadj
    exact ⟨hadj.1, (hpath delta' hdelta').trans
      (Relation.ReflTransGen.single hadj')⟩

private lemma main_principal_component_ncard_eq_one
    (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) :
    (main_deltaComponent c h12
      (deltaNu c h12 (main_principalIrr c))).ncard = 1 := by
  classical
  let oneIrr : Irr (↥c.H0) := main_principalIrr c
  let oneB : Irr (↥c.B) :=
    ⟨(1 : ClassFunction (↥c.B)), isIrreducibleCharacter_one (↥c.B)⟩
  have hones : conjChar c.H0 (s_normalizes_H0 c h12) oneIrr.1 = oneIrr.1 := by
    ext x
    simp [oneIrr, main_principalIrr, conjChar]
  have honet : oneIrr.1 (tH0 c) = oneIrr.1 1 := by
    simp [oneIrr, main_principalIrr]
  have honeDelta : deltaNu c h12 oneIrr ∈ Delta c h12 := by
    rw [Delta]
    exact ⟨oneIrr, hones, honet, rfl⟩
  let DeltaOne : Set (ClassFunction G) :=
    main_deltaComponent c h12 (deltaNu c h12 oneIrr)
  have hcomp : IsConnectedComponent c h12 DeltaOne :=
    main_deltaComponent_isConnected c h12 honeDelta
  have honeMem : deltaNu c h12 oneIrr ∈ DeltaOne :=
    ⟨honeDelta, Relation.ReflTransGen.refl⟩
  have honeHat : nuHat c h12 oneIrr = oneB := by
    simpa [oneIrr, oneB] using
      main_nuHat_principal_eq_principal c h12 hSC hS4
  by_contra hcard
  rcases theorem_4_3 c h12 hSC hS4 DeltaOne hcomp hcard with
    ⟨nu1, nu2, _nu3, hnu1Mem, hnu2Mem, _hnu3Mem, hnu12, _hnu23, _hnu13,
      _chi1, _chi2, _chi3, _chi4, _hchi1, _hchi2, _hchi3, _hchi4,
      _h12, _h13, _h14, _h23, _h24, _h34, _hdelta1, _hdelta2, _hdelta3,
      _hset, hconj⟩
  have recover (nu : Irr (↥c.H0)) (hnuMem : deltaNu c h12 nu ∈ DeltaOne) :
      deltaNu c h12 nu = deltaNu c h12 oneIrr := by
    rcases hcomp.2.1 hnuMem with ⟨mu, hmus, hmut, heq⟩
    have hmuMem : deltaNu c h12 mu ∈ DeltaOne := by rwa [heq] at hnuMem
    rcases hconj oneIrr mu honeMem hmuMem with ⟨g, hg, hghat⟩
    have hgOne : conjIrrB c (B_conj_mem_of_normalizerS c hg) oneB = oneB := by
      apply Subtype.ext
      funext b
      simp [oneB, conjIrrB]
    have hmuHat : nuHat c h12 mu = nuHat c h12 oneIrr := by
      rw [honeHat] at hghat ⊢
      simpa [hgOne] using hghat.symm
    have hmueq : mu = oneIrr :=
      nuHat_injective_on_Delta c h12 hSC hS4 hmus hmut hones honet hmuHat
    rw [heq, hmueq]
  exact hnu12 ((recover nu1 hnu1Mem).trans (recover nu2 hnu2Mem).symm)

private lemma main_not_disjoint_of_pmIrr_pairings
    {psi delta epsilon : ClassFunction G} (hpsi : IsPMIrr G psi)
    (hdelta : scalarProduct G psi delta ≠ 0)
    (hepsilon : scalarProduct G psi epsilon ≠ 0) :
    ¬ Theory.Character.Disjoint delta epsilon := by
  intro hdisjoint
  rcases hpsi with hpsi | hpsi
  · exact hepsilon (hdisjoint psi hpsi hdelta)
  · have hdelta' : scalarProduct G (-psi) delta ≠ 0 := by
      rw [scalarProduct_neg_left]
      exact neg_ne_zero.mpr hdelta
    have hepsilon' : scalarProduct G (-psi) epsilon ≠ 0 := by
      rw [scalarProduct_neg_left]
      exact neg_ne_zero.mpr hepsilon
    exact hepsilon' (hdisjoint (-psi) hpsi hdelta')

private lemma main_scalarProduct_self_eq_one_of_isPMIrr
    {chi : ClassFunction G} (hchi : IsPMIrr G chi) :
    scalarProduct G chi chi = 1 := by
  rcases hchi with hchi | hchi
  · exact scalarProduct_irreducible_self hchi
  · have h' : scalarProduct G (-chi) (-chi) = 1 :=
      scalarProduct_irreducible_self hchi
    rw [scalarProduct_neg_left, scalarProduct_neg_right] at h'
    simpa using h'

private lemma main_singleton_component_constituent_facts (c : Hyp11 G)
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {kappa : Irr (↥c.H0)}
    (hkappas : conjChar c.H0 (s_normalizes_H0 c h12) kappa.1 = kappa.1)
    (hkappat : kappa.1 (tH0 c) = kappa.1 1) (hkappaone : kappa.1 1 = 1)
    {Delta0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Delta0)
    (hkappaDelta0 : deltaNu c h12 kappa ∈ Delta0)
    (hDelta0 : Delta0 = {deltaNu c h12 kappa})
    {psi : ClassFunction G} (hpsi : IsPMIrr G psi)
    (hpair : scalarProduct G psi (deltaNu c h12 kappa) = 1) :
    psi c.t = 1 ∧ ∃ n : ℤ, (n : ℂ) = psi 1 ∧ Odd n := by
  classical
  have hkappaB : kappa ∈ BPrimeOf c h12 psi := by
    rw [BPrime_mem_iff_scalar]
    exact ⟨hkappas, hkappat, by rw [hpair]; norm_num⟩
  have hBset : BPrimeOf c h12 psi = {kappa} := by
    ext nu
    constructor
    · intro hnuB
      rcases (BPrime_mem_iff_scalar c h12 psi nu).1 hnuB with
        ⟨hnus, hnut, hnupair⟩
      have hnuDelta : deltaNu c h12 nu ∈ Delta c h12 := by
        rw [Delta]
        exact ⟨nu, hnus, hnut, rfl⟩
      have hnuDelta0 : deltaNu c h12 nu ∈ Delta0 := by
        by_contra hnot
        have hne : deltaNu c h12 nu ≠ deltaNu c h12 kappa := by
          intro heq
          apply hnot
          rw [hDelta0, heq]
          simp
        have hadj : deltaAdjacent c h12 (deltaNu c h12 nu)
            (deltaNu c h12 kappa) := by
          refine ⟨hnuDelta, hcomp.2.1 hkappaDelta0, hne, ?_⟩
          exact main_not_disjoint_of_pmIrr_pairings hpsi hnupair
            (by rw [hpair]; norm_num)
        exact (hcomp.2.2.2 (deltaNu c h12 nu) hnot
          (deltaNu c h12 kappa) hkappaDelta0) hadj
      have hdeltaeq : deltaNu c h12 nu = deltaNu c h12 kappa := by
        have hmem : deltaNu c h12 nu ∈
            ({deltaNu c h12 kappa} : Set (ClassFunction G)) := by
          rwa [← hDelta0]
        simpa using hmem
      have hnueq : nu = kappa :=
        deltaNu_injective c h12 hSC hS4 hnus hnut hkappas hkappat hdeltaeq
      simpa [hnueq]
    · intro hnukappa
      have hnueq : nu = kappa := by simpa using hnukappa
      simpa [hnueq] using hkappaB
  have h41 := lemma_4_1 c h12 hSC hS4 hpsi ⟨kappa, hkappaB⟩
  have hvalue := h41.2.1
  rw [hBset] at hvalue
  refine ⟨?_, h41.2.2.2.1⟩
  simpa [hpair, hkappaone] using hvalue

private lemma main_singleton_component_four_values (c : Hyp11 G)
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {kappa : Irr (↥c.H0)}
    (hkappas : conjChar c.H0 (s_normalizes_H0 c h12) kappa.1 = kappa.1)
    (hkappat : kappa.1 (tH0 c) = kappa.1 1) (hkappaone : kappa.1 1 = 1)
    {Delta0 : Set (ClassFunction G)} (hcomp : IsConnectedComponent c h12 Delta0)
    (hkappaDelta0 : deltaNu c h12 kappa ∈ Delta0)
    (hDelta0 : Delta0 = {deltaNu c h12 kappa}) :
    ∃ psi : Fin 4 → ClassFunction G,
      (∀ i, IsPMIrr G (psi i)) ∧
      (∀ {i j}, i ≠ j → scalarProduct G (psi i) (psi j) = 0) ∧
      deltaNu c h12 kappa = ∑ i, psi i ∧
      (∀ i, scalarProduct G (psi i) (deltaNu c h12 kappa) = 1) ∧
      (∀ i, psi i c.t = 1) ∧
      (∀ i, ∃ n : ℤ, (n : ℂ) = psi i 1 ∧ Odd n) := by
  classical
  rcases signed_four_decomp_fin c h12 hSC hS4 hkappas with
    ⟨a, sign, ha, hainj, hsign, hdelta⟩
  let psi : Fin 4 → ClassFunction G := fun i => (sign i : ℂ) • a i
  have hpsi : ∀ i, IsPMIrr G (psi i) := by
    intro i
    rcases hsign i with hi | hi
    · left
      simpa [psi, hi] using ha i
    · right
      simpa [psi, hi] using ha i
  have horth : ∀ {i j}, i ≠ j → scalarProduct G (psi i) (psi j) = 0 := by
    intro i j hij
    have haij : a i ≠ a j := by
      intro heq
      exact hij (hainj heq)
    rw [show psi i = (sign i : ℂ) • a i by rfl,
      show psi j = (sign j : ℂ) • a j by rfl,
      scalarProduct_smul_left, scalarProduct_smul_right,
      scalarProduct_irr_ite (ha i) (ha j)]
    simp [haij]
  have hdeltasum : deltaNu c h12 kappa = ∑ i, psi i := by
    simpa [psi] using hdelta
  have hpair : ∀ i, scalarProduct G (psi i) (deltaNu c h12 kappa) = 1 := by
    intro i
    rw [hdeltasum, scalarProduct_sum_right]
    rw [Finset.sum_eq_single i]
    · exact main_scalarProduct_self_eq_one_of_isPMIrr (hpsi i)
    · intro j _ hji
      exact horth hji.symm
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have hfacts : ∀ i, psi i c.t = 1 ∧
      ∃ n : ℤ, (n : ℂ) = psi i 1 ∧ Odd n := by
    intro i
    exact main_singleton_component_constituent_facts c h12 hSC hS4
      hkappas hkappat hkappaone hcomp hkappaDelta0 hDelta0
      (hpsi i) (hpair i)
  exact ⟨psi, hpsi, horth, hdeltasum, hpair,
    (fun i => (hfacts i).1), (fun i => (hfacts i).2)⟩

/-- The principal Section-4 component is a four-term orthogonal signed
irreducible decomposition; every constituent takes value `1` at `t` and has
odd signed degree. -/
public lemma main_principal_delta_decomposition_of_section4 (c : Hyp11 G)
    (h12 : Hyp12 c) (hSC : Section3Hyp c) (hS4 : Section4Hyp c) :
    ∃ psi : Fin 4 → ClassFunction G,
      (∀ i, IsPMIrr G (psi i)) ∧
      (∀ {i j}, i ≠ j → scalarProduct G (psi i) (psi j) = 0) ∧
      deltaNu c h12 (main_principalIrr c) = ∑ i, psi i ∧
      (∀ i, scalarProduct G (psi i)
        (deltaNu c h12 (main_principalIrr c)) = 1) ∧
      (∀ i, psi i c.t = 1) ∧
      (∀ i, ∃ n : ℤ, (n : ℂ) = psi i 1 ∧ Odd n) := by
  classical
  let oneIrr : Irr (↥c.H0) := main_principalIrr c
  have hones : conjChar c.H0 (s_normalizes_H0 c h12) oneIrr.1 = oneIrr.1 := by
    ext x
    simp [oneIrr, main_principalIrr, conjChar]
  have honet : oneIrr.1 (tH0 c) = oneIrr.1 1 := by
    simp [oneIrr, main_principalIrr]
  have honeone : oneIrr.1 1 = 1 := by simp [oneIrr, main_principalIrr]
  have honeDelta : deltaNu c h12 oneIrr ∈ Delta c h12 := by
    rw [Delta]
    exact ⟨oneIrr, hones, honet, rfl⟩
  let DeltaOne : Set (ClassFunction G) :=
    main_deltaComponent c h12 (deltaNu c h12 oneIrr)
  have hcomp : IsConnectedComponent c h12 DeltaOne :=
    main_deltaComponent_isConnected c h12 honeDelta
  have honeMem : deltaNu c h12 oneIrr ∈ DeltaOne :=
    ⟨honeDelta, Relation.ReflTransGen.refl⟩
  have hcard : DeltaOne.ncard = 1 := by
    simpa [DeltaOne, oneIrr] using
      main_principal_component_ncard_eq_one c h12 hSC hS4
  rcases Set.ncard_eq_one.mp hcard with ⟨deltaOne, hDeltaOne'⟩
  have hdeltaOne : deltaOne = deltaNu c h12 oneIrr := by
    have hmem : deltaNu c h12 oneIrr ∈
        ({deltaOne} : Set (ClassFunction G)) := by
      rwa [← hDeltaOne']
    simpa using hmem.symm
  have hDeltaOne : DeltaOne = {deltaNu c h12 oneIrr} := by
    rw [hDeltaOne', hdeltaOne]
  simpa [oneIrr] using main_singleton_component_four_values c h12 hSC hS4
    hones honet honeone hcomp honeMem hDeltaOne

end PrincipalSection4Component

section PrincipalEquation

/-- Every `deltaNu` vanishes at the identity. -/
public lemma main_deltaNu_one_eq_zero (c : Hyp11 G) (h12 : Hyp12 c)
    (nu : Irr (↥c.H0)) : deltaNu c h12 nu 1 = 0 := by
  classical
  rw [deltaNu_eq_induced]
  unfold inducedClassFunction
  simp [LambdaChar]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro x hx
  have hone (h : (1 : G) ∈ c.H0) : (⟨1, h⟩ : ↥c.H0) = 1 := by
    apply Subtype.ext
    simp
  simp [hone]

private lemma main_signed_irr_t_sum (t : G) {psi : ClassFunction G}
    (hpsi : IsPMIrr G psi) :
    (∑ chi : Irr G, (chi.1 t ^ 2 / chi.1 1) *
      scalarProduct G chi.1 psi) = psi t ^ 2 / psi 1 := by
  classical
  rcases hpsi with hpsi | hpsi
  · let rho : Irr G := ⟨psi, hpsi⟩
    have hpair : ∀ chi : Irr G, scalarProduct G chi.1 psi =
        if chi = rho then 1 else 0 := by
      intro chi
      by_cases hchirho : chi = rho
      · subst hchirho
        rw [scalarProduct_irreducible_self hpsi]
        simp
      · have hchipsi : chi.1 ≠ psi := by
          intro heq
          exact hchirho (Subtype.ext heq)
        rw [scalarProduct_irreducible_orthogonal chi.2 hpsi hchipsi]
        simp [hchirho]
    calc
      (∑ chi : Irr G, (chi.1 t ^ 2 / chi.1 1) * scalarProduct G chi.1 psi) =
          ∑ chi : Irr G, (chi.1 t ^ 2 / chi.1 1) *
            (if chi = rho then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro chi hchi
              rw [hpair chi]
      _ = psi t ^ 2 / psi 1 := by simp [rho]
  · let rho : Irr G := ⟨-psi, hpsi⟩
    have hpair : ∀ chi : Irr G, scalarProduct G chi.1 psi =
        if chi = rho then -1 else 0 := by
      intro chi
      by_cases hchirho : chi = rho
      · subst hchirho
        rw [scalarProduct_neg_left]
        have hself : scalarProduct G psi psi = 1 := by
          rw [show psi = -(-psi) by simp]
          rw [scalarProduct_neg_left, scalarProduct_neg_right]
          simpa using scalarProduct_irreducible_self hpsi
        rw [hself]
        simp
      · have hchipsi : chi.1 ≠ -psi := by
          intro heq
          exact hchirho (Subtype.ext heq)
        rw [show psi = -(-psi) by simp]
        rw [scalarProduct_neg_right]
        rw [scalarProduct_irreducible_orthogonal chi.2 hpsi hchipsi]
        simp [hchirho]
    calc
      (∑ chi : Irr G, (chi.1 t ^ 2 / chi.1 1) * scalarProduct G chi.1 psi) =
          ∑ chi : Irr G, (chi.1 t ^ 2 / chi.1 1) *
            (if chi = rho then -1 else 0) := by
              apply Finset.sum_congr rfl
              intro chi hchi
              rw [hpair chi]
      _ = -(rho.1 t ^ 2 / rho.1 1) := by simp [rho]
      _ = psi t ^ 2 / psi 1 := by
        have hpsirho : psi = -rho.1 := by simp [rho]
        rw [hpsirho]
        simp [pow_two, div_neg]

private noncomputable def main_lambdaTwoIrr (c : Hyp11 G) (h12 : Hyp12 c) :
    Irr (↥c.H0) :=
  lambdaTwoMul c h12 (main_principalIrr c)

private lemma main_principal_mem_lambdaTwo_orbit (c : Hyp11 G)
    (h12 : Hyp12 c) :
    (main_principalIrr c).1 ∈ orbit c.H0 c.U (main_lambdaTwoIrr c h12).1 := by
  classical
  refine Finset.mem_image.mpr
    ⟨(lambdaTwo c h12)⁻¹, Finset.mem_univ _, ?_⟩
  ext x
  change (LambdaChar ((lambdaTwo c h12)⁻¹).1 *
    (LambdaChar (lambdaTwo c h12).1 * (1 : ClassFunction (↥c.H0)))) x = 1
  simp [LambdaChar]

private lemma main_principal_V_equation (c : Hyp11 G) (h12 : Hyp12 c)
    (hk12 : c.k1 = c.k2) :
    lemma_2_2_V c (main_principalIrr c).1 (main_lambdaTwoIrr c h12).1 =
      (2 * c.k ^ 2 : ℂ) := by
  have h2 := lemma_2_2 c h12 (μ := main_principalIrr c)
    (ν := main_lambdaTwoIrr c h12)
    (hEq := main_principal_mem_lambdaTwo_orbit c h12)
    (κ1 := (1 : ClassFunction (↥c.H0)))
    (isLinearCharacter_one (G := ↥c.H0)) (by simp) (by simp)
  apply h2.2.2 rfl
  · rw [kappa_eq_lambda_mul]
    rfl
  · exact hk12

private lemma main_principal_V_eq_delta_sum (c : Hyp11 G) (h12 : Hyp12 c) :
    lemma_2_2_V c (main_principalIrr c).1 (main_lambdaTwoIrr c h12).1 =
      (c.H.index : ℂ) *
        (∑ chi : Irr G, (chi.1 c.t ^ 2 / chi.1 1) *
          scalarProduct G chi.1 (deltaNu c h12 (main_principalIrr c))) := by
  rw [lemma_2_2_V, deltaNu_eq_induced]
  rfl

/-- Lemma 2.2 specialized to the principal character in the Section-4 case. -/
public lemma main_principal_delta_equation (c : Hyp11 G) (h12 : Hyp12 c)
    (hk12 : c.k1 = c.k2) :
    (c.H.index : ℂ) *
      (∑ chi : Irr G, (chi.1 c.t ^ 2 / chi.1 1) *
        scalarProduct G chi.1 (deltaNu c h12 (main_principalIrr c))) =
      (2 * c.k ^ 2 : ℂ) := by
  rw [← main_principal_V_eq_delta_sum c h12]
  exact main_principal_V_equation c h12 hk12

/-- The principal character occurs with coefficient one in the principal
`deltaNu`. -/
public lemma main_delta_trivial_principal_pairing (c : Hyp11 G)
    (h12 : Hyp12 c) :
    scalarProduct G (1 : ClassFunction G)
      (deltaNu c h12 (main_principalIrr c)) = 1 := by
  classical
  let oneIrr : Irr (↥c.H0) := main_principalIrr c
  have honeClass : IsClassFunction (1 : ClassFunction G) :=
    irreducibleCharacter_isClassFunction (isIrreducibleCharacter_one G)
  have hres := scalarProduct_restrict_induced c.H0 honeClass
    ((1 : ClassFunction (↥c.H0)) -
      LambdaChar (lambdaTwo c h12).1 * (1 : ClassFunction (↥c.H0)))
  have hlambda : LambdaChar (lambdaTwo c h12).1 *
      (1 : ClassFunction (↥c.H0)) = LambdaChar (lambdaTwo c h12).1 := by simp
  have hlambdaIrr : IsIrreducibleCharacter (LambdaChar (lambdaTwo c h12).1) :=
    (isLinearCharacter_of_hom (lambdaTwo c h12).1).1
  have hlambdaNe : (1 : ClassFunction (↥c.H0)) ≠
      LambdaChar (lambdaTwo c h12).1 := by
    intro heq
    apply lambdaTwo_ne_one c h12
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Units.ext
    have hx := congrFun heq x
    simpa [LambdaChar] using hx.symm
  have hsub : scalarProduct (↥c.H0) (1 : ClassFunction (↥c.H0))
      ((1 : ClassFunction (↥c.H0)) - LambdaChar (lambdaTwo c h12).1) = 1 := by
    rw [scalarProduct_sub_right,
      scalarProduct_irreducible_self (isIrreducibleCharacter_one (↥c.H0)),
      scalarProduct_irr_ite (isIrreducibleCharacter_one (↥c.H0)) hlambdaIrr]
    simp [hlambdaNe]
  change scalarProduct G (1 : ClassFunction G) (deltaNu c h12 oneIrr) = 1
  rw [deltaNu_eq_induced]
  change scalarProduct G (1 : ClassFunction G)
      (inducedClassFunction c.H0
        ((1 : ClassFunction (↥c.H0)) -
          LambdaChar (lambdaTwo c h12).1 * (1 : ClassFunction (↥c.H0)))) = 1
  rw [← hres]
  have honeRes : (fun x : ↥c.H0 => (1 : ClassFunction G) (x : G)) =
      (1 : ClassFunction (↥c.H0)) := by rfl
  rw [honeRes, hlambda]
  exact hsub

/-- A four-term signed-irreducible sum with principal scalar product one
contains the principal character. -/
public lemma main_exists_principal_in_four_sum
    (psi : Fin 4 → ClassFunction G) (hpsi : ∀ i, IsPMIrr G (psi i))
    (hsum : scalarProduct G (1 : ClassFunction G) (∑ i, psi i) = 1) :
    ∃ i, psi i = 1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hnonpos : ∀ i,
      (scalarProduct G (1 : ClassFunction G) (psi i)).re ≤ 0 := by
    intro i
    rcases hpsi i with hpos | hneg
    · have hne : (1 : ClassFunction G) ≠ psi i := (hnone i).symm
      rw [scalarProduct_irr_ite (isIrreducibleCharacter_one G) hpos,
        if_neg hne]
      norm_num
    · rw [show psi i = -(-psi i) by simp, scalarProduct_neg_right]
      rw [scalarProduct_irr_ite (isIrreducibleCharacter_one G) hneg]
      split_ifs <;> norm_num
  have hle : (∑ i, (scalarProduct G (1 : ClassFunction G) (psi i)).re) ≤ 0 :=
    Finset.sum_nonpos fun i _ => hnonpos i
  have hre := congrArg Complex.re hsum
  simp only [scalarProduct_sum_right, Complex.re_sum, Complex.one_re] at hre
  rw [hre] at hle
  norm_num at hle

/-- Expand the character sum of a signed four-term decomposition as the sum
of reciprocal signed degrees. -/
public lemma main_four_reciprocal_sum (c : Hyp11 G)
    {delta : ClassFunction G} (psi : Fin 4 → ClassFunction G)
    (hpsi : ∀ i, IsPMIrr G (psi i)) (hdelta : delta = ∑ i, psi i)
    (hpsit : ∀ i, psi i c.t = 1) :
    (∑ chi : Irr G, (chi.1 c.t ^ 2 / chi.1 1) *
      scalarProduct G chi.1 delta) = ∑ i, (psi i 1)⁻¹ := by
  classical
  rw [hdelta]
  simp_rw [scalarProduct_sum_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [main_signed_irr_t_sum c.t (hpsi i), hpsit i]
  norm_num

end PrincipalEquation

section PrincipalArithmetic

/-- A Section-4 signed irreducible taking value one at `t` cannot have signed
degree `-1`: otherwise its negative would be a linear character nontrivial on
the commutator `t`. -/
public lemma main_signed_degree_ne_neg_one (c : Hyp11 G)
    (hS4 : Section4Hyp c) {psi : ClassFunction G} (hpsi : IsPMIrr G psi)
    (hpsit : psi c.t = 1) {n : ℤ} (hn : (n : ℂ) = psi 1) (_hnodd : Odd n) :
    n ≠ -1 := by
  intro hnegone
  rcases hpsi with hpos | hneg
  · rcases hpos with ⟨d, rho, hirr, hpsi⟩
    have hdegree : psi 1 = (d : ℂ) := by
      rw [hpsi, Representation.char_one, Module.finrank_pi, Fintype.card_fin]
    have hcast : (n : ℂ) = (d : ℂ) := hn.trans hdegree
    have hnd : n = (d : ℤ) := by exact_mod_cast hcast
    omega
  · have hlin : IsLinearCharacter (-psi) := by
      refine ⟨hneg, ?_⟩
      rw [Pi.neg_apply, ← hn, hnegone]
      norm_num
    have htker := Abelianization.commutator_subset_ker (linearCharHom hlin)
      (main_t_mem_commutator_of_section4 c hS4)
    have htval : (-psi) c.t = 1 := by
      have hunit := congrArg (fun z : ℂˣ => (z : ℂ)) htker
      simpa [MonoidHom.mem_ker, linearCharHom_apply] using hunit
    rw [Pi.neg_apply, hpsit] at htval
    norm_num at htval

private lemma main_odd_inv_bounds {n : ℤ} (hnodd : Odd n) (hne : n ≠ -1) :
    (0 < n ∧ (0 : ℚ) < (n : ℚ)⁻¹ ∧ (n : ℚ)⁻¹ ≤ 1) ∨
      (n < 0 ∧ (-1 / 3 : ℚ) ≤ (n : ℚ)⁻¹ ∧ (n : ℚ)⁻¹ < 0) := by
  rcases hnodd with ⟨k, hk⟩
  by_cases hnpos : 0 < n
  · left
    have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
    have hone : (1 : ℚ) ≤ (n : ℚ) := by
      exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    have hinvpos : (0 : ℚ) < (n : ℚ)⁻¹ := inv_pos.mpr hnq
    refine ⟨hnpos, hinvpos, ?_⟩
    have hmul : (n : ℚ) * (n : ℚ)⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hnq)
    nlinarith
  · right
    have hnneg : n < 0 := by omega
    have hnle : n ≤ -3 := by omega
    have hnq : (n : ℚ) < 0 := by exact_mod_cast hnneg
    have hnleq : (n : ℚ) ≤ -3 := by exact_mod_cast hnle
    have hinvneg : (n : ℚ)⁻¹ < 0 := inv_lt_zero'.mpr hnq
    refine ⟨hnneg, ?_, hinvneg⟩
    have hmul : (n : ℚ) * (n : ℚ)⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_lt hnq)
    nlinarith

private lemma main_three_odd_reciprocal_bounds {a b d : ℤ}
    (haodd : Odd a) (hane : a ≠ -1) (hbodd : Odd b) (hbne : b ≠ -1)
    (hdodd : Odd d) (hdne : d ≠ -1) (hsum : a + b + d = -1) :
    (1 / 3 : ℚ) < 1 + (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (d : ℚ)⁻¹ ∧
      1 + (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (d : ℚ)⁻¹ < 3 := by
  rcases main_odd_inv_bounds haodd hane with ha | ha
  · rcases main_odd_inv_bounds hbodd hbne with hb | hb
    · rcases main_odd_inv_bounds hdodd hdne with hd | hd
      · omega
      · constructor <;>
          nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, hd.2.1, hd.2.2]
    · rcases main_odd_inv_bounds hdodd hdne with hd | hd
      · constructor <;>
          nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, hd.2.1, hd.2.2]
      · constructor <;>
          nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, hd.2.1, hd.2.2]
  · rcases main_odd_inv_bounds hbodd hbne with hb | hb
    · rcases main_odd_inv_bounds hdodd hdne with hd | hd
      · constructor <;>
          nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, hd.2.1, hd.2.2]
      · constructor <;>
          nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, hd.2.1, hd.2.2]
    · rcases main_odd_inv_bounds hdodd hdne with hd | hd
      · constructor <;>
          nlinarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2, hd.2.1, hd.2.2]
      · omega

/-- Four odd integers summing to zero, one equal to `1` and none equal to
`-1`, have reciprocal sum strictly between `1/3` and `3`. -/
public lemma main_four_odd_reciprocal_bounds (n : Fin 4 → ℤ)
    (hnodd : ∀ i, Odd (n i)) (hnne : ∀ i, n i ≠ -1)
    {i0 : Fin 4} (hi0 : n i0 = 1) (hsum : ∑ i, n i = 0) :
    (1 / 3 : ℚ) < ∑ i, ((n i : ℤ) : ℚ)⁻¹ ∧
      (∑ i, ((n i : ℤ) : ℚ)⁻¹) < 3 := by
  let e : Fin 4 ≃ Fin 4 := Equiv.swap 0 i0
  have he0 : n (e 0) = 1 := by simp [e, hi0]
  have hsum' : ∑ i, n (e i) = 0 := by
    rw [Equiv.sum_comp]
    exact hsum
  have hsum'' : 1 + (n (e 1) + (n (e 2) + n (e 3))) = 0 := by
    simpa [Fin.sum_univ_succ, he0] using hsum'
  have habd : n (e 1) + n (e 2) + n (e 3) = -1 := by omega
  have hbounds := main_three_odd_reciprocal_bounds
    (hnodd (e 1)) (hnne (e 1)) (hnodd (e 2)) (hnne (e 2))
    (hnodd (e 3)) (hnne (e 3)) habd
  have hreindex : (∑ i, ((n i : ℤ) : ℚ)⁻¹) =
      1 + ((n (e 1) : ℤ) : ℚ)⁻¹ + ((n (e 2) : ℤ) : ℚ)⁻¹ +
        ((n (e 3) : ℤ) : ℚ)⁻¹ := by
    calc
      (∑ i, ((n i : ℤ) : ℚ)⁻¹) = ∑ i, ((n (e i) : ℤ) : ℚ)⁻¹ :=
        (Equiv.sum_comp e (fun i => ((n i : ℤ) : ℚ)⁻¹)).symm
      _ = 1 + ((n (e 1) : ℤ) : ℚ)⁻¹ + ((n (e 2) : ℤ) : ℚ)⁻¹ +
          ((n (e 3) : ℤ) : ℚ)⁻¹ := by
            simp [Fin.sum_univ_succ, he0, add_assoc]
  rwa [hreindex]

/-- Transfer the complex principal-component equation back to its rational
form. -/
public lemma main_ratio_eq_reciprocal_sum (c : Hyp11 G) (n : Fin 4 → ℤ)
    (heq : (c.H.index : ℂ) * (∑ i, ((n i : ℤ) : ℂ)⁻¹) =
      (2 * c.k ^ 2 : ℂ)) :
    (2 * (c.k : ℚ) ^ 2) / (c.H.index : ℚ) =
      ∑ i, ((n i : ℤ) : ℚ)⁻¹ := by
  have hindexC : (c.H.index : ℂ) ≠ 0 := by
    rw [Subgroup.index_eq_card]
    exact_mod_cast (Nat.card_pos (α := G ⧸ c.H)).ne'
  have hdivC : (2 * (c.k : ℂ) ^ 2) / (c.H.index : ℂ) =
      ∑ i, ((n i : ℤ) : ℂ)⁻¹ := by
    apply (div_eq_iff hindexC).2
    simpa [mul_comm] using heq.symm
  apply (Rat.cast_injective (α := ℂ))
  push_cast
  exact hdivC

end PrincipalArithmetic

end CFSG.BenderGlauberman
