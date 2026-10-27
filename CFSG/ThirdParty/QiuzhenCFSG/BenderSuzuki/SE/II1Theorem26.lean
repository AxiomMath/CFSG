module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PermutationQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_6
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.I.theorem_18_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.theorem_7_15
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_6_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.proposition_2_9
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.BrauerPermutation

namespace CFSG
end CFSG
open CFSG

/-!
# GLS Part II, Chapter 1, Theorem 2.6

This file proves the permutation theorem used in Section 9.  A finite group
containing a regular subgroup whose nonidentity elements are self-centralizing
is either doubly transitive or is the product of the pointwise action kernel
and the normalizer of the regular subgroup.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFchapter1section1
open scoped Pointwise

universe u v w

private theorem ii1Theorem26_regular_disjoint_core
    {X : Type u} {Omega : Type v}
    [Group X] [MulAction X Omega] [Nonempty Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega)) :
    Disjoint K (pointStabilizerCore X Omega) := by
  rw [Subgroup.disjoint_def]
  intro x hxK hxcore
  let alpha : Omega := Classical.choice (inferInstance : Nonempty Omega)
  have hxfix : x • alpha = alpha :=
    pointStabilizerCore_le_stabilizer alpha hxcore
  obtain ⟨k, hk, huniq⟩ :=
    hreg (alpha := alpha) (beta := alpha) (by trivial) (by trivial)
  let xK : K := ⟨x, hxK⟩
  have hxK_eq : xK = k := huniq xK hxfix
  have hone_eq : (1 : K) = k := huniq 1 (by simp)
  exact congrArg Subtype.val (hxK_eq.trans hone_eq.symm)

private theorem ii1Theorem26_regular_card
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega)) :
    Nat.card K = Nat.card Omega := by
  let alpha : Omega := Classical.choice (inferInstance : Nonempty Omega)
  let orbitMap : K → Omega := fun k => (k : X) • alpha
  have hsurj : Function.Surjective orbitMap := by
    intro beta
    obtain ⟨k, hk, _huniq⟩ :=
      hreg (alpha := alpha) (beta := beta) (by trivial) (by trivial)
    exact ⟨k, hk⟩
  have hinj : Function.Injective orbitMap := by
    intro a b hab
    obtain ⟨k, _hk, huniq⟩ :=
      hreg (alpha := alpha) (beta := orbitMap a) (by trivial) (by trivial)
    exact (huniq a rfl).trans (huniq b hab.symm).symm
  exact Nat.card_congr (Equiv.ofBijective orbitMap ⟨hinj, hsurj⟩)

private theorem ii1Theorem26_regular_pretransitive
    {X : Type u} {Omega : Type v}
    [Group X] [MulAction X Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega)) :
    MulAction.IsPretransitive X Omega := by
  constructor
  intro alpha beta
  obtain ⟨k, hk, _huniq⟩ :=
    hreg (alpha := alpha) (beta := beta) (by trivial) (by trivial)
  exact ⟨(k : X), hk⟩

private theorem ii1Theorem26_regular_commutative
    {X : Type u} [Group X]
    (K : Subgroup X)
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K) :
    IsMulCommutative K := by
  refine ⟨⟨?_⟩⟩
  intro a b
  apply Subtype.ext
  by_cases ha : (a : X) = 1
  · simp [ha]
  have hbcent : (b : X) ∈ Subgroup.centralizer ({(a : X)} : Set X) := by
    rw [hcent (a : X) a.property ha]
    exact b.property
  exact (Subgroup.mem_centralizer_singleton_iff.mp hbcent).symm

private theorem ii1Theorem26_card_conjBy
    {X : Type u} [Group X] [Finite X]
    (K : Subgroup X) (g : X) :
    Nat.card (K.conjBy g) = Nat.card K := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := K) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)

private theorem ii1Theorem26_mem_normalizer_of_conjBy_eq
    {X : Type u} [Group X]
    {K : Subgroup X} {g : X} (hg : K.conjBy g = K) :
    g ∈ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ K.conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ K.conjBy g := by
      simpa [hg] using hx
    rw [Subgroup.conjBy, Subgroup.mem_map] at hx'
    rcases hx' with ⟨y, hy, hyx⟩
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by simp [mul_assoc]
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [← hyx']
        _ = y := by simp [mul_assoc]
    simpa [hxy] using hy

private theorem ii1Theorem26_isTI_normalizer
    {X : Type u} [Group X] [Finite X]
    (K : Subgroup X)
    (hKne : K ≠ ⊥)
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K) :
    External.Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (K : Set X)) (K : Set X) := by
  let N : Subgroup X := Subgroup.normalizer (K : Set X)
  have hKleN : K ≤ N := Subgroup.le_normalizer
  have hKcomm : IsMulCommutative K :=
    ii1Theorem26_regular_commutative K hcent
  letI : IsMulCommutative K := hKcomm
  have hKnontriv : ∃ k ∈ (K : Set X), k ≠ 1 := by
    obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
    exact ⟨k, k.property, fun hk1 => hk (Subtype.ext hk1)⟩
  have hNnorm : N ≤ Subgroup.normalizer (K : Set X) := le_rfl
  apply (External.Suzuki.VI.suzuki_ch6_proposition_2_8 N (K : Set X)
      hKleN hNnorm hKnontriv).2
  intro g hg z hz
  rcases hz.1 with ⟨x, hxK, hxz⟩
  have hzK : z ∈ K := hz.2
  by_cases hz1 : z = 1
  · simp [hz1]
  · have hconj_le : K.conjBy g ≤
        Subgroup.centralizer ({z} : Set X) := by
      intro y hy
      rcases hy with ⟨y0, hy0, hyEq⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hxz, ← hyEq]
      have hcomm : y0 * x = x * y0 := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := K)).comm
            ⟨y0, hy0⟩ ⟨x, hxK⟩)
      calc
        (g * y0 * g⁻¹) * (g * x * g⁻¹) =
            g * (y0 * x) * g⁻¹ := by group
        _ = g * (x * y0) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * (g * y0 * g⁻¹) := by group
    have hconj_le_K : K.conjBy g ≤ K := by
      intro y hy
      have hy' := hconj_le hy
      rw [hcent z hzK hz1] at hy'
      exact hy'
    have hEq : K.conjBy g = K :=
      Subgroup.eq_of_le_of_card_ge hconj_le_K
        (le_of_eq (ii1Theorem26_card_conjBy K g).symm)
    exfalso
    exact hg (ii1Theorem26_mem_normalizer_of_conjBy_eq hEq)

private theorem ii1Theorem26_isTI_self_normalizing
    {X : Type u} [Group X] [Finite X]
    (K : Subgroup X)
    (hKne : K ≠ ⊥)
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K)
    (hNK : Subgroup.normalizer (K : Set X) = K) :
    ∀ g : X, g ∉ K → Disjoint K (K.conjBy g) := by
  have hrel : External.Suzuki.VI.IsTISubsetRelative K (K : Set X) := by
    simpa [hNK] using ii1Theorem26_isTI_normalizer K hKne hcent
  have hKnontriv : ∃ k : X, k ∈ (K : Set X) ∧ k ≠ 1 := by
    obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
    exact ⟨k, k.property, fun hk1 => hk (Subtype.ext hk1)⟩
  have hinter :=
    (External.Suzuki.VI.suzuki_ch6_proposition_2_8 K (K : Set X)
      (fun _ hx => hx) Subgroup.le_normalizer hKnontriv).1 hrel
  intro g hg
  rw [Subgroup.disjoint_def]
  intro x hxK hxconj
  have hxImage : x ∈ (fun y : X => g * y * g⁻¹) '' (K : Set X) := by
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj
    rcases hxconj with ⟨y, hy, hyx⟩
    exact ⟨y, hy, by simpa [MulAut.conj_apply] using hyx⟩
  have hxone := hinter g hg ⟨hxImage, hxK⟩
  simpa using hxone

private theorem ii1Theorem26_normalizer_frobenius
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K)
    (hKne : K ≠ ⊥)
    (alpha : Omega)
    (hNK : Subgroup.normalizer (K : Set X) ≠ K) :
    let N := Subgroup.normalizer (K : Set X)
    let F := K.subgroupOf N
    let D := MulAction.stabilizer N alpha
    IsFrobeniusGroupWithKernelComplement F D := by
  classical
  let N := Subgroup.normalizer (K : Set X)
  let F := K.subgroupOf N
  let D := MulAction.stabilizer N alpha
  change IsFrobeniusGroupWithKernelComplement F D
  have hKleN : K ≤ N := Subgroup.le_normalizer
  have hFnormal : F.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKleN).2 le_rfl
  have hfree : ∀ f : F, f • alpha = alpha → f = 1 := by
    intro f hf
    obtain ⟨k, _hk, huniq⟩ :=
      hreg (alpha := alpha) (beta := alpha) (by trivial) (by trivial)
    let fK : K := ⟨(((f : F) : N) : X), f.property⟩
    change (((f : F) : X) • alpha = alpha) at hf
    have hfK : fK = k := huniq fK (by simpa [fK] using hf)
    have h1K : (1 : K) = k := huniq 1 (by simp)
    exact Subtype.ext (Subtype.ext (by
      simpa [fK] using congrArg Subtype.val (hfK.trans h1K.symm)))
  have hmove : ∀ n : N, ∃ f : F, f • n • alpha = alpha := by
    intro n
    obtain ⟨k, hk, _huniq⟩ :=
      hreg (alpha := (n : X) • alpha) (beta := alpha)
        (by trivial) (by trivial)
    let f : F := ⟨⟨(k : X), hKleN k.property⟩, k.property⟩
    refine ⟨f, ?_⟩
    simpa [f, Subgroup.smul_def, mul_smul] using hk
  have hcomp : F.IsComplement' D := by
    simpa [D] using
      (Subgroup.isComplement'_stabilizer (G := N) alpha hfree hmove)
  have hFne : F ≠ ⊥ := by
    intro hFbot
    exact hKne
      ((Subgroup.subgroupOf_eq_bot.mp hFbot).eq_bot_of_le hKleN)
  have hDne : D ≠ ⊥ := by
    intro hDbot
    have hFcard : Nat.card F = Nat.card K :=
      natCard_subgroupOf_eq K N hKleN
    have hDcard : Nat.card D = 1 := by simp [hDbot]
    have hcard : Nat.card N = Nat.card K := by
      calc
        Nat.card N = Nat.card F * Nat.card D := hcomp.card_mul.symm
        _ = Nat.card K := by rw [hFcard, hDcard, mul_one]
    have hKN : K = N :=
      Subgroup.eq_of_le_of_card_ge hKleN (le_of_eq hcard)
    exact hNK hKN.symm
  apply (lemma_3_1 F D hFne hDne hFnormal hcomp).2
  intro d hd
  rw [Subgroup.eq_bot_iff_forall]
  intro f hf
  by_contra hfne
  let fF : F := ⟨f, hf.1⟩
  have hfneX : (f : X) ≠ 1 := by
    intro h
    apply hfne
    exact Subtype.ext h
  have hdCent : (((d : D) : N) : X) ∈
      Subgroup.centralizer ({(f : X)} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hf.2).symm
  have hdK : (((d : D) : N) : X) ∈ K := by
    rw [← hcent (f : X) fF.property hfneX]
    exact hdCent
  let dF : F := ⟨(d : N), hdK⟩
  have hdFfix : dF • alpha = alpha := d.property
  have hdFone : dF = 1 := hfree dF hdFfix
  apply hd
  exact Subtype.ext (by
    simpa [dF] using congrArg Subtype.val hdFone)

private theorem ii1Theorem26_quotient_regular
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega)) :
    let W := pointStabilizerCore X Omega
    letI : W.Normal := pointStabilizerCore_normal
    letI : MulAction (X ⧸ W) Omega := pointStabilizerCoreQuotientAction
    IsRegularOn (K.map (QuotientGroup.mk' W)) (Set.univ : Set Omega) := by
  classical
  let W := pointStabilizerCore X Omega
  letI : W.Normal := pointStabilizerCore_normal
  letI : MulAction (X ⧸ W) Omega := pointStabilizerCoreQuotientAction
  let q : X →* X ⧸ W := QuotientGroup.mk' W
  let Kbar : Subgroup (X ⧸ W) := K.map q
  change IsRegularOn Kbar (Set.univ : Set Omega)
  intro alpha beta _halpha _hbeta
  obtain ⟨k, hk, huniq⟩ :=
    hreg (alpha := alpha) (beta := beta) (by trivial) (by trivial)
  let kbar : Kbar := ⟨q (k : X), Subgroup.mem_map.mpr
    ⟨(k : X), k.property, rfl⟩⟩
  refine ⟨kbar, ?_, ?_⟩
  · change ((QuotientGroup.mk' W) (k : X)) • alpha = beta
    exact (pointStabilizerCoreQuotientAction_mk_smul (k : X) alpha).trans hk
  · intro lbar hlbar
    rcases Subgroup.mem_map.mp lbar.property with ⟨l, hlK, hlq⟩
    let lK : K := ⟨l, hlK⟩
    have hlKact : (lK : X) • alpha = beta := by
      change l • alpha = beta
      calc
        l • alpha = ((QuotientGroup.mk' W) l) • alpha :=
          (pointStabilizerCoreQuotientAction_mk_smul l alpha).symm
        _ = (lbar : X ⧸ W) • alpha := congrArg (fun g => g • alpha) hlq
        _ = beta := hlbar
    have hlkeq : lK = k := huniq lK hlKact
    apply Subtype.ext
    change (lbar : X ⧸ W) = q (k : X)
    rw [← hlq, show l = (lK : X) from rfl, hlkeq]

private theorem ii1Theorem26_quotient_card
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega)) :
    let W := pointStabilizerCore X Omega
    letI : W.Normal := pointStabilizerCore_normal
    Nat.card (K.map (QuotientGroup.mk' W)) = Nat.card K := by
  classical
  let W := pointStabilizerCore X Omega
  letI : W.Normal := pointStabilizerCore_normal
  let q : X →* X ⧸ W := QuotientGroup.mk' W
  let Kbar : Subgroup (X ⧸ W) := K.map q
  let toKbar : K → Kbar := fun k =>
    ⟨q (k : X), Subgroup.mem_map.mpr ⟨(k : X), k.property, rfl⟩⟩
  have hdisj : Disjoint K W :=
    ii1Theorem26_regular_disjoint_core K hreg
  have hinj : Function.Injective toKbar := by
    intro a b hab
    apply Subtype.ext
    apply (div_eq_one.mp ?_)
    have hqeq : q ((a : X) / (b : X)) = 1 := by
      rw [map_div]
      exact div_eq_one.mpr (congrArg Subtype.val hab)
    have hdivW : (a : X) / (b : X) ∈ W :=
      (QuotientGroup.eq_one_iff (N := W) ((a : X) / (b : X))).1 hqeq
    have hdivK : (a : X) / (b : X) ∈ K :=
      K.div_mem a.property b.property
    exact Subgroup.disjoint_def.mp hdisj hdivK hdivW
  have hsurj : Function.Surjective toKbar := by
    intro kbar
    rcases Subgroup.mem_map.mp kbar.property with ⟨k, hk, hkq⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    exact hkq
  exact (Nat.card_congr (Equiv.ofBijective toKbar ⟨hinj, hsurj⟩)).symm

private theorem ii1Theorem26_quotient_centralizer
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K) :
    let W := pointStabilizerCore X Omega
    letI : W.Normal := pointStabilizerCore_normal
    let q : X →* X ⧸ W := QuotientGroup.mk' W
    let Kbar : Subgroup (X ⧸ W) := K.map q
    ∀ xbar : X ⧸ W, xbar ∈ Kbar → xbar ≠ 1 →
      Subgroup.centralizer ({xbar} : Set (X ⧸ W)) = Kbar := by
  classical
  let W := pointStabilizerCore X Omega
  letI : W.Normal := pointStabilizerCore_normal
  let q : X →* X ⧸ W := QuotientGroup.mk' W
  let Kbar : Subgroup (X ⧸ W) := K.map q
  have hKcomm : IsMulCommutative K :=
    ii1Theorem26_regular_commutative K hcent
  letI : IsMulCommutative K := hKcomm
  have hKbarCard : Nat.card Kbar = Nat.card K := by
    simpa [W, q, Kbar] using ii1Theorem26_quotient_card K hreg
  change ∀ xbar : X ⧸ W, xbar ∈ Kbar → xbar ≠ 1 →
    Subgroup.centralizer ({xbar} : Set (X ⧸ W)) = Kbar
  intro xbar hxbar hxbarne
  rcases Subgroup.mem_map.mp hxbar with ⟨x, hxK, hxq⟩
  have hxne : x ≠ 1 := by
    intro hxone
    apply hxbarne
    rw [← hxq, hxone, map_one]
  have hle : Kbar ≤
      Subgroup.centralizer ({xbar} : Set (X ⧸ W)) := by
    intro ybar hybar
    rcases Subgroup.mem_map.mp hybar with ⟨y, hyK, hyq⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hxq, ← hyq, ← map_mul, ← map_mul]
    exact congrArg q
      (congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := K)).comm
          (⟨y, hyK⟩ : K) (⟨x, hxK⟩ : K)))
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hKbarCard, ← hcent x hxK hxne]
  simpa [q, hxq] using ig916_quotient_centralizer_card_le W x

private theorem ii1Theorem26_two_pretransitive_of_core_quotient
    {X : Type u} {Omega : Type v}
    [Group X] [MulAction X Omega]
    (htwo :
      let W := pointStabilizerCore X Omega
      letI : W.Normal := pointStabilizerCore_normal
      letI : MulAction (X ⧸ W) Omega := pointStabilizerCoreQuotientAction
      MulAction.IsMultiplyPretransitive (X ⧸ W) Omega 2) :
    MulAction.IsMultiplyPretransitive X Omega 2 := by
  let W := pointStabilizerCore X Omega
  letI : W.Normal := pointStabilizerCore_normal
  letI : MulAction (X ⧸ W) Omega := pointStabilizerCoreQuotientAction
  change MulAction.IsMultiplyPretransitive (X ⧸ W) Omega 2 at htwo
  rw [MulAction.is_two_pretransitive_iff] at htwo ⊢
  intro a b c d hab hcd
  obtain ⟨gbar, hgac, hgbd⟩ := htwo hab hcd
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W gbar
  have hgac' : (QuotientGroup.mk' W g) • a = c := by simpa using hgac
  have hgbd' : (QuotientGroup.mk' W g) • b = d := by simpa using hgbd
  exact ⟨g,
    (pointStabilizerCoreQuotientAction_mk_smul g a).symm.trans hgac',
    (pointStabilizerCoreQuotientAction_mk_smul g b).symm.trans hgbd'⟩

private theorem ii1Theorem26_fixedPointSubgroup_bot_of_regular_prime
    {H R : Type*} [Group H] [Finite H] [Group R] [Finite R]
    [MulDistribMulAction R H] (hregular : ActsRegularly R H)
    {P : Subgroup R} (hPprime : Nat.Prime (Nat.card P)) :
    letI : MulDistribMulAction P H :=
      MulDistribMulAction.compHom H P.subtype
    fixedPointSubgroup (↥P) H = ⊥ := by
  classical
  letI : MulDistribMulAction P H :=
    MulDistribMulAction.compHom H P.subtype
  have hP_ne_bot : P ≠ ⊥ := by
    intro hPbot
    exact hPprime.ne_one (by simp [hPbot])
  letI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hP_ne_bot
  obtain ⟨x, hx_ne⟩ := exists_ne (1 : P)
  apply le_antisymm
  · intro y hy
    have hxR_ne : (x : R) ≠ 1 := by
      intro hxR
      exact hx_ne (Subtype.ext hxR)
    have hy_z :
        y ∈ fixedPointSubgroup (↥(Subgroup.zpowers (x : R))) H := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy ⊢
      intro z
      have hzP : (z : R) ∈ P :=
        (Subgroup.zpowers_le).2 x.2 z.2
      have hyP := hy ⟨(z : R), hzP⟩
      change (z : R) • y = y at hyP
      exact hyP
    simpa [hregular (x : R) hxR_ne] using hy_z
  · exact bot_le

private theorem ii1Theorem26_coprime_card_of_regular_action
    {H R : Type*} [Group H] [Finite H] [Group R] [Finite R]
    [MulDistribMulAction R H] (hregular : ActsRegularly R H) :
    Nat.Coprime (Nat.card H) (Nat.card R) := by
  classical
  refine Nat.coprime_of_dvd ?_
  intro r hr_prime hr_dvd_H hr_dvd_R
  letI : Fact r.Prime := ⟨hr_prime⟩
  obtain ⟨P, hPcard_pow⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := R) r (n := 1) (by
      simpa using hr_dvd_R)
  have hPcard : Nat.card P = r := by simpa using hPcard_pow
  have hPprime : Nat.Prime (Nat.card P) := by simpa [hPcard] using hr_prime
  letI : MulDistribMulAction P H :=
    MulDistribMulAction.compHom H P.subtype
  have hfix : fixedPointSubgroup (↥P) H = ⊥ :=
    ii1Theorem26_fixedPointSubgroup_bot_of_regular_prime hregular hPprime
  have hPp : IsPGroup r P :=
    IsPGroup.of_card (G := P) (p := r) (n := 1) (by simp [hPcard])
  have hone_fix : (1 : H) ∈ MulAction.fixedPoints (↥P) H := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨x, hx_fix, hx_ne_one⟩ :=
    hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := H) hr_dvd_H hone_fix
  have hx_mem : x ∈ fixedPointSubgroup (↥P) H := by
    rw [FixedPoints.mem_subgroup]
    exact MulAction.mem_fixedPoints.mp hx_fix
  have hx_bot : x ∈ (⊥ : Subgroup H) := by
    simpa [hfix] using hx_mem
  exact hx_ne_one (Subgroup.mem_bot.mp hx_bot).symm

private theorem ii1Theorem26_normalizer_factor_of_quotient_normal
    {X : Type u} [Group X] [Finite X]
    (W K : Subgroup X) [W.Normal]
    (hdisj : Disjoint K W)
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K)
    (hKbarNormal : (K.map (QuotientGroup.mk' W)).Normal) :
    (Set.univ : Set X) =
      (W : Set X) * (Subgroup.normalizer (K : Set X) : Set X) := by
  classical
  let q : X →* X ⧸ W := QuotientGroup.mk' W
  let Kbar : Subgroup (X ⧸ W) := K.map q
  let S : Subgroup X := W ⊔ K
  have hS_eq : S = Kbar.comap q := by
    calc
      S = K ⊔ W := by simp [S, sup_comm]
      _ = K ⊔ q.ker := by simp [q, QuotientGroup.ker_mk']
      _ = Kbar.comap q := (Subgroup.comap_map_eq q K).symm
  have hSnormal : S.Normal := by
    rw [hS_eq]
    exact hKbarNormal.comap q
  letI : S.Normal := hSnormal
  by_cases hKbot : K = ⊥
  · have hNtop : Subgroup.normalizer (K : Set X) = ⊤ := by
      apply Subgroup.normalizer_eq_top_iff.mpr
      simpa [hKbot] using (inferInstance : (⊥ : Subgroup X).Normal)
    rw [eq_comm, Set.eq_univ_iff_forall]
    intro x
    exact ⟨1, W.one_mem, x, by simp [hNtop], by simp⟩
  by_cases hWbot : W = ⊥
  · have hKnormal : K.Normal := by
      simpa [S, hWbot] using hSnormal
    have hNtop : Subgroup.normalizer (K : Set X) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hKnormal
    rw [eq_comm, Set.eq_univ_iff_forall]
    intro x
    exact ⟨1, by simp [hWbot], x, by simp [hNtop], by simp⟩
  have hWleS : W ≤ S := le_sup_left
  have hKleS : K ≤ S := le_sup_right
  let Wsub : Subgroup S := W.subgroupOf S
  let Ksub : Subgroup S := K.subgroupOf S
  have hWsubNormal : Wsub.Normal :=
    (inferInstance : W.Normal).subgroupOf S
  letI : Wsub.Normal := hWsubNormal
  have hcomp : Wsub.IsComplement' Ksub := by
    simpa [Wsub, Ksub, S] using
      (isComplement'_subgroupOf_sup_of_disjoint W K hdisj.symm)
  have hWsubne : Wsub ≠ ⊥ := by
    intro hbot
    exact hWbot ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hWleS)
  have hKsubne : Ksub ≠ ⊥ := by
    intro hbot
    exact hKbot ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hKleS)
  have hFrob : IsFrobeniusGroupWithKernelComplement Wsub Ksub := by
    apply (lemma_3_1 Wsub Ksub hWsubne hKsubne hWsubNormal hcomp).2
    intro k hk
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have hkK : (((k : Ksub) : S) : X) ∈ K := k.property
    have hkXne : (((k : Ksub) : S) : X) ≠ 1 := by
      intro hkone
      apply hk
      exact Subtype.ext (Subtype.ext hkone)
    have hwCent : (((w : S) : X)) ∈
        Subgroup.centralizer ({(((k : Ksub) : S) : X)} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp hw.2)
    have hwK : (((w : S) : X)) ∈ K := by
      rw [← hcent (((k : Ksub) : S) : X) hkK hkXne]
      exact hwCent
    have hwW : (((w : S) : X)) ∈ W := hw.1
    have hwone : (((w : S) : X)) = 1 :=
      Subgroup.disjoint_def.mp hdisj hwK hwW
    exact Subtype.ext hwone
  have hregularConj : ActsRegularly Ksub Wsub := hFrob.regular_conj_action
  have hcoprimeWK : Nat.Coprime (Nat.card Wsub) (Nat.card Ksub) :=
    ii1Theorem26_coprime_card_of_regular_action hregularConj
  have hquotCard : Nat.card (S ⧸ Wsub) = Nat.card Ksub := by
    calc
      Nat.card (S ⧸ Wsub) = Wsub.index :=
        (Subgroup.index_eq_card Wsub).symm
      _ = Nat.card Ksub := hcomp.symm.index_eq_card
  have hcoprimeQuot :
      Nat.Coprime (Nat.card Wsub) (Nat.card (S ⧸ Wsub)) := by
    simpa [hquotCard] using hcoprimeWK
  rw [eq_comm, Set.eq_univ_iff_forall]
  intro x
  let Kx : Subgroup X := K.conjBy x
  have hKxleS : Kx ≤ S := by
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    exact hSnormal.conj_mem k (hKleS hk) x
  let Kxsub : Subgroup S := Kx.subgroupOf S
  have hdisjWKx : Disjoint W Kx := by
    have hmapped :=
      Subgroup.disjoint_map (f := (MulAut.conj x).toMonoidHom)
        (MulAut.conj x).injective hdisj.symm
    change Disjoint (W.conjBy x) Kx at hmapped
    have hWconj : W.conjBy x = W := by
      change MulAut.conj x • W = W
      exact Subgroup.Normal.conj_smul_eq_self x W
    simpa [hWconj] using hmapped
  have hdisjSub : Disjoint Wsub Kxsub := by
    rw [Subgroup.disjoint_def]
    intro y hyW hyKx
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdisjWKx hyW hyKx
  have hcardKx : Nat.card Kx = Nat.card K := by
    simpa [Kx, Subgroup.conjBy] using
      (Subgroup.card_map_of_injective
        (K := K) (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective)
  have hcardKxsub : Nat.card Kxsub = Nat.card Ksub := by
    calc
      Nat.card Kxsub = Nat.card Kx :=
        natCard_subgroupOf_eq Kx S hKxleS
      _ = Nat.card K := hcardKx
      _ = Nat.card Ksub := (natCard_subgroupOf_eq K S hKleS).symm
  have hcompX : Wsub.IsComplement' Kxsub := by
    apply Subgroup.isComplement'_of_card_mul_and_disjoint
    · rw [hcardKxsub]
      exact hcomp.card_mul
    · exact hdisjSub
  obtain ⟨s, hs⟩ :=
    External.huppert_I_18_3_complements_conjugate
      Wsub Ksub Kxsub hcoprimeQuot hcomp hcompX
  have hsAmbient : K.conjBy x = K.conjBy (s : X) := by
    calc
      K.conjBy x = Kx := rfl
      _ = Kxsub.map S.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKxleS]
      _ = (Ksub.map (MulAut.conj s).toMonoidHom).map S.subtype := by
        rw [hs]
      _ = K.map (MulAut.conj (s : X)).toMonoidHom :=
        map_subgroupOf_map_conj_eq hKleS s
      _ = K.conjBy (s : X) := rfl
  obtain ⟨w, hwW, k, hkK, hsk⟩ :=
    (Subgroup.mem_sup_of_normal_left
      (s := W) (t := K) (x := ((s : S) : X))).1
      (by simpa [S] using s.property)
  have hKk : K.conjBy k = K := by
    change MulAut.conj k • K = K
    exact Subgroup.conj_smul_eq_self_of_mem hkK
  have hsConjW : K.conjBy (s : X) = K.conjBy w := by
    calc
      K.conjBy (s : X) = K.conjBy (w * k) := by rw [hsk]
      _ = (K.conjBy k).conjBy w := Subgroup.conjBy_mul K w k
      _ = K.conjBy w := by rw [hKk]
  have hnormalizes : w⁻¹ * x ∈ Subgroup.normalizer (K : Set X) := by
    apply ii1Theorem26_mem_normalizer_of_conjBy_eq
    exact Subgroup.conjBy_inv_mul_cancel K (hsAmbient.trans hsConjW).symm
  exact ⟨w, hwW, w⁻¹ * x, hnormalizes, by group⟩

private theorem ii1Theorem26_frobenius_not_mem_kernel_conjugate_mem_complement
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    {x : H} (hxnotF : x ∉ F) :
    ∃ a : F, ∃ r : D,
      (a : H)⁻¹ * x * (a : H) = (r : H) := by
  classical
  letI : F.Normal := hFrob.normal
  have hxSup : x ∈ F ⊔ D := by
    simp [hFrob.isComplement'.sup_eq_top]
  rcases (Subgroup.mem_sup_of_normal_left (s := F) (t := D) (x := x)).1 hxSup with
    ⟨k, hkF, r, hrD, hkr⟩
  let rD : D := ⟨r, hrD⟩
  have hrne : rD ≠ 1 := by
    intro hr1
    apply hxnotF
    rw [← hkr]
    have hr_eq : r = 1 := by
      simpa [rD] using congrArg Subtype.val hr1
    simp [hr_eq, hkF]
  have hcent : elementCentralizerIn F (rD : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob rD hrne
  let delta : F → F := fun a =>
    ⟨(a : H) * r * (a : H)⁻¹ * r⁻¹, by
      have hconjF : r * (a : H)⁻¹ * r⁻¹ ∈ F :=
        hFrob.normal.conj_mem ((a : H)⁻¹) (F.inv_mem a.2) r
      simpa [mul_assoc] using F.mul_mem a.2 hconjF⟩
  have hdelta_inj : Function.Injective delta := by
    intro a b hab
    have habH :
        (a : H) * r * (a : H)⁻¹ * r⁻¹ =
          (b : H) * r * (b : H)⁻¹ * r⁻¹ := congrArg Subtype.val hab
    have hcomm :
        (b : H)⁻¹ * (a : H) * r = r * ((b : H)⁻¹ * (a : H)) := by
      have hab1 :
          (a : H) * r * (a : H)⁻¹ =
            (b : H) * r * (b : H)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : H => t * r) habH
      have hab2 := congrArg (fun t : H => (b : H)⁻¹ * t * (a : H)) hab1
      simpa [mul_assoc] using hab2
    let c : F :=
      ⟨(b : H)⁻¹ * (a : H), F.mul_mem (F.inv_mem b.2) a.2⟩
    have hcCent : (c : H) ∈ elementCentralizerIn F (rD : H) := by
      refine ⟨c.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa [c, rD] using hcomm)
    have hcBot : (c : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hcCent
    have hc_eq : (c : H) = 1 := by simpa using hcBot
    apply Subtype.ext
    have h := congrArg (fun t : H => (b : H) * t) hc_eq
    simpa [c, mul_assoc] using h
  have hdelta_surj : Function.Surjective delta :=
    Finite.surjective_of_injective hdelta_inj
  rcases hdelta_surj ⟨k, hkF⟩ with ⟨a, ha⟩
  have haH : (a : H) * r * (a : H)⁻¹ * r⁻¹ = k :=
    congrArg Subtype.val ha
  have hconj_x : (a : H)⁻¹ * x * (a : H) = r := by
    rw [← hkr]
    have hk_eq : k = (a : H) * r * (a : H)⁻¹ * r⁻¹ := haH.symm
    rw [hk_eq]
    group
  exact ⟨a, rD, by simpa [rD] using hconj_x⟩

private theorem ii1Theorem26_self_normalizing_false
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    [FaithfulSMul X Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (hKne : K ≠ ⊥) (hKproper : K ≠ ⊤)
    (hTI : ∀ g : X, g ∉ K → Disjoint K (K.conjBy g)) : False := by
  classical
  obtain ⟨Y, hFrob⟩ :=
    External.Suzuki.VI.suzuki_ch6_theorem_2_3 K hKne hKproper hTI
  let alpha : Omega := Classical.choice (inferInstance : Nonempty Omega)
  let H := MulAction.stabilizer X alpha
  have htrans : MulAction.IsPretransitive X Omega :=
    ii1Theorem26_regular_pretransitive K hreg
  have hHleY : H ≤ Y := by
    intro x hxH
    by_contra hxY
    obtain ⟨a, r, hconj⟩ :=
      ii1Theorem26_frobenius_not_mem_kernel_conjugate_mem_complement
        Y K hFrob hxY
    have hrfix : (r : X) • ((a : X)⁻¹ • alpha) =
        (a : X)⁻¹ • alpha := by
      calc
        (r : X) • ((a : X)⁻¹ • alpha) =
            ((a : X)⁻¹ * x * (a : X)) • ((a : X)⁻¹ • alpha) := by rw [hconj]
        _ = (a : X)⁻¹ • (x • alpha) := by simp [mul_smul]
        _ = (a : X)⁻¹ • alpha := by
          rw [MulAction.mem_stabilizer_iff.mp hxH]
    obtain ⟨k, _hk, huniq⟩ :=
      hreg (alpha := (a : X)⁻¹ • alpha)
        (beta := (a : X)⁻¹ • alpha) (by trivial) (by trivial)
    have hrk : r = k := huniq r hrfix
    have honek : (1 : K) = k := huniq 1 (by simp)
    have hrone : r = 1 := hrk.trans honek.symm
    have hxone : x = 1 := by
      have hc := hconj
      rw [hrone] at hc
      have hc' := congrArg (fun z : X => (a : X) * z * (a : X)⁻¹) hc
      simpa [mul_assoc] using hc'
    exact hxY (by simpa [hxone])
  have hKcard : Nat.card K = Nat.card Omega :=
    ii1Theorem26_regular_card K hreg
  have hHindex : H.index = Nat.card Omega := by
    letI : MulAction.IsPretransitive X Omega := htrans
    exact MulAction.index_stabilizer_of_transitive X alpha
  have hHmul : Nat.card H * Nat.card K = Nat.card X := by
    rw [hKcard, ← hHindex]
    exact Subgroup.card_mul_index H
  have hYmul : Nat.card Y * Nat.card K = Nat.card X :=
    hFrob.isComplement'.card_mul
  have hHYcard : Nat.card H = Nat.card Y := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := K))
    exact hHmul.trans hYmul.symm
  have hHY : H = Y :=
    Subgroup.eq_of_le_of_card_ge hHleY (le_of_eq hHYcard.symm)
  have hYfix : ∀ y : Y, ∀ beta : Omega, (y : X) • beta = beta := by
    intro y beta
    letI : MulAction.IsPretransitive X Omega := htrans
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X alpha beta
    have hconjY : g⁻¹ * (y : X) * g ∈ Y := by
      simpa using hFrob.normal.conj_mem (y : X) y.property g⁻¹
    have hfixAlpha : (g⁻¹ * (y : X) * g) • alpha = alpha := by
      apply MulAction.mem_stabilizer_iff.mp
      change g⁻¹ * (y : X) * g ∈ H
      rw [hHY]
      exact hconjY
    calc
      (y : X) • beta = (y : X) • (g • alpha) := by rw [hg]
      _ = g • ((g⁻¹ * (y : X) * g) • alpha) := by
        simp [mul_smul]
      _ = g • alpha := by rw [hfixAlpha]
      _ = beta := hg
  have hYbot : Y = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    exact (faithfulSMul_iff.mp (inferInstance : FaithfulSMul X Omega)) y
      (hYfix ⟨y, hy⟩)
  exact hFrob.kernel_ne_bot hYbot

section

open Section1

private theorem ii1Theorem26_permutationCharacter_apply
    {X : Type u} {Q : Type v}
    [Group X] [Finite X] [MulAction X Q] [Fintype Q]
    (g : X) :
    (Representation.ofMulAction ℂ X Q).character g =
      (Nat.card (MulAction.fixedBy Q g) : ℂ) := by
  classical
  letI : Fintype (MulAction.fixedBy Q g) := Fintype.ofFinite _
  let sigma : Equiv.Perm Q := MulAction.toPerm g
  let T : MonoidAlgebra ℂ Q ≃ₗ[ℂ] MonoidAlgebra ℂ Q :=
    MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ sigma
  have hT : ∀ q, T (MonoidAlgebra.basis Q ℂ q) =
      MonoidAlgebra.basis Q ℂ (sigma q) := by
    intro q
    simp [T]
  have hmap : (Representation.ofMulAction ℂ X Q g) = T.toLinearMap := by
    apply (MonoidAlgebra.basis Q ℂ).ext
    intro q
    simp [T, sigma]
  change LinearMap.trace ℂ (MonoidAlgebra ℂ Q)
      (Representation.ofMulAction ℂ X Q g) = _
  rw [hmap]
  rw [Theory.Character.trace_linearEquiv_eq_ncard_fixedPoints_of_permutes_basis
    (MonoidAlgebra.basis Q ℂ) sigma T hT]
  congr 1

private theorem ii1Theorem26_permutationCharacter_isCharacter
    {X : Type u} {Q : Type v}
    [Group X] [Finite X] [MulAction X Q] [Fintype Q] [Nonempty Q]
    (htrans : MulAction.IsPretransitive X Q) :
    IsCharacter (Representation.ofMulAction ℂ X Q).character := by
  classical
  let alpha : Q := Classical.choice (inferInstance : Nonempty Q)
  let H := MulAction.stabilizer X alpha
  let toQ : X ⧸ H → Q := MulAction.ofQuotientStabilizer X alpha
  have htoQInj : Function.Injective toQ :=
    MulAction.injective_ofQuotientStabilizer X alpha
  have htoQSurj : Function.Surjective toQ := by
    intro q
    letI : MulAction.IsPretransitive X Q := htrans
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X alpha q
    exact ⟨(g : X ⧸ H), by simpa [toQ, H] using hg⟩
  let e : (X ⧸ H) ≃ Q := Equiv.ofBijective toQ ⟨htoQInj, htoQSurj⟩
  have heSmul : ∀ g : X, ∀ q : X ⧸ H, e (g • q) = g • e q := by
    intro g q
    exact MulAction.ofQuotientStabilizer_smul X alpha g q
  letI : Fintype (X ⧸ H) := Fintype.ofFinite (X ⧸ H)
  let fixedEquiv (g : X) :
      MulAction.fixedBy (X ⧸ H) g ≃ MulAction.fixedBy Q g :=
    { toFun := fun q => ⟨e q.1, by
        calc
          g • e q.1 = e (g • q.1) := (heSmul g q.1).symm
          _ = e q.1 := congrArg e q.2⟩
      invFun := fun q => ⟨e.symm q.1, by
        apply e.injective
        calc
          e (g • e.symm q.1) = g • e (e.symm q.1) := heSmul g _
          _ = g • q.1 := by rw [e.apply_symm_apply]
          _ = q.1 := q.2
          _ = e (e.symm q.1) := (e.apply_symm_apply q.1).symm⟩
      left_inv := by intro q; apply Subtype.ext; simp
      right_inv := by intro q; apply Subtype.ext; simp }
  have hcharEq : (Representation.ofMulAction ℂ X Q).character =
      (Representation.ofMulAction ℂ X (X ⧸ H)).character := by
    ext g
    rw [ii1Theorem26_permutationCharacter_apply,
      ii1Theorem26_permutationCharacter_apply]
    congr 1
    exact (Nat.card_congr (fixedEquiv g)).symm
  rw [hcharEq]
  let rho := Representation.ofMulAction ℂ X (X ⧸ H)
  exact ⟨MonoidAlgebra ℂ (X ⧸ H), inferInstance, inferInstance,
    inferInstance, rho, rfl⟩

private theorem ii1Theorem26_permutationCharacter_restrict_regular
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Fintype Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (hcard : Nat.card K = Nat.card Omega) :
    subgroupRestriction K (Representation.ofMulAction ℂ X Omega).character =
      Section6.regularCharacter K := by
  classical
  ext k
  simp only [subgroupRestriction, Section6.regularCharacter]
  rw [ii1Theorem26_permutationCharacter_apply]
  by_cases hk : k = 1
  · subst k
    simpa [Nat.card_eq_fintype_card] using hcard.symm
  · rw [if_neg hk]
    haveI : IsEmpty (MulAction.fixedBy Omega (k : X)) :=
      ⟨fun z => by
        obtain ⟨a, _ha, huniq⟩ :=
          hreg (alpha := z.1) (beta := z.1) (by trivial) (by trivial)
        have hka : k = a := huniq k z.2
        have h1a : (1 : K) = a := huniq 1 (by simp)
        exact hk (hka.trans h1a.symm)⟩
    simp

private theorem ii1Theorem26_coset_regular
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (alpha : Omega) :
    let H := MulAction.stabilizer X alpha
    IsRegularOn K (Set.univ : Set (X ⧸ H)) := by
  dsimp only
  intro q r _hq _hr
  obtain ⟨k, hk, huniq⟩ :=
    hreg
      (alpha := MulAction.ofQuotientStabilizer X alpha q)
      (beta := MulAction.ofQuotientStabilizer X alpha r)
      (by trivial) (by trivial)
  refine ⟨k, ?_, ?_⟩
  · apply MulAction.injective_ofQuotientStabilizer X alpha
    change MulAction.ofQuotientStabilizer X alpha ((k : X) • q) =
      MulAction.ofQuotientStabilizer X alpha r
    rw [MulAction.ofQuotientStabilizer_smul]
    exact hk
  · intro l hl
    apply huniq l
    calc
      (l : X) • MulAction.ofQuotientStabilizer X alpha q =
          MulAction.ofQuotientStabilizer X alpha ((l : X) • q) := by
            rw [MulAction.ofQuotientStabilizer_smul]
      _ = MulAction.ofQuotientStabilizer X alpha r := by rw [hl]

private theorem ii1Theorem26_two_pretransitive_of_coset
    {X : Type u} {Omega : Type v}
    [Group X] [MulAction X Omega]
    (alpha : Omega)
    (htrans : MulAction.IsPretransitive X Omega)
    (htwo : MulAction.IsMultiplyPretransitive X
      (X ⧸ MulAction.stabilizer X alpha) 2) :
    MulAction.IsMultiplyPretransitive X Omega 2 := by
  have hsurj : Function.Surjective
      (MulAction.ofQuotientStabilizer X alpha) := by
    intro beta
    letI : MulAction.IsPretransitive X Omega := htrans
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X alpha beta
    exact ⟨(g : X ⧸ MulAction.stabilizer X alpha), by simpa using hg⟩
  rw [MulAction.is_two_pretransitive_iff] at htwo ⊢
  intro a b c d hab hcd
  obtain ⟨qa, hqa⟩ := hsurj a
  obtain ⟨qb, hqb⟩ := hsurj b
  obtain ⟨qc, hqc⟩ := hsurj c
  obtain ⟨qd, hqd⟩ := hsurj d
  have hqab : qa ≠ qb := by
    intro h
    apply hab
    exact hqa.symm.trans ((congrArg
      (MulAction.ofQuotientStabilizer X alpha) h).trans hqb)
  have hqcd : qc ≠ qd := by
    intro h
    apply hcd
    exact hqc.symm.trans ((congrArg
      (MulAction.ofQuotientStabilizer X alpha) h).trans hqd)
  obtain ⟨g, hga, hgb⟩ := htwo hqab hqcd
  refine ⟨g, ?_, ?_⟩
  · calc
      g • a = g • MulAction.ofQuotientStabilizer X alpha qa := by rw [hqa]
      _ = MulAction.ofQuotientStabilizer X alpha (g • qa) := by
        rw [MulAction.ofQuotientStabilizer_smul]
      _ = MulAction.ofQuotientStabilizer X alpha qc := by rw [hga]
      _ = c := hqc
  · calc
      g • b = g • MulAction.ofQuotientStabilizer X alpha qb := by rw [hqb]
      _ = MulAction.ofQuotientStabilizer X alpha (g • qb) := by
        rw [MulAction.ofQuotientStabilizer_smul]
      _ = MulAction.ofQuotientStabilizer X alpha qd := by rw [hgb]
      _ = d := hqd

private theorem ii1Theorem26_two_pretransitive_of_permutationCharacter_self
    {G : Type u} {Q : Type v}
    [Group G] [Finite G] [MulAction G Q] [Fintype Q]
    (hQcard : 1 < Fintype.card Q)
    (hself : scalarProduct G
      (Representation.ofMulAction ℂ G Q).character
      (Representation.ofMulAction ℂ G Q).character = 2) :
    MulAction.IsMultiplyPretransitive G Q 2 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let fix : G → ℕ := fun g => Fintype.card (MulAction.fixedBy Q g)
  have hcardG : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hsumComplex :
      (∑ g : G, (fix g : ℂ) ^ 2) = 2 * (Nat.card G : ℂ) := by
    unfold scalarProduct at hself
    simp only [ii1Theorem26_permutationCharacter_apply, star_natCast] at hself
    field_simp [hcardG] at hself
    simpa [fix, pow_two, mul_comm] using hself
  have hsumNat : ∑ g : G, fix g ^ 2 = 2 * Nat.card G := by
    exact_mod_cast hsumComplex
  let Q2 := Quotient (MulAction.orbitRel G (Q × Q))
  letI : Fintype Q2 := Fintype.ofFinite Q2
  have hfixProd (g : G) :
      Fintype.card (MulAction.fixedBy (Q × Q) g) = fix g ^ 2 := by
    let e : MulAction.fixedBy (Q × Q) g ≃
        MulAction.fixedBy Q g × MulAction.fixedBy Q g :=
      { toFun := fun x =>
          (⟨x.1.1, congrArg Prod.fst x.2⟩,
            ⟨x.1.2, congrArg Prod.snd x.2⟩)
        invFun := fun x => ⟨(x.1.1, x.2.1), by exact Prod.ext x.1.2 x.2.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro x; ext <;> rfl }
    calc
      Fintype.card (MulAction.fixedBy (Q × Q) g) =
          Fintype.card (MulAction.fixedBy Q g ×
            MulAction.fixedBy Q g) := Fintype.card_congr e
      _ = fix g ^ 2 := by simp [fix, pow_two]
  have hburnside :
      (∑ g : G, fix g ^ 2) = Nat.card Q2 * Nat.card G := by
    have h :=
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Q × Q)
    simpa [Q2, hfixProd, Nat.card_eq_fintype_card] using h
  have hQ2card : Nat.card Q2 = 2 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := G))
    exact hburnside.symm.trans hsumNat
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hQcard
  let qdiag : Q2 := Quotient.mk (MulAction.orbitRel G (Q × Q)) (a, a)
  let qoff : Q2 := Quotient.mk (MulAction.orbitRel G (Q × Q)) (a, b)
  have hqoff : qoff ≠ qdiag := by
    intro h
    have hrel := Quotient.exact h
    rcases hrel with ⟨g, hg⟩
    have hga : g • a = a := congrArg Prod.fst hg
    have hgb : g • a = b := congrArg Prod.snd hg
    exact hab (hga.symm.trans hgb)
  obtain ⟨qother, hqother, hqunique⟩ :=
    (Nat.card_eq_two_iff' qdiag).mp hQ2card
  have hqoffOther : qoff = qother := hqunique qoff hqoff
  rw [MulAction.is_two_pretransitive_iff]
  intro c d e f hcd hef
  let qcd : Q2 := Quotient.mk (MulAction.orbitRel G (Q × Q)) (c, d)
  let qef : Q2 := Quotient.mk (MulAction.orbitRel G (Q × Q)) (e, f)
  have hqcd : qcd ≠ qdiag := by
    intro h
    have hrel := Quotient.exact h
    rcases hrel with ⟨g, hg⟩
    have hgc : g • a = c := congrArg Prod.fst hg
    have hgd : g • a = d := congrArg Prod.snd hg
    exact hcd (hgc.symm.trans hgd)
  have hqef : qef ≠ qdiag := by
    intro h
    have hrel := Quotient.exact h
    rcases hrel with ⟨g, hg⟩
    have hge : g • a = e := congrArg Prod.fst hg
    have hgf : g • a = f := congrArg Prod.snd hg
    exact hef (hge.symm.trans hgf)
  have hqcdOther : qcd = qother := hqunique qcd hqcd
  have hqefOther : qef = qother := hqunique qef hqef
  have hrel := Quotient.exact (hqefOther.trans hqcdOther.symm)
  rcases hrel with ⟨g, hg⟩
  exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

private theorem ii1Theorem26_permutationCharacter_principal
    {G : Type u} {Q : Type v}
    [Group G] [Finite G] [MulAction G Q] [Fintype Q] [Nonempty Q]
    (htrans : MulAction.IsPretransitive G Q) :
    scalarProduct G (Representation.ofMulAction ℂ G Q).character
      (principalCharacter G) = 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let fix : G → ℕ := fun g => Fintype.card (MulAction.fixedBy Q g)
  let Q1 := Quotient (MulAction.orbitRel G Q)
  letI : Fintype Q1 := Fintype.ofFinite Q1
  have hQ1card : Fintype.card Q1 = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let q : Q := Classical.choice (inferInstance : Nonempty Q)
    let q0 : Q1 := Quotient.mk (MulAction.orbitRel G Q) q
    refine ⟨q0, ?_⟩
    intro z
    rw [← Quotient.out_eq z]
    apply Quotient.sound
    letI : MulAction.IsPretransitive G Q := htrans
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G q (Quotient.out z)
    exact ⟨g, hg⟩
  have hsum : ∑ g : G, fix g = Nat.card G := by
    have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G Q
    simpa [fix, Q1, hQ1card, Nat.card_eq_fintype_card] using h
  unfold scalarProduct principalCharacter
  simp only [star_one, mul_one, ii1Theorem26_permutationCharacter_apply]
  simp only [Nat.card_eq_fintype_card]
  have hsum' :
      (∑ g : G, Fintype.card (MulAction.fixedBy Q g)) = Fintype.card G := by
    simpa [fix, Nat.card_eq_fintype_card] using hsum
  rw [show (∑ g : G, (Fintype.card (MulAction.fixedBy Q g) : ℂ)) =
      (Fintype.card G : ℂ) by exact_mod_cast hsum']
  have hcardG : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  field_simp [hcardG]

private theorem ii1Theorem26_permutationCharacter_self_of_decomposition
    {G : Type u} {I : Type w}
    [Group G] [Finite G] [Finite I] [DecidableEq I]
    (psi : I → ClassFunction G)
    (hirr : ∀ i, IsIrreducibleCharacterOnGroup (psi i))
    (hpair : Pairwise (fun i j => psi i ≠ psi j))
    {pi : ClassFunction G}
    (hdecomp : pi = weightedFamilySum (fun _ : I => (1 : ℂ)) psi) :
    scalarProduct G pi pi = (Nat.card I : ℂ) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  have horth : ∀ i j,
      scalarProduct G (psi i) (psi j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact scalarProduct_irreducibleCharacter_self (hirr i)
    · rw [if_neg hij]
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hirr i) (hirr j) (hpair hij)
  rw [hdecomp, scalarProduct_weightedFamilySum_left]
  simp_rw [scalarProduct_weightedFamilySum_right]
  simp [horth, Nat.card_eq_fintype_card]

private theorem ii1Theorem26_decomposition_card_eq_two_of_le_two
    {G : Type u} {Q : Type v} {I : Type w}
    [Group G] [Finite G] [MulAction G Q] [Fintype Q] [Nonempty Q]
    [Finite I] [DecidableEq I]
    (hQcard : 1 < Fintype.card Q)
    (htrans : MulAction.IsPretransitive G Q)
    (psi : I → ClassFunction G)
    (hirr : ∀ i, IsIrreducibleCharacterOnGroup (psi i))
    (hdecomp : (Representation.ofMulAction ℂ G Q).character =
      weightedFamilySum (fun _ : I => (1 : ℂ)) psi)
    (hle : Nat.card I ≤ 2) :
    Nat.card I = 2 := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  have hprincipal := ii1Theorem26_permutationCharacter_principal htrans
  have hex : ∃ i : I, psi i = principalCharacter G := by
    by_contra h
    push_neg at h
    have hzero : ∀ i : I,
        scalarProduct G (psi i) (principalCharacter G) = 0 := by
      intro i
      exact scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
        (hirr i) (h i)
    rw [hdecomp, scalarProduct_weightedFamilySum_left] at hprincipal
    simp [hzero] at hprincipal
  obtain ⟨i0, hi0⟩ := hex
  letI : Nonempty I := ⟨i0⟩
  have hpos : 0 < Nat.card I := Nat.card_pos
  by_contra hne
  have hcardOne : Nat.card I = 1 := by omega
  have hcardOne' : Fintype.card I = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardOne
  letI : Subsingleton I :=
    Finite.card_le_one_iff_subsingleton.mp (le_of_eq hcardOne)
  have hpiPrincipal :
      (Representation.ofMulAction ℂ G Q).character = principalCharacter G := by
    rw [hdecomp]
    ext g
    simp only [weightedFamilySum]
    have hfun : (fun i : I => (1 : ℂ) * psi i g) =
        fun _i : I => principalCharacter G g := by
      funext i
      rw [Subsingleton.elim i i0, hi0]
      simp
    rw [hfun]
    simp [hcardOne']
  have hone : (Nat.card Q : ℂ) = 1 := by
    calc
      (Nat.card Q : ℂ) =
          (Representation.ofMulAction ℂ G Q).character (1 : G) := by
            rw [ii1Theorem26_permutationCharacter_apply]
            simp
      _ = principalCharacter G (1 : G) := congrFun hpiPrincipal 1
      _ = 1 := rfl
  have hQone : Fintype.card Q = 1 := by
    have hQoneNat : Nat.card Q = 1 := by exact_mod_cast hone
    simpa [Nat.card_eq_fintype_card] using hQoneNat
  omega

private theorem ii1Theorem26_two_pretransitive_of_decomposition_card_le_two
    {G : Type u} {Q : Type v} {I : Type w}
    [Group G] [Finite G] [MulAction G Q] [Fintype Q] [Nonempty Q]
    [Finite I] [DecidableEq I]
    (hQcard : 1 < Fintype.card Q)
    (htrans : MulAction.IsPretransitive G Q)
    (psi : I → ClassFunction G)
    (hirr : ∀ i, IsIrreducibleCharacterOnGroup (psi i))
    (hpair : Pairwise (fun i j => psi i ≠ psi j))
    (hdecomp : (Representation.ofMulAction ℂ G Q).character =
      weightedFamilySum (fun _ : I => (1 : ℂ)) psi)
    (hle : Nat.card I ≤ 2) :
    MulAction.IsMultiplyPretransitive G Q 2 := by
  have hcard := ii1Theorem26_decomposition_card_eq_two_of_le_two
    hQcard htrans psi hirr hdecomp hle
  have hself := ii1Theorem26_permutationCharacter_self_of_decomposition
    psi hirr hpair hdecomp
  rw [hcard] at hself
  exact ii1Theorem26_two_pretransitive_of_permutationCharacter_self hQcard hself

private theorem ii1Theorem26_two_pretransitive_of_frobenius_complement_card
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K)
    (alpha : Omega)
    (hOmegaCard : Nat.card K = Nat.card Omega)
    (hFrob : IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf (Subgroup.normalizer (K : Set X)))
      (MulAction.stabilizer (Subgroup.normalizer (K : Set X)) alpha))
    (hcard :
      Nat.card (MulAction.stabilizer
        (Subgroup.normalizer (K : Set X)) alpha) =
      Nat.card (K.subgroupOf (Subgroup.normalizer (K : Set X))) - 1) :
    MulAction.IsMultiplyPretransitive X Omega 2 := by
  classical
  let N := Subgroup.normalizer (K : Set X)
  let F := K.subgroupOf N
  let D := MulAction.stabilizer N alpha
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change Nat.card D = Nat.card F - 1 at hcard
  let orbitAt : K → Omega := fun k => (k : X) • alpha
  have horbitSurj : Function.Surjective orbitAt := by
    intro beta
    obtain ⟨k, hk, _huniq⟩ :=
      hreg (alpha := alpha) (beta := beta) (by trivial) (by trivial)
    exact ⟨k, hk⟩
  letI : Finite Omega := Finite.of_surjective orbitAt horbitSurj
  letI : Fintype Omega := Fintype.ofFinite Omega
  letI : Fintype K := Fintype.ofFinite K
  let Omega0 := {beta : Omega // beta ≠ alpha}
  letI : Fintype Omega0 := Fintype.ofFinite Omega0
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype F := Fintype.ofFinite F
  have hKleN : K ≤ N := Subgroup.le_normalizer
  have hFcard : Nat.card F = Nat.card K :=
    natCard_subgroupOf_eq K N hKleN
  have hOmega0card : Fintype.card Omega0 = Fintype.card D := by
    have hKOmega : Fintype.card K = Fintype.card Omega := by
      simpa [Nat.card_eq_fintype_card] using hOmegaCard
    have hFK : Fintype.card F = Fintype.card K := by
      simpa [Nat.card_eq_fintype_card] using hFcard
    have hDF : Fintype.card D = Fintype.card F - 1 := by
      simpa [Nat.card_eq_fintype_card] using hcard
    calc
      Fintype.card Omega0 = Fintype.card Omega - 1 := by
        simpa [Omega0] using
          (Fintype.card_subtype_compl (fun beta : Omega => beta = alpha))
      _ = Fintype.card K - 1 := by rw [hKOmega]
      _ = Fintype.card F - 1 := by rw [hFK]
      _ = Fintype.card D := hDF.symm
  have hDtrans : ∀ beta gamma : Omega0, ∃ d : D,
      ((d : N) : X) • (beta : Omega) = gamma := by
    intro beta gamma
    let orbitMap : D → Omega0 := fun d =>
      ⟨((d : N) : X) • (beta : Omega), by
        intro hEq
        apply beta.property
        have hdAlpha : ((d : N) : X) • alpha = alpha := d.property
        exact (MulAction.toPerm (((d : N) : X))).injective
          (hEq.trans hdAlpha.symm)⟩
    have horbitInj : Function.Injective orbitMap := by
      intro d1 d2 hd12
      let d : D := d2⁻¹ * d1
      have hdfixBeta : ((d : N) : X) • (beta : Omega) = beta := by
        have hd12' : ((d1 : N) : X) • (beta : Omega) =
            ((d2 : N) : X) • (beta : Omega) := by
          simpa [orbitMap] using congrArg Subtype.val hd12
        calc
          ((d : N) : X) • (beta : Omega) =
              ((d2 : N) : X)⁻¹ •
                (((d1 : N) : X) • (beta : Omega)) := by
                  simp [d, mul_smul]
          _ = ((d2 : N) : X)⁻¹ •
                (((d2 : N) : X) • (beta : Omega)) := by rw [hd12']
          _ = beta := inv_smul_smul _ _
      have hdfixAlpha : ((d : N) : X) • alpha = alpha := d.property
      obtain ⟨k, hk, huniq⟩ :=
        hreg (alpha := alpha) (beta := (beta : Omega))
          (by trivial) (by trivial)
      have hkne : (k : X) ≠ 1 := by
        intro hkone
        apply beta.property
        calc
          (beta : Omega) = (k : X) • alpha := hk.symm
          _ = alpha := by rw [hkone]; simp
      have hdNorm : ((d : N) : X) ∈ Subgroup.normalizer (K : Set X) :=
        (d : N).property
      have hconjK :
          ((d : N) : X) * (k : X) * ((d : N) : X)⁻¹ ∈ K := by
        exact (Subgroup.mem_normalizer_iff.mp hdNorm (k : X)).1 k.property
      let kConj : K :=
        ⟨((d : N) : X) * (k : X) * ((d : N) : X)⁻¹, hconjK⟩
      have hkConjFix : (kConj : X) • alpha = beta := by
        calc
          (kConj : X) • alpha =
              ((d : N) : X) •
                ((k : X) • (((d : N) : X)⁻¹ • alpha)) := by
                  simp [kConj, mul_smul]
          _ = ((d : N) : X) • ((k : X) • alpha) := by
            rw [show ((d : N) : X)⁻¹ • alpha = alpha by
              calc
                ((d : N) : X)⁻¹ • alpha =
                    ((d : N) : X)⁻¹ • (((d : N) : X) • alpha) := by
                      rw [hdfixAlpha]
                _ = alpha := inv_smul_smul _ _]
          _ = ((d : N) : X) • beta := by rw [hk]
          _ = beta := hdfixBeta
      have hkConjEq : kConj = k := by
        have h1 := huniq kConj hkConjFix
        have h2 := huniq k hk
        exact h1.trans h2.symm
      have hconjEq :
          ((d : N) : X) * (k : X) * ((d : N) : X)⁻¹ = (k : X) :=
        congrArg Subtype.val hkConjEq
      have hcomm : ((d : N) : X) * (k : X) =
          (k : X) * ((d : N) : X) := by
        have h := congrArg (fun z : X => z * ((d : N) : X)) hconjEq
        simpa [mul_assoc] using h
      have hdK : ((d : N) : X) ∈ K := by
        rw [← hcent (k : X) k.property hkne]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      have hdBot : (d : N) ∈ (⊥ : Subgroup N) :=
        hFrob.isComplement'.disjoint.le_bot ⟨hdK, d.property⟩
      have hdOne : d = 1 := by
        apply Subtype.ext
        simpa using hdBot
      apply Subtype.ext
      have h := congrArg (fun z : N => (d2 : N) * z)
        (congrArg Subtype.val hdOne)
      simpa [d, mul_assoc] using h
    have horbitSurj : Function.Surjective orbitMap :=
      (Fintype.bijective_iff_injective_and_card orbitMap).mpr
        ⟨horbitInj, hOmega0card.symm⟩ |>.2
    obtain ⟨d, hd⟩ := horbitSurj gamma
    exact ⟨d, congrArg Subtype.val hd⟩
  have htrans : MulAction.IsPretransitive X Omega := by
    exact ⟨fun a b => by
      obtain ⟨k, hk, _huniq⟩ :=
        hreg (alpha := a) (beta := b) (by trivial) (by trivial)
      exact ⟨(k : X), hk⟩⟩
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c e hab hce
  letI : MulAction.IsPretransitive X Omega := htrans
  obtain ⟨x, hxa⟩ := MulAction.exists_smul_eq X a alpha
  obtain ⟨y, hyc⟩ := MulAction.exists_smul_eq X c alpha
  have hxb : x • b ≠ alpha := by
    intro h
    apply hab
    exact (MulAction.toPerm x).injective (hxa.trans h.symm)
  have hye : y • e ≠ alpha := by
    intro h
    apply hce
    exact (MulAction.toPerm y).injective (hyc.trans h.symm)
  obtain ⟨d, hd⟩ := hDtrans ⟨x • b, hxb⟩ ⟨y • e, hye⟩
  refine ⟨y⁻¹ * ((d : N) : X) * x, ?_, ?_⟩
  · calc
      (y⁻¹ * ((d : N) : X) * x) • a =
          y⁻¹ • (((d : N) : X) • (x • a)) := by simp [mul_smul]
      _ = y⁻¹ • (((d : N) : X) • alpha) := by rw [hxa]
      _ = y⁻¹ • alpha := by
        rw [show ((d : N) : X) • alpha = alpha from d.property]
      _ = c := by rw [← hyc, inv_smul_smul]
  · calc
      (y⁻¹ * ((d : N) : X) * x) • b =
          y⁻¹ • (((d : N) : X) • (x • b)) := by simp [mul_smul]
      _ = y⁻¹ • (y • e) := by rw [hd]
      _ = e := inv_smul_smul _ _

private theorem ii1Theorem26_irreducible_hasPositiveDegree
    {G : Type*} [Group G] [Finite G]
    {phi : ClassFunction G}
    (hirr : IsIrreducibleCharacterOnGroup phi) :
    ∃ n : ℕ, 0 < n ∧ degree phi = (n : ℂ) := by
  rcases hirr with ⟨n, rho, hrho, hphi⟩
  have hdeg : degree phi = (n : ℂ) := by
    rw [hphi]
    simp [degree, Representation.character]
  have hnne : n ≠ 0 := by
    intro hn
    apply Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup phi
      ⟨n, rho, hrho, hphi⟩
    rw [hdeg, hn]
    norm_num
  exact ⟨n, Nat.pos_of_ne_zero hnne, hdeg⟩

private theorem ii1Theorem26_coherentExtension_signed_irreducible_family
    {L G : Type u} [Group L] [Finite L] [Group G] [Finite G]
    {Y : Finset (Section1.ClassFunction L)}
    {T tau : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (htau : Section6.coherentExtension Y T tau)
    (hYirr : ∀ eta : Y,
      Section1.IsIrreducibleCharacterOnGroup (eta : Section1.ClassFunction L)) :
    ∃ epsilon : Y → ℂ, ∃ mu : Y → Section1.ClassFunction G,
      (∀ eta, Section1.IsSign (epsilon eta)) ∧
        (∀ eta, Section1.IsIrreducibleCharacterOnGroup (mu eta)) ∧
          (∀ eta : Y, tau (eta : Section1.ClassFunction L) =
            epsilon eta • mu eta) ∧ Function.Injective mu := by
  classical
  have hsigned : ∀ eta : Y,
      Section3.IsSignedIrreducibleCharacter
        (tau (eta : Section1.ClassFunction L)) := by
    intro eta
    exact Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      htau eta.2 (hYirr eta)
  choose epsilon hepsilon mu hmu htau_mu using hsigned
  refine ⟨epsilon, mu, hepsilon, hmu, htau_mu, ?_⟩
  intro eta xi hmu_eq
  apply Subtype.ext
  by_contra heta_xi
  have hsource_zero :
      Section1.scalarProduct L (eta : Section1.ClassFunction L)
        (xi : Section1.ClassFunction L) = 0 :=
    Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hYirr eta) (hYirr xi) heta_xi
  have himage_zero :
      Section1.scalarProduct G
        (tau (eta : Section1.ClassFunction L))
        (tau (xi : Section1.ClassFunction L)) = 0 := by
    rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
      htau.1 eta.2 xi.2, hsource_zero]
  rw [htau_mu eta, htau_mu xi, hmu_eq,
    Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
    Section1.scalarProduct_irreducibleCharacter_self (hmu xi)] at himage_zero
  rcases hepsilon eta with hepsilon_eta | hepsilon_eta <;>
    rcases hepsilon xi with hepsilon_xi | hepsilon_xi <;>
      simp [hepsilon_eta, hepsilon_xi] at himage_zero

private theorem ii1Theorem26_coherent_signed_family_common
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (F : Subgroup N) [F.Normal]
    (Y : Finset (ClassFunction N))
    (hYirr : ∀ eta : Y,
      IsIrreducibleCharacterOnGroup (eta : ClassFunction N))
    (hYbot : Section6.inducedKernelFamily F ⊥ Y)
    (hindPunct : ∀ phi : ClassFunction N,
      Section5.integerSpanOn Y Section5.puncturedSet phi →
        Theory.Character.IsVirtualCharacter (Section1.inducedCFLinear N phi) ∧
          Section1.supportedOn (Section1.inducedCFLinear N phi)
            Section5.puncturedSet)
    (hdegree : ∀ eta xi : Y,
      degree (eta : ClassFunction N) = degree (xi : ClassFunction N))
    (hcoh : Section5.IsCoherentTriple Section5.puncturedSet Y
      (Section1.inducedCFLinear N)) :
    ∃ tau : ClassFunction N →ₗ[ℂ] ClassFunction G,
      ∃ epsilon : Y → ℂ, ∃ mu : Y → ClassFunction G,
        Section6.coherentExtension Y (Section1.inducedCFLinear N) tau ∧
        (∀ eta, IsSign (epsilon eta)) ∧
        (∀ eta, IsIrreducibleCharacterOnGroup (mu eta)) ∧
        (∀ eta : Y, tau (eta : ClassFunction N) = epsilon eta • mu eta) ∧
        Function.Injective mu ∧
        (∀ eta xi, epsilon eta = epsilon xi) ∧
        (∀ eta xi, degree (mu eta) = degree (mu xi)) ∧
        ∀ eta xi x,
          x ∉ Section2.conjugateSet
            (Section6.subgroupImagePuncturedSet N F) →
          mu eta x = mu xi x := by
  classical
  rcases hcoh with
    ⟨_hsource, _hnonempty, tau, htauIso, htauVirtual, htauAgree⟩
  have htau :
      Section6.coherentExtension Y (Section1.inducedCFLinear N) tau :=
    ⟨htauIso, htauVirtual, htauAgree⟩
  obtain ⟨epsilon, mu, hepsilon, hmuIrr, htauMu, hmuInj⟩ :=
    ii1Theorem26_coherentExtension_signed_irreducible_family
      htau hYirr
  have hspan : ∀ eta xi : Y,
      Section5.integerSpanOn Y Section5.puncturedSet
        ((eta : ClassFunction N) - (xi : ClassFunction N)) := by
    intro eta xi
    refine ⟨Section5.integerSpan_sub
      (Section5.integerSpan_of_mem Y eta.property)
      (Section5.integerSpan_of_mem Y xi.property), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change degree (eta : ClassFunction N) - degree (xi : ClassFunction N) = 0
    rw [hdegree eta xi]
    simp
  have hdegreeTau : ∀ eta xi : Y,
      degree (tau ((eta : ClassFunction N) - (xi : ClassFunction N))) = 0 := by
    intro eta xi
    rw [htauAgree _ (hspan eta xi)]
    exact (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).1
      (hindPunct _ (hspan eta xi)).2
  have hepsilonEq : ∀ eta xi : Y, epsilon eta = epsilon xi := by
    intro eta xi
    obtain ⟨nη, hnη, hdegη⟩ :=
      ii1Theorem26_irreducible_hasPositiveDegree (G := G) (hmuIrr eta)
    obtain ⟨nξ, hnξ, hdegξ⟩ :=
      ii1Theorem26_irreducible_hasPositiveDegree (G := G) (hmuIrr xi)
    have hzero :
        degree (epsilon eta • mu eta - epsilon xi • mu xi) = 0 := by
      simpa [map_sub, htauMu] using hdegreeTau eta xi
    change epsilon eta * degree (mu eta) - epsilon xi * degree (mu xi) = 0 at hzero
    rcases hepsilon eta with hη | hη <;>
      rcases hepsilon xi with hξ | hξ
    · simpa [hη, hξ]
    · exfalso
      rw [hη, hξ, hdegη, hdegξ] at hzero
      have hsum : ((nη + nξ : ℕ) : ℂ) = 0 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzero
      have hnat : nη + nξ = 0 := by exact_mod_cast hsum
      omega
    · exfalso
      rw [hη, hξ, hdegη, hdegξ] at hzero
      have hsum : ((nη + nξ : ℕ) : ℂ) = 0 := by
        have hh := congrArg (fun z : ℂ => -z) hzero
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh
      have hnat : nη + nξ = 0 := by exact_mod_cast hsum
      omega
    · simpa [hη, hξ]
  have hmuDegree : ∀ eta xi : Y, degree (mu eta) = degree (mu xi) := by
    intro eta xi
    have hzero := hdegreeTau eta xi
    rw [map_sub, htauMu eta, htauMu xi, hepsilonEq xi eta] at hzero
    rcases hepsilon eta with heta | heta
    · rw [heta] at hzero
      exact sub_eq_zero.mp (by simpa [degree] using hzero)
    · rw [heta] at hzero
      exact (sub_eq_zero.mp (by
        simpa [degree, sub_eq_add_neg, add_comm] using hzero)).symm
  have hmuCommon : ∀ eta xi x,
      x ∉ Section2.conjugateSet
        (Section6.subgroupImagePuncturedSet N F) →
      mu eta x = mu xi x := by
    intro eta xi x hx
    have hCFOn : Section2.CFOn N
        (Section6.subgroupImagePuncturedSet N F)
        ((eta : ClassFunction N) - (xi : ClassFunction N)) :=
      Section6.theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn
        hYbot (hspan eta xi)
    have hzeroInd : Section1.inducedCF N
        ((eta : ClassFunction N) - (xi : ClassFunction N)) x = 0 :=
      Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn
        N _ hCFOn hx
    have hzeroTau :
        tau ((eta : ClassFunction N) - (xi : ClassFunction N)) x = 0 := by
      rw [htauAgree _ (hspan eta xi)]
      exact hzeroInd
    rw [map_sub, htauMu eta, htauMu xi, hepsilonEq xi eta] at hzeroTau
    have hepsne : epsilon eta ≠ 0 := by
      rcases hepsilon eta with heta | heta <;> simp [heta]
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hepsne
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub] using hzeroTau
  exact ⟨tau, epsilon, mu, htau, hepsilon, hmuIrr, htauMu, hmuInj,
    hepsilonEq, hmuDegree, hmuCommon⟩



private theorem ii1Theorem26_scalarProduct_subgroupOf_transport
    {G : Type u} [Group G] [Finite G]
    (K N : Subgroup G) (hKN : K ≤ N)
    (theta : ClassFunction K) (phi : ClassFunction G) :
    let F := K.subgroupOf N
    let e : F ≃* K := Subgroup.subgroupOfEquivOfLe hKN
    scalarProduct F
        (classFunctionLinearEquivOfMulEquiv e.symm theta)
        (subgroupRestriction F (subgroupRestriction N phi)) =
      scalarProduct K theta (subgroupRestriction K phi) := by
  classical
  let F := K.subgroupOf N
  let e : F ≃* K := Subgroup.subgroupOfEquivOfLe hKN
  let thetaF := classFunctionLinearEquivOfMulEquiv e.symm theta
  let phiF := subgroupRestriction F (subgroupRestriction N phi)
  have htheta : classFunctionLinearEquivOfMulEquiv e thetaF = theta := by
    exact (classFunctionLinearEquivOfMulEquiv e).apply_symm_apply theta
  have hphi : classFunctionLinearEquivOfMulEquiv e phiF =
      subgroupRestriction K phi := by
    ext k
    rfl
  calc
    scalarProduct F thetaF phiF =
        scalarProduct K (classFunctionLinearEquivOfMulEquiv e thetaF)
          (classFunctionLinearEquivOfMulEquiv e phiF) := by
      symm
      exact scalarProduct_classFunctionLinearEquivOfMulEquiv e thetaF phiF
    _ = scalarProduct K theta (subgroupRestriction K phi) := by
      rw [htheta, hphi]

private theorem ii1Theorem26_exists_irreducible_constituent_of_subgroupRestriction
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ θ : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0 := by
  rcases hχ with ⟨n, ρ, hρirr, hρchar⟩
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  letI : Nontrivial (Fin n → ℂ) :=
    Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨φ, hφirr⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρK
  letI : Nontrivial φ.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial φ.toRepresentation
  let incl : Theory.Representation.RepMap φ.toRepresentation ρK := by
    refine Theory.Representation.RepMap.mk φ.toSubmodule.subtype ?_
    intro k
    ext v
    rfl
  have hincl_ne : incl ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : φ.toSubmodule)
    have hval : incl v = 0 := by
      simpa using
        congrArg (fun f : Theory.Representation.RepMap φ.toRepresentation ρK => f v) hzero
    have hsub : v = 0 := by
      apply Subtype.ext
      simpa [incl] using hval
    exact hv hsub
  have hinner_res :
      Section1.scalarProduct K ρK.character φ.toRepresentation.character ≠ 0 := by
    have hfinpos :
        0 < Module.finrank ℂ
          (Representation.IntertwiningMap φ.toRepresentation ρK) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨incl, hincl_ne⟩
    rw [Section1.scalarProduct_representation_char_eq_finrank]
    exact_mod_cast (Nat.ne_of_gt hfinpos)
  have hresChar :
      Section1.subgroupRestriction K χ = ρK.character := by
    ext k
    simp [ρK, Section1.subgroupRestriction, hρchar, Representation.character]
  refine ⟨φ.toRepresentation.character, ?_, ?_⟩
  · refine ⟨Module.finrank ℂ φ.toSubmodule,
      Section1.standardizeRepresentation φ.toRepresentation, ?_, ?_⟩
    · exact Section1.standardizeRepresentation_irreducible φ.toRepresentation hφirr
    · ext k
      symm
      exact Section1.standardizeRepresentation_character φ.toRepresentation k
  · have hinner_res' :
        Section1.scalarProduct K (Section1.subgroupRestriction K χ)
          φ.toRepresentation.character ≠ 0 := by
      simpa [hresChar] using hinner_res
    exact
      (Section1.scalarProduct_ne_zero_swap
        φ.toRepresentation.character (Section1.subgroupRestriction K χ)).2 hinner_res'

private theorem ii1Theorem26_nonprincipal_constituent_mem_exceptional
    {G : Type u} {I : Type w}
    [Group G] [Finite G] [Fintype I] [DecidableEq I]
    (K N : Subgroup G) (hKN : K ≤ N)
    (Y : Finset (ClassFunction N))
    (hYbot : Section6.inducedKernelFamily (K.subgroupOf N) ⊥ Y)
    (hYdegree : ∀ eta xi : Y,
      degree (eta : ClassFunction N) = degree (xi : ClassFunction N))
    (tau : ClassFunction N →ₗ[ℂ] ClassFunction G)
    (htau : Section6.coherentExtension Y (Section1.inducedCFLinear N) tau)
    (epsilon : Y → ℂ) (mu : Y → ClassFunction G)
    (hmuIrr : ∀ eta, IsIrreducibleCharacterOnGroup (mu eta))
    (htauMu : ∀ eta : Y, tau (eta : ClassFunction N) = epsilon eta • mu eta)
    (psi : I → ClassFunction G)
    (hpsiIrr : ∀ i, IsIrreducibleCharacterOnGroup (psi i))
    (hcover : ∀ theta : ClassFunction K,
      IsIrreducibleCharacterOnGroup theta →
      ∃ i, ∀ j,
        scalarProduct K theta (subgroupRestriction K (psi j)) =
          if j = i then 1 else 0)
    (i0 : I) (hi0 : psi i0 = principalCharacter G)
    (hcard : 3 ≤ Fintype.card I) :
    ∀ i, i ≠ i0 → ∃ eta : Y, psi i = mu eta := by
  classical
  have hprincipalIrr :
      IsIrreducibleCharacterOnGroup (principalCharacter K) := by
    have hchar : principalCharacter K =
        (Representation.trivial ℂ K ℂ).character := by
      ext k
      simp [principalCharacter, Representation.character, Representation.isTrivial_def]
    rw [hchar]
    exact isIrreducibleCharacterOnGroup_of_representation
      (Representation.trivial ℂ K ℂ)
      Theory.Character.trivial_complex_irreducible
  have hprincipalZero : ∀ i, i ≠ i0 →
      scalarProduct K (principalCharacter K)
        (subgroupRestriction K (psi i)) = 0 := by
    obtain ⟨j0, hj0⟩ := hcover (principalCharacter K) hprincipalIrr
    have hi0coef : scalarProduct K (principalCharacter K)
        (subgroupRestriction K (psi i0)) = 1 := by
      rw [hi0]
      have hres : subgroupRestriction K (principalCharacter G) =
          principalCharacter K := by
        ext k
        rfl
      rw [hres]
      exact scalarProduct_irreducibleCharacter_self hprincipalIrr
    have hj0eq : j0 = i0 := by
      have h := hj0 i0
      by_contra hne
      rw [ite_eq_right (Ne.symm hne)] at h
      rw [hi0coef] at h
      norm_num at h
    subst j0
    intro i hi
    simpa [hi] using hj0 i
  intro i hi
  by_contra hnot
  push_neg at hnot
  obtain ⟨thetaIn, hthetaInIrr, hthetaInNeZero⟩ :=
    ii1Theorem26_exists_irreducible_constituent_of_subgroupRestriction
      K (hpsiIrr i)
  have hthetaInNePrincipal : thetaIn ≠ principalCharacter K := by
    intro htheta
    rw [htheta, hprincipalZero i hi] at hthetaInNeZero
    exact hthetaInNeZero rfl
  obtain ⟨iIn, hiIn⟩ := hcover thetaIn hthetaInIrr
  have hiInEq : iIn = i := by
    by_contra hne
    have h := hiIn i
    rw [ite_eq_right (Ne.symm hne)] at h
    exact hthetaInNeZero h
  have hthetaInCoeff : scalarProduct K thetaIn
      (subgroupRestriction K (psi i)) = 1 := by
    simpa [hiInEq] using hiIn i
  let equivI := Fintype.equivFin I
  obtain ⟨k, hki, hki0⟩ := Fin.exists_ne_and_ne_of_two_lt
    (equivI i) (equivI i0) (by omega)
  let j : I := equivI.symm k
  have hji : j ≠ i := by
    intro h
    apply hki
    simpa [j] using congrArg equivI h
  have hji0 : j ≠ i0 := by
    intro h
    apply hki0
    simpa [j] using congrArg equivI h
  obtain ⟨thetaOut, hthetaOutIrr, hthetaOutNeZero⟩ :=
    ii1Theorem26_exists_irreducible_constituent_of_subgroupRestriction
      K (hpsiIrr j)
  have hthetaOutNePrincipal : thetaOut ≠ principalCharacter K := by
    intro htheta
    rw [htheta, hprincipalZero j hji0] at hthetaOutNeZero
    exact hthetaOutNeZero rfl
  obtain ⟨iOut, hiOut⟩ := hcover thetaOut hthetaOutIrr
  have hiOutEq : iOut = j := by
    by_contra hne
    have h := hiOut j
    rw [ite_eq_right (Ne.symm hne)] at h
    exact hthetaOutNeZero h
  have hthetaOutCoeff : scalarProduct K thetaOut
      (subgroupRestriction K (psi i)) = 0 := by
    have hiiOut : i ≠ iOut := by simpa [hiOutEq] using hji.symm
    simpa [hiiOut] using hiOut i
  let F := K.subgroupOf N
  let e : F ≃* K := Subgroup.subgroupOfEquivOfLe hKN
  let thetaInF : ClassFunction F :=
    classFunctionLinearEquivOfMulEquiv e.symm thetaIn
  let thetaOutF : ClassFunction F :=
    classFunctionLinearEquivOfMulEquiv e.symm thetaOut
  have hthetaInFIrr : IsIrreducibleCharacterOnGroup thetaInF :=
    isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      e.symm hthetaInIrr
  have hthetaOutFIrr : IsIrreducibleCharacterOnGroup thetaOutF :=
    isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
      e.symm hthetaOutIrr
  have hthetaInFNePrincipal : thetaInF ≠ principalCharacter F := by
    intro htheta
    apply hthetaInNePrincipal
    calc
      thetaIn = classFunctionLinearEquivOfMulEquiv e
          (classFunctionLinearEquivOfMulEquiv e.symm thetaIn) :=
        (classFunctionLinearEquivOfMulEquiv e).apply_symm_apply thetaIn |>.symm
      _ = classFunctionLinearEquivOfMulEquiv e (principalCharacter F) := by
        rw [← htheta]
      _ = principalCharacter K :=
        principalCharacter_classFunctionLinearEquivOfMulEquiv e
  have hthetaOutFNePrincipal : thetaOutF ≠ principalCharacter F := by
    intro htheta
    apply hthetaOutNePrincipal
    calc
      thetaOut = classFunctionLinearEquivOfMulEquiv e
          (classFunctionLinearEquivOfMulEquiv e.symm thetaOut) :=
        (classFunctionLinearEquivOfMulEquiv e).apply_symm_apply thetaOut |>.symm
      _ = classFunctionLinearEquivOfMulEquiv e (principalCharacter F) := by
        rw [← htheta]
      _ = principalCharacter K :=
        principalCharacter_classFunctionLinearEquivOfMulEquiv e
  have hthetaInFBot : subgroupInKernel' thetaInF
      ((⊥ : Subgroup N).subgroupOf F) := by
    intro f
    have hf : (f : F) = 1 := by
      apply Subtype.ext
      simpa using f.property
    rw [hf]
    rfl
  have hthetaOutFBot : subgroupInKernel' thetaOutF
      ((⊥ : Subgroup N).subgroupOf F) := by
    intro f
    have hf : (f : F) = 1 := by
      apply Subtype.ext
      simpa using f.property
    rw [hf]
    rfl
  let etaInCF : ClassFunction N := inducedCF F thetaInF
  let etaOutCF : ClassFunction N := inducedCF F thetaOutF
  have hetaInMem : etaInCF ∈ Y := by
    apply (hYbot.2 etaInCF).2
    exact ⟨thetaInF, hthetaInFIrr, hthetaInFBot,
      hthetaInFNePrincipal, rfl⟩
  have hetaOutMem : etaOutCF ∈ Y := by
    apply (hYbot.2 etaOutCF).2
    exact ⟨thetaOutF, hthetaOutFIrr, hthetaOutFBot,
      hthetaOutFNePrincipal, rfl⟩
  let etaIn : Y := ⟨etaInCF, hetaInMem⟩
  let etaOut : Y := ⟨etaOutCF, hetaOutMem⟩
  have hpsiClass : IsClassFunction (psi i) :=
    isCharacter_isClassFunction _
      (isCharacter_of_isIrreducibleCharacterOnGroup (hpsiIrr i))
  have hresNClass : IsClassFunction (subgroupRestriction N (psi i)) := by
    intro x g
    exact hpsiClass (x : G) (g : G)
  have hetaInCoeff : scalarProduct N (etaIn : ClassFunction N)
      (subgroupRestriction N (psi i)) = 1 := by
    calc
      scalarProduct N (etaIn : ClassFunction N)
          (subgroupRestriction N (psi i)) =
          scalarProduct F thetaInF
            (subgroupRestriction F (subgroupRestriction N (psi i))) := by
        change scalarProduct N (inducedCF F thetaInF)
          (subgroupRestriction N (psi i)) = _
        exact scalarProduct_inducedCF_left F thetaInF _ hresNClass
      _ = scalarProduct K thetaIn (subgroupRestriction K (psi i)) :=
        ii1Theorem26_scalarProduct_subgroupOf_transport K N hKN thetaIn (psi i)
      _ = 1 := hthetaInCoeff
  have hetaOutCoeff : scalarProduct N (etaOut : ClassFunction N)
      (subgroupRestriction N (psi i)) = 0 := by
    calc
      scalarProduct N (etaOut : ClassFunction N)
          (subgroupRestriction N (psi i)) =
          scalarProduct F thetaOutF
            (subgroupRestriction F (subgroupRestriction N (psi i))) := by
        change scalarProduct N (inducedCF F thetaOutF)
          (subgroupRestriction N (psi i)) = _
        exact scalarProduct_inducedCF_left F thetaOutF _ hresNClass
      _ = scalarProduct K thetaOut (subgroupRestriction K (psi i)) :=
        ii1Theorem26_scalarProduct_subgroupOf_transport K N hKN thetaOut (psi i)
      _ = 0 := hthetaOutCoeff
  have hspan : Section5.integerSpanOn Y Section5.puncturedSet
      ((etaIn : ClassFunction N) - (etaOut : ClassFunction N)) := by
    refine ⟨Section5.integerSpan_sub
      (Section5.integerSpan_of_mem Y etaIn.property)
      (Section5.integerSpan_of_mem Y etaOut.property), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change degree (etaIn : ClassFunction N) -
      degree (etaOut : ClassFunction N) = 0
    rw [hYdegree etaIn etaOut]
    simp
  have hleft : scalarProduct G
      (tau ((etaIn : ClassFunction N) - (etaOut : ClassFunction N)))
      (psi i) = 0 := by
    have hmuZero : ∀ eta : Y, scalarProduct G (mu eta) (psi i) = 0 := by
      intro eta
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hmuIrr eta) (hpsiIrr i) (Ne.symm (hnot eta))
    rw [map_sub, htauMu etaIn, htauMu etaOut,
      Section5.scalarProduct_sub_left, scalarProduct_smul_left,
      scalarProduct_smul_left, hmuZero etaIn, hmuZero etaOut]
    simp
  have hright : scalarProduct G
      (tau ((etaIn : ClassFunction N) - (etaOut : ClassFunction N)))
      (psi i) = 1 := by
    rw [htau.2.2 _ hspan]
    rw [map_sub, Section5.scalarProduct_sub_left]
    change scalarProduct G (inducedCF N (etaIn : ClassFunction N)) (psi i) -
      scalarProduct G (inducedCF N (etaOut : ClassFunction N)) (psi i) = 1
    rw [scalarProduct_inducedCF_left N _ _ hpsiClass,
      scalarProduct_inducedCF_left N _ _ hpsiClass,
      hetaInCoeff, hetaOutCoeff]
    norm_num
  rw [hleft] at hright
  norm_num at hright

private noncomputable def ii1Theorem26OutsideSum
    {X : Type*} [Finite X] (S : Set X) (f : X → ℂ) : ℂ := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  exact ∑ x : X, if x ∈ S then 0 else f x

private lemma ii1Theorem26_sum_eq_sum_subgroup_of_supported
    {G M : Type*} [Group G] [Fintype G] [AddCommMonoid M]
    (H : Subgroup G) [Fintype H] (f : G → M)
    (hzero : ∀ g : G, g ∉ H → f g = 0) :
    (∑ g : G, f g) = ∑ h : H, f h := by
  classical
  let s : Finset G := Finset.univ.filter fun g : G => g ∈ H
  have hs : ∀ g : G, g ∈ s ↔ g ∈ H := by
    intro g
    simp [s]
  have hsub : ∑ g ∈ s, f g = ∑ h : H, f h :=
    Finset.sum_subtype (s := s) (p := fun g : G => g ∈ H) hs f
  calc
    (∑ g : G, f g) = ∑ g : G, if g ∈ H then f g else 0 := by
      refine Finset.sum_congr rfl ?_
      intro g _hg
      by_cases hgH : g ∈ H
      · simp [hgH]
      · simp [hgH, hzero g hgH]
    _ = ∑ g ∈ s, f g := by
      simpa [s] using
        (Finset.sum_filter (s := (Finset.univ : Finset G))
          (p := fun g : G => g ∈ H) f).symm
    _ = ∑ h : H, f h := hsub

private lemma ii1Theorem26_inducedCF_apply_of_suzuki_ti_ne_one
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (K : Set G)
    (hTI : External.Suzuki.VI.IsTISubsetRelative H K)
    {theta : Section1.ClassFunction H}
    (hthetaClass : Section1.IsClassFunction theta)
    (hthetaSupport : ∀ h : H, (h : G) ∉ K → theta h = 0)
    {x : G} (hx : x ∈ K) (hxne : x ≠ 1) :
    Section1.inducedCF H theta x = theta ⟨x, hTI.1 hx⟩ := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype H := Fintype.ofFinite H
  let xH : H := ⟨x, hTI.1 hx⟩
  let f : G → ℂ := fun y =>
    if hy : y * x * y⁻¹ ∈ H then theta ⟨y * x * y⁻¹, hy⟩ else 0
  have hzero : ∀ y : G, y ∉ H → f y = 0 := by
    intro y hyH
    by_cases hyconjH : y * x * y⁻¹ ∈ H
    · by_cases hyconjK : y * x * y⁻¹ ∈ K
      · obtain ⟨h, hh⟩ := hTI.2.2.1 hx hyconjK ⟨y, rfl⟩
        have hc : (h : G)⁻¹ * y ∈ Subgroup.centralizer ({x} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          have ha_eq : a = x := by simpa using ha
          subst a
          calc
            x * ((h : G)⁻¹ * y) =
                (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * y := by group
            _ = (h : G)⁻¹ * (y * x * y⁻¹) * y := by rw [hh]
            _ = ((h : G)⁻¹ * y) * x := by group
        have hcH : (h : G)⁻¹ * y ∈ H :=
          hTI.2.2.2 x hx hxne hc
        have hyH' : y ∈ H := by
          have := H.mul_mem h.property hcH
          simpa using this
        exact False.elim (hyH hyH')
      · have hvanish :
            theta ⟨y * x * y⁻¹, hyconjH⟩ = 0 :=
          hthetaSupport ⟨y * x * y⁻¹, hyconjH⟩ hyconjK
        simp [f, hyconjH, hvanish]
    · simp [f, hyconjH]
  have hconst : ∀ y : H, f y = theta xH := by
    intro y
    have hyconjH : (y : G) * x * (y : G)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem y.property xH.property) (H.inv_mem y.property)
    have hsub :
        (⟨(y : G) * x * (y : G)⁻¹, hyconjH⟩ : H) = y * xH * y⁻¹ := by
      ext
      rfl
    have hclass :
        theta ⟨(y : G) * x * (y : G)⁻¹, hyconjH⟩ = theta xH := by
      simpa [hsub] using hthetaClass y xH
    simp [f, hyconjH, hclass]
  have hsum : (∑ y : G, f y) = ∑ y : H, f y := by
    exact ii1Theorem26_sum_eq_sum_subgroup_of_supported H f hzero
  have hsumConst : (∑ y : H, f y) = (Nat.card H : ℂ) * theta xH := by
    simp [hconst, Finset.card_univ]
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  unfold Section1.inducedCF Section1.inducedClassFunction
  change (Nat.card H : ℂ)⁻¹ * (∑ y : G, f y) = theta xH
  rw [hsum, hsumConst]
  field_simp [hcardH]

private theorem ii1Theorem26_ti_outside_sum
    {X : Type*} [Group X] [Finite X]
    (K N : Subgroup X)
    (hTI : External.Suzuki.VI.IsTISubsetRelative N (K : Set X))
    (f : ClassFunction X) (hfclass : IsClassFunction f)
    (hglobal : scalarProduct X f (principalCharacter X) = 0)
    (hlocal : scalarProduct K (subgroupRestriction K f)
      (principalCharacter K) = 0) :
    let A : Set X := (K : Set X) \ ({1} : Set X)
    ii1Theorem26OutsideSum (Section2.conjugateSet A) f =
      (N.index : ℂ) * f 1 := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype N := Fintype.ofFinite N
  let A : Set X := (K : Set X) \ ({1} : Set X)
  let F : Subgroup N := K.subgroupOf N
  letI : Fintype F := Fintype.ofFinite F
  let theta : ClassFunction N := fun n =>
    if hn : (n : X) ∈ A then f n else 0
  have hthetaClass : IsClassFunction theta := by
    intro n x
    have hnNorm : (n : X) ∈ Subgroup.normalizer (K : Set X) := by
      rw [hTI.2.1]
      exact n.property
    have hnorm : ∀ y : X,
        y ∈ K ↔ (n : X) * y * (n : X)⁻¹ ∈ K := by
      simpa [Subgroup.mem_normalizer_iff] using hnNorm
    have hAconj : (x : X) ∈ A ↔
        (n : X) * (x : X) * (n : X)⁻¹ ∈ A := by
      constructor
      · rintro ⟨hxK, hxne⟩
        refine ⟨(hnorm (x : X)).1 hxK, ?_⟩
        simpa only [Set.mem_singleton_iff] using
          (show (n : X) * (x : X) * (n : X)⁻¹ ≠ 1 by
            intro h
            apply hxne
            have h' := congrArg (fun z : X => (n : X)⁻¹ * z * (n : X)) h
            simpa [mul_assoc] using h')
      · rintro ⟨hxK, hxne⟩
        refine ⟨(hnorm (x : X)).2 hxK, ?_⟩
        simpa only [Set.mem_singleton_iff] using
          (show (x : X) ≠ 1 by
            intro h
            apply hxne
            simp [h])
    by_cases hxA : (x : X) ∈ A
    · have hconjA := hAconj.mp hxA
      dsimp [theta]
      rw [if_pos hxA]
      rw [if_pos hconjA]
      exact hfclass (n : X) (x : X)
    · have hconjA : (n : X) * (x : X) * (n : X)⁻¹ ∉ A :=
        fun h => hxA (hAconj.mpr h)
      dsimp [theta]
      rw [if_neg hxA]
      rw [if_neg hconjA]
  have hthetaSupport : ∀ n : N, (n : X) ∉ (K : Set X) → theta n = 0 := by
    intro n hnK
    have hnA : (n : X) ∉ A := fun hnA => hnK hnA.1
    simp [theta, hnA]
  have hthetaCFOn : Section2.CFOn N A theta := by
    refine ⟨hthetaClass, ?_⟩
    intro n hnA
    simp [theta, hnA]
  have hind : ∀ x : X,
      Section1.inducedCF N theta x =
        if x ∈ Section2.conjugateSet A then f x else 0 := by
    intro x
    by_cases hxA : x ∈ Section2.conjugateSet A
    · rcases hxA with ⟨a, haA, g, hga⟩
      have haK : a ∈ (K : Set X) := haA.1
      have hane : a ≠ 1 := by simpa using haA.2
      have hval :=
        ii1Theorem26_inducedCF_apply_of_suzuki_ti_ne_one
          N (K : Set X) hTI hthetaClass hthetaSupport haK hane
      have hthetaA : theta ⟨a, hTI.1 haK⟩ = f a := by
        dsimp [theta]
        rw [if_pos haA]
      have hindClass := Section1.inducedCF_isClassFunction N theta g a
      have hfconj := hfclass g a
      change g * a * g⁻¹ = x at hga
      rw [hga] at hindClass hfconj
      rw [if_pos ⟨a, haA, g, by simpa [Section2.conjBy] using hga⟩]
      exact hindClass.trans (hval.trans (hthetaA.trans hfconj.symm))
    · rw [if_neg hxA]
      exact Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn
        N theta hthetaCFOn hxA
  have hsumGlobal : ∑ x : X, f x = 0 := by
    unfold scalarProduct principalCharacter at hglobal
    simp only [star_one, mul_one] at hglobal
    exact (mul_eq_zero.mp hglobal).resolve_left
      (inv_ne_zero (by exact_mod_cast (Nat.card_pos (α := X)).ne'))
  have hsumLocal : ∑ k : K, f k = 0 := by
    unfold scalarProduct subgroupRestriction principalCharacter at hlocal
    simp only [star_one, mul_one] at hlocal
    exact (mul_eq_zero.mp hlocal).resolve_left
      (inv_ne_zero (by exact_mod_cast (Nat.card_pos (α := K)).ne'))
  have hsumThetaSub : (∑ n : N, theta n) = ∑ z : F, theta z := by
    apply ii1Theorem26_sum_eq_sum_subgroup_of_supported F theta
    intro n hnF
    have hnK : (n : X) ∉ K := by
      intro hnK
      exact hnF hnK
    exact hthetaSupport n hnK
  have hsumF : (∑ z : F, theta z) = - f 1 := by
    let e : F ≃ K := (Subgroup.subgroupOfEquivOfLe hTI.1).toEquiv
    calc
      (∑ z : F, theta z) = ∑ k : K, theta (e.symm k) := by
        exact Fintype.sum_equiv e (fun z : F => theta z)
          (fun k : K => theta (e.symm k)) (fun z => by simp)
      _ = ∑ k : K, if k = 1 then 0 else f k := by
        apply Finset.sum_congr rfl
        intro k _hk
        have hecoe : (((e.symm k : F) : N) : X) = (k : X) := by
          rfl
        by_cases hk : k = 1
        · rw [if_pos hk]
          dsimp [theta]
          rw [if_neg]
          intro hA
          apply hA.2
          simpa [Set.mem_singleton_iff, hk] using hecoe
        · rw [if_neg hk]
          dsimp [theta]
          rw [if_pos]
          · rw [hecoe]
          · change (((e.symm k : F) : N) : X) ∈ (K : Set X) \ ({1} : Set X)
            rw [hecoe]
            exact ⟨k.property, by simpa [Set.mem_singleton_iff] using hk⟩
      _ = (∑ k : K, f k) - f 1 := by
        have hpartition :
            (∑ k : K, f k) =
              (∑ k : K, if k = 1 then f k else 0) +
                ∑ k : K, if k = 1 then 0 else f k := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _hk
          by_cases hk : k = 1 <;> simp [hk]
        have hone : (∑ k : K, if k = 1 then f k else 0) = f 1 := by
          simp
        rw [hone] at hpartition
        apply (eq_sub_iff_add_eq).2
        rw [add_comm]
        exact hpartition.symm
      _ = - f 1 := by rw [hsumLocal]; ring
  have hsumTheta : (∑ n : N, theta n) = - f 1 := hsumThetaSub.trans hsumF
  have hfrob : scalarProduct X (Section1.inducedCF N theta)
      (principalCharacter X) =
      scalarProduct N theta (principalCharacter N) := by
    exact Section1.inducedClassFunction_frobenius_general N theta
      (principalCharacter X) (by intro x g; rfl)
  have hsumInduced : ∑ x : X, Section1.inducedCF N theta x =
      (N.index : ℂ) * (∑ n : N, theta n) := by
    unfold scalarProduct principalCharacter at hfrob
    simp only [star_one, mul_one] at hfrob
    have hcardX : (Nat.card X : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := X)).ne'
    have hcardN : (Nat.card N : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := N)).ne'
    have hindex : (N.index : ℂ) * (Nat.card N : ℂ) = Nat.card X := by
      exact_mod_cast N.index_mul_card
    field_simp [hcardX, hcardN] at hfrob
    apply mul_left_cancel₀ hcardN
    calc
      (Nat.card N : ℂ) * ∑ x : X, Section1.inducedCF N theta x =
          (∑ x : X, Section1.inducedCF N theta x) * Nat.card N := by ring
      _ = (Nat.card X : ℂ) * ∑ n : N, theta n := hfrob
      _ = ((N.index : ℂ) * Nat.card N) * ∑ n : N, theta n := by
        rw [hindex]
      _ = (Nat.card N : ℂ) *
          ((N.index : ℂ) * ∑ n : N, theta n) := by ring
  have hsumConj :
      (∑ x : X, if x ∈ Section2.conjugateSet A then f x else 0) =
        - (N.index : ℂ) * f 1 := by
    calc
      _ = ∑ x : X, Section1.inducedCF N theta x := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [hind]
      _ = (N.index : ℂ) * (∑ n : N, theta n) := hsumInduced
      _ = - (N.index : ℂ) * f 1 := by rw [hsumTheta]; ring
  change (∑ x : X, if x ∈ Section2.conjugateSet A then 0 else f x) = _
  have hpartition :
      (∑ x : X, f x) =
        (∑ x : X, if x ∈ Section2.conjugateSet A then f x else 0) +
          ∑ x : X, if x ∈ Section2.conjugateSet A then 0 else f x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hx : x ∈ Section2.conjugateSet A <;> simp [hx]
  rw [hsumGlobal, hsumConj] at hpartition
  calc
    (∑ x : X, if x ∈ Section2.conjugateSet A then 0 else f x) =
        (- (N.index : ℂ) * f 1 +
          ∑ x : X, if x ∈ Section2.conjugateSet A then 0 else f x) +
            (N.index : ℂ) * f 1 := by ring
    _ = 0 + (N.index : ℂ) * f 1 := by rw [← hpartition]
    _ = (N.index : ℂ) * f 1 := zero_add _



private theorem ii1Theorem26_irreducible_value_isIntegral
    {G : Type*} [Group G] [Finite G]
    {phi : ClassFunction G}
    (hirr : IsIrreducibleCharacterOnGroup phi) (x : G) :
    IsIntegral ℤ (phi x) := by
  rcases hirr with ⟨n, rho, _hrho, hphi⟩
  rw [hphi]
  exact Theory.Character.representation_character_isIntegral rho x


private theorem ii1Theorem26_burnside_normalizer_eq_top
    {G : Type u} {Q : Type v} {I : Type w}
    [Group G] [Finite G] [MulAction G Q] [Fintype Q] [Nonempty Q]
    [FaithfulSMul G Q] [Finite I] [DecidableEq I]
    (K N : Subgroup G)
    (hTI : External.Suzuki.VI.IsTISubsetRelative N (K : Set G))
    (psi : I → ClassFunction G)
    (hpsiIrr : ∀ i, IsIrreducibleCharacterOnGroup (psi i))
    (hpair : Pairwise (fun i j => psi i ≠ psi j))
    (hdecomp : (Representation.ofMulAction ℂ G Q).character =
      weightedFamilySum (fun _ : I => (1 : ℂ)) psi)
    (horthK : ∀ i j, i ≠ j →
      scalarProduct K (subgroupRestriction K (psi i))
        (subgroupRestriction K (psi j)) = 0)
    (i0 : I) (hi0 : psi i0 = principalCharacter G)
    (hcard : 3 ≤ Nat.card I)
    (hdegree : ∀ i j, i ≠ i0 → j ≠ i0 →
      degree (psi i) = degree (psi j))
    (hcommon : ∀ i j, i ≠ i0 → j ≠ i0 → ∀ x,
      x ∉ Section2.conjugateSet ((K : Set G) \ ({1} : Set G)) →
        psi i x = psi j x) :
    N = ⊤ := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype I := Fintype.ofFinite I
  have hcardF : 3 ≤ Fintype.card I := by
    simpa [Nat.card_eq_fintype_card] using hcard
  obtain ⟨i1, hi1⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i0
  let equivI := Fintype.equivFin I
  obtain ⟨k, hki1, hki0⟩ := Fin.exists_ne_and_ne_of_two_lt
    (equivI i1) (equivI i0) (by omega)
  let i2 : I := equivI.symm k
  have hi21 : i2 ≠ i1 := by
    intro h
    apply hki1
    simpa [i2] using congrArg equivI h
  have hi20 : i2 ≠ i0 := by
    intro h
    apply hki0
    simpa [i2] using congrArg equivI h
  obtain ⟨s, hspos, hsdeg⟩ :=
    ii1Theorem26_irreducible_hasPositiveDegree (G := G) (hpsiIrr i1)
  let A : Set G := (K : Set G) \ ({1} : Set G)
  have hOneOutside : (1 : G) ∉ Section2.conjugateSet A := by
    rintro ⟨a, ha, g, hga⟩
    have haone : a = 1 := by
      have h := congrArg (fun z : G => g⁻¹ * z * g) hga
      simpa [Section2.conjBy, mul_assoc] using h
    exact ha.2 (by simpa [Set.mem_singleton_iff] using haone)
  let m := Fintype.card I - 1
  have hmpos : 0 < m := by omega
  have hmge : 2 ≤ m := by omega
  have hpiFormula : ∀ x,
      x ∉ Section2.conjugateSet A →
      (Representation.ofMulAction ℂ G Q).character x =
        1 + (m : ℂ) * psi i1 x := by
    intro x hx
    rw [hdecomp]
    simp only [weightedFamilySum, one_mul]
    calc
      (∑ i : I, psi i x) =
          psi i0 x + ∑ i ∈ Finset.univ.erase i0, psi i x := by
        exact (Finset.add_sum_erase Finset.univ (fun i => psi i x)
          (Finset.mem_univ i0)).symm
      _ = 1 + ∑ i ∈ Finset.univ.erase i0, psi i x := by
        rw [hi0]
        rfl
      _ = 1 + ∑ _i ∈ Finset.univ.erase i0, psi i1 x := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hiMem
        exact hcommon i i1 (Finset.ne_of_mem_erase hiMem) hi1 x hx
      _ = 1 + (m : ℂ) * psi i1 x := by
        simp [m, mul_comm]
  have hvalueNat : ∀ x,
      x ∉ Section2.conjugateSet A →
      ∃ c : ℕ, psi i1 x = (c : ℂ) := by
    intro x hx
    have hint := ii1Theorem26_irreducible_value_isIntegral (hpsiIrr i1) x
    have hrat : ∃ q : ℚ, psi i1 x = (q : ℂ) := by
      let fixed := Nat.card (MulAction.fixedBy Q x)
      refine ⟨((fixed : ℚ) - 1) / (m : ℚ), ?_⟩
      have hformula := hpiFormula x hx
      rw [ii1Theorem26_permutationCharacter_apply] at hformula
      have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
      have hquot : psi i1 x = ((fixed : ℂ) - 1) / (m : ℂ) := by
        apply (eq_div_iff hmC).2
        calc
          psi i1 x * (m : ℂ) = (m : ℂ) * psi i1 x := by ring
          _ = (fixed : ℂ) - 1 := by linear_combination -hformula
      rw [hquot]
      norm_num
    obtain ⟨z, hz⟩ := Theory.Character.isaacs_lemma_3_2_core hint hrat
    let fixed := Nat.card (MulAction.fixedBy Q x)
    have hformula := hpiFormula x hx
    rw [ii1Theorem26_permutationCharacter_apply, hz] at hformula
    have hformulaInt : (fixed : ℤ) = 1 + (m : ℤ) * z := by
      exact_mod_cast hformula
    have hznonneg : 0 ≤ z := by
      have hfixednonneg : (0 : ℤ) ≤ fixed := by positivity
      have hmgeInt : (2 : ℤ) ≤ m := by exact_mod_cast hmge
      by_contra hznot
      have hzle : z ≤ -1 := by omega
      nlinarith
    refine ⟨z.toNat, ?_⟩
    rw [hz]
    exact_mod_cast (Int.toNat_of_nonneg hznonneg).symm
  let c : G → ℕ := fun x =>
    if hx : x ∉ Section2.conjugateSet A then
      Classical.choose (hvalueNat x hx)
    else 0
  have hc : ∀ x, x ∉ Section2.conjugateSet A →
      psi i1 x = (c x : ℂ) := by
    intro x hx
    simp only [c, dif_pos hx]
    exact Classical.choose_spec (hvalueNat x hx)
  have hcInside : ∀ x, x ∈ Section2.conjugateSet A → c x = 0 := by
    intro x hx
    simp [c, hx]
  have hcOne : c 1 = s := by
    have h := (hc 1 hOneOutside).symm.trans hsdeg
    exact_mod_cast h
  have hfixEq : ∀ x, x ∉ Section2.conjugateSet A →
      Nat.card (MulAction.fixedBy Q x) = 1 + m * c x := by
    intro x hx
    have h := hpiFormula x hx
    rw [ii1Theorem26_permutationCharacter_apply, hc x hx] at h
    exact_mod_cast h
  have hQcard : Nat.card Q = 1 + m * s := by
    have h := hfixEq 1 hOneOutside
    rw [hcOne] at h
    simpa using h
  have hcLe : ∀ x, c x ≤ s := by
    intro x
    by_cases hx : x ∈ Section2.conjugateSet A
    · rw [hcInside x hx]
      omega
    · have hfix := hfixEq x hx
      have hsub : Nat.card (MulAction.fixedBy Q x) ≤ Fintype.card Q := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_le
          (fun q : Q => q ∈ MulAction.fixedBy Q x)
      have hsub' : Nat.card (MulAction.fixedBy Q x) ≤ Nat.card Q := by
        simpa [Nat.card_eq_fintype_card] using hsub
      have hmulLe : m * c x ≤ m * s := by
        omega
      exact Nat.le_of_mul_le_mul_left hmulLe hmpos
  have hcLt : ∀ x, x ∉ Section2.conjugateSet A → x ≠ 1 → c x < s := by
    intro x hx hxone
    have hle := hcLe x
    apply lt_of_le_of_ne hle
    intro hcs
    have hfixedCard : Fintype.card (MulAction.fixedBy Q x) = Fintype.card Q := by
      have hfix := hfixEq x hx
      rw [hcs] at hfix
      have hfixQ : Nat.card (MulAction.fixedBy Q x) = Nat.card Q :=
        hfix.trans hQcard.symm
      simpa [Nat.card_eq_fintype_card] using hfixQ
    let incl : MulAction.fixedBy Q x → Q := fun q => q.1
    have hincl : Function.Injective incl := Subtype.val_injective
    have hsurj : Function.Surjective incl :=
      (Fintype.bijective_iff_injective_and_card incl).mpr
        ⟨hincl, hfixedCard⟩ |>.2
    have hfixAll : ∀ q : Q, x • q = q := by
      intro q
      obtain ⟨z, hz⟩ := hsurj q
      calc
        x • q = x • incl z := by rw [hz]
        _ = incl z := z.property
        _ = q := hz
    exact hxone ((faithfulSMul_iff.mp
      (inferInstance : FaithfulSMul G Q)) x hfixAll)
  have hpsiClass1 : IsClassFunction (psi i1) :=
    isCharacter_isClassFunction _
      (isCharacter_of_isIrreducibleCharacterOnGroup (hpsiIrr i1))
  have hpsiClass2 : IsClassFunction (psi i2) :=
    isCharacter_isClassFunction _
      (isCharacter_of_isIrreducibleCharacterOnGroup (hpsiIrr i2))
  have hprodClass : IsClassFunction (psi i1 * star (psi i2)) := by
    intro g x
    simp only [Pi.mul_apply, star, RCLike.star_def]
    rw [hpsiClass1 g x, hpsiClass2 g x]
  have hpsi1NePrincipal : psi i1 ≠ principalCharacter G := by
    simpa [hi0] using hpair hi1
  have hglobal1 : scalarProduct G (psi i1) (principalCharacter G) = 0 :=
    scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
      (hpsiIrr i1) hpsi1NePrincipal
  have hlocal1 : scalarProduct K (subgroupRestriction K (psi i1))
      (principalCharacter K) = 0 := by
    have h := horthK i1 i0 hi1
    have hres : subgroupRestriction K (principalCharacter G) =
        principalCharacter K := by
      ext k
      rfl
    rw [hi0, hres] at h
    exact h
  have hglobal12 : scalarProduct G (psi i1 * star (psi i2))
      (principalCharacter G) = 0 := by
    have h := scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hpsiIrr i1) (hpsiIrr i2) (hpair hi21.symm)
    calc
      scalarProduct G (psi i1 * star (psi i2)) (principalCharacter G) =
          scalarProduct G (psi i1) (psi i2) := by
        unfold scalarProduct
        congr 1
        apply Finset.sum_congr rfl
        intro g _hg
        simp [principalCharacter_apply]
      _ = 0 := h
  have hlocal12 : scalarProduct K
      (subgroupRestriction K (psi i1 * star (psi i2)))
      (principalCharacter K) = 0 := by
    have h := horthK i1 i2 hi21.symm
    calc
      scalarProduct K (subgroupRestriction K (psi i1 * star (psi i2)))
          (principalCharacter K) =
          scalarProduct K (subgroupRestriction K (psi i1))
            (subgroupRestriction K (psi i2)) := by
        unfold scalarProduct
        congr 1
        apply Finset.sum_congr rfl
        intro g _hg
        simp [subgroupRestriction, principalCharacter_apply]
      _ = 0 := h
  have hsum1 := ii1Theorem26_ti_outside_sum K N hTI (psi i1)
    hpsiClass1 hglobal1 hlocal1
  have hsum12 := ii1Theorem26_ti_outside_sum K N hTI
    (psi i1 * star (psi i2)) hprodClass hglobal12 hlocal12
  change ii1Theorem26OutsideSum (Section2.conjugateSet A) (psi i1) =
    (N.index : ℂ) * psi i1 1 at hsum1
  change ii1Theorem26OutsideSum (Section2.conjugateSet A)
    (psi i1 * star (psi i2)) =
      (N.index : ℂ) * (psi i1 * star (psi i2)) 1 at hsum12
  have hsum1Complex : (∑ x : G, (c x : ℂ)) =
      (N.index : ℂ) * (s : ℂ) := by
    calc
      (∑ x : G, (c x : ℂ)) =
          ii1Theorem26OutsideSum (Section2.conjugateSet A) (psi i1) := by
        unfold ii1Theorem26OutsideSum
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hx : x ∈ Section2.conjugateSet A
        · simp [hx, hcInside x hx]
        · simp [hx, hc x hx]
      _ = (N.index : ℂ) * psi i1 1 := hsum1
      _ = (N.index : ℂ) * (s : ℂ) := by
        rw [← hsdeg, degree_apply]
  have hsum12Complex : (∑ x : G, ((c x) ^ 2 : ℂ)) =
      (N.index : ℂ) * ((s : ℂ) ^ 2) := by
    calc
      (∑ x : G, ((c x) ^ 2 : ℂ)) =
          ii1Theorem26OutsideSum (Section2.conjugateSet A)
            (psi i1 * star (psi i2)) := by
        unfold ii1Theorem26OutsideSum
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hx : x ∈ Section2.conjugateSet A
        · simp [hx, hcInside x hx]
        · have hcommon12 := hcommon i2 i1 hi20 hi1 x hx
          simp only [Pi.mul_apply]
          rw [if_neg hx, Pi.star_apply, hcommon12, hc x hx]
          norm_num [pow_two]
      _ = (N.index : ℂ) * (psi i1 * star (psi i2)) 1 := hsum12
      _ = (N.index : ℂ) * ((s : ℂ) ^ 2) := by
        simp only [Pi.mul_apply]
        rw [show psi i1 1 = (s : ℂ) from hsdeg,
          Pi.star_apply, show psi i2 1 = (s : ℂ) by
            exact (hdegree i2 i1 hi20 hi1).trans hsdeg]
        norm_num [pow_two]
  have hsum1Nat : ∑ x : G, c x = N.index * s := by
    exact_mod_cast hsum1Complex
  have hsum12Nat : ∑ x : G, c x ^ 2 = N.index * s ^ 2 := by
    exact_mod_cast hsum12Complex
  have hsumZeroReal :
      (∑ x : G, (c x : ℝ) * ((s : ℝ) - c x)) = 0 := by
    have hsum1Real : (∑ x : G, (c x : ℝ)) = (N.index : ℝ) * s := by
      exact_mod_cast hsum1Nat
    have hsum12Real : (∑ x : G, ((c x : ℝ) ^ 2)) =
        (N.index : ℝ) * (s : ℝ) ^ 2 := by
      exact_mod_cast hsum12Nat
    calc
      (∑ x : G, (c x : ℝ) * ((s : ℝ) - c x)) =
          (s : ℝ) * (∑ x : G, (c x : ℝ)) -
            ∑ x : G, ((c x : ℝ) ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = 0 := by rw [hsum1Real, hsum12Real]; ring
  have htermZero : ∀ x : G,
      (c x : ℝ) * ((s : ℝ) - c x) = 0 := by
    have hnonneg : ∀ x ∈ (Finset.univ : Finset G),
        (0 : ℝ) ≤ (c x : ℝ) * ((s : ℝ) - c x) := by
      intro x _hx
      apply mul_nonneg
      · positivity
      · apply sub_nonneg.mpr
        exact_mod_cast hcLe x
    exact fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumZeroReal x
        (Finset.mem_univ x)
  have hcZero : ∀ x : G, x ≠ 1 → c x = 0 := by
    intro x hxone
    by_cases hx : x ∈ Section2.conjugateSet A
    · exact hcInside x hx
    · have hlt := hcLt x hx hxone
      have hz := htermZero x
      by_contra hcne
      have hcpos : 0 < c x := Nat.pos_of_ne_zero hcne
      have hltReal : (c x : ℝ) < (s : ℝ) := by exact_mod_cast hlt
      have hgap : (0 : ℝ) < (s : ℝ) - c x := by linarith
      have hcposReal : (0 : ℝ) < c x := by exact_mod_cast hcpos
      nlinarith
  have hsumEqS : ∑ x : G, c x = s := by
    calc
      (∑ x : G, c x) = c 1 := by
        apply Finset.sum_eq_single 1
        · intro x _hx hxone
          exact hcZero x hxone
        · simp
      _ = s := hcOne
  have hindexOne : N.index = 1 := by
    apply Nat.eq_of_mul_eq_mul_right hspos
    calc
      N.index * s = ∑ x : G, c x := hsum1Nat.symm
      _ = s := hsumEqS
      _ = 1 * s := by simp
  exact Subgroup.index_eq_one.mp hindexOne

end

open Section1

private theorem ii1Theorem26_proper_normalizer_two_pretransitive
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    [FaithfulSMul X Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K)
    (hKne : K ≠ ⊥)
    (hNK : Subgroup.normalizer (K : Set X) ≠ K)
    (hNtop : Subgroup.normalizer (K : Set X) ≠ ⊤) :
    MulAction.IsMultiplyPretransitive X Omega 2 := by
  classical
  let alpha : Omega := Classical.choice (inferInstance : Nonempty Omega)
  let N : Subgroup X := Subgroup.normalizer (K : Set X)
  let F : Subgroup N := K.subgroupOf N
  let D : Subgroup N := MulAction.stabilizer N alpha
  have hKN : K ≤ N := Subgroup.le_normalizer
  have hFrob : IsFrobeniusGroupWithKernelComplement F D := by
    simpa [N, F, D] using
      (ii1Theorem26_normalizer_frobenius K hreg hcent hKne alpha hNK)
  letI : F.Normal := hFrob.normal
  have hKcomm : IsMulCommutative K :=
    ii1Theorem26_regular_commutative K hcent
  letI : IsMulCommutative K := hKcomm
  have hFcomm : IsMulCommutative F := by
    refine ⟨⟨?_⟩⟩
    intro a b
    let aK : K := ⟨(((a : F) : N) : X), a.property⟩
    let bK : K := ⟨(((b : F) : N) : X), b.property⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [aK, bK] using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := K)).comm aK bK)
  have hTI : External.Suzuki.VI.IsTISubsetRelative N (K : Set X) := by
    simpa [N] using ii1Theorem26_isTI_normalizer K hKne hcent
  have hFmap : F.map N.subtype = K := by
    simpa [N, F] using Subgroup.map_subgroupOf_eq_of_le hKN
  have hTIF : External.Suzuki.VI.IsTISubsetRelative N
      (F.map N.subtype : Set X) := by
    rw [hFmap]
    exact hTI
  obtain ⟨Y, hYirr, _hYnonker, _hYcomplete, hYisometry,
      hYvirtual, hYbot, hYdegreeD, hYcardEq⟩ :=
    External.huppert_XI_6_5_abelian_frobenius_nonker_family
      N F D hFrob hFcomm hTIF
  have hYdegree : ∀ eta xi : Y,
      degree (eta : ClassFunction N) = degree (xi : ClassFunction N) := by
    intro eta xi
    rw [hYdegreeD eta, hYdegreeD xi]
  have hYpos : 0 < Y.card := by
    by_contra hnot
    have hYzero : Y.card = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hYzero, zero_mul] at hYcardEq
    have hFgt : 1 < Nat.card F :=
      (Subgroup.one_lt_card_iff_ne_bot F).2 hFrob.kernel_ne_bot
    omega
  have hOmegaCard : Nat.card K = Nat.card Omega :=
    ii1Theorem26_regular_card K hreg
  by_cases hYone : Y.card = 1
  · have hDcard : Nat.card D = Nat.card F - 1 := by
      simpa [hYone] using hYcardEq
    exact ii1Theorem26_two_pretransitive_of_frobenius_complement_card
      K hreg hcent alpha hOmegaCard
        (by simpa [N, F, D] using hFrob)
        (by simpa [N, F, D] using hDcard)
  have hYge : 2 ≤ Y.card := by omega
  have hcoherent : Section5.IsCoherentTriple Section5.puncturedSet Y
      (Section1.inducedCFLinear N) :=
    External.Isaacs.VII.isaacs_theorem_7_15 N Y
      (Section1.inducedCFLinear N) hYirr hYisometry hYvirtual
      hYdegree hYge
  obtain ⟨tau, epsilon, mu, htau, _hepsilon, hmuIrr, htauMu,
      _hmuInj, _hepsilonEq, hmuDegree, hmuCommon⟩ :=
    ii1Theorem26_coherent_signed_family_common N F Y hYirr hYbot
      hYvirtual hYdegree hcoherent
  let orbitAt : K → Omega := fun k => (k : X) • alpha
  have horbitSurj : Function.Surjective orbitAt := by
    intro beta
    obtain ⟨k, hk, _huniq⟩ :=
      hreg (alpha := alpha) (beta := beta) (by trivial) (by trivial)
    exact ⟨k, hk⟩
  letI : Finite Omega := Finite.of_surjective orbitAt horbitSurj
  letI : Fintype Omega := Fintype.ofFinite Omega
  letI : Fintype K := Fintype.ofFinite K
  have hOmegaGt : 1 < Fintype.card Omega := by
    have hKgt : 1 < Nat.card K :=
      (Subgroup.one_lt_card_iff_ne_bot K).2 hKne
    rw [hOmegaCard] at hKgt
    simpa [Nat.card_eq_fintype_card] using hKgt
  have htrans : MulAction.IsPretransitive X Omega :=
    ii1Theorem26_regular_pretransitive K hreg
  obtain ⟨I, hIFintype, hIDecidableEq, psi, hpsiIrr, hpair,
      hdecomp, horthK, hcover⟩ :=
    External.huppert_XI_regular_restriction_multiplicity_free K hKcomm
      (Representation.ofMulAction ℂ X Omega).character
      (ii1Theorem26_permutationCharacter_isCharacter htrans)
      (ii1Theorem26_permutationCharacter_restrict_regular K hreg hOmegaCard)
  letI : Fintype I := hIFintype
  letI : DecidableEq I := hIDecidableEq
  by_cases hIle : Nat.card I ≤ 2
  · exact ii1Theorem26_two_pretransitive_of_decomposition_card_le_two
      hOmegaGt htrans psi hpsiIrr hpair hdecomp hIle
  have hIcard : 3 ≤ Nat.card I := by omega
  have hIcardF : 3 ≤ Fintype.card I := by
    simpa [Nat.card_eq_fintype_card] using hIcard
  have hprincipal := ii1Theorem26_permutationCharacter_principal htrans
  have hex : ∃ i : I, psi i = principalCharacter X := by
    by_contra h
    push_neg at h
    have hzero : ∀ i : I,
        scalarProduct X (psi i) (principalCharacter X) = 0 := by
      intro i
      exact scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
        (hpsiIrr i) (h i)
    rw [hdecomp, scalarProduct_weightedFamilySum_left] at hprincipal
    simp [hzero] at hprincipal
  obtain ⟨i0, hi0⟩ := hex
  have hmem : ∀ i, i ≠ i0 → ∃ eta : Y, psi i = mu eta :=
    ii1Theorem26_nonprincipal_constituent_mem_exceptional K N hKN Y
      hYbot hYdegree tau htau epsilon mu hmuIrr htauMu psi hpsiIrr
      hcover i0 hi0 hIcardF
  have hdegreePsi : ∀ i j, i ≠ i0 → j ≠ i0 →
      degree (psi i) = degree (psi j) := by
    intro i j hi hj
    obtain ⟨eta, heta⟩ := hmem i hi
    obtain ⟨xi, hxi⟩ := hmem j hj
    rw [heta, hxi]
    exact hmuDegree eta xi
  have hpunct : Section6.subgroupImagePuncturedSet N F =
      (K : Set X) \ ({1} : Set X) := by
    rw [Section6.theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured,
      hFmap]
    ext x
    simp [Set.mem_singleton_iff]
  have hcommonPsi : ∀ i j, i ≠ i0 → j ≠ i0 → ∀ x,
      x ∉ Section2.conjugateSet ((K : Set X) \ ({1} : Set X)) →
        psi i x = psi j x := by
    intro i j hi hj x hx
    obtain ⟨eta, heta⟩ := hmem i hi
    obtain ⟨xi, hxi⟩ := hmem j hj
    rw [heta, hxi]
    apply hmuCommon eta xi x
    rw [hpunct]
    exact hx
  have hNtop' : N = ⊤ :=
    ii1Theorem26_burnside_normalizer_eq_top K N hTI psi hpsiIrr
      hpair hdecomp horthK i0 hi0 hIcard hdegreePsi hcommonPsi
  exact (hNtop (by simpa [N] using hNtop')).elim

private theorem ii1Theorem26Faithful
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    [FaithfulSMul X Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K) :
    MulAction.IsMultiplyPretransitive X Omega 2 ∨
      Subgroup.normalizer (K : Set X) = ⊤ := by
  by_cases hKbot : K = ⊥
  · left
    have hsub : Subsingleton Omega := by
      constructor
      intro alpha beta
      obtain ⟨k, hk, _huniq⟩ :=
        hreg (alpha := alpha) (beta := beta) (by trivial) (by trivial)
      have hkone : k = 1 := by
        apply Subtype.ext
        simpa [hKbot] using k.property
      calc
        alpha = (1 : X) • alpha := by simp
        _ = (k : X) • alpha := by rw [hkone]; simp
        _ = beta := hk
    rw [MulAction.is_two_pretransitive_iff]
    intro alpha beta _gamma _delta hab _hcd
    exact (hab (hsub.elim alpha beta)).elim
  · by_cases hNtop : Subgroup.normalizer (K : Set X) = ⊤
    · exact Or.inr hNtop
    left
    by_cases hNK : Subgroup.normalizer (K : Set X) = K
    · exfalso
      have hKproper : K ≠ ⊤ := by
        intro hKtop
        apply hNtop
        rw [hNK, hKtop]
      exact ii1Theorem26_self_normalizing_false K hreg hKbot hKproper
        (ii1Theorem26_isTI_self_normalizing K hKbot hcent hNK)
    · exact ii1Theorem26_proper_normalizer_two_pretransitive
        K hreg hcent hKbot hNK hNtop

/-- GLS `[II1; Theorem 2.6]`, in action form. -/
public theorem ii1Theorem26Action
    {X : Type u} {Omega : Type v}
    [Group X] [Finite X] [MulAction X Omega] [Nonempty Omega]
    (K : Subgroup X)
    (hreg : IsRegularOn K (Set.univ : Set Omega))
    (hcent : ∀ x : X, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set X) = K) :
    MulAction.IsMultiplyPretransitive X Omega 2 ∨
      (Set.univ : Set X) =
        (pointStabilizerCore X Omega : Set X) *
          (Subgroup.normalizer (K : Set X) : Set X) := by
  classical
  let W := pointStabilizerCore X Omega
  letI : W.Normal := pointStabilizerCore_normal
  let q : X →* X ⧸ W := QuotientGroup.mk' W
  let Kbar : Subgroup (X ⧸ W) := K.map q
  letI : MulAction (X ⧸ W) Omega := pointStabilizerCoreQuotientAction
  letI : FaithfulSMul (X ⧸ W) Omega :=
    faithfulSMul_pointStabilizerCoreQuotientAction
  have hregbar : IsRegularOn Kbar (Set.univ : Set Omega) := by
    simpa [W, q, Kbar] using ii1Theorem26_quotient_regular K hreg
  have hcentbar : ∀ xbar : X ⧸ W, xbar ∈ Kbar → xbar ≠ 1 →
      Subgroup.centralizer ({xbar} : Set (X ⧸ W)) = Kbar := by
    simpa [W, q, Kbar] using
      ii1Theorem26_quotient_centralizer K hreg hcent
  rcases ii1Theorem26Faithful Kbar hregbar hcentbar with htwo | hNtop
  · left
    apply ii1Theorem26_two_pretransitive_of_core_quotient
    simpa [W] using htwo
  · right
    apply ii1Theorem26_normalizer_factor_of_quotient_normal W K
      (ii1Theorem26_regular_disjoint_core K hreg) hcent
    have hKbarNormal : Kbar.Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNtop
    simpa [q, Kbar] using hKbarNormal

end CFSG.BenderSuzuki
