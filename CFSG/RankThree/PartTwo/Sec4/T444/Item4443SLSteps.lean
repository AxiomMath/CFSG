module

import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.RankThree.PartTwo.Sec18.Item184a
import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeisCore
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SL447
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLInner
public import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
public import CFSG.RankThree.PartTwo.Sec4.T444.Step451
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly.RankThreeEven (projSL)
open Subgroup

variable {G : Type} [Group G] [Finite G]

section Ctx

theorem Ctx4443.isQuasisimple_quotient {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s) :
    CFSG.IsQuasisimple (inSubgroup perfectResidual H ⧸
      CFSG.pCore 2 (inSubgroup perfectResidual H)) := by
  obtain ⟨-, hIC, -⟩ := h.mem_scriptH₀
  rw [mem_oTwoComponentsIn_iff] at hIC
  obtain ⟨hIH, -, -, hq⟩ := hIC
  set e := subgroupOfEquivOfLe hIH
  exact LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)) hq

theorem Ctx4443.commutator_A_eq_general {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s) :
    ⁅inSubgroup perfectResidual H, A⁆ = inSubgroup perfectResidual H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I := inSubgroup perfectResidual H with hI
  have hIp : Group.IsPerfect I :=
    isPerfect_iff.mpr (Sec18.commutator_inSubgroup_perfectResidual H)
  have hAH : A ≤ H := Sec18.le_of_mem_scriptH₀ h.mem_scriptH₀
  have hHI : H ≤ normalizer (I : Set G) := Sec18.le_normalizer_inSubgroup_perfectResidual H
  by_contra hne
  have hcen := forall_mem_pCoreOf_of_commutator_ne hIp (Ctx4443.isQuasisimple_quotient h)
    (hAH.trans hHI) hne
  obtain ⟨hsP, -, -, hsH, X, hXn, hXZ, hXtop, -⟩ := h.concl4442
  set P := CFSG.pCore 2 H with hP
  set φ := QuotientGroup.mk' P with hφ
  set sb := φ ⟨s, hsH⟩ with hsb
  set q := QuotientGroup.mk' X with hq
  have hpow : ∀ z : H ⧸ P, q z ∈ zpowers (q sb) := by
    intro z
    have hz : z ∈ X ⊔ zpowers sb := hXtop ▸ mem_top z
    have hz' := mem_map_of_mem q hz
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers,
      (map_eq_bot_iff X).mpr (by rw [hq, QuotientGroup.ker_mk']), bot_sup_eq] at hz'
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)) ⟨s, hsP⟩
  have hj' : (⟨s, hsH⟩ : H) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
  have hsb2 : (q sb) ^ (2 ^ j) = 1 := by rw [hsb, ← map_pow, ← map_pow, hj', map_one, map_one]
  have hq2 : ∀ z : H ⧸ P, (q z) ^ (2 ^ j) = 1 := by
    intro z
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hpow z)
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsb2, one_zpow]
  have haX : ∀ (a : G) (ha : a ∈ A), φ ⟨a, hAH ha⟩ ∈ X := by
    intro a ha
    obtain ⟨e, he⟩ := h.ctx444.isE27.isPGroup ⟨a, ha⟩
    have he' : (⟨a, hAH ha⟩ : H) ^ (3 ^ e) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val he)
    have h3 : (q (φ ⟨a, hAH ha⟩)) ^ (3 ^ e) = 1 := by
      rw [← map_pow, ← map_pow, he', map_one, map_one]
    have h1 := KFacts.KS18.eq_one_of_pow_two_of_pow_three (hq2 _) h3
    rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hTP : CFSG.Open.pCoreOf 2 I ≤ CFSG.Open.pCoreOf 2 H := by
    have := CFSG.LieType.BorelTits.pCore_characteristic (G := I) 2
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 I).trans (map_subtype_le _)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I)
    exact hHI.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.Open.pCore 2 I))
  set R := CFSG.perfectResidual H with hR
  have hAc : ∀ (a : G) (ha : a ∈ A), ∀ r ∈ R,
      φ ⟨a, hAH ha⟩ * φ r = φ r * φ ⟨a, hAH ha⟩ := by
    intro a ha r hr
    have h1 := hTP (hcen a ha (r : G) ⟨r, hr, rfl⟩)
    have h2 : (⟨a, hAH ha⟩ * r * (⟨a, hAH ha⟩ : H)⁻¹ * r⁻¹ : H) ∈ P := by
      rw [Sec18.mem_pCore_iff_mem_pCoreOf]
      simpa using h1
    have h3 : φ (⟨a, hAH ha⟩ * r * (⟨a, hAH ha⟩ : H)⁻¹ * r⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  have hle : ∀ K : Subgroup X, ⁅K, K⁆ = K → K.map X.subtype ≤ R.map φ := by
    intro K hK
    have hKp : ⁅K.map X.subtype, K.map X.subtype⁆ = K.map X.subtype := by
      rw [← map_commutator, hK]
    rw [Sec18.map_perfectResidual_eq (QuotientGroup.mk'_surjective P)]
    exact le_perfectResidual_of_commutator_eq hKp
  set Ab : Subgroup X := ((A.subgroupOf H).map φ).subgroupOf X with hAb
  have hAbX : (A.subgroupOf H).map φ ≤ X := by
    rintro _ ⟨a, ha, rfl⟩
    exact haX (a : G) (mem_subgroupOf.mp ha)
  have hAbcard : Nat.card Ab = 27 := by
    have hAp : IsPGroup 3 (A.subgroupOf H) :=
      h.ctx444.isE27.isPGroup.of_equiv (subgroupOfEquivOfLe hAH).symm
    have hinf : A.subgroupOf H ⊓ φ.ker = ⊥ := by
      rw [hφ, QuotientGroup.ker_mk']
      exact inf_eq_bot_of_isPGroup_of_not_dvd Nat.prime_three hAp
        (not_three_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup)
    rw [hAb, Nat.card_congr (subgroupOfEquivOfLe hAbX).toEquiv,
      card_map_eq_of_inf_ker_eq_bot _ hinf, Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv,
      h.ctx444.isE27.2]
  have hAbcomm : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, hax⟩ := mem_subgroupOf.mp hx
    obtain ⟨b, hb, hby⟩ := mem_subgroupOf.mp hy
    have hab : a * b = b * a := Subtype.ext (by
      have := congrArg Subtype.val (h.ctx444.isE27.1.1.is_comm.comm
        (⟨(a : G), mem_subgroupOf.mp ha⟩ : A) ⟨(b : G), mem_subgroupOf.mp hb⟩)
      simpa using this)
    apply Subtype.ext
    change (x : H ⧸ P) * y = y * x
    rw [← hax, ← hby, ← map_mul, ← map_mul, hab]
  have hAbC : ∀ K : Subgroup X, ⁅K, K⁆ = K → Ab ≤ centralizer (K : Set X) := by
    intro K hK x hx
    rw [mem_centralizer_iff]
    intro k hk
    obtain ⟨r, hr, hrk⟩ := hle K hK ⟨k, hk, rfl⟩
    simp only [Subgroup.coe_subtype] at hrk
    obtain ⟨a, ha, hax⟩ := mem_subgroupOf.mp hx
    apply Subtype.ext
    change (k : H ⧸ P) * x = x * k
    rw [← hrk, ← hax]
    exact (hAc (a : G) (mem_subgroupOf.mp ha) r hr).symm
  rcases hXZ with ⟨⟨e⟩⟩ | ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩
  ·
    set L := projSL 3 (GaloisField 2 2)
    have : Group.IsPerfect L := isPerfect_projSL
    set Pw : Subgroup X := ((MonoidHom.inr (Multiplicative (ZMod 3)) L).range).comap
      e.toMonoidHom with hPw
    have hPwe : Pw.map e.toMonoidHom = (MonoidHom.inr (Multiplicative (ZMod 3)) L).range :=
      map_comap_eq_self_of_surjective e.surjective _
    set ePw : Pw ≃* L := (Pw.equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hPwe).trans
        ((MonoidHom.inr (Multiplicative (ZMod 3)) L).ofInjective
          (fun a b h => congrArg Prod.snd h)).symm) with hePw
    have hPwp : ⁅Pw, Pw⁆ = Pw := isPerfect_iff.mp
      (Group.IsPerfect.ofSurjective (f := ePw.symm.toMonoidHom) ePw.symm.surjective)
    have hsnd : ∀ x ∈ Ab, (e x).2 = 1 := by
      intro x hx
      have hc : (e x).2 ∈ center L := by
        rw [mem_center_iff]
        intro p
        have hpPw : e.symm (1, p) ∈ Pw := ⟨p, by
          change (1, p) = e (e.symm (1, p))
          rw [MulEquiv.apply_symm_apply]⟩
        have h1 := mem_centralizer_iff.mp (hAbC Pw hPwp hx) _ hpPw
        have h2 := congrArg (fun w => (e w).2) h1
        simpa using h2
      rw [center_projSL_eq_bot] at hc
      exact hc
    have hinj : Function.Injective (fun x : Ab => (e x).1) := by
      intro x y hxy
      apply Subtype.ext
      apply e.injective
      exact Prod.ext hxy ((hsnd x x.2).trans (hsnd y y.2).symm)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hAbcard, Nat.card_eq_fintype_card] at h1
    exact absurd h1 (by decide)
  ·
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    have hVp : ⁅V, V⁆ = V := isPerfect_iff.mp
      (Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective)
    have hAbU : Ab ≤ U := by
      rw [← KFacts.L34.centralizer_eq_of_isHeisSL hUV hcomm ⟨eV⟩ hcard]
      exact hAbC V hVp
    have hAbeq : Ab = U := eq_of_le_of_card_ge hAbU (by rw [hAbcard, hU.2.1])
    have hcenU : center U = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rw [mem_center_iff]
      intro v
      apply Subtype.ext
      have hu : (u : X) ∈ Ab := hAbeq ▸ u.2
      have hv : (v : X) ∈ Ab := hAbeq ▸ v.2
      exact hAbcomm _ hv _ hu
    have h1 := hU.1.2.2.2
    rw [hcenU, card_top, hU.2.1] at h1
    norm_num at h1

theorem Ctx4443.isSolvable_sup_zpowers {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s) :
    A ≤ normalizer (zpowers s : Set G) ∧ Group.IsSolvable (A ⊔ zpowers s : Subgroup G) := by
  have hs2 : IsPGroup 2 (zpowers s) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)).to_le (zpowers_le.mpr h.concl4442.1)
  have hAs : A ≤ normalizer (zpowers s : Set G) :=
    (le_centralizer_iff.mp (zpowers_le.mpr h.concl4442.2.1)).trans
      (centralizer_le_normalizer _)
  exact ⟨hAs, Sec18.isSolvable_sup_of_le_normalizer h.ctx444.isE27.1.1 hs2 hAs⟩

theorem Ctx4443.isZ3L34OrHeisSL34_map (h434 : Item4_34Sec) (h45 : Item4_5)
    {A M H : Subgroup G} {s : G} (h : Ctx4443 G A M H s) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLM : ¬ L ≤ M) (hsL : s ∈ normalizer (L : Set G))
    (hss : ¬ (zpowers s).map (starQuot G) ≤
      centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G)) := by
  obtain ⟨hAs, hsolv⟩ := Ctx4443.isSolvable_sup_zpowers h
  exact isZ3L34OrHeisSL34_of_item4_34Sec h434 h.ctx444 hL
    (h.ctx444.three_dvd_card_of_not_le h45 hL hLM) hLM
    (h.ctx444.le_normalizer_of_mem_thetaComponents h45 hL) (zpowers_le.mpr hsL) hAs
    (Ctx4443.not_three_dvd_card_zpowers h) hsolv hss

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item4443SL
