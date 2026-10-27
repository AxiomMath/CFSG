module
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4Planes
import CFSG.GroupTheory.AbelianSylowThreeComponents
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.GroupTheory.PGroup.OmegaComm
import CFSG.GroupTheory.ElemAbelianExtension
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.StronglyEmbedded.SteinbergBTPRegularCoreEquality
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.StronglyEmbedded.SteinbergCBPRegularEquivalences


public section
namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {c : Counterexample4 G}

namespace Case811L4
variable (t : Case811L4 c)

private theorem vA2_nonconstant :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd (vA2 : Multiplicative (Fin 4 → ZMod 3)) = fun _ => s := by
  decide
private theorem vA1_nonconstant :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd (vA1 : Multiplicative (Fin 4 → ZMod 3)) = fun _ => s := by
  decide
private theorem vD2_nonconstant :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd (vD2 : Multiplicative (Fin 4 → ZMod 3)) = fun _ => s := by
  decide

private theorem orderOf_a1 : orderOf t.a1 = 3 := t.orderOf_e (vA1_nonconstant)
private theorem orderOf_a2 : orderOf t.a2 = 3 := t.orderOf_e (vA2_nonconstant)
private theorem orderOf_d2 : orderOf t.d2 = 3 := t.orderOf_e (vD2_nonconstant)
private theorem card_zpowers_a1 : Nat.card (Subgroup.zpowers t.a1) = 3 :=
  t.card_zpowers_e (vA1_nonconstant)
private theorem card_zpowers_a2 : Nat.card (Subgroup.zpowers t.a2) = 3 :=
  t.card_zpowers_e (vA2_nonconstant)
private theorem card_zpowers_d2 : Nat.card (Subgroup.zpowers t.d2) = 3 :=
  t.card_zpowers_e (vD2_nonconstant)
private theorem a1_mem_A : t.a1 ∈ t.A := t.e_mem_A vA1
private theorem a2_mem_A : t.a2 ∈ t.A := t.e_mem_A vA2
private theorem d2_mem_A : t.d2 ∈ t.A := t.e_mem_A vD2
private theorem A_comm : ∀ x ∈ t.A, ∀ y ∈ t.A, x * y = y * x := by
  intro x hx y hy
  simpa using (t.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
private theorem A_pow_three : ∀ x ∈ t.A, x ^ 3 = 1 := t.elemAbelian.2

private noncomputable def Q : Subgroup G := Classical.choose t.sylow_a2
private theorem A_le_Q : t.A ≤ Q t := (Classical.choose_spec t.sylow_a2).1
private theorem Q_comm : IsMulCommutative ↥(Q t) := (Classical.choose_spec t.sylow_a2).2.1
private theorem Q_sylow :
    CFSG.ABGLocalTools.IsSylowOf 3 (Q t)
      (c.S.M ⊓ Subgroup.centralizer ({t.a2} : Set G)) :=
  (Classical.choose_spec t.sylow_a2).2.2
private theorem Q_le : Q t ≤ c.S.M ⊓ Subgroup.centralizer ({t.a2} : Set G) := (Q_sylow t).le
private theorem Q_le_M : Q t ≤ c.S.M := (Q_le t).trans inf_le_left
private theorem Q_isPGroup : IsPGroup 3 (Q t) := (Q_sylow t).isPGroup
private theorem a2_mem_Q : t.a2 ∈ Q t := (A_le_Q t) (a2_mem_A t)
private theorem a1_mem_Q : t.a1 ∈ Q t := (A_le_Q t) (a1_mem_A t)
private theorem d2_mem_Q : t.d2 ∈ Q t := (A_le_Q t) (d2_mem_A t)
private theorem zpowers_a1_le_Q : Subgroup.zpowers t.a1 ≤ Q t :=
  Subgroup.zpowers_le.mpr (a1_mem_Q t)
private theorem zpowers_d2_le_Q : Subgroup.zpowers t.d2 ≤ Q t :=
  Subgroup.zpowers_le.mpr (d2_mem_Q t)

private noncomputable def Omega : Subgroup G :=
  (CFSG.omega₁ ↥(Q t) (p := 3)).map (Q t).subtype

private theorem mem_Omega_iff {x : G} :
    x ∈ Omega t ↔ x ∈ Q t ∧ x ^ 3 = 1 := by
  haveI : IsMulCommutative ↥(Q t) := Q_comm t
  constructor
  · intro hx
    rw [Omega, Subgroup.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    have hq' : q ^ 3 = 1 :=
      (CFSG.mem_omega₁_iff_of_comm (X := ↥(Q t)) (p := 3) (fun a b => mul_comm' a b)).mp hq
    exact ⟨q.2, by simpa using congrArg Subtype.val hq'⟩
  · rintro ⟨hxQ, hx3⟩
    rw [Omega, Subgroup.mem_map]
    refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
    exact (CFSG.mem_omega₁_iff_of_comm (X := ↥(Q t)) (p := 3)
      (fun a b => mul_comm' a b)).mpr (by simpa using hx3)

private theorem A_le_Omega : t.A ≤ Omega t := by
  intro x hx
  exact (mem_Omega_iff t).mpr ⟨(A_le_Q t) hx, A_pow_three t x hx⟩

private theorem Omega_elemAbelian : IsElemAbelian 3 (Omega t) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsMulCommutative ↥(Q t) := Q_comm t
  have h : IsElemAbelian 3 (CFSG.omega₁ ↥(Q t) (p := 3)) :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.omega₁_of_isMulCommutative (p := 3) ↥(Q t))
  exact h.map (Q t).subtype

private theorem normalizer_Q_le_normalizer_Omega :
    Subgroup.normalizer (Q t : Set G) ≤ Subgroup.normalizer (Omega t : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hn' : ∀ y : G, y ∈ Q t ↔ n * y * n⁻¹ ∈ Q t :=
    (Subgroup.mem_normalizer_iff.mp hn)
  rw [mem_Omega_iff t, mem_Omega_iff t]
  constructor
  · rintro ⟨hxQ, hx3⟩
    refine ⟨(hn' x).mp hxQ, ?_⟩
    calc (n * x * n⁻¹) ^ 3 = (MulAut.conj n) (x ^ 3) := by
          rw [map_pow, MulAut.conj_apply]
      _ = 1 := by rw [hx3, map_one]
  · rintro ⟨hxQ, hx3⟩
    constructor
    · by_contra hx
      have hxn : x ∈ Q t := by
        by_contra hxq
        have h := (hn' x).mpr hxQ
        exact hxq h
      exact hx hxn
    ·
      have hxeq : x = (MulAut.conj n⁻¹) (n * x * n⁻¹) := by
        rw [MulAut.conj_apply]
        group
      rw [hxeq, ← map_pow, hx3, map_one]

private theorem Omega_eq_A : Omega t = t.A := by
  by_contra hne
  have hAΩ : t.A ≤ Omega t := A_le_Omega t
  have hcardle : Nat.card t.A ≤ Nat.card (Omega t) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hAΩ)
      (Subgroup.inclusion_injective hAΩ)
  have hcardne : Nat.card t.A ≠ Nat.card (Omega t) := by
    intro hc
    exact hne (Subgroup.eq_of_le_of_card_ge hAΩ (by rw [hc])).symm
  have hlt : Nat.card t.A < Nat.card (Omega t) := lt_of_le_of_ne hcardle hcardne
  obtain ⟨B, hBΩ, hBea, hBcard, hBne⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_pow_three_ne_of_lt hAΩ (Omega_elemAbelian t)
      t.card_A hlt
  have hΩM : Omega t ≤ c.S.M := (Subgroup.map_subtype_le _).trans (Q_le_M t)
  have hΩP : IsPGroup 3 (Omega t) :=
    (Q_isPGroup t).to_le (Subgroup.map_subtype_le _)
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (G := ↥c.S.M) (p := 3)
    (P := (Omega t).subgroupOf c.S.M) hΩP.comap_subtype
  let Sg : Subgroup G := (S : Subgroup ↥c.S.M).map c.S.M.subtype
  have hSg_syl : CFSG.ABGLocalTools.IsSylowOf 3 Sg c.S.M := ⟨S, rfl⟩
  have hΩSg : Omega t ≤ Sg := by
    have hmap : Subgroup.map c.S.M.subtype ((Omega t).subgroupOf c.S.M) ≤ Sg :=
      Subgroup.map_mono hS
    rwa [Subgroup.map_subgroupOf_eq_of_le hΩM] at hmap
  obtain ⟨k, hkM, hconj⟩ := (t.sylow).exists_mem_conj hSg_syl
  have hkΩ : Subgroup.map (MulAut.conj k⁻¹).toMonoidHom (Omega t) ≤ t.P := by
    rintro y ⟨x, hxΩ, rfl⟩
    simpa [MulAut.conj_apply] using (hconj x).mp (hΩSg hxΩ)
  have hBkP : Subgroup.map (MulAut.conj k⁻¹).toMonoidHom B ≤ t.P :=
    (Subgroup.map_mono hBΩ).trans hkΩ
  have hAkP : Subgroup.map (MulAut.conj k⁻¹).toMonoidHom t.A ≤ t.P :=
    (Subgroup.map_mono hAΩ).trans hkΩ
  have hBk_card : Nat.card (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom B) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hBcard]
    norm_num
  have hAk_card : Nat.card (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom t.A) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, t.card_A]
  have hBk_eq : Subgroup.map (MulAut.conj k⁻¹).toMonoidHom B = t.A :=
    t.unique _ hBkP (hBea.map _) hBk_card
  have hAk_eq : Subgroup.map (MulAut.conj k⁻¹).toMonoidHom t.A = t.A :=
    t.unique _ hAkP (t.elemAbelian.map _) hAk_card
  have hmap : Subgroup.map (MulAut.conj k⁻¹).toMonoidHom B =
      Subgroup.map (MulAut.conj k⁻¹).toMonoidHom t.A := by rw [hBk_eq, hAk_eq]
  have hBA := congrArg (Subgroup.comap (MulAut.conj k⁻¹).toMonoidHom) hmap
  have hBc : Subgroup.comap (MulAut.conj k⁻¹).toMonoidHom
      (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom B) = B :=
    Subgroup.comap_map_eq_self_of_injective (MulAut.conj k⁻¹).injective B
  have hAc : Subgroup.comap (MulAut.conj k⁻¹).toMonoidHom
      (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom t.A) = t.A :=
    Subgroup.comap_map_eq_self_of_injective (MulAut.conj k⁻¹).injective t.A
  rw [hBc, hAc] at hBA
  exact hBne hBA



private abbrev H : Subgroup G := Subgroup.centralizer ({t.a2} : Set G)

private theorem A_le_H : t.A ≤ H t := by
  intro x hx
  rw [H, Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y = t.a2 := by simpa using hy
  subst y
  exact (A_comm t x hx t.a2 (a2_mem_A t)).symm

private theorem Q_le_H : Q t ≤ H t := by
  simpa [H] using (Q_le t).trans inf_le_right

private theorem normalizer_Q_le_M
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    Subgroup.normalizer (Q t : Set G) ≤ c.S.M := by
  have hsub : Subgroup.normalizer (Q t : Set G) ≤
      Subgroup.normalizer (Omega t : Set G) := normalizer_Q_le_normalizer_Omega t
  rw [Omega_eq_A t] at hsub
  exact hsub.trans (normalizer_A_le t hN1 hN3)

private theorem Q_sylow_H
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Q t) (H t) := by
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 (Q t) (c.S.M ⊓ H t) := by
    simpa [H] using Q_sylow t
  have hN : Subgroup.normalizer (Q t : Set G) ⊓ H t ≤ c.S.M :=
    inf_le_left.trans (normalizer_Q_le_M t hN1 hN3)
  exact CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le (H := c.S.M) (M := H t) hT hN

private theorem pRank_Q_eq_three : CFSG.Open.pRank 3 (Q t) = 3 := by
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) ?_
    intro E hEQ hEea
    have hEA : E ≤ t.A := by
      intro e he
      have heΩ : e ∈ Omega t :=
        (mem_Omega_iff t).mpr ⟨hEQ he, hEea.2 e he⟩
      rwa [Omega_eq_A t] at heΩ
    exact (Subgroup.card_le_of_le hEA).trans (by rw [t.card_A]; norm_num)
  · exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (A_le_Q t)
      t.elemAbelian (k := 3) (by rw [t.card_A]; norm_num)

private theorem pRank_H_eq_three
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.Open.pRank 3 (H t) = 3 := by
  have hQH : Q t ≤ H t := Q_le_H t
  obtain ⟨S, hS⟩ := (Q_sylow_H t hN1 hN3).exists_sylow_eq_subgroupOf
  have hQsub : CFSG.Open.pRank 3 ((Q t).subgroupOf (H t)) =
      CFSG.Open.pRank 3 (Q t) :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.K31.pRank_subgroupOf_eq (p := 3) (by norm_num) hQH
  have hSrank : CFSG.Open.pRank 3 (S : Subgroup ↥(H t)) = 3 := by
    rw [hS, hQsub, pRank_Q_eq_three t]
  have hsyl := CFSG.SectionRank.pRank_sylow (p := 3) S
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(H t)) = 3 := by
    rw [← hsyl.1, hSrank]
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H t), htop]



private theorem mem_normalizer_zpowers_a2_of_mem_H {n : G} (hn : n ∈ H t) :
    n ∈ Subgroup.normalizer (Subgroup.zpowers t.a2 : Set G) := by
  have hcomm : Commute n t.a2 := by
    have h := (Subgroup.mem_centralizer_iff.mp hn) t.a2 (by simp)
    exact h.symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    have hc : Commute n (t.a2 ^ k) := hcomm.zpow_right k
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hc : Commute n⁻¹ (t.a2 ^ k) := hcomm.inv_left.zpow_right k
    symm
    calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
      _ = n⁻¹ * t.a2 ^ k * n := by rw [← hk]
      _ = t.a2 ^ k * n⁻¹ * n := by rw [hc.eq]
      _ = t.a2 ^ k := by rw [mul_assoc, inv_mul_cancel, mul_one]

private theorem normalizer_le_normalizer_sup_zpowers_a2 {U : Subgroup G} :
    Subgroup.normalizer (U : Set G) ⊓ H t ≤
      Subgroup.normalizer (U ⊔ Subgroup.zpowers t.a2 : Subgroup G) := by
  intro n hn
  exact CFSG.StronglyEmbedded.mem_normalizer_sup hn.1
    (mem_normalizer_zpowers_a2_of_mem_H t hn.2)

private theorem pRank_A_eq_three : CFSG.Open.pRank 3 (t.A) = 3 := by
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) ?_
    intro E hEA _
    exact (Subgroup.card_le_of_le hEA).trans (by rw [t.card_A]; norm_num)
  · exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl t.A)
      t.elemAbelian (k := 3) (by rw [t.card_A]; norm_num)

private theorem le_A_of_le_Q_of_pow_three {U : Subgroup G} (hUQ : U ≤ Q t)
    (hUexp : ∀ u ∈ U, u ^ 3 = 1) : U ≤ t.A := by
  intro u hu
  have huΩ : u ∈ Omega t := (mem_Omega_iff t).mpr ⟨hUQ hu, hUexp u hu⟩
  rwa [Omega_eq_A t] at huΩ

private theorem isElemAbelian_of_le_Q_of_pow_three {U : Subgroup G} (hUQ : U ≤ Q t)
    (hUexp : ∀ u ∈ U, u ^ 3 = 1) : IsElemAbelian 3 U := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, hUexp⟩
  exact Subtype.ext (by
    haveI : IsMulCommutative ↥(Q t) := Q_comm t
    simpa using congrArg Subtype.val
      (mul_comm' (⟨a.1, hUQ a.2⟩ : Q t) ⟨b.1, hUQ b.2⟩))

private theorem isElemAbelian_sup_zpowers_a2_of_le_Q {U : Subgroup G} (hUQ : U ≤ Q t)
    (hUexp : ∀ u ∈ U, u ^ 3 = 1) :
    IsElemAbelian 3 (U ⊔ Subgroup.zpowers t.a2) := by
  refine IsElemAbelian.sup_of_commute (isElemAbelian_of_le_Q_of_pow_three t hUQ hUexp)
    (isElemAbelian_zpowers (by rw [← orderOf_a2 t]; exact pow_orderOf_eq_one t.a2)) ?_
  intro u hu z hz
  exact A_comm t u (le_A_of_le_Q_of_pow_three t hUQ hUexp hu) z
    ((Subgroup.zpowers_le.mpr (a2_mem_A t)) hz)

private theorem sup_zpowers_a2_le_A_of_le_Q {U : Subgroup G} (hUQ : U ≤ Q t)
    (hUexp : ∀ u ∈ U, u ^ 3 = 1) : U ⊔ Subgroup.zpowers t.a2 ≤ t.A :=
  sup_le (le_A_of_le_Q_of_pow_three t hUQ hUexp)
    (Subgroup.zpowers_le.mpr (a2_mem_A t))

private theorem two_le_pRank_sup_zpowers_a2_of_not_le {U : Subgroup G} (hUQ : U ≤ Q t)
    (hUexp : ∀ u ∈ U, u ^ 3 = 1) (hUne : ¬ U ≤ Subgroup.zpowers t.a2) :
    2 ≤ CFSG.Open.pRank 3 (U ⊔ Subgroup.zpowers t.a2) := by
  obtain ⟨u, huU, huNot⟩ := Set.not_subset.mp hUne
  have hu1 : u ≠ 1 := by
    intro h
    exact huNot (by simpa [h] using Subgroup.one_mem (Subgroup.zpowers t.a2))
  have huord : orderOf u = 3 := orderOf_eq_prime (hUexp u huU) hu1
  have hEu := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (X := Subgroup.zpowers t.a2) (v := u) (card_zpowers_a2 t) huord huNot
    (by
      intro a ha
      exact A_comm t a ((Subgroup.zpowers_le.mpr (a2_mem_A t)) ha) u
        (le_A_of_le_Q_of_pow_three t hUQ hUexp huU))
  have hle : Subgroup.zpowers t.a2 ⊔ Subgroup.zpowers u ≤ U ⊔ Subgroup.zpowers t.a2 :=
    sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left huU))
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hle hEu.1 (k := 2) hEu.2

private theorem pRank_sup_zpowers_a2_le_three {U : Subgroup G} (hUQ : U ≤ Q t)
    (hUexp : ∀ u ∈ U, u ^ 3 = 1) :
    CFSG.Open.pRank 3 (U ⊔ Subgroup.zpowers t.a2) ≤ 3 :=
  (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
    (sup_zpowers_a2_le_A_of_le_Q t hUQ hUexp)).trans (le_of_eq (pRank_A_eq_three t))

private theorem normalizer_le_of_le_Q_of_pow_three
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {U : Subgroup G} (hUQ : U ≤ Q t) (hUexp : ∀ u ∈ U, u ^ 3 = 1)
    (hUne : ¬ U ≤ Subgroup.zpowers t.a2) :
    Subgroup.normalizer (U : Set G) ⊓ H t ≤ c.S.M := by
  have hVea : IsElemAbelian 3 (U ⊔ Subgroup.zpowers t.a2) :=
    isElemAbelian_sup_zpowers_a2_of_le_Q t hUQ hUexp
  have hVA : U ⊔ Subgroup.zpowers t.a2 ≤ t.A :=
    sup_zpowers_a2_le_A_of_le_Q t hUQ hUexp
  have hNV : Subgroup.normalizer (U : Set G) ⊓ H t ≤
      Subgroup.normalizer (U ⊔ Subgroup.zpowers t.a2 : Subgroup G) :=
    normalizer_le_normalizer_sup_zpowers_a2 t (U := U)
  by_cases hVAeq : (U ⊔ Subgroup.zpowers t.a2 : Subgroup G) = t.A
  · rw [hVAeq] at hNV
    exact hNV.trans (normalizer_A_le t hN1 hN3)
  · have h2 : 2 ≤ CFSG.Open.pRank 3 (U ⊔ Subgroup.zpowers t.a2) :=
      two_le_pRank_sup_zpowers_a2_of_not_le t hUQ hUexp hUne
    have h3 : CFSG.Open.pRank 3 (U ⊔ Subgroup.zpowers t.a2) ≤ 3 :=
      pRank_sup_zpowers_a2_le_three t hUQ hUexp
    have hp : CFSG.Open.pRank 3 (U ⊔ Subgroup.zpowers t.a2) = 2 := by
      have hne3 : CFSG.Open.pRank 3 (U ⊔ Subgroup.zpowers t.a2) ≠ 3 := by
        intro h
        have hcard : Nat.card (U ⊔ Subgroup.zpowers t.a2 : Subgroup G) = 27 := by
          rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hVea, h]
          norm_num
        exact hVAeq (Subgroup.eq_of_le_of_card_ge hVA (by rw [hcard, t.card_A]))
      omega
    have hcardV : Nat.card (U ⊔ Subgroup.zpowers t.a2 : Subgroup G) = 9 := by
      rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hVea, hp]
      norm_num
    exact hNV.trans (normalizer_le_of_le_A_of_card_nine t hN1 hN3 hVA hcardV)



private theorem pPrimeCore_H_le_M
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    (CFSG.pPrimeCore 3 ↥(H t)).map (H t).subtype ≤ c.S.M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥(H t)).map (H t).subtype
  change O ≤ c.S.M
  have hHnorm : H t ≤ Subgroup.normalizer (O : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨o, ho, rfl⟩
      refine ⟨⟨h, hh⟩ * o * ⟨h, hh⟩⁻¹,
        (CFSG.pPrimeCore_normal (p := 3) (G := ↥(H t))).conj_mem o ho ⟨h, hh⟩, ?_⟩
      rfl
    · intro hx
      obtain ⟨o, ho, hxo⟩ := hx
      let hH : ↥(H t) := ⟨h, hh⟩
      refine ⟨hH⁻¹ * o * hH,
        ?_, ?_⟩
      · have hconj := (CFSG.pPrimeCore_normal (p := 3) (G := ↥(H t))).conj_mem o ho hH⁻¹
        simpa [hH] using hconj
      · have ho_eq : (o : G) = h * x * h⁻¹ := hxo
        change (hH : G)⁻¹ * (o : G) * (hH : G) = x
        rw [show (hH : G) = h from rfl, ho_eq]
        group
  have hAO : t.A ≤ Subgroup.normalizer (O : Set G) := (A_le_H t).trans hHnorm
  have hOcop : Nat.Coprime 3 (Nat.card O) := by
    have hOcard : Nat.card O = Nat.card ↥(CFSG.pPrimeCore 3 ↥(H t)) := by
      dsimp [O]
      rw [Subgroup.card_map_of_injective (H t).subtype_injective]
    rw [hOcard]
    exact CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥(H t))
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
    (G := G) (p := 3) (by norm_num) (A := t.A) (X := O) t.elemAbelian
    (by rw [t.card_A]; norm_num) hAO hOcop
  rw [← hgen]
  refine iSup₂_le fun B hB => ?_
  have hBA : B ≤ t.A := hB.1
  have hBcard : Nat.card B = 9 := by
    have h := hB.2
    rw [t.card_A] at h
    omega
  calc O ⊓ Subgroup.centralizer (B : Set G)
      ≤ Subgroup.normalizer (B : Set G) :=
        inf_le_right.trans (Subgroup.centralizer_le_normalizer (B : Set G))
    _ ≤ c.S.M := normalizer_le_of_le_A_of_card_nine t hN1 hN3 hBA hBcard

private theorem mem_normalizer_Q_of_mem_normalizer_subgroupOf {n : ↥(H t)}
    (hn : n ∈ Subgroup.normalizer
      (((Q t).subgroupOf (H t) : Subgroup ↥(H t)) : Set ↥(H t))) :
    (n : G) ∈ Subgroup.normalizer (Q t : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  constructor
  · intro hxQ
    have hxH : x ∈ H t := Q_le_H t hxQ
    have hxS : (⟨x, hxH⟩ : ↥(H t)) ∈ (Q t).subgroupOf (H t) := hxQ
    have h := (hn ⟨x, hxH⟩).mp hxS
    simpa [Subgroup.mem_subgroupOf] using h
  · intro hxQ
    have hxH : x ∈ H t := by
      have hxQH : (n : G) * x * (n : G)⁻¹ ∈ H t := Q_le_H t hxQ
      have h1 : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) ∈ H t :=
        (H t).mul_mem ((H t).inv_mem n.2) hxQH
      have h2 : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) ∈ H t :=
        (H t).mul_mem h1 n.2
      simpa [mul_assoc] using h2
    have hxS : ((n : ↥(H t)) * ⟨x, hxH⟩ * n⁻¹) ∈ (Q t).subgroupOf (H t) := by
      rw [Subgroup.mem_subgroupOf]
      exact hxQ
    have h := (hn ⟨x, hxH⟩).mpr hxS
    exact h

private theorem weaklyClosed_zpowers_in_Q {x : G} (hxQ : x ∈ Q t) (hxH : x ∈ H t)
    (hN : ∀ n : G, n ∈ Subgroup.normalizer (t.A : Set G) → n * t.a2 = t.a2 * n →
      n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G))
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {h : G} (hh : h ∈ H t)
    (hle : CFSG.conjugate (Subgroup.zpowers x) h ≤ Q t) :
    CFSG.conjugate (Subgroup.zpowers x) h = Subgroup.zpowers x := by
  classical
  haveI : IsMulCommutative ↥(Q t) := Q_comm t
  obtain ⟨S, hS⟩ := (Q_sylow_H t hN1 hN3).exists_sylow_eq_subgroupOf
  let hH : ↥(H t) := ⟨h, hh⟩
  let xH : ↥(H t) := ⟨x, hxH⟩
  have hxCent : xH ∈ Subgroup.centralizer (S : Set ↥(H t)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ : (y : G) ∈ Q t := by
      have hyS : y ∈ (S : Subgroup ↥(H t)) := hy
      rw [hS] at hyS
      exact hyS
    exact Subtype.ext (by
      simpa using mul_comm' (⟨(y : G), hyQ⟩ : Q t) (⟨x, hxQ⟩ : Q t))
  have hxmap : (MulAut.conj h⁻¹) x ∈ CFSG.conjugate (Subgroup.zpowers x) h :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers x)
  have hyQ : h⁻¹ * x * h ∈ Q t := by
    have := hle hxmap
    simpa [CFSG.conjugate, MulAut.conj_apply] using this
  let yH : ↥(H t) := ⟨h⁻¹ * x * h, Q_le_H t hyQ⟩
  have hyCent : yH ∈ Subgroup.centralizer (S : Set ↥(H t)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyQ' : (y : G) ∈ Q t := by
      have hyS : y ∈ (S : Subgroup ↥(H t)) := hy
      rw [hS] at hyS
      exact hyS
    exact Subtype.ext (by
      simpa [yH] using mul_comm' (⟨(y : G), hyQ'⟩ : Q t)
        (⟨h⁻¹ * x * h, hyQ⟩ : Q t))
  have hhH : hH⁻¹ * xH * hH = yH := by rfl
  obtain ⟨n, hnS, heq⟩ :=
    Sylow.conj_eq_normalizer_conj_of_mem_centralizer S xH hH hxCent (hhH ▸ hyCent)
  have heqG : h⁻¹ * x * h = (n : G)⁻¹ * x * (n : G) := by
    have := congrArg Subtype.val heq
    simpa [hH, xH] using this
  let Sg : Subgroup ↥(H t) := S
  have hSg : Sg = (Q t).subgroupOf (H t) := hS
  have hnS' : n ∈ Subgroup.normalizer (Sg : Set ↥(H t)) := hnS
  rw [hSg] at hnS'
  have hnQ : (n : G) ∈ Subgroup.normalizer (Q t : Set G) :=
    mem_normalizer_Q_of_mem_normalizer_subgroupOf t hnS'
  have hnA : (n : G) ∈ Subgroup.normalizer (t.A : Set G) := by
    have h := (normalizer_Q_le_normalizer_Omega t) hnQ
    rwa [Omega_eq_A t] at h
  have hncent : (n : G) * t.a2 = t.a2 * (n : G) := by
    have h := (Subgroup.mem_centralizer_iff.mp n.2) t.a2 (by simp)
    exact h.symm
  have hnD : (n : G) ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := hN n hnA hncent
  have hconjEq : CFSG.conjugate (Subgroup.zpowers x) h =
      CFSG.conjugate (Subgroup.zpowers x) (n : G) := by
    rw [CFSG.conjugate, CFSG.conjugate, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    have hxeq : (MulEquiv.toMonoidHom (MulAut.conj h⁻¹)) x =
        (MulEquiv.toMonoidHom (MulAut.conj ((n : G)⁻¹))) x := by
      simpa [MulAut.conj_apply] using heqG
    rw [hxeq]
  rw [hconjEq, CFSG.conjugate_eq_self_of_mem_normalizer hnD]

private theorem H_ne_top : H t ≠ ⊤ := by
  haveI : IsSimpleGroup G := c.standing.simple
  intro htop
  have ha2center : t.a2 ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ H t := by rw [htop]; trivial
    have h := (Subgroup.mem_centralizer_iff.mp hg) t.a2 (by simp)
    exact h.symm
  have hDcenter : Subgroup.zpowers t.a2 ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr ha2center
  have hnormal : (Subgroup.zpowers t.a2).Normal :=
    Subgroup.Normal.mk fun n hn g => by
      have hc := Subgroup.mem_center_iff.mp (hDcenter hn) g
      have hconj : g * n * g⁻¹ = n := by
        calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [hc]
          _ = n := by group
      rwa [hconj]
  haveI : (Subgroup.zpowers t.a2).Normal := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers t.a2) with hbot | hDtop
  · have ha2bot : t.a2 ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact Subgroup.mem_zpowers t.a2
    have ha21 : t.a2 = 1 := Subgroup.mem_bot.mp ha2bot
    have hord : orderOf (1 : G) = 3 := by simpa [ha21] using orderOf_a2 t
    simp at hord
  · have hcomm : ∀ x y : G, x * y = y * x := by
      intro x y
      have hx : x ∈ Subgroup.zpowers t.a2 := by rw [hDtop]; trivial
      have hy : y ∈ Subgroup.zpowers t.a2 := by rw [hDtop]; trivial
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← zpow_add, add_comm]
    obtain ⟨x, y, hxy⟩ := c.standing.nonab
    exact hxy (hcomm x y)



private theorem QH_sylow_top
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 ((Q t).subgroupOf (H t)) ⊤ := by
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (K := H t)]
  simpa [Subgroup.map_subgroupOf_eq_of_le (Q_le_H t), Subgroup.map_top,
    Subgroup.range_subtype] using Q_sylow_H t hN1 hN3

private theorem QH_comm : IsMulCommutative ↥((Q t).subgroupOf (H t)) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  apply Subtype.ext
  haveI : IsMulCommutative ↥(Q t) := Q_comm t
  simpa using congrArg Subtype.val
    (mul_comm' (⟨a.1.1, a.2⟩ : Q t) (⟨b.1.1, b.2⟩ : Q t))

private theorem weaklyClosed_zpowers_in_Q_subgroupOf {x : G} (hxQ : x ∈ Q t)
    (hxH : x ∈ H t)
    (hN : ∀ n : G, n ∈ Subgroup.normalizer (t.A : Set G) → n * t.a2 = t.a2 * n →
      n ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G))
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn
      ((Subgroup.zpowers x).subgroupOf (H t)) ((Q t).subgroupOf (H t)) := by
  intro g hg
  have hgH : (g : G) ∈ H t := g.2
  have hmap_le : CFSG.conjugate (Subgroup.zpowers x) (g : G) ≤ Q t := by
    have hmap := Subgroup.map_mono (f := (H t).subtype) hg
    rw [CFSG.StronglyEmbedded.map_subtype_conjugate,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hxH)] at hmap
    rwa [Subgroup.map_subgroupOf_eq_of_le (Q_le_H t)] at hmap
  have hDeq := weaklyClosed_zpowers_in_Q t hxQ hxH hN hN1 hN3 hgH hmap_le
  have hmapEq : Subgroup.map (H t).subtype
      (CFSG.conjugate ((Subgroup.zpowers x).subgroupOf (H t)) g) =
      Subgroup.map (H t).subtype ((Subgroup.zpowers x).subgroupOf (H t)) := by
    rw [CFSG.StronglyEmbedded.map_subtype_conjugate,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hxH)]
    exact hDeq
  exact (Subgroup.map_injective (H t).subtype_injective) hmapEq

private theorem zpowers_a1_le_H : Subgroup.zpowers t.a1 ≤ H t :=
  Subgroup.zpowers_le.mpr (A_le_H t (a1_mem_A t))

private theorem zpowers_d2_le_H : Subgroup.zpowers t.d2 ≤ H t :=
  Subgroup.zpowers_le.mpr (A_le_H t (d2_mem_A t))

private theorem weaklyClosed_a1_in_Q_subgroupOf
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn
      ((Subgroup.zpowers t.a1).subgroupOf (H t)) ((Q t).subgroupOf (H t)) :=
  weaklyClosed_zpowers_in_Q_subgroupOf t (a1_mem_Q t)
    (A_le_H t (a1_mem_A t))
    (fun n hnA hncent =>
      (mem_normalizer_zpowers_of_mem_normalizer_A t hN1 hN3 hnA hncent).1)
    hN1 hN3

private theorem weaklyClosed_d2_in_Q_subgroupOf
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn
      ((Subgroup.zpowers t.d2).subgroupOf (H t)) ((Q t).subgroupOf (H t)) :=
  weaklyClosed_zpowers_in_Q_subgroupOf t (d2_mem_Q t)
    (A_le_H t (d2_mem_A t))
    (fun n hnA hncent =>
      (mem_normalizer_zpowers_of_mem_normalizer_A t hN1 hN3 hnA hncent).2)
    hN1 hN3

private theorem pRank_normalClosure_eq_one_of_weaklyClosed_in_Q
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {Z : Subgroup ↥(H t)} (hZcard : Nat.card Z = 3)
    (hZQ : Z ≤ (Q t).subgroupOf (H t))
    (hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z ((Q t).subgroupOf (H t))) :
    CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set ↥(H t))) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hK : CFSG.Open.IsKGroup ↥(H t) :=
    CFSG.Open.IsKProper.isKGroup c.standing.kProper (H t) (H_ne_top t)
  have htop3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(H t)) = 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H t)]
    exact pRank_H_eq_three t hN1 hN3
  have hrank : CFSG.Open.pRank 3 ((Q t).subgroupOf (H t)) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top).trans
      (le_of_eq htop3)
  have hΩ : ∀ x ∈ (Q t).subgroupOf (H t), x ^ 3 = 1 →
      ∀ y ∈ (Q t).subgroupOf (H t), y ^ 3 = 1 → x * y = y * x := by
    intro x hx _ y hy _
    haveI : IsMulCommutative ↥((Q t).subgroupOf (H t)) := QH_comm t
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥((Q t).subgroupOf (H t)))
      (⟨y, hy⟩ : ↥((Q t).subgroupOf (H t))))
  exact hK332 ↥(H t) hK ((Q t).subgroupOf (H t)) (QH_sylow_top t hN1 hN3)
    hΩ hrank Z hZQ hZcard hwc

private def H1 : Subgroup G :=
  (Subgroup.normalClosure (((Subgroup.zpowers t.a1).subgroupOf (H t) : Subgroup ↥(H t)) :
    Set ↥(H t))).map (H t).subtype

private def H2 : Subgroup G :=
  (Subgroup.normalClosure (((Subgroup.zpowers t.d2).subgroupOf (H t) : Subgroup ↥(H t)) :
    Set ↥(H t))).map (H t).subtype

private theorem H1_le_H : H1 t ≤ H t := Subgroup.map_subtype_le _

private theorem H2_le_H : H2 t ≤ H t := Subgroup.map_subtype_le _

private theorem pRank_H1_eq_one
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.Open.pRank 3 (H1 t) = 1 := by
  have hZcard : Nat.card ((Subgroup.zpowers t.a1).subgroupOf (H t)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_a1_le_H t)).toEquiv]
    exact card_zpowers_a1 t
  have hZQ : (Subgroup.zpowers t.a1).subgroupOf (H t) ≤ (Q t).subgroupOf (H t) := by
    intro x hx
    exact zpowers_a1_le_Q t hx
  have hrankH := pRank_normalClosure_eq_one_of_weaklyClosed_in_Q t hK332 hN1 hN3
    hZcard hZQ (weaklyClosed_a1_in_Q_subgroupOf t hN1 hN3)
  have hH1le : H1 t ≤ H t := Subgroup.map_subtype_le _
  have hsub : (H1 t).subgroupOf (H t) =
      Subgroup.normalClosure (((Subgroup.zpowers t.a1).subgroupOf (H t) : Subgroup ↥(H t)) :
        Set ↥(H t)) :=
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have h := CFSG.LocalAnalysis.UniquenessCase.UCK.K31.pRank_subgroupOf_eq
    (p := 3) (by norm_num) hH1le
  rw [hsub, hrankH] at h
  exact h.symm

private theorem pRank_H2_eq_one
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.Open.pRank 3 (H2 t) = 1 := by
  have hZcard : Nat.card ((Subgroup.zpowers t.d2).subgroupOf (H t)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_d2_le_H t)).toEquiv]
    exact card_zpowers_d2 t
  have hZQ : (Subgroup.zpowers t.d2).subgroupOf (H t) ≤ (Q t).subgroupOf (H t) := by
    intro x hx
    exact zpowers_d2_le_Q t hx
  have hrankH := pRank_normalClosure_eq_one_of_weaklyClosed_in_Q t hK332 hN1 hN3
    hZcard hZQ (weaklyClosed_d2_in_Q_subgroupOf t hN1 hN3)
  have hH2le : H2 t ≤ H t := Subgroup.map_subtype_le _
  have hsub : (H2 t).subgroupOf (H t) =
      Subgroup.normalClosure (((Subgroup.zpowers t.d2).subgroupOf (H t) : Subgroup ↥(H t)) :
        Set ↥(H t)) :=
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have h := CFSG.LocalAnalysis.UniquenessCase.UCK.K31.pRank_subgroupOf_eq
    (p := 3) (by norm_num) hH2le
  rw [hsub, hrankH] at h
  exact h.symm

private theorem nonconstant_vA1_mul_vD2_inv :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd
      ((vA1 : Multiplicative (Fin 4 → ZMod 3)) * vD2⁻¹) = fun _ => s := by
  decide

private theorem nonconstant_vA1_mul_vD2_sq_inv :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd
      ((vA1 : Multiplicative (Fin 4 → ZMod 3)) * (vD2 ^ 2)⁻¹) = fun _ => s := by
  decide

private theorem nonconstant_vD2_mul_vA2_inv :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd
      ((vD2 : Multiplicative (Fin 4 → ZMod 3)) * vA2⁻¹) = fun _ => s := by
  decide

private theorem nonconstant_vD2_mul_vA2_sq_inv :
    ¬ ∃ s : ZMod 3, Multiplicative.toAdd
      ((vD2 : Multiplicative (Fin 4 → ZMod 3)) * (vA2 ^ 2)⁻¹) = fun _ => s := by
  decide

private theorem swap_vA2 :
    (Multiplicative.ofAdd (fun i => Multiplicative.toAdd
      (vA2 : Multiplicative (Fin 4 → ZMod 3)) (Equiv.swap 0 1 i))) =
      (vA2⁻¹ : Multiplicative (Fin 4 → ZMod 3)) := by
  decide

private theorem zpowers_a1_ne_zpowers_d2 : Subgroup.zpowers t.a1 ≠ Subgroup.zpowers t.d2 := by
  intro heq
  have ha1mem : t.a1 ∈ Subgroup.zpowers t.d2 := heq ▸ Subgroup.mem_zpowers t.a1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha1mem
  have hd2pow : t.d2 ^ (3 : ℤ) = 1 := by
    simpa [zpow_natCast] using ((orderOf_d2 t) ▸ pow_orderOf_eq_one t.d2)
  have hkmod : t.d2 ^ k = t.d2 ^ (k % 3) := zpow_eq_zpow_emod k hd2pow
  have har : t.a1 = t.d2 ^ (k % 3) := by rw [← hk, hkmod]
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases h : k % 3
  · have ha1 : t.a1 = 1 := by simpa [h] using har
    have hord : orderOf (1 : G) = 3 := by simpa [ha1] using orderOf_a1 t
    simp at hord
  · have ha1 : t.a1 = t.d2 := by simpa [h] using har
    have hprod : t.e ((vA1 : Multiplicative (Fin 4 → ZMod 3)) * vD2⁻¹) = 1 := by
      rw [map_mul]
      rw [show t.e (vD2⁻¹) = (t.e vD2)⁻¹ from map_inv t.e vD2]
      rw [show t.e vA1 = t.d2 from ha1, show t.e vD2 = t.d2 from rfl]
      simp
    exact nonconstant_vA1_mul_vD2_inv ((t.e_eq_one_iff _).mp hprod)
  · have ha1z : t.a1 = t.d2 ^ (2 : ℤ) := by simpa [h] using har
    have ha1 : t.a1 = t.d2 ^ 2 := by simpa [zpow_ofNat] using ha1z
    have hprod : t.e ((vA1 : Multiplicative (Fin 4 → ZMod 3)) * (vD2 ^ 2)⁻¹) = 1 := by
      rw [map_mul]
      rw [show t.e ((vD2 ^ 2)⁻¹) = (t.e (vD2 ^ 2))⁻¹ from map_inv t.e (vD2 ^ 2)]
      rw [map_pow]
      rw [show t.e vA1 = t.d2 ^ 2 from ha1, show t.e vD2 = t.d2 from rfl]
      simp
    exact nonconstant_vA1_mul_vD2_sq_inv ((t.e_eq_one_iff _).mp hprod)

private theorem d2_not_mem_zpowers_a2 : t.d2 ∉ Subgroup.zpowers t.a2 := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have ha2pow : t.a2 ^ (3 : ℤ) = 1 := by
    simpa [zpow_natCast] using ((orderOf_a2 t) ▸ pow_orderOf_eq_one t.a2)
  have hkmod : t.a2 ^ k = t.a2 ^ (k % 3) := zpow_eq_zpow_emod k ha2pow
  have har : t.d2 = t.a2 ^ (k % 3) := by rw [← hk, hkmod]
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases h : k % 3
  · have hd2 : t.d2 = 1 := by simpa [h] using har
    have hord : orderOf (1 : G) = 3 := by simpa [hd2] using orderOf_d2 t
    simp at hord
  · have hd2 : t.d2 = t.a2 := by simpa [h] using har
    have hprod : t.e ((vD2 : Multiplicative (Fin 4 → ZMod 3)) * vA2⁻¹) = 1 := by
      rw [map_mul]
      rw [show t.e (vA2⁻¹) = (t.e vA2)⁻¹ from map_inv t.e vA2]
      rw [show t.e vD2 = t.a2 from hd2, show t.e vA2 = t.a2 from rfl]
      simp
    exact nonconstant_vD2_mul_vA2_inv ((t.e_eq_one_iff _).mp hprod)
  · have hd2z : t.d2 = t.a2 ^ (2 : ℤ) := by simpa [h] using har
    have hd2 : t.d2 = t.a2 ^ 2 := by simpa [zpow_ofNat] using hd2z
    have hprod : t.e ((vD2 : Multiplicative (Fin 4 → ZMod 3)) * (vA2 ^ 2)⁻¹) = 1 := by
      rw [map_mul]
      rw [show t.e ((vA2 ^ 2)⁻¹) = (t.e (vA2 ^ 2))⁻¹ from map_inv t.e (vA2 ^ 2)]
      rw [map_pow]
      rw [show t.e vD2 = t.a2 ^ 2 from hd2, show t.e vA2 = t.a2 from rfl]
      simp
    exact nonconstant_vD2_mul_vA2_sq_inv ((t.e_eq_one_iff _).mp hprod)

private theorem exists_conj_a2_inv :
    ∃ n ∈ c.L, n * t.a2 * n⁻¹ = t.a2⁻¹ := by
  obtain ⟨n, hnL, hperm⟩ := t.exists_perm (Equiv.swap 0 1)
  refine ⟨n, hnL, ?_⟩
  have h := hperm vA2
  rw [swap_vA2] at h
  rw [show t.e (vA2⁻¹) = (t.e vA2)⁻¹ from map_inv t.e vA2] at h
  simpa [a2] using h

private theorem conj_a2_eq_a2_or_inv {g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers t.a2 : Set G)) :
    g * t.a2 * g⁻¹ = t.a2 ∨ g * t.a2 * g⁻¹ = t.a2⁻¹ := by
  have hconj : g * t.a2 * g⁻¹ ∈ Subgroup.zpowers t.a2 :=
    (Subgroup.mem_normalizer_iff.mp hg t.a2).mp (Subgroup.mem_zpowers t.a2)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj
  have ha2pow : t.a2 ^ (3 : ℤ) = 1 := by
    simpa [zpow_natCast] using ((orderOf_a2 t) ▸ pow_orderOf_eq_one t.a2)
  have hkmod : t.a2 ^ k = t.a2 ^ (k % 3) := zpow_eq_zpow_emod k ha2pow
  have har : g * t.a2 * g⁻¹ = t.a2 ^ (k % 3) := by rw [← hk, hkmod]
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have hr3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases h : k % 3
  · have h1 : g * t.a2 * g⁻¹ = 1 := by simpa [h] using har
    have ha21 : t.a2 = 1 := by
      calc t.a2 = g⁻¹ * (g * t.a2 * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have hord : orderOf (1 : G) = 3 := by simpa [ha21] using orderOf_a2 t
    simp at hord
  · left
    simpa [h] using har
  · right
    have h2 : g * t.a2 * g⁻¹ = t.a2 ^ 2 := by simpa [h] using har
    calc g * t.a2 * g⁻¹ = t.a2 ^ 2 := h2
      _ = t.a2⁻¹ := by
        have h3 : t.a2 * t.a2 ^ 2 = 1 := by
          have h3' : t.a2 ^ 3 = 1 := by
            simpa [zpow_natCast] using (orderOf_a2 t) ▸ pow_orderOf_eq_one t.a2
          calc t.a2 * t.a2 ^ 2 = t.a2 ^ 3 := by rw [← pow_succ']
            _ = 1 := h3'
        exact eq_inv_of_mul_eq_one_right h3

private noncomputable abbrev QH : Subgroup ↥(H t) := (Q t).subgroupOf (H t)

private noncomputable abbrev D1H : Subgroup ↥(H t) := (Subgroup.zpowers t.a1).subgroupOf (H t)

private noncomputable abbrev D2H : Subgroup ↥(H t) := (Subgroup.zpowers t.d2).subgroupOf (H t)

private noncomputable abbrev N1H : Subgroup ↥(H t) :=
  Subgroup.normalClosure (D1H t : Set ↥(H t))

private noncomputable abbrev N2H : Subgroup ↥(H t) :=
  Subgroup.normalClosure (D2H t : Set ↥(H t))

private noncomputable abbrev O3'H : Subgroup ↥(H t) := CFSG.pPrimeCore 3 ↥(H t)

private noncomputable abbrev piH : ↥(H t) →* (↥(H t) ⧸ O3'H t) := QuotientGroup.mk' (O3'H t)

private theorem QH_isPGroup : IsPGroup 3 (QH t) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact (Q_isPGroup t).of_equiv (Subgroup.subgroupOfEquivOfLe (Q_le_H t)).symm

private theorem pRank_N1H_eq_one
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.Open.pRank 3 (N1H t) = 1 := by
  have hsub : (H1 t).subgroupOf (H t) = N1H t := by
    dsimp [H1]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have h := CFSG.LocalAnalysis.UniquenessCase.UCK.K31.pRank_subgroupOf_eq
    (p := 3) (by norm_num) (H1_le_H t)
  rw [hsub] at h
  rw [h] 
  exact pRank_H1_eq_one t hK332 hN1 hN3

private theorem pRank_N2H_eq_one
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.Open.pRank 3 (N2H t) = 1 := by
  have hsub : (H2 t).subgroupOf (H t) = N2H t := by
    dsimp [H2]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have h := CFSG.LocalAnalysis.UniquenessCase.UCK.K31.pRank_subgroupOf_eq
    (p := 3) (by norm_num) (H2_le_H t)
  rw [hsub] at h
  rw [h]
  exact pRank_H2_eq_one t hK332 hN1 hN3

private theorem isCyclic_QH_inf_N1H
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    IsCyclic ↥(QH t ⊓ N1H t) := by
  have hp : IsPGroup 3 ↥(QH t ⊓ N1H t) := (QH_isPGroup t).to_le inf_le_left
  refine CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one
    (p := 3) (by norm_num) (by norm_num) hp ?_
  exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (inf_le_right :
    QH t ⊓ N1H t ≤ N1H t)).trans (le_of_eq (pRank_N1H_eq_one t hK332 hN1 hN3))

private theorem isCyclic_QH_inf_N2H
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    IsCyclic ↥(QH t ⊓ N2H t) := by
  have hp : IsPGroup 3 ↥(QH t ⊓ N2H t) := (QH_isPGroup t).to_le inf_le_left
  refine CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one
    (p := 3) (by norm_num) (by norm_num) hp ?_
  exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (inf_le_right :
    QH t ⊓ N2H t ≤ N2H t)).trans (le_of_eq (pRank_N2H_eq_one t hK332 hN1 hN3))

private theorem D1H_le_N1H : D1H t ≤ N1H t := Subgroup.le_normalClosure

private theorem D2H_le_N2H : D2H t ≤ N2H t := Subgroup.le_normalClosure

private theorem D1H_le_QH : D1H t ≤ QH t := by
  intro x hx
  exact zpowers_a1_le_Q t hx

private theorem D2H_le_QH : D2H t ≤ QH t := by
  intro x hx
  exact zpowers_d2_le_Q t hx

private theorem card_D1H : Nat.card (D1H t) = 3 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_a1_le_H t)).toEquiv]
  exact card_zpowers_a1 t

private theorem card_D2H : Nat.card (D2H t) = 3 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_d2_le_H t)).toEquiv]
  exact card_zpowers_d2 t

private theorem eq_D1H_of_le_QH_inf_N1H_of_card_three
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {U : Subgroup ↥(H t)} (hU : U ≤ QH t ⊓ N1H t) (hUcard : Nat.card U = 3) :
    U = D1H t := by
  let C : Subgroup ↥(H t) := QH t ⊓ N1H t
  haveI : IsCyclic ↥C := isCyclic_QH_inf_N1H t hK332 hN1 hN3
  have hD1C : D1H t ≤ C := le_inf (D1H_le_QH t) (D1H_le_N1H t)
  have hUC : U ≤ C := hU
  have hsub : U.subgroupOf C = (D1H t).subgroupOf C := by
    apply (IsCyclic.subgroup_eq_iff_card_eq).mpr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD1C).toEquiv]
    rw [hUcard, card_D1H t]
  have hmap := congrArg (Subgroup.map C.subtype) hsub
  rwa [Subgroup.map_subgroupOf_eq_of_le hUC, Subgroup.map_subgroupOf_eq_of_le hD1C] at hmap

private theorem eq_D2H_of_le_QH_inf_N2H_of_card_three
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {U : Subgroup ↥(H t)} (hU : U ≤ QH t ⊓ N2H t) (hUcard : Nat.card U = 3) :
    U = D2H t := by
  let C : Subgroup ↥(H t) := QH t ⊓ N2H t
  haveI : IsCyclic ↥C := isCyclic_QH_inf_N2H t hK332 hN1 hN3
  have hD2C : D2H t ≤ C := le_inf (D2H_le_QH t) (D2H_le_N2H t)
  have hUC : U ≤ C := hU
  have hsub : U.subgroupOf C = (D2H t).subgroupOf C := by
    apply (IsCyclic.subgroup_eq_iff_card_eq).mpr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD2C).toEquiv]
    rw [hUcard, card_D2H t]
  have hmap := congrArg (Subgroup.map C.subtype) hsub
  rwa [Subgroup.map_subgroupOf_eq_of_le hUC, Subgroup.map_subgroupOf_eq_of_le hD2C] at hmap

private theorem QH_inf_N1H_inf_N2H_eq_bot
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    QH t ⊓ N1H t ⊓ N2H t = ⊥ := by
  by_contra hne
  let E : Subgroup ↥(H t) := QH t ⊓ N1H t ⊓ N2H t
  have hEp : IsPGroup 3 E := (QH_isPGroup t).to_le (by
    intro x hx
    exact hx.1.1)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    have hcard1 : Nat.card E = 1 := by rw [hn, hn0]; simp
    exact hne (by simpa [E] using Subgroup.eq_bot_of_card_eq E hcard1)
  have hdvd : 3 ∣ Nat.card E := by
    rw [hn]
    exact dvd_pow_self 3 (by omega)
  letI : Fintype E := Fintype.ofFinite E
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card 3 (G := E)
    (by simpa [Nat.card_eq_fintype_card] using hdvd)
  let X : Subgroup ↥(H t) := Subgroup.zpowers (x : ↥(H t))
  have hXE : X ≤ E := Subgroup.zpowers_le.mpr x.2
  have hXcard : Nat.card X = 3 := by
    change Nat.card (Subgroup.zpowers (x : ↥(H t))) = 3
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact hxord
  have hXQN1 : X ≤ QH t ⊓ N1H t := hXE.trans (by intro y hy; exact hy.1)
  have hX_eq1 : X = D1H t := eq_D1H_of_le_QH_inf_N1H_of_card_three t hK332 hN1 hN3
    hXQN1 hXcard
  have hXQN2 : X ≤ QH t ⊓ N2H t :=
    le_inf (hXE.trans (by intro y hy; exact hy.1.1)) (hXE.trans (by intro y hy; exact hy.2))
  have hX_eq2 : X = D2H t := eq_D2H_of_le_QH_inf_N2H_of_card_three t hK332 hN1 hN3
    hXQN2 hXcard
  have hD1D2 : D1H t = D2H t := hX_eq1.symm.trans hX_eq2
  have hmap : Subgroup.zpowers t.a1 = Subgroup.zpowers t.d2 := by
    have := congrArg (Subgroup.map (H t).subtype) hD1D2
    rwa [Subgroup.map_subgroupOf_eq_of_le (zpowers_a1_le_H t),
      Subgroup.map_subgroupOf_eq_of_le (zpowers_d2_le_H t)] at this
  exact zpowers_a1_ne_zpowers_d2 t hmap


private theorem QH_inf_N1H_sylow
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (QH t ⊓ N1H t) (N1H t) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : (N1H t).Normal := Subgroup.normalClosure_normal
  exact (QH_sylow_top t hN1 hN3).inf_of_le_normalizer (by simp)
    (by rw [Subgroup.normalizer_eq_top])

private theorem QH_inf_sup_N1H_sylow
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (QH t ⊓ (N1H t ⊔ O3'H t))
      (N1H t ⊔ O3'H t) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : (N1H t).Normal := Subgroup.normalClosure_normal
  haveI : (O3'H t).Normal := CFSG.pPrimeCore_normal
  exact (QH_sylow_top t hN1 hN3).inf_of_le_normalizer (by simp)
    (by rw [Subgroup.normalizer_eq_top])

private theorem factorization_card_sup_O3'H_eq (N : Subgroup ↥(H t)) [N.Normal] :
    (Nat.card ↥(N ⊔ O3'H t)).factorization 3 = (Nat.card ↥N).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : (O3'H t).Normal := CFSG.pPrimeCore_normal
  haveI : (N ⊔ O3'H t).Normal := inferInstance
  have hOcop : Nat.Coprime 3 (Nat.card (O3'H t)) := CFSG.pPrimeCore_coprime_card
  have hOnot : ¬ 3 ∣ Nat.card ↥(O3'H t) :=
    (Nat.prime_three.coprime_iff_not_dvd).mp hOcop
  have hIOnot : ¬ 3 ∣ Nat.card ↥(N ⊓ O3'H t) :=
    fun h => hOnot (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hOfac : (Nat.card ↥(O3'H t)).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hOnot
  have hIOfac : (Nat.card ↥(N ⊓ O3'H t)).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hIOnot
  have hB : O3'H t ≤ Subgroup.normalizer (N : Set ↥(H t)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
    (A := N) (B := O3'H t) hB
  have hfac := congrArg (fun n => n.factorization 3) hcard
  rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')] at hfac
  rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')] at hfac
  rw [Finsupp.add_apply] at hfac
  rw [Finsupp.add_apply] at hfac
  rw [hOfac, hIOfac, add_zero, add_zero] at hfac
  exact hfac

private theorem card_QH_inf_sup_N1H_eq
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    Nat.card ↥(QH t ⊓ (N1H t ⊔ O3'H t)) = Nat.card ↥(QH t ⊓ N1H t) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : (N1H t).Normal := Subgroup.normalClosure_normal
  haveI : (O3'H t).Normal := CFSG.pPrimeCore_normal
  haveI : (N1H t ⊔ O3'H t).Normal := inferInstance
  rw [(QH_inf_sup_N1H_sylow t hN1 hN3).card_eq,
    (QH_inf_N1H_sylow t hN1 hN3).card_eq,
    factorization_card_sup_O3'H_eq (t := t) (N := N1H t)]

private theorem QH_inf_sup_N1H_eq
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    QH t ⊓ (N1H t ⊔ O3'H t) = QH t ⊓ N1H t := by
  have hle : QH t ⊓ N1H t ≤ QH t ⊓ (N1H t ⊔ O3'H t) :=
    inf_le_inf_left _ le_sup_left
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_QH_inf_sup_N1H_eq t hN1 hN3])).symm

private theorem QH_inf_N2H_sylow
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (QH t ⊓ N2H t) (N2H t) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : (N2H t).Normal := Subgroup.normalClosure_normal
  exact (QH_sylow_top t hN1 hN3).inf_of_le_normalizer (by simp)
    (by rw [Subgroup.normalizer_eq_top])

private theorem QH_inf_sup_N2H_sylow
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 (QH t ⊓ (N2H t ⊔ O3'H t))
      (N2H t ⊔ O3'H t) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : (N2H t).Normal := Subgroup.normalClosure_normal
  haveI : (O3'H t).Normal := CFSG.pPrimeCore_normal
  exact (QH_sylow_top t hN1 hN3).inf_of_le_normalizer (by simp)
    (by rw [Subgroup.normalizer_eq_top])

private theorem card_QH_inf_sup_N2H_eq
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    Nat.card ↥(QH t ⊓ (N2H t ⊔ O3'H t)) = Nat.card ↥(QH t ⊓ N2H t) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : (N2H t).Normal := Subgroup.normalClosure_normal
  haveI : (O3'H t).Normal := CFSG.pPrimeCore_normal
  haveI : (N2H t ⊔ O3'H t).Normal := inferInstance
  rw [(QH_inf_sup_N2H_sylow t hN1 hN3).card_eq,
    (QH_inf_N2H_sylow t hN1 hN3).card_eq,
    factorization_card_sup_O3'H_eq (t := t) (N := N2H t)]

private theorem QH_inf_sup_N2H_eq
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    QH t ⊓ (N2H t ⊔ O3'H t) = QH t ⊓ N2H t := by
  have hle : QH t ⊓ N2H t ≤ QH t ⊓ (N2H t ⊔ O3'H t) :=
    inf_le_inf_left _ le_sup_left
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_QH_inf_sup_N2H_eq t hN1 hN3])).symm

private theorem comap_images_eq
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    Subgroup.comap (piH t) ((N1H t).map (piH t) ⊓ (N2H t).map (piH t)) =
      (N1H t ⊔ O3'H t) ⊓ (N2H t ⊔ O3'H t) := by
  rw [Subgroup.comap_inf, Subgroup.comap_map_eq, Subgroup.comap_map_eq]
  change (N1H t ⊔ (QuotientGroup.mk' (O3'H t)).ker) ⊓
    (N2H t ⊔ (QuotientGroup.mk' (O3'H t)).ker) =
    (N1H t ⊔ O3'H t) ⊓ (N2H t ⊔ O3'H t)
  rw [QuotientGroup.ker_mk']

private theorem W_le_O3'H
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    Subgroup.comap (piH t) ((N1H t).map (piH t) ⊓ (N2H t).map (piH t)) ≤ O3'H t := by
  let W : Subgroup ↥(H t) :=
    Subgroup.comap (piH t) ((N1H t).map (piH t) ⊓ (N2H t).map (piH t))
  have hWnorm : W.Normal := by
    have h1 : ((N1H t).map (piH t) ⊓ (N2H t).map (piH t)).Normal := by
      infer_instance
    exact Subgroup.Normal.comap h1 (piH t)
  haveI : W.Normal := hWnorm
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hQWsyl : CFSG.ABGLocalTools.IsSylowOf 3 (QH t ⊓ W) W :=
    (QH_sylow_top t hN1 hN3).inf_of_le_normalizer (by simp)
      (by rw [Subgroup.normalizer_eq_top])
  have hQWbot : QH t ⊓ W = ⊥ := by
    rw [show W = (N1H t ⊔ O3'H t) ⊓ (N2H t ⊔ O3'H t) from comap_images_eq t hN1 hN3]
    calc QH t ⊓ ((N1H t ⊔ O3'H t) ⊓ (N2H t ⊔ O3'H t))
        = (QH t ⊓ N1H t) ⊓ (N2H t ⊔ O3'H t) := by
          rw [← inf_assoc, QH_inf_sup_N1H_eq t hN1 hN3]
      _ = ((QH t ⊓ N1H t) ⊓ QH t) ⊓ (N2H t ⊔ O3'H t) := by
          rw [inf_eq_left.mpr inf_le_left]
      _ = (QH t ⊓ N1H t) ⊓ (QH t ⊓ (N2H t ⊔ O3'H t)) := by
          rw [inf_assoc]
      _ = (QH t ⊓ N1H t) ⊓ (QH t ⊓ N2H t) := by
          rw [QH_inf_sup_N2H_eq t hN1 hN3]
      _ = QH t ⊓ N1H t ⊓ N2H t := by
          rw [← inf_assoc, inf_eq_left.mpr inf_le_left]
      _ = ⊥ := QH_inf_N1H_inf_N2H_eq_bot t hK332 hN1 hN3
  have hcardQW : Nat.card ↥(QH t ⊓ W) = 1 := by rw [hQWbot]; simp
  have hfac : (Nat.card ↥W).factorization 3 = 0 := by
    have h := hQWsyl.card_eq
    rw [hcardQW] at h
    by_contra hf
    have hpos : 0 < (Nat.card ↥W).factorization 3 := Nat.pos_of_ne_zero hf
    have hge : 3 ≤ 3 ^ (Nat.card ↥W).factorization 3 := by
      calc 3 = 3 ^ 1 := by rw [pow_one]
        _ ≤ 3 ^ (Nat.card ↥W).factorization 3 :=
          Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have hnotdvd : ¬ 3 ∣ Nat.card W := by
    rcases (Nat.factorization_eq_zero_iff (Nat.card W) 3).mp hfac with h | h | h
    · exact absurd Nat.prime_three h
    · exact h
    · exact absurd h (Nat.card_pos.ne')
  have hWcop : Nat.Coprime 3 (Nat.card W) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr hnotdvd
  exact le_sSup (s := {K : Subgroup ↥(H t) | K.Normal ∧ Nat.Coprime 3 (Nat.card K)})
    ⟨hWnorm, hWcop⟩

private theorem normalClosure_maps_inf_eq_bot
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    (N1H t).map (piH t) ⊓ (N2H t).map (piH t) = ⊥ := by
  let W : Subgroup ↥(H t) :=
    Subgroup.comap (piH t) ((N1H t).map (piH t) ⊓ (N2H t).map (piH t))
  have hWle : W ≤ O3'H t := W_le_O3'H t hK332 hN1 hN3
  have hπW : Subgroup.map (piH t) W =
      (N1H t).map (piH t) ⊓ (N2H t).map (piH t) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (O3'H t)) _
  apply le_antisymm _ bot_le
  rintro y hy
  rw [← hπW] at hy
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
  change (QuotientGroup.mk' (O3'H t)) w ∈ (⊥ : Subgroup (↥(H t) ⧸ O3'H t))
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hWle hw


theorem centralizer_a2_le
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    Subgroup.centralizer ({t.a2} : Set G) ≤ c.S.M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let z : ↥(H t) := ⟨t.a2, by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rfl⟩
  have hQHrank : CFSG.Open.pRank 3 (QH t) = 3 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (QH t),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
        (Subgroup.subgroupOfEquivOfLe (Q_le_H t)),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Q t)]
    exact pRank_Q_eq_three t
  have hQcyc : ¬ IsCyclic ↥(QH t) := by
    intro hcyc
    have h1 := CFSG.LocalAnalysis.UniquenessCase.UCK.K31.pRank_top_le_one_of_isCyclic
      (p := 3) (by norm_num) hcyc
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (QH t)] at h1
    omega
  have hzQ : z ∈ QH t := a2_mem_Q t
  have hzZ : z ∈ Subgroup.center ↥(H t) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h := (Subgroup.mem_centralizer_iff.mp g.2) t.a2 (by simp)
    exact h.symm
  have hzord : orderOf z = 3 := by
    dsimp [z]
    rw [← Subgroup.orderOf_coe]
    exact orderOf_a2 t
  have hN : ∀ U : Subgroup ↥(H t), U ≤ QH t →
      (∀ u ∈ U, u ^ 3 = 1) → ¬ U ≤ Subgroup.zpowers z →
      Subgroup.normalizer (U : Set ↥(H t)) ≤ (H t ⊓ c.S.M).subgroupOf (H t) := by
    intro U hUQ hUexp hUne
    have hUmapQ : U.map (H t).subtype ≤ Q t := by
      rintro y ⟨u, hu, rfl⟩
      exact hUQ hu
    have hUexp' : ∀ u ∈ U.map (H t).subtype, u ^ 3 = 1 := by
      rintro y ⟨u, hu, rfl⟩
      simpa using congrArg Subtype.val (hUexp u hu)
    have hUne' : ¬ U.map (H t).subtype ≤ Subgroup.zpowers t.a2 := by
      intro hle
      apply hUne
      intro u hu
      have humap : (u : G) ∈ U.map (H t).subtype := Subgroup.mem_map_of_mem _ hu
      have hu2 : (u : G) ∈ Subgroup.zpowers t.a2 := hle humap
      have hzEq : Subgroup.zpowers z = (Subgroup.zpowers t.a2).subgroupOf (H t) := by
        ext w
        rw [Subgroup.mem_subgroupOf]
        constructor
        · intro hw
          rw [Subgroup.mem_zpowers_iff] at hw ⊢
          obtain ⟨k, hk⟩ := hw
          exact ⟨k, by simpa [z] using congrArg Subtype.val hk⟩
        · intro hw
          rw [Subgroup.mem_zpowers_iff] at hw ⊢
          obtain ⟨k, hk⟩ := hw
          exact ⟨k, by apply Subtype.ext; simpa [z] using hk⟩
      rw [hzEq]
      exact hu2
    have hNamb := normalizer_le_of_le_Q_of_pow_three t hN1 hN3 hUmapQ hUexp' hUne'
    intro n hn
    refine Subgroup.mem_subgroupOf.mpr ⟨n.2, ?_⟩
    have hnconj : CFSG.conjugate U n = U :=
      (CFSG.StronglyEmbedded.SteinbergBU.conjugate_eq_self_iff).mpr hn
    have hmap := congrArg (Subgroup.map (H t).subtype) hnconj
    rw [CFSG.StronglyEmbedded.map_subtype_conjugate] at hmap
    have hnmap : (n : G) ∈ Subgroup.normalizer (U.map (H t).subtype : Set G) :=
      (CFSG.StronglyEmbedded.SteinbergBU.conjugate_eq_self_iff).mp hmap
    exact hNamb ⟨hnmap, n.2⟩
  have hC1 : Subgroup.centralizer (D1H t : Set ↥(H t)) ≤
    (H t ⊓ c.S.M).subgroupOf (H t) := by
    intro n hn
    refine Subgroup.mem_subgroupOf.mpr ⟨n.2, ?_⟩
    have hnmap : (n : G) ∈ Subgroup.centralizer (Subgroup.zpowers t.a1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hn ⊢
      intro x hx
      have hxH : x ∈ H t := zpowers_a1_le_H t hx
      have hxDH : (⟨x, hxH⟩ : ↥(H t)) ∈ D1H t := hx
      exact congrArg Subtype.val (hn ⟨x, hxH⟩ hxDH)
    exact hN1 (Subgroup.centralizer_le_normalizer _ hnmap)
  have hC2 : Subgroup.centralizer (D2H t : Set ↥(H t)) ≤
    (H t ⊓ c.S.M).subgroupOf (H t) := by
    intro n hn
    refine Subgroup.mem_subgroupOf.mpr ⟨n.2, ?_⟩
    have hnmap : (n : G) ∈ Subgroup.centralizer (Subgroup.zpowers t.d2 : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hn ⊢
      intro x hx
      have hxH : x ∈ H t := zpowers_d2_le_H t hx
      have hxDH : (⟨x, hxH⟩ : ↥(H t)) ∈ D2H t := hx
      exact congrArg Subtype.val (hn ⟨x, hxH⟩ hxDH)
    have hnN : (n : G) ∈ Subgroup.normalizer (Subgroup.zpowers t.d2 : Set G) :=
      Subgroup.centralizer_le_normalizer _ hnmap
    have hUne : ¬ Subgroup.zpowers t.d2 ≤ Subgroup.zpowers t.a2 := by
      intro hle
      exact d2_not_mem_zpowers_a2 t (hle (Subgroup.mem_zpowers t.d2))
    have hpow : ∀ u ∈ Subgroup.zpowers t.d2, u ^ 3 = 1 := fun u hu => by
      rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_d2 t]
      exact orderOf_dvd_of_mem_zpowers hu
    exact normalizer_le_of_le_Q_of_pow_three t hN1 hN3 (zpowers_d2_le_Q t) hpow hUne
      ⟨hnN, n.2⟩
  have hKtop : (H t ⊓ c.S.M).subgroupOf (H t) = ⊤ :=
    CFSG.GroupTheory.eq_top_of_abelianSylowThree (X := ↥(H t))
      (K := (H t ⊓ c.S.M).subgroupOf (H t)) (Q := QH t)
      (D₁ := D1H t) (D₂ := D2H t) (z := z)
      (by
        intro o ho
        refine Subgroup.mem_subgroupOf.mpr ⟨o.2, ?_⟩
        exact pPrimeCore_H_le_M t hN1 hN3 (Subgroup.mem_map_of_mem (H t).subtype ho))
      (by
        intro q hq
        exact Subgroup.mem_subgroupOf.mpr ⟨q.2, Q_le_M t hq⟩)
      (QH_sylow_top t hN1 hN3) (QH_comm t) hQcyc hzQ hzZ hzord hN
      (D1H_le_QH t) (D2H_le_QH t) hC1 hC2
      (normalClosure_maps_inf_eq_bot t hK332 hN1 hN3)
  intro x hx
  have hxK : (⟨x, hx⟩ : ↥(H t)) ∈ (H t ⊓ c.S.M).subgroupOf (H t) := by
    rw [hKtop]
    trivial
  exact (Subgroup.mem_subgroupOf.mp hxK).2


theorem normalizer_a2_le
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb)
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    Subgroup.normalizer ((Subgroup.zpowers t.a2 : Subgroup G) : Set G) ≤ c.S.M := by
  have hHle : H t ≤ c.S.M := centralizer_a2_le t hK332 hN1 hN3
  obtain ⟨n, hnL, hnconj⟩ := exists_conj_a2_inv t
  intro g hg
  rcases conj_a2_eq_a2_or_inv t hg with h | h
  · have hgH : g ∈ H t := by
      rw [H, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      calc t.a2 * g = (g * t.a2 * g⁻¹) * g := by rw [h]
        _ = g * t.a2 := by group
    exact hHle hgH
  · have hgnH : g * n ∈ H t := by
      rw [H, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hconj_gn : (g * n) * t.a2 * (g * n)⁻¹ = t.a2 := by
        calc (g * n) * t.a2 * (g * n)⁻¹ = g * (n * t.a2 * n⁻¹) * g⁻¹ := by group
          _ = g * t.a2⁻¹ * g⁻¹ := by rw [hnconj]
          _ = (g * t.a2 * g⁻¹)⁻¹ := by group
          _ = (t.a2⁻¹)⁻¹ := by rw [h]
          _ = t.a2 := by group
      calc t.a2 * (g * n) = ((g * n) * t.a2 * (g * n)⁻¹) * (g * n) := by rw [hconj_gn]
        _ = (g * n) * t.a2 := by group
    have hMgn : g * n ∈ c.S.M := hHle hgnH
    have hMn : n ∈ c.S.M := c.hyp81.1 hnL
    have heq : g = (g * n) * n⁻¹ := by group
    rw [heq]
    exact c.S.M.mul_mem hMgn (c.S.M.inv_mem hMn)

end Case811L4
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
