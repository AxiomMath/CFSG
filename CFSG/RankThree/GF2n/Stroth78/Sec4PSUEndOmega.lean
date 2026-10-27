module

public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.RankThree.GF2n.Tim79aCitedInvol

import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaLocal
import CFSG.Quasithin.Background.BlueprintB2Frattini
import CFSG.Quasithin.Background.E2SeventeenSolv
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndAut
import CFSG.Sporadic.Recognition.LyonsAmalgamExtAut

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.Fischer.Classification.Unitary

namespace Sec4PSUEnd

private theorem inf_centralizer_eq_bot {Y : Type} [Group Y] {X : Subgroup Y}
    (hZ : Subgroup.center ↥X = ⊥) : X ⊓ Subgroup.centralizer (X : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  have hgZ : (⟨g, hg.1⟩ : ↥X) ∈ Subgroup.center ↥X :=
    Subgroup.mem_center_iff.mpr fun h => Subtype.ext (Subgroup.mem_centralizer_iff.mp hg.2 h h.2)
  rw [hZ, Subgroup.mem_bot] at hgZ
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hgZ)

private theorem notMem_of_conj_eq_inv {Y : Type} [Group Y] {X : Subgroup Y} {ρ : Y}
    (hρ : orderOf ρ = 3) (hρC : Subgroup.zpowers ρ = Subgroup.centralizer (X : Set Y)) {l : Y}
    (hlρ : l * ρ * l⁻¹ = ρ⁻¹) : l ∉ X := by
  intro hl
  have hρX : ρ ∈ Subgroup.centralizer (X : Set Y) := hρC ▸ Subgroup.mem_zpowers ρ
  rw [Subgroup.mem_centralizer_iff.mp hρX l hl, mul_inv_cancel_right] at hlρ
  have h2 : ρ ^ 2 = 1 := by rw [sq]; exact mul_eq_one_iff_eq_inv.mpr hlρ
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hρ] at h3
  exact absurd h3 (by norm_num)

private theorem sup_zpowers_inf_centralizer_eq_bot {Y : Type} [Group Y] {X : Subgroup Y}
    [X.Normal] (hZ : Subgroup.center ↥X = ⊥) {ρ : Y} (hρ : orderOf ρ = 3)
    (hρC : Subgroup.zpowers ρ = Subgroup.centralizer (X : Set Y)) {l : Y} (hl2 : l * l = 1) :
    (X ⊔ Subgroup.zpowers l) ⊓ Subgroup.centralizer (X : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_inf, ← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hc
  obtain ⟨⟨x, hx, y, hy, rfl⟩, hcC⟩ := hc
  have hyy : y * y = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hl2, one_zpow]
  have hcc : x * y * (x * y) ∈ X ⊓ Subgroup.centralizer (X : Set Y) := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mul_mem _ hcC hcC⟩
    have h : x * y * (x * y) = x * (y * x * y⁻¹) * (y * y) := by group
    rw [h, hyy, mul_one]
    exact X.mul_mem hx (Subgroup.Normal.conj_mem inferInstance x hx y)
  rw [inf_centralizer_eq_bot hZ, Subgroup.mem_bot] at hcc
  rw [← hρC] at hcC
  have hc3 : (x * y) ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hρ ▸ orderOf_dvd_of_mem_zpowers hcC)
  rw [pow_three, hcc, mul_one] at hc3
  exact Subgroup.mem_bot.mpr hc3

private theorem ne_sup_zpowers {Y : Type} [Group Y] {X : Subgroup Y} {ρ : Y}
    (hρ : orderOf ρ = 3) (hρC : Subgroup.zpowers ρ = Subgroup.centralizer (X : Set Y)) {l : Y}
    (hlρ : l * ρ * l⁻¹ = ρ⁻¹) : X ≠ X ⊔ Subgroup.zpowers l := by
  intro h
  apply notMem_of_conj_eq_inv hρ hρC hlρ
  rw [h]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers l)

private theorem bijective_conjNormal_sup {Y : Type} [Group Y] [Finite Y] {X : Subgroup Y}
    [X.Normal] (φ : ↥X ≃* U2 4) (hZ : Subgroup.center ↥X = ⊥) {ρ : Y} (hρ : orderOf ρ = 3)
    (hρC : Subgroup.zpowers ρ = Subgroup.centralizer (X : Set Y)) {l : Y} (hl2 : l * l = 1)
    (hlρ : l * ρ * l⁻¹ = ρ⁻¹) :
    Function.Bijective ((MulAut.conjNormal (H := X)).comp (X ⊔ Subgroup.zpowers l).subtype) :=
  bijective_conjNormal_comp_subtype φ le_sup_left (ne_sup_zpowers hρ hρC hlρ)
    (sup_zpowers_inf_centralizer_eq_bot hZ hρ hρC hl2)

private theorem sup_centralizer_eq_top {Y : Type} [Group Y] {X : Subgroup Y} [X.Normal]
    {K : Subgroup Y} (hK : Function.Surjective ((MulAut.conjNormal (H := X)).comp K.subtype)) :
    K ⊔ Subgroup.centralizer (X : Set Y) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨k, hk⟩ := hK (MulAut.conjNormal y)
  have hc : (k : Y)⁻¹ * y ∈ Subgroup.centralizer (X : Set Y) := by
    apply CFSG.Quasithin.BlueprintB2.mem_centralizer_of_conjNormal_eq_one
    change MulAut.conjNormal (k : Y) = MulAut.conjNormal y at hk
    rw [map_mul, map_inv, hk, inv_mul_cancel]
  rw [← mul_inv_cancel_left (k : Y) y]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hc)

private theorem commutator_eq_subgroupOf {Y : Type} [Group Y] {X : Subgroup Y} [X.Normal]
    {K : Subgroup Y} (hXK : X ≤ K) (hXX : ⁅X, X⁆ = X) (h2 : X.relIndex K = 2) :
    commutator ↥K = X.subgroupOf K := by
  refine le_antisymm ?_ ?_
  · have : IsCyclic (↥K ⧸ X.subgroupOf K) :=
      isCyclic_of_prime_card (α := ↥K ⧸ X.subgroupOf K) (p := 2) h2
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  · rw [← Subgroup.map_subtype_le_map_subtype, Subgroup.map_subgroupOf_eq_of_le hXK,
      Subgroup.map_subtype_commutator]
    exact hXX.ge.trans (Subgroup.commutator_mono hXK hXK)

private theorem nonempty_mulEquiv_commutator {Y : Type} [Group Y] {X K : Subgroup Y}
    (hXK : X ≤ K) (hc : commutator ↥K = X.subgroupOf K) {G : Type*} [Group G] (e : ↥K ≃* G) :
    Nonempty (↥X ≃* ↥(commutator G)) := by
  have hmap : (commutator ↥K).map (e : ↥K →* G) = commutator G := by
    rw [map_commutator_eq, MulEquiv.range_eq_top, commutator_def]
  exact ⟨(Subgroup.subgroupOfEquivOfLe hXK).symm.trans <| (MulEquiv.subgroupCongr hc.symm).trans <|
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)⟩

private theorem index_eq_six {Y : Type} [Group Y] {X : Subgroup Y} [X.Normal]
    (φ : ↥X ≃* U2 4) {ρ : Y} (hρ : orderOf ρ = 3)
    (hρC : Subgroup.zpowers ρ = Subgroup.centralizer (X : Set Y))
    (hsurj : Function.Surjective (MulAut.conjNormal (H := X))) : X.index = 6 := by
  have hY : Nat.card Y = 51840 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAut.conjNormal (H := X)).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
      card_mulAut_of_mulEquiv_U2 φ,
      CFSG.Sporadic.Recognition.LyonsSims.ker_conjNormal_eq_centralizer, ← hρC, Nat.card_zpowers,
      hρ]
  have h := X.card_mul_index
  rw [(Nat.card_congr φ.toEquiv).trans CFSG.GH74.Exceptional.card_U2_four, hY] at h
  omega

theorem isOmegaMinusSixByThree_of_mulEquiv_U2 {Y : Type} [Group Y] [Finite Y]
    {X : Subgroup Y} [X.Normal] (φ : ↥X ≃* U2 4) (hXX : ⁅X, X⁆ = X)
    (hZ : Subgroup.center ↥X = ⊥) {ρ : Y} (hρ : orderOf ρ = 3)
    (hρC : Subgroup.zpowers ρ = Subgroup.centralizer (X : Set Y)) {l : Y} (hl2 : l * l = 1)
    (hlρ : l * ρ * l⁻¹ = ρ⁻¹) :
    IsOmegaMinusSixByThree Y := by
  have hl1 : l ≠ 1 := fun h => notMem_of_conj_eq_inv hρ hρC hlρ (h ▸ X.one_mem)
  have hbij := bijective_conjNormal_sup φ hZ hρ hρC hl2 hlρ
  obtain ⟨ψ⟩ := nonempty_mulAut_mulEquiv_oMinusSixTwo φ
  let e := (MulEquiv.ofBijective _ hbij).trans ψ
  have h2 : X.relIndex (X ⊔ Subgroup.zpowers l) = 2 := by
    have h := X.relIndex_mul_card (X ⊔ Subgroup.zpowers l)
    rw [inf_of_le_left le_sup_left, (Nat.card_congr φ.toEquiv).trans
      CFSG.GH74.Exceptional.card_U2_four, Nat.card_congr (Equiv.ofBijective _ hbij),
      card_mulAut_of_mulEquiv_U2 φ] at h
    omega
  refine ⟨X, Subgroup.zpowers ρ, l, fun a ha c hc => ?_, ?_,
    nonempty_mulEquiv_commutator le_sup_left (commutator_eq_subgroupOf le_sup_left hXX h2) e,
    ?_, ?_, ⟨e⟩, CFSG.Quasithin.E2.nonempty_zpowers_sup_mulEquiv_perm_three hρ hl2 hl1 hlρ⟩
  · rw [hρC] at hc
    exact Subgroup.mem_centralizer_iff.mp hc a ha
  · rw [hρC]
    exact inf_centralizer_eq_bot hZ
  · rw [Nat.card_zpowers, hρ]
  · rw [sup_right_comm, hρC]
    exact sup_centralizer_eq_top hbij.2

theorem commutator_commutator_le_of_mulEquiv_U2 {Y : Type} [Group Y] [Finite Y]
    {X : Subgroup Y} [X.Normal] (φ : ↥X ≃* U2 4) (hZ : Subgroup.center ↥X = ⊥) {ρ : Y}
    (hρ : orderOf ρ = 3) (hρC : Subgroup.zpowers ρ = Subgroup.centralizer (X : Set Y)) {l : Y}
    (hl2 : l * l = 1) (hlρ : l * ρ * l⁻¹ = ρ⁻¹) :
    ⁅commutator Y, commutator Y⁆ ≤ X := by
  have hsurj : Function.Surjective (MulAut.conjNormal (H := X)) := fun a =>
    let ⟨k, hk⟩ := (bijective_conjNormal_sup φ hZ hρ hρC hl2 hlρ).2 a
    ⟨k, hk⟩
  have h6 : X.relIndex ⊤ = 6 := by
    rw [Subgroup.relIndex_top_right]
    exact index_eq_six φ hρ hρC hsurj
  rw [commutator_def]
  exact CFSG.EvenSmallLie.UnitarySix.Yamada.commutator_commutator_le_of_relIndex_dvd_six
    (H := ⊤) le_top inferInstance (dvd_of_eq h6) le_top

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
