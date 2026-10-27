module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof155P

private theorem le_pPrimeCoreOf_of_img148_eq_bot {A M X : Subgroup G} [(ker148 A M).Normal]
    (hXM : X ≤ M) (h : img148 A M X = ⊥) : X ≤ pPrimeCoreOf 3 M := by
  have hle : X.subgroupOf (M ⊔ A) ≤ (QuotientGroup.mk' (ker148 A M)).ker := by
    rw [← Subgroup.map_eq_bot_iff]
    exact h
  intro x hx
  have hx' : (⟨x, Subgroup.mem_sup_left (hXM hx)⟩ : ↥(M ⊔ A)) ∈
      X.subgroupOf (M ⊔ A) := Subgroup.mem_subgroupOf.mpr hx
  have hxker : (⟨x, Subgroup.mem_sup_left (hXM hx)⟩ : ↥(M ⊔ A)) ∈
      (QuotientGroup.mk' (ker148 A M)).ker := hle hx'
  rw [QuotientGroup.ker_mk', ker148, Subgroup.mem_subgroupOf] at hxker
  exact hxker

private theorem nonempty_quot_equiv_img148 {A M W : Subgroup G} [(ker148 A M).Normal]
    (hWM : W ≤ M) [((pPrimeCoreOf 3 M).subgroupOf W).Normal] :
    Nonempty (↥W ⧸ (pPrimeCoreOf 3 M).subgroupOf W ≃* ↥(img148 A M W)) := by
  let ψ : ↥W →* ↥(M ⊔ A) ⧸ ker148 A M :=
    (QuotientGroup.mk' (ker148 A M)).comp (Subgroup.inclusion (hWM.trans le_sup_left))
  have hrange : ψ.range = img148 A M W := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : ψ.ker = (pPrimeCoreOf 3 M).subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (ker148 A M)
      (Subgroup.inclusion (hWM.trans le_sup_left) w) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ker148, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem img148_ne_bot_of_not_le {A M W : Subgroup G} [(ker148 A M).Normal] (hWM : W ≤ M)
    (hW : ¬ W ≤ pPrimeCoreOf 3 M) : img148 A M W ≠ ⊥ := by
  intro hbot
  exact hW (le_pPrimeCoreOf_of_img148_eq_bot hWM hbot)

theorem card_img148_eq_index {A M W : Subgroup G} [(ker148 A M).Normal] (hWM : W ≤ M) :
    Nat.card (img148 A M W) = ((pPrimeCoreOf 3 M).subgroupOf W).index := by
  haveI : ((pPrimeCoreOf 3 M).subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hWM.trans (le_normalizer_pPrimeCoreOf 3 M))
  obtain ⟨e⟩ := nonempty_quot_equiv_img148 (A := A) (M := M) (W := W) hWM
  rw [← Nat.card_congr e.toEquiv]
  exact (Subgroup.index_eq_card _).symm

theorem nonempty_theta_quot_equiv_img148 {A M W : Subgroup G} [(ker148 A M).Normal]
    (hWM : W ≤ M) (hθ : inSubgroup (aschbacherSolvableCore 3) W = W ⊓ pPrimeCoreOf 3 M) :
    Nonempty (↥W ⧸ aschbacherSolvableCore 3 ↥W ≃* ↥(img148 A M W)) := by
  haveI : ((pPrimeCoreOf 3 M).subgroupOf W).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hWM.trans (le_normalizer_pPrimeCoreOf 3 M))
  obtain ⟨e⟩ := nonempty_quot_equiv_img148 (A := A) (M := M) (W := W) hWM
  have hker : (pPrimeCoreOf 3 M).subgroupOf W = aschbacherSolvableCore 3 ↥W := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype]
    exact (hθ.trans (inf_comm _ _)).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans e⟩

theorem pPrimeCoreOf_deltaZero_le {A M : Subgroup G} {LB : Subgroup G → Subgroup G}
    [(ker148 A M).Normal]
    (hN : ∀ N : Subgroup ↥(img148 A M (deltaZero A LB M)), N.Normal → ¬ 3 ∣ Nat.card N →
      N = ⊥) :
    pPrimeCoreOf 3 (deltaZero A LB M) ≤ pPrimeCoreOf 3 M := by
  set O : Subgroup G := pPrimeCoreOf 3 (deltaZero A LB M) with hOdef
  have hOD : O ≤ deltaZero A LB M := by
    rw [hOdef]
    exact pPrimeCoreOf_le 3 _
  have hDM : deltaZero A LB M ≤ M := deltaZero_le M
  have hODM : O ≤ M := hOD.trans hDM
  have hmono : img148 A M O ≤ img148 A M (deltaZero A LB M) := img148_mono hOD
  have hnorm : img148 A M (deltaZero A LB M) ≤
      Subgroup.normalizer (img148 A M O : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
    img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 (deltaZero A LB M))
  have hnormal : ((img148 A M O).subgroupOf (img148 A M (deltaZero A LB M))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hcard : Nat.card ((img148 A M O).subgroupOf (img148 A M (deltaZero A LB M))) =
      Nat.card (img148 A M O) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmono).toEquiv
  have hindex : Nat.card (img148 A M O) = ((pPrimeCoreOf 3 M).subgroupOf O).index :=
    card_img148_eq_index (A := A) (M := M) (W := O) hODM
  have hdiv : Nat.card (img148 A M O) ∣ Nat.card O := by
    rw [hindex]
    exact Subgroup.index_dvd_card _
  have hcop : Nat.Coprime 3 (Nat.card O) := by
    rw [hOdef]
    exact coprime_card_pPrimeCoreOf 3 (deltaZero A LB M)
  have h3' : ¬ 3 ∣ Nat.card (img148 A M O) := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop (h3.trans hdiv)
  have hbot : (img148 A M O).subgroupOf (img148 A M (deltaZero A LB M)) = ⊥ := by
    refine hN _ hnormal ?_
    rwa [hcard]
  have himg : img148 A M O = ⊥ := by
    have hdisj : Disjoint (img148 A M O) (img148 A M (deltaZero A LB M)) :=
      Subgroup.subgroupOf_eq_bot.mp hbot
    exact disjoint_self.mp (hdisj.mono_right hmono)
  exact le_pPrimeCoreOf_of_img148_eq_bot hODM himg

theorem commutator_mem_of_dec {A M : Subgroup G} {LB : Subgroup G → Subgroup G} {d : G}
    (hdec : deltaZero A LB M = pPrimeCoreOf 3 (deltaZero A LB M) ⊔
      deltaZero A LB (M ⊓ Subgroup.centralizer ({d} : Set G)))
    (hO : pPrimeCoreOf 3 (deltaZero A LB M) ≤ pPrimeCoreOf 3 M)
    (hd : d ∈ Subgroup.normalizer (pPrimeCoreOf 3 M : Set G)) :
    ∀ y ∈ deltaZero A LB M, ⁅y, d⁆ ∈ pPrimeCoreOf 3 M := by
  set O : Subgroup G := pPrimeCoreOf 3 M with hOdef
  let H : Subgroup G :=
    { carrier := {y : G | y ∈ Subgroup.normalizer (O : Set G) ∧ ⁅y, d⁆ ∈ O}
      one_mem' := by
        refine ⟨Subgroup.one_mem _, ?_⟩
        simp [commutatorElement_def]
      mul_mem' := by
        rintro y z ⟨hyN, hy⟩ ⟨hzN, hz⟩
        refine ⟨Subgroup.mul_mem (Subgroup.normalizer (O : Set G)) hyN hzN, ?_⟩
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN _).mp hz) hy
      inv_mem' := by
        rintro y ⟨hyN, hy⟩
        refine ⟨Subgroup.inv_mem (Subgroup.normalizer (O : Set G)) hyN, ?_⟩
        rw [commutatorElement_inv_left]
        have hdy : ⁅d, y⁆ ∈ O := by
          rw [← commutatorElement_inv]
          exact O.inv_mem hy
        have hmem := (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem (Subgroup.normalizer (O : Set G)) hyN) _).mp hdy
        simpa using hmem }
  have hmemH : ∀ y : G, y ∈ H ↔
      y ∈ Subgroup.normalizer (O : Set G) ∧ ⁅y, d⁆ ∈ O := fun y => Iff.rfl
  have hO_le_H : O ≤ H := by
    intro y hy
    have hyM : y ∈ M := pPrimeCoreOf_le 3 M (hOdef ▸ hy)
    rw [hmemH]
    refine ⟨le_normalizer_pPrimeCoreOf 3 M hyM, ?_⟩
    have hdy : d * y⁻¹ * d⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp hd _).mp (O.inv_mem hy)
    have hcomm : ⁅y, d⁆ = y * (d * y⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    exact O.mul_mem hy hdy
  have hDc_le_H : deltaZero A LB (M ⊓ Subgroup.centralizer ({d} : Set G)) ≤ H := by
    intro y hy
    have hyMc : y ∈ M ⊓ Subgroup.centralizer ({d} : Set G) :=
      deltaZero_le (M ⊓ Subgroup.centralizer ({d} : Set G)) hy
    rw [hmemH]
    refine ⟨le_normalizer_pPrimeCoreOf 3 M hyMc.1, ?_⟩
    have hc : ⁅y, d⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hyMc.2) d (Set.mem_singleton d)
    rw [hc]
    exact O.one_mem
  have hD_le_H : deltaZero A LB M ≤ H := by
    rw [hdec]
    exact sup_le (hO.trans hO_le_H) hDc_le_H
  intro y hy
  exact ((hmemH y).mp (hD_le_H hy)).2

end Proof155P

end CFSG.RankThree.PartTwo.Sec15
